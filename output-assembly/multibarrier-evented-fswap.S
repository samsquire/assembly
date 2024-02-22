
multibarrier-evented-fswap:     file format elf64-x86-64


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
  if (a > b) { return a; }
  if (b > a) { return b; }
  return a;
}

void fatal_error(const char *syscall) {
    25c0:	f3 0f 1e fa          	endbr64
    25c4:	50                   	push   %rax
    25c5:	58                   	pop    %rax
    25c6:	50                   	push   %rax
    perror(syscall);
    25c7:	e8 34 ff ff ff       	call   2500 <perror@plt>
    exit(1);
    25cc:	bf 01 00 00 00       	mov    $0x1,%edi
    25d1:	e8 3a ff ff ff       	call   2510 <exit@plt>

00000000000025d6 <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    25d6:	48 8d 3d 49 5c 00 00 	lea    0x5c49(%rip),%rdi        # 8226 <_IO_stdin_used+0x226>
    25dd:	e8 de ff ff ff       	call   25c0 <fatal_error>

00000000000025e2 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    25e2:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
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
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    2616:	48 8d 3d d9 5b 00 00 	lea    0x5bd9(%rip),%rdi        # 81f6 <_IO_stdin_used+0x1f6>
    261d:	e8 9e ff ff ff       	call   25c0 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    2622:	48 8d 3d 51 5b 00 00 	lea    0x5b51(%rip),%rdi        # 817a <_IO_stdin_used+0x17a>
    2629:	e8 92 ff ff ff       	call   25c0 <fatal_error>
    fatal_error("listen()");
    262e:	48 8d 3d 65 5b 00 00 	lea    0x5b65(%rip),%rdi        # 819a <_IO_stdin_used+0x19a>
    2635:	e8 86 ff ff ff       	call   25c0 <fatal_error>
    263a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2642:	0f 0b                	ud2
    2644:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    264c:	0f 0b                	ud2
      fatal_error("socket()");
    264e:	48 8d 3d 1c 5b 00 00 	lea    0x5b1c(%rip),%rdi        # 8171 <_IO_stdin_used+0x171>
    2655:	e8 66 ff ff ff       	call   25c0 <fatal_error>
      fatal_error("bind()");
    265a:	48 8d 3d 32 5b 00 00 	lea    0x5b32(%rip),%rdi        # 8193 <_IO_stdin_used+0x193>
    2661:	e8 5a ff ff ff       	call   25c0 <fatal_error>
    2666:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000002670 <main>:
    }


  return 0;
}
int main() {
    2670:	f3 0f 1e fa          	endbr64
    2674:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2676:	48 8d 3d 1b 60 00 00 	lea    0x601b(%rip),%rdi        # 8698 <_IO_stdin_used+0x698>
    267d:	41 56                	push   %r14
    267f:	41 55                	push   %r13
    2681:	41 54                	push   %r12
    2683:	55                   	push   %rbp
    2684:	48 8d 2d f1 5c 00 00 	lea    0x5cf1(%rip),%rbp        # 837c <_IO_stdin_used+0x37c>
    268b:	53                   	push   %rbx
    268c:	48 81 ec f8 00 00 00 	sub    $0xf8,%rsp
    2693:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    269c:	48 89 84 24 e8 00 00 00 	mov    %rax,0xe8(%rsp)
    26a4:	48 8d 05 85 1e 00 00 	lea    0x1e85(%rip),%rax        # 4530 <barriered_reset>
    26ab:	66 48 0f 6e f0       	movq   %rax,%xmm6
    26b0:	0f 16 35 a1 85 00 00 	movhps 0x85a1(%rip),%xmm6        # ac58 <__do_global_dtors_aux_fini_array_entry+0x8>
    26b7:	0f 29 b4 24 a0 00 00 00 	movaps %xmm6,0xa0(%rsp)
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
    27b7:	48 8d 35 42 5f 00 00 	lea    0x5f42(%rip),%rsi        # 8700 <_IO_stdin_used+0x700>
    27be:	31 c0                	xor    %eax,%eax
    27c0:	bf 01 00 00 00       	mov    $0x1,%edi
    27c5:	e8 e6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27ca:	ba 01 00 00 00       	mov    $0x1,%edx
    27cf:	48 8d 35 5a 5f 00 00 	lea    0x5f5a(%rip),%rsi        # 8730 <_IO_stdin_used+0x730>
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
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    281e:	be 18 00 00 00       	mov    $0x18,%esi
    2823:	bf 03 00 00 00       	mov    $0x3,%edi
    2828:	e8 d3 fb ff ff       	call   2400 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    282d:	be e0 00 00 00       	mov    $0xe0,%esi
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
    2832:	45 31 f6             	xor    %r14d,%r14d
  int cc = 0; 
    2835:	45 31 ed             	xor    %r13d,%r13d
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2838:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    283d:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2845:	e8 b6 fb ff ff       	call   2400 <calloc@plt>
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    284a:	be 28 00 00 00       	mov    $0x28,%esi
    284f:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2854:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    2859:	e8 a2 fb ff ff       	call   2400 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    285e:	be 28 00 00 00       	mov    $0x28,%esi
    2863:	bf 64 00 00 00       	mov    $0x64,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    2868:	48 89 84 24 c0 00 00 00 	mov    %rax,0xc0(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    2870:	e8 8b fb ff ff       	call   2400 <calloc@plt>
    2875:	48 89 84 24 c8 00 00 00 	mov    %rax,0xc8(%rsp)
  for (int x = 0 ; x < total_threads; x++) {
    287d:	49 89 c7             	mov    %rax,%r15
int main() {
    2880:	4d 89 fc             	mov    %r15,%r12
    for (int y = 0 ; y < total_threads; y++) {
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
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    28a5:	4c 89 e7             	mov    %r12,%rdi
    28a8:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    28aa:	49 83 c4 28          	add    $0x28,%r12
      pthread_mutex_init(&swapmutex[cc++], NULL);
    28ae:	e8 cd fc ff ff       	call   2580 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    28b3:	83 fb 0a             	cmp    $0xa,%ebx
    28b6:	75 d0                	jne    2888 <main+0x218>
    28b8:	41 83 c5 0a          	add    $0xa,%r13d
  for (int x = 0 ; x < total_threads; x++) {
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
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    28fd:	be 10 00 00 00       	mov    $0x10,%esi
    2902:	bf 0c 00 00 00       	mov    $0xc,%edi
    2907:	e8 f4 fa ff ff       	call   2400 <calloc@plt>
    290c:	48 89 84 24 b0 00 00 00 	mov    %rax,0xb0(%rsp)
    2914:	48 89 c5             	mov    %rax,%rbp
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2917:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    291e:	49 89 c6             	mov    %rax,%r14
    buffers[x].count = buffer_size;
    2921:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2928:	be 00 01 00 00       	mov    $0x100,%esi
    292d:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2932:	49 83 c6 10          	add    $0x10,%r14
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2936:	e8 c5 fa ff ff       	call   2400 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    293b:	be 20 00 00 00       	mov    $0x20,%esi
    2940:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2945:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    2949:	49 89 c4             	mov    %rax,%r12
      buffers[x].buffer[y].available = 0;
    294c:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2956:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2960:	e8 9b fa ff ff       	call   2400 <calloc@plt>
    2965:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
  for (int x = 0 ; x < buffers_required; x++) {
    296d:	4c 39 f3             	cmp    %r14,%rbx
    2970:	75 af                	jne    2921 <main+0x2b1>
    2972:	48 8b b4 24 90 00 00 00 	mov    0x90(%rsp),%rsi
    297a:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  int swap = 0;
    297f:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
  int dataid = 0;
    2987:	45 31 e4             	xor    %r12d,%r12d
  int cur_buffer = 0;
    298a:	c7 44 24 74 00 00 00 00 	movl   $0x0,0x74(%rsp)
    2992:	45 89 e7             	mov    %r12d,%r15d
    2995:	48 89 b4 24 80 00 00 00 	mov    %rsi,0x80(%rsp)
    299d:	48 89 9c 24 98 00 00 00 	mov    %rbx,0x98(%rsp)
  int curcpu = 0;
    29a5:	c7 44 24 70 00 00 00 00 	movl   $0x0,0x70(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    29ad:	48 63 44 24 74       	movslq 0x74(%rsp),%rax
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    29b2:	49 89 d9             	mov    %rbx,%r9
    29b5:	45 89 e6             	mov    %r12d,%r14d
    29b8:	48 89 9c 24 d0 00 00 00 	mov    %rbx,0xd0(%rsp)
    29c0:	48 89 b4 24 b8 00 00 00 	mov    %rsi,0xb8(%rsp)
    29c8:	48 c1 e0 04          	shl    $0x4,%rax
    29cc:	48 89 ac 24 d8 00 00 00 	mov    %rbp,0xd8(%rsp)
    29d4:	48 01 e8             	add    %rbp,%rax
    29d7:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    29dc:	43 8d 04 24          	lea    (%r12,%r12,1),%eax
    29e0:	8d 78 01             	lea    0x1(%rax),%edi
    29e3:	83 c0 03             	add    $0x3,%eax
    29e6:	89 7c 24 18          	mov    %edi,0x18(%rsp)
    29ea:	89 84 24 8c 00 00 00 	mov    %eax,0x8c(%rsp)
    29f1:	44 8b 64 24 18       	mov    0x18(%rsp),%r12d
    29f6:	44 89 f2             	mov    %r14d,%edx
    29f9:	bf 01 00 00 00       	mov    $0x1,%edi
    29fe:	31 c0                	xor    %eax,%eax
    2a00:	48 8d 35 51 5d 00 00 	lea    0x5d51(%rip),%rsi        # 8758 <_IO_stdin_used+0x758>
    2a07:	4c 89 0c 24          	mov    %r9,(%rsp)
      int x = (k * threads_per_group) + d;
    2a0b:	45 8d 44 24 ff       	lea    -0x1(%r12),%r8d
    2a10:	44 89 c1             	mov    %r8d,%ecx
    2a13:	44 89 44 24 10       	mov    %r8d,0x10(%rsp)
    2a18:	45 89 c5             	mov    %r8d,%r13d
    2a1b:	e8 90 fa ff ff       	call   24b0 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a20:	be 08 00 00 00       	mov    $0x8,%esi
    2a25:	bf 02 00 00 00       	mov    $0x2,%edi
    2a2a:	e8 d1 f9 ff ff       	call   2400 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a2f:	be 80 00 00 00       	mov    $0x80,%esi
    2a34:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a39:	48 89 c3             	mov    %rax,%rbx
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a3c:	e8 bf f9 ff ff       	call   2400 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2a41:	45 89 e8             	mov    %r13d,%r8d
    2a44:	4c 8b 0c 24          	mov    (%rsp),%r9
    2a48:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a4c:	48 89 c5             	mov    %rax,%rbp
      if (x % 2 == 1) {
    2a4f:	44 89 44 24 50       	mov    %r8d,0x50(%rsp)
    2a54:	0f 84 13 11 00 00    	je     3b6d <main+0x14fd>
        other = abs(x - 1) % total_threads;
    2a5a:	41 8d 54 24 fe       	lea    -0x2(%r12),%edx
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    2a5f:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2a64:	48 8d 04 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rax
        other = abs(x - 1) % total_threads;
    2a6c:	49 89 d5             	mov    %rdx,%r13
        my_thread_data[0] = &thread_data[other]; 
    2a6f:	48 29 d0             	sub    %rdx,%rax
        my_thread_data[1] = &thread_data[x]; 
    2a72:	4c 89 ca             	mov    %r9,%rdx
        my_thread_data[0] = &thread_data[other]; 
    2a75:	48 c1 e0 05          	shl    $0x5,%rax
    2a79:	48 01 f8             	add    %rdi,%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2a7c:	48 8d 7b 08          	lea    0x8(%rbx),%rdi
    2a80:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    2a85:	48 8b bc 24 b8 00 00 00 	mov    0xb8(%rsp),%rdi
    2a8d:	48 89 03             	mov    %rax,(%rbx)
    2a90:	44 89 e9             	mov    %r13d,%ecx
    2a93:	48 8d 35 ee 5c 00 00 	lea    0x5cee(%rip),%rsi        # 8788 <_IO_stdin_used+0x788>
        thread_data[x].thread_index = 1;
    2a9a:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2a9e:	31 c0                	xor    %eax,%eax
        thread_data[x].protected_state = &protected_state[k];
    2aa0:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2aa4:	bf 01 00 00 00       	mov    $0x1,%edi
    2aa9:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    2aad:	8b 54 24 10          	mov    0x10(%rsp),%edx
    2ab1:	4c 89 0c 24          	mov    %r9,(%rsp)
    2ab5:	e8 f6 f9 ff ff       	call   24b0 <__printf_chk@plt>
      thread_data[x].other = other;
    2aba:	4c 8b 0c 24          	mov    (%rsp),%r9
    2abe:	8b 4c 24 70          	mov    0x70(%rsp),%ecx
    2ac2:	31 c0                	xor    %eax,%eax
    2ac4:	48 8d 35 ed 5c 00 00 	lea    0x5ced(%rip),%rsi        # 87b8 <_IO_stdin_used+0x7b8>
    2acb:	bf 01 00 00 00       	mov    $0x1,%edi
    2ad0:	45 89 a9 b8 00 00 00 	mov    %r13d,0xb8(%r9)
    2ad7:	44 8b 6c 24 10       	mov    0x10(%rsp),%r13d
    2adc:	44 89 ea             	mov    %r13d,%edx
    2adf:	e8 cc f9 ff ff       	call   24b0 <__printf_chk@plt>
        if (x < thread_count) {
    2ae4:	41 83 fd 01          	cmp    $0x1,%r13d
    2ae8:	4c 8b 0c 24          	mov    (%rsp),%r9
    2aec:	0f 87 aa 10 00 00    	ja     3b9c <main+0x152c>
          CPU_SET(curcpu, sendercpu);
    2af2:	48 63 44 24 70       	movslq 0x70(%rsp),%rax
    2af7:	48 89 c7             	mov    %rax,%rdi
    2afa:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2b00:	77 13                	ja     2b15 <main+0x4a5>
    2b02:	48 c1 e8 06          	shr    $0x6,%rax
    2b06:	ba 01 00 00 00       	mov    $0x1,%edx
    2b0b:	89 f9                	mov    %edi,%ecx
    2b0d:	48 d3 e2             	shl    %cl,%rdx
    2b10:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
          curcpu += 2;
    2b15:	83 44 24 70 02       	addl   $0x2,0x70(%rsp)
      thread_data[x].threads = my_thread_data;
    2b1a:	49 89 59 18          	mov    %rbx,0x18(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b1e:	be 10 00 00 00       	mov    $0x10,%esi
    2b23:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].swapmutex = swapmutex;
    2b28:	48 8b 84 24 c8 00 00 00 	mov    0xc8(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    2b30:	49 89 a9 b0 00 00 00 	mov    %rbp,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2b37:	31 ed                	xor    %ebp,%ebp
      thread_data[x].swapmutex = swapmutex;
    2b39:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2b40:	48 8b 84 24 c0 00 00 00 	mov    0xc0(%rsp),%rax
      thread_data[x].kind = KERNEL_THREAD;
    2b48:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2b4f:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].real_thread_index = x;
    2b56:	8b 44 24 10          	mov    0x10(%rsp),%eax
      thread_data[x].task_count = total_barrier_count;
    2b5a:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].real_thread_index = x;
    2b62:	41 89 41 08          	mov    %eax,0x8(%r9)
      thread_data[x].all_threads = thread_data;
    2b66:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].task_count = total_barrier_count;
    2b6b:	4c 89 0c 24          	mov    %r9,(%rsp)
      thread_data[x].all_threads = thread_data;
    2b6f:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2b73:	48 8b 05 a6 61 00 00 	mov    0x61a6(%rip),%rax        # 8d20 <_IO_stdin_used+0xd20>
    2b7a:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2b81:	48 8b 05 a0 61 00 00 	mov    0x61a0(%rip),%rax        # 8d28 <_IO_stdin_used+0xd28>
    2b88:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b8c:	e8 6f f8 ff ff       	call   2400 <calloc@plt>
    2b91:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2b95:	be 10 00 00 00       	mov    $0x10,%esi
    2b9a:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b9f:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2ba3:	e8 58 f8 ff ff       	call   2400 <calloc@plt>
    2ba8:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bac:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2bb1:	66 0f 6f 3d 37 61 00 00 	movdqa 0x6137(%rip),%xmm7        # 8cf0 <_IO_stdin_used+0xcf0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bb9:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2bbe:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2bc2:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bca:	e8 31 f8 ff ff       	call   2400 <calloc@plt>
    2bcf:	4c 8b 0c 24          	mov    (%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2bd3:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2bd8:	66 0f 6f 35 10 61 00 00 	movdqa 0x6110(%rip),%xmm6        # 8cf0 <_IO_stdin_used+0xcf0>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2be0:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2be5:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2bec:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2bf4:	e8 07 f8 ff ff       	call   2400 <calloc@plt>
        thread_data[x].tasks = barriers;
    2bf9:	4c 8b 0c 24          	mov    (%rsp),%r9
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2bfd:	4c 89 e7             	mov    %r12,%rdi
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c00:	49 89 c5             	mov    %rax,%r13
        thread_data[x].tasks = barriers;
    2c03:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c07:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
            data[0].messages_count = 0;
    2c0c:	4c 89 e9             	mov    %r13,%rcx
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c0f:	48 0f af f8          	imul   %rax,%rdi
            data[0].messages_count = 0;
    2c13:	4c 89 4c 24 48       	mov    %r9,0x48(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c18:	48 c1 ef 22          	shr    $0x22,%rdi
    2c1c:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2c1f:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    2c23:	01 c0                	add    %eax,%eax
    2c25:	29 c7                	sub    %eax,%edi
            data[0].messages_count = 0;
    2c27:	89 bc 24 88 00 00 00 	mov    %edi,0x88(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c2e:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c31:	be 80 01 00 00       	mov    $0x180,%esi
    2c36:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c3b:	45 31 ed             	xor    %r13d,%r13d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c3e:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2c43:	48 c1 e0 09          	shl    $0x9,%rax
    2c47:	4c 8d 24 01          	lea    (%rcx,%rax,1),%r12
    2c4b:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2c50:	48 8d 05 99 18 00 00 	lea    0x1899(%rip),%rax        # 44f0 <do_protected_write>
    2c57:	49 89 84 24 20 01 00 00 	mov    %rax,0x120(%r12)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c5f:	e8 9c f7 ff ff       	call   2400 <calloc@plt>
    2c64:	8b 74 24 50          	mov    0x50(%rsp),%esi
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2c68:	49 89 84 24 70 01 00 00 	mov    %rax,0x170(%r12)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c70:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c73:	85 f6                	test   %esi,%esi
    2c75:	0f 84 87 01 00 00    	je     2e02 <main+0x792>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2c7b:	8b 44 24 18          	mov    0x18(%rsp),%eax
    2c7f:	48 89 4c 24 78       	mov    %rcx,0x78(%rsp)
    2c84:	49 89 cc             	mov    %rcx,%r12
    2c87:	83 e8 02             	sub    $0x2,%eax
    2c8a:	89 44 24 68          	mov    %eax,0x68(%rsp)
    2c8e:	eb 15                	jmp    2ca5 <main+0x635>
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c90:	41 83 c5 01          	add    $0x1,%r13d
    2c94:	49 81 c4 80 01 00 00 	add    $0x180,%r12
    2c9b:	41 83 fd 06          	cmp    $0x6,%r13d
    2c9f:	0f 84 db 02 00 00    	je     2f80 <main+0x910>
            int group_of = b / threads_per_group;
    2ca5:	44 89 eb             	mov    %r13d,%ebx
    2ca8:	31 c0                	xor    %eax,%eax
    2caa:	44 89 ea             	mov    %r13d,%edx
    2cad:	bf 01 00 00 00       	mov    $0x1,%edi
    2cb2:	d1 fb                	sar    %ebx
    2cb4:	48 8d 35 01 57 00 00 	lea    0x5701(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2cbb:	89 d9                	mov    %ebx,%ecx
    2cbd:	e8 ee f7 ff ff       	call   24b0 <__printf_chk@plt>
            if (k == group_of) {
    2cc2:	41 39 de             	cmp    %ebx,%r14d
    2cc5:	75 c9                	jne    2c90 <main+0x620>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2cc7:	be 08 00 00 00       	mov    $0x8,%esi
    2ccc:	bf 01 00 00 00       	mov    $0x1,%edi
    2cd1:	e8 2a f7 ff ff       	call   2400 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cd6:	be 08 00 00 00       	mov    $0x8,%esi
    2cdb:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ce0:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ce5:	e8 16 f7 ff ff       	call   2400 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2cea:	be 80 03 00 00       	mov    $0x380,%esi
    2cef:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cf4:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2cf9:	e8 02 f7 ff ff       	call   2400 <calloc@plt>
              data[0].a = x;
    2cfe:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2d02:	44 89 ea             	mov    %r13d,%edx
              mailboxes[b].pending_lower = NULL;
    2d05:	49 c7 84 24 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r12)
              struct Data *data = calloc(3, sizeof(struct Data));
    2d11:	49 89 c1             	mov    %rax,%r9
              data[0].b = y;
    2d14:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
    2d1a:	48 8d 35 b7 5a 00 00 	lea    0x5ab7(%rip),%rsi        # 87d8 <_IO_stdin_used+0x7d8>
    2d21:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].kind = MAILBOX_LOWER;
    2d26:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].a = x;
    2d30:	89 98 1c 03 00 00    	mov    %ebx,0x31c(%rax)
              data[0].c = b;
    2d36:	44 89 a8 24 03 00 00 	mov    %r13d,0x324(%rax)
              data[0].id = dataid++;
    2d3d:	41 8d 47 01          	lea    0x1(%r15),%eax
              data[1].id = dataid++;
    2d41:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2d48:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2d4f:	49 89 84 24 80 00 00 00 	mov    %rax,0x80(%r12)
    2d57:	8b 44 24 68          	mov    0x68(%rsp),%eax
              data[0].id = dataid++;
    2d5b:	45 89 b9 28 03 00 00 	mov    %r15d,0x328(%r9)
              data[1].id = dataid++;
    2d62:	41 83 c7 02          	add    $0x2,%r15d
              data[1].kind = MAILBOX_HIGHER;
    2d66:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
    2d71:	89 c1                	mov    %eax,%ecx
              data[1].a = x;
    2d73:	41 89 99 9c 06 00 00 	mov    %ebx,0x69c(%r9)
              data[1].b = y;
    2d7a:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[1].c = b;
    2d81:	45 89 a9 a4 06 00 00 	mov    %r13d,0x6a4(%r9)
              mailboxes[b].lower = &data[0];
    2d88:	4d 89 0c 24          	mov    %r9,(%r12)
              data[0].finished_reading = 1;
    2d8c:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    2d97:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
    2da2:	41 89 84 24 b4 00 00 00 	mov    %eax,0xb4(%r12)
    2daa:	31 c0                	xor    %eax,%eax
              mailboxes[b].pending_higher = NULL;
    2dac:	49 c7 84 24 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r12)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2db8:	41 c7 84 24 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%r12)
              data[1].finished_reading = 1;
    2dc4:	4c 89 0c 24          	mov    %r9,(%rsp)
    2dc8:	e8 e3 f6 ff ff       	call   24b0 <__printf_chk@plt>
              data[0].messages = messages;
    2dcd:	4c 8b 0c 24          	mov    (%rsp),%r9
    2dd1:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
              data[0].messages_count = 0;
    2dd6:	66 0f 6f 35 22 5f 00 00 	movdqa 0x5f22(%rip),%xmm6        # 8d00 <_IO_stdin_used+0xd00>
              data[1].messages = messages2;
    2dde:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
              data[0].messages = messages;
    2de3:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2de6:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2ded:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2df5:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
    2dfd:	e9 8e fe ff ff       	jmp    2c90 <main+0x620>
    2e02:	45 89 ec             	mov    %r13d,%r12d
    2e05:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    2e0a:	49 89 c5             	mov    %rax,%r13
    2e0d:	eb 16                	jmp    2e25 <main+0x7b5>
    2e0f:	90                   	nop
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e10:	41 83 c4 01          	add    $0x1,%r12d
    2e14:	49 81 c5 80 01 00 00 	add    $0x180,%r13
    2e1b:	41 83 fc 06          	cmp    $0x6,%r12d
    2e1f:	0f 84 61 06 00 00    	je     3486 <main+0xe16>
            int group_of = b / threads_per_group;
    2e25:	44 89 e3             	mov    %r12d,%ebx
    2e28:	31 c0                	xor    %eax,%eax
    2e2a:	44 89 e2             	mov    %r12d,%edx
    2e2d:	bf 01 00 00 00       	mov    $0x1,%edi
    2e32:	d1 fb                	sar    %ebx
    2e34:	48 8d 35 81 55 00 00 	lea    0x5581(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2e3b:	89 d9                	mov    %ebx,%ecx
    2e3d:	e8 6e f6 ff ff       	call   24b0 <__printf_chk@plt>
            if (k == group_of) {
    2e42:	41 39 de             	cmp    %ebx,%r14d
    2e45:	75 c9                	jne    2e10 <main+0x7a0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e47:	be 08 00 00 00       	mov    $0x8,%esi
    2e4c:	bf 01 00 00 00       	mov    $0x1,%edi
    2e51:	e8 aa f5 ff ff       	call   2400 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e56:	be 08 00 00 00       	mov    $0x8,%esi
    2e5b:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e60:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e65:	e8 96 f5 ff ff       	call   2400 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2e6a:	be 80 03 00 00       	mov    $0x380,%esi
    2e6f:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e74:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2e79:	e8 82 f5 ff ff       	call   2400 <calloc@plt>
              data[0].a = x;
    2e7e:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
    2e82:	44 89 e2             	mov    %r12d,%edx
              mailboxes[b].pending_lower = NULL;
    2e85:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
              struct Data *data = calloc(3, sizeof(struct Data));
    2e90:	49 89 c1             	mov    %rax,%r9
              data[0].b = y;
    2e93:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
    2e99:	48 8d 35 38 59 00 00 	lea    0x5938(%rip),%rsi        # 87d8 <_IO_stdin_used+0x7d8>
    2ea0:	bf 01 00 00 00       	mov    $0x1,%edi
              data[0].kind = MAILBOX_LOWER;
    2ea5:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].a = x;
    2eaf:	89 98 1c 03 00 00    	mov    %ebx,0x31c(%rax)
              data[0].c = b;
    2eb5:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
              data[0].id = dataid++;
    2ebc:	41 8d 47 01          	lea    0x1(%r15),%eax
              data[1].id = dataid++;
    2ec0:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2ec7:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2ece:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    2ed5:	8b 84 24 88 00 00 00 	mov    0x88(%rsp),%eax
              data[0].id = dataid++;
    2edc:	45 89 b9 28 03 00 00 	mov    %r15d,0x328(%r9)
              data[1].id = dataid++;
    2ee3:	41 83 c7 02          	add    $0x2,%r15d
              data[1].kind = MAILBOX_HIGHER;
    2ee7:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
    2ef2:	89 c1                	mov    %eax,%ecx
              data[1].a = x;
    2ef4:	41 89 99 9c 06 00 00 	mov    %ebx,0x69c(%r9)
              data[1].b = y;
    2efb:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[1].c = b;
    2f02:	45 89 a1 a4 06 00 00 	mov    %r12d,0x6a4(%r9)
              mailboxes[b].lower = &data[0];
    2f09:	4d 89 4d 00          	mov    %r9,0x0(%r13)
              data[0].finished_reading = 1;
    2f0d:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    2f18:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
    2f23:	41 89 85 b4 00 00 00 	mov    %eax,0xb4(%r13)
    2f2a:	31 c0                	xor    %eax,%eax
              mailboxes[b].pending_higher = NULL;
    2f2c:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2f37:	41 c7 85 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%r13)
              data[1].finished_reading = 1;
    2f42:	4c 89 0c 24          	mov    %r9,(%rsp)
    2f46:	e8 65 f5 ff ff       	call   24b0 <__printf_chk@plt>
              data[0].messages = messages;
    2f4b:	4c 8b 0c 24          	mov    (%rsp),%r9
    2f4f:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
              data[0].messages_count = 0;
    2f54:	66 0f 6f 35 a4 5d 00 00 	movdqa 0x5da4(%rip),%xmm6        # 8d00 <_IO_stdin_used+0xd00>
              data[1].messages = messages2;
    2f5c:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
              data[0].messages = messages;
    2f61:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2f64:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2f6b:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2f73:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
    2f7b:	e9 90 fe ff ff       	jmp    2e10 <main+0x7a0>
    2f80:	48 8b 4c 24 78       	mov    0x78(%rsp),%rcx
    2f85:	44 89 34 24          	mov    %r14d,(%rsp)
    2f89:	31 db                	xor    %ebx,%ebx
    2f8b:	49 89 cc             	mov    %rcx,%r12
    2f8e:	41 89 ee             	mov    %ebp,%r14d
    2f91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            int group_of = b / threads_per_group;
    2f98:	89 d8                	mov    %ebx,%eax
    2f9a:	d1 f8                	sar    %eax
            if (k == group_of) {
    2f9c:	39 04 24             	cmp    %eax,(%rsp)
    2f9f:	0f 84 76 01 00 00    	je     311b <main+0xaab>
    2fa5:	89 da                	mov    %ebx,%edx
    2fa7:	48 8d 35 1e 54 00 00 	lea    0x541e(%rip),%rsi        # 83cc <_IO_stdin_used+0x3cc>
    2fae:	bf 01 00 00 00       	mov    $0x1,%edi
    2fb3:	31 c0                	xor    %eax,%eax
    2fb5:	e8 f6 f4 ff ff       	call   24b0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2fba:	be 08 00 00 00       	mov    $0x8,%esi
    2fbf:	bf 01 00 00 00       	mov    $0x1,%edi
    2fc4:	e8 37 f4 ff ff       	call   2400 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2fc9:	be 08 00 00 00       	mov    $0x8,%esi
    2fce:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2fd3:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2fd8:	e8 23 f4 ff ff       	call   2400 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2fdd:	be 80 03 00 00       	mov    $0x380,%esi
    2fe2:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2fe7:	48 89 c5             	mov    %rax,%rbp
            struct Data *data = calloc(3, sizeof(struct Data));
    2fea:	e8 11 f4 ff ff       	call   2400 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2fef:	be 80 03 00 00       	mov    $0x380,%esi
    2ff4:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2ff9:	49 89 c5             	mov    %rax,%r13
            struct Data **stack = calloc(3, sizeof(struct Data));
    2ffc:	e8 ff f3 ff ff       	call   2400 <calloc@plt>
            data[0].a = x;
    3001:	8b 7c 24 10          	mov    0x10(%rsp),%edi
            data[0].id = dataid++;
    3005:	41 8d 77 01          	lea    0x1(%r15),%esi
            data[0].messages = messages;
    3009:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
            data[0].messages_count = 0;
    300e:	66 0f 6f 35 ea 5c 00 00 	movdqa 0x5cea(%rip),%xmm6        # 8d00 <_IO_stdin_used+0xd00>
            mailboxes[b].lower = &data[0];
    3016:	4d 89 2c 24          	mov    %r13,(%r12)
            data[1].id = dataid++;
    301a:	41 89 b5 a8 06 00 00 	mov    %esi,0x6a8(%r13)
            mailboxes[b].higher = &data[1];
    3021:	49 8d b5 80 03 00 00 	lea    0x380(%r13),%rsi
            data[0].id = dataid++;
    3028:	45 89 bd 28 03 00 00 	mov    %r15d,0x328(%r13)
            data[1].id = dataid++;
    302f:	41 83 c7 02          	add    $0x2,%r15d
            data[0].kind = MAILBOX_LOWER;
    3033:	41 c7 85 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r13)
            data[0].a = x;
    303e:	41 89 bd 1c 03 00 00 	mov    %edi,0x31c(%r13)
            data[0].b = y;
    3045:	45 89 b5 20 03 00 00 	mov    %r14d,0x320(%r13)
            data[0].c = b;
    304c:	41 89 9d 24 03 00 00 	mov    %ebx,0x324(%r13)
            data[1].kind = MAILBOX_HIGHER;
    3053:	41 c7 85 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r13)
            data[1].a = x;
    305e:	41 89 bd 9c 06 00 00 	mov    %edi,0x69c(%r13)
            data[1].b = y;
    3065:	45 89 b5 a0 06 00 00 	mov    %r14d,0x6a0(%r13)
            data[1].c = b;
    306c:	41 89 9d a4 06 00 00 	mov    %ebx,0x6a4(%r13)
            mailboxes[b].my_lower = &data[0];
    3073:	4d 89 ac 24 a0 00 00 00 	mov    %r13,0xa0(%r12)
            mailboxes[b].higher = &data[1];
    307b:	49 89 b4 24 80 00 00 00 	mov    %rsi,0x80(%r12)
            mailboxes[b].pending_lower = NULL;
    3083:	49 c7 84 24 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r12)
            mailboxes[b].pending_higher = NULL;
    308f:	49 c7 84 24 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r12)
            data[0].finished_reading = 1;
    309b:	41 c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r13)
            data[1].finished_reading = 1;
    30a6:	41 c7 85 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r13)
            mailboxes[b].my_higher = &data[1];
    30b1:	49 89 b4 24 a8 00 00 00 	mov    %rsi,0xa8(%r12)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    30b9:	41 c7 84 24 b0 00 00 00 02 00 00 00 	movl   $0x2,0xb0(%r12)
            stack[0] = mailboxes[b].lower;
    30c5:	4c 89 28             	mov    %r13,(%rax)
            stack[1] = mailboxes[b].higher;
    30c8:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    30cc:	49 89 84 24 98 00 00 00 	mov    %rax,0x98(%r12)
            data[0].available_sending = 0;
    30d4:	41 c7 85 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r13)
            data[0].available_receiving = 0;
    30df:	41 c7 85 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r13)
            data[0].messages = messages;
    30ea:	49 89 55 00          	mov    %rdx,0x0(%r13)
            data[1].messages = messages2;
    30ee:	49 89 ad 80 03 00 00 	mov    %rbp,0x380(%r13)
            data[1].available_sending = 1;
    30f5:	41 c7 85 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r13)
            data[1].available_receiving = 0;
    3100:	41 c7 85 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r13)
            data[0].messages_count = 0;
    310b:	41 0f 29 b5 80 00 00 00 	movaps %xmm6,0x80(%r13)
            data[1].messages_count = 0;
    3113:	41 0f 29 b5 00 04 00 00 	movaps %xmm6,0x400(%r13)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    311b:	83 c3 01             	add    $0x1,%ebx
    311e:	49 81 c4 80 01 00 00 	add    $0x180,%r12
    3125:	83 fb 06             	cmp    $0x6,%ebx
    3128:	0f 85 6a fe ff ff    	jne    2f98 <main+0x928>
          char *message = malloc(sizeof(char) * 256);
    312e:	be 01 00 00 00       	mov    $0x1,%esi
    3133:	bf 00 01 00 00       	mov    $0x100,%edi
    3138:	44 89 f5             	mov    %r14d,%ebp
    313b:	44 8b 34 24          	mov    (%rsp),%r14d
    313f:	e8 bc f2 ff ff       	call   2400 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    3144:	bf 30 00 00 00       	mov    $0x30,%edi
          char *message = malloc(sizeof(char) * 256);
    3149:	49 89 c4             	mov    %rax,%r12
          struct Message *messaged = malloc(sizeof(struct Message));
    314c:	e8 1f f3 ff ff       	call   2470 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3151:	48 83 ec 08          	sub    $0x8,%rsp
    3155:	41 89 e9             	mov    %ebp,%r9d
    3158:	4c 89 e7             	mov    %r12,%rdi
    315b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3160:	48 8d 0d 99 56 00 00 	lea    0x5699(%rip),%rcx        # 8800 <_IO_stdin_used+0x800>
    3167:	ba 00 01 00 00       	mov    $0x100,%edx
    316c:	31 c0                	xor    %eax,%eax
    316e:	41 56                	push   %r14
    3170:	44 8b 44 24 20       	mov    0x20(%rsp),%r8d
    3175:	be 01 00 00 00       	mov    $0x1,%esi
    317a:	e8 21 f4 ff ff       	call   25a0 <__sprintf_chk@plt>
          messaged->message = message;
    317f:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
          messaged->thread_index = thread_data[x].real_thread_index;
    3184:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3189:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->task_index = y;
    318e:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
          thread_data[x].tasks[y].swap = swap;
    3193:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3198:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].swap = swap;
    319d:	48 8b 4b 38          	mov    0x38(%rbx),%rcx
          messaged->message = message;
    31a1:	4d 89 22             	mov    %r12,(%r10)
          messaged->task_index = y;
    31a4:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    31a8:	48 63 43 08          	movslq 0x8(%rbx),%rax
          thread_data[x].tasks[y].swap = swap;
    31ac:	48 01 ca             	add    %rcx,%rdx
          messaged->group = k;
    31af:	45 89 72 18          	mov    %r14d,0x18(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    31b3:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].swap = swap;
    31b7:	8b 44 24 30          	mov    0x30(%rsp),%eax
          thread_data[x].tasks[y].group = k;
    31bb:	44 89 b2 94 01 00 00 	mov    %r14d,0x194(%rdx)
          thread_data[x].tasks[y].swap = swap;
    31c2:	89 82 98 01 00 00    	mov    %eax,0x198(%rdx)
          swap += 1;
    31c8:	83 c0 01             	add    $0x1,%eax
    31cb:	89 44 24 30          	mov    %eax,0x30(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    31cf:	8d 45 01             	lea    0x1(%rbp),%eax
    31d2:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    31d5:	c7 02 41 00 00 00    	movl   $0x41,(%rdx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    31db:	89 82 90 01 00 00    	mov    %eax,0x190(%rdx)
          thread_data[x].tasks[y].message = messaged;
    31e1:	4c 89 92 88 01 00 00 	mov    %r10,0x188(%rdx)
          thread_data[x].tasks[y].sending = 1;
    31e8:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
          thread_data[x].tasks[y].snapshot_count = 99;
    31f2:	48 c7 82 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rdx)
    31fd:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
          thread_data[x].tasks[y].swap = swap;
    3202:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3207:	e8 f4 f1 ff ff       	call   2400 <calloc@plt>
    320c:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    3211:	48 89 82 50 01 00 00 	mov    %rax,0x150(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3218:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    321d:	48 c7 82 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3228:	48 8b 00             	mov    (%rax),%rax
    322b:	8b 70 04             	mov    0x4(%rax),%esi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    322e:	48 39 d8             	cmp    %rbx,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    3231:	48 89 82 28 01 00 00 	mov    %rax,0x128(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3238:	89 b2 30 01 00 00    	mov    %esi,0x130(%rdx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    323e:	41 5d                	pop    %r13
    3240:	59                   	pop    %rcx
    3241:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    3246:	0f 85 a0 11 00 00    	jne    43ec <main+0x1d7c>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    324c:	66 0f 6f 05 bc 5a 00 00 	movdqa 0x5abc(%rip),%xmm0        # 8d10 <_IO_stdin_used+0xd10>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    3254:	89 6a 04             	mov    %ebp,0x4(%rdx)
          thread_data[x].tasks[y].available = 1;
    3257:	4c 8b 25 d2 5a 00 00 	mov    0x5ad2(%rip),%r12        # 8d30 <_IO_stdin_used+0xd30>
          thread_data[x].tasks[y].arrived = 0;
    325e:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
          thread_data[x].tasks[y].worker_count = thread_count;
    3268:	c7 82 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rdx)
          thread_data[x].tasks[y].available = 1;
    3272:	4c 89 a2 44 01 00 00 	mov    %r12,0x144(%rdx)
          thread_data[x].tasks[y].thread_count = 2;
    3279:	0f 11 82 34 01 00 00 	movups %xmm0,0x134(%rdx)
          if (y == barrier_count - 1) {
    3280:	83 fd 01             	cmp    $0x1,%ebp
    3283:	0f 84 1f 02 00 00    	je     34a8 <main+0xe38>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    3289:	85 ed                	test   %ebp,%ebp
    328b:	0f 84 ff 01 00 00    	je     3490 <main+0xe20>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    3291:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
    3296:	48 8d 05 83 37 00 00 	lea    0x3783(%rip),%rax        # 6a20 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    329d:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    32a2:	49 89 cd             	mov    %rcx,%r13
    32a5:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    32ac:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
    32b1:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    32bc:	4c 89 0c 24          	mov    %r9,(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    32c0:	e8 3b f1 ff ff       	call   2400 <calloc@plt>
    32c5:	4c 8b 0c 24          	mov    (%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    32c9:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    32ce:	66 0f 6f bc 24 a0 00 00 00 	movdqa 0xa0(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    32d7:	83 44 24 18 01       	addl   $0x1,0x18(%rsp)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    32dc:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    32df:	48 83 c3 10          	add    $0x10,%rbx
    32e3:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    32ea:	49 89 81 70 ff ff ff 	mov    %rax,-0x90(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    32f1:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    32f6:	83 44 24 74 01       	addl   $0x1,0x74(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    32fb:	48 8b 00             	mov    (%rax),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    32fe:	48 89 5c 24 60       	mov    %rbx,0x60(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    3303:	41 c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r13)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    330e:	49 89 85 28 05 00 00 	mov    %rax,0x528(%r13)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    3315:	41 c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r13)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    3320:	41 c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r13)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    332b:	41 8b 81 24 ff ff ff 	mov    -0xdc(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3332:	41 0f 11 bd 18 05 00 00 	movups %xmm7,0x518(%r13)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    333a:	41 89 85 30 05 00 00 	mov    %eax,0x530(%r13)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3341:	8b 44 24 18          	mov    0x18(%rsp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    3345:	41 c7 85 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r13)
        thread_data[x].tasks[barrier_count].available = 1; 
    3350:	4d 89 a5 44 05 00 00 	mov    %r12,0x544(%r13)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3357:	39 84 24 8c 00 00 00 	cmp    %eax,0x8c(%rsp)
    335e:	0f 85 8d f6 ff ff    	jne    29f1 <main+0x381>
    3364:	48 8b 9c 24 d0 00 00 00 	mov    0xd0(%rsp),%rbx
    336c:	48 8b b4 24 b8 00 00 00 	mov    0xb8(%rsp),%rsi
    3374:	45 89 f4             	mov    %r14d,%r12d
  for (int k = 0 ; k < group_count ; k++) {
    3377:	41 83 c4 01          	add    $0x1,%r12d
    337b:	48 8b ac 24 d8 00 00 00 	mov    0xd8(%rsp),%rbp
    3383:	48 83 c6 18          	add    $0x18,%rsi
    3387:	48 81 c3 c0 01 00 00 	add    $0x1c0,%rbx
    338e:	41 83 fc 03          	cmp    $0x3,%r12d
    3392:	0f 85 15 f6 ff ff    	jne    29ad <main+0x33d>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3398:	be 08 00 00 00       	mov    $0x8,%esi
    339d:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    33a2:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    33a5:	e8 56 f0 ff ff       	call   2400 <calloc@plt>
    33aa:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    33af:	48 89 c5             	mov    %rax,%rbp
    33b2:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    33b4:	49 89 d1             	mov    %rdx,%r9
    33b7:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    33b9:	45 8b 51 40          	mov    0x40(%r9),%r10d
    33bd:	45 85 d2             	test   %r10d,%r10d
    33c0:	0f 8e ab 00 00 00    	jle    3471 <main+0xe01>
    33c6:	49 8b 79 38          	mov    0x38(%r9),%rdi
    33ca:	4d 63 c2             	movslq %r10d,%r8
    33cd:	49 63 cc             	movslq %r12d,%rcx
    33d0:	49 c1 e0 09          	shl    $0x9,%r8
    33d4:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    33d9:	49 01 f8             	add    %rdi,%r8
    33dc:	0f 1f 40 00          	nopl   0x0(%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    33e0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    33e7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    33ee:	48 83 c6 60          	add    $0x60,%rsi
    33f2:	f3 0f 7e a1 80 01 00 00 	movq   0x180(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    33fa:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    33fe:	f3 0f 7e 99 00 03 00 00 	movq   0x300(%rcx),%xmm3
    3406:	f3 0f 7e 91 80 04 00 00 	movq   0x480(%rcx),%xmm2
    340e:	f3 0f 7e 89 00 06 00 00 	movq   0x600(%rcx),%xmm1
    3416:	0f 16 a1 00 02 00 00 	movhps 0x200(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    341d:	f3 0f 7e 81 80 07 00 00 	movq   0x780(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3425:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    342c:	0f 16 99 80 03 00 00 	movhps 0x380(%rcx),%xmm3
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3433:	0f 16 91 00 05 00 00 	movhps 0x500(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    343a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    343e:	0f 16 89 80 06 00 00 	movhps 0x680(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3445:	0f 16 81 00 08 00 00 	movhps 0x800(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    344c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3450:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3454:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3458:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    345c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3460:	49 39 f8             	cmp    %rdi,%r8
    3463:	0f 85 77 ff ff ff    	jne    33e0 <main+0xd70>
    3469:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    346d:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    3471:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    3478:	85 db                	test   %ebx,%ebx
    347a:	75 3a                	jne    34b6 <main+0xe46>
    347c:	bb 01 00 00 00       	mov    $0x1,%ebx
    3481:	e9 33 ff ff ff       	jmp    33b9 <main+0xd49>
    3486:	48 8b 4c 24 68       	mov    0x68(%rsp),%rcx
    348b:	e9 f5 fa ff ff       	jmp    2f85 <main+0x915>
    3490:	48 8d 05 29 3a 00 00 	lea    0x3a29(%rip),%rax        # 6ec0 <barriered_work_ingest_andwork>
    3497:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    349c:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    34a3:	e9 86 f7 ff ff       	jmp    2c2e <main+0x5be>
    34a8:	48 8d 05 71 35 00 00 	lea    0x3571(%rip),%rax        # 6a20 <barriered_work>
    34af:	bd 02 00 00 00       	mov    $0x2,%ebp
    34b4:	eb e6                	jmp    349c <main+0xe2c>
  for (int k = 0 ; k < group_count ; k++) {
    34b6:	83 c0 02             	add    $0x2,%eax
    34b9:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    34c0:	83 f8 06             	cmp    $0x6,%eax
    34c3:	0f 85 eb fe ff ff    	jne    33b4 <main+0xd44>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    34c9:	48 8d 3d 1a 4f 00 00 	lea    0x4f1a(%rip),%rdi        # 83ea <_IO_stdin_used+0x3ea>
    34d0:	e8 5b ee ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    34d5:	48 8d 35 23 4f 00 00 	lea    0x4f23(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    34dc:	48 8d 3d 1e 4f 00 00 	lea    0x4f1e(%rip),%rdi        # 8401 <_IO_stdin_used+0x401>
    34e3:	e8 08 f0 ff ff       	call   24f0 <fopen@plt>
    34e8:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas_size; x++) {
    34eb:	45 85 e4             	test   %r12d,%r12d
    34ee:	7e 75                	jle    3565 <main+0xef5>
    34f0:	4d 63 e4             	movslq %r12d,%r12
    34f3:	4c 8d 35 e4 4e 00 00 	lea    0x4ee4(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    34fa:	4c 8d 2d 21 4f 00 00 	lea    0x4f21(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    3501:	4a 8d 44 e5 00       	lea    0x0(%rbp,%r12,8),%rax
    3506:	48 89 04 24          	mov    %rax,(%rsp)
    char * c = calloc(250, sizeof(char));
    350a:	be 01 00 00 00       	mov    $0x1,%esi
    350f:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    3514:	48 83 c5 08          	add    $0x8,%rbp
    char * c = calloc(250, sizeof(char));
    3518:	e8 e3 ee ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    351d:	4c 89 f1             	mov    %r14,%rcx
    3520:	ba fa 00 00 00       	mov    $0xfa,%edx
    3525:	be 01 00 00 00       	mov    $0x1,%esi
    352a:	49 89 c4             	mov    %rax,%r12
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    352d:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    3531:	4c 89 e7             	mov    %r12,%rdi
    3534:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    353b:	31 c0                	xor    %eax,%eax
    353d:	e8 5e f0 ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3542:	4c 89 e2             	mov    %r12,%rdx
    3545:	4c 89 ee             	mov    %r13,%rsi
    3548:	bf 01 00 00 00       	mov    $0x1,%edi
    354d:	31 c0                	xor    %eax,%eax
    354f:	e8 5c ef ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3554:	4c 89 fe             	mov    %r15,%rsi
    3557:	4c 89 e7             	mov    %r12,%rdi
    355a:	e8 61 ee ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    355f:	48 39 2c 24          	cmp    %rbp,(%rsp)
    3563:	75 a5                	jne    350a <main+0xe9a>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    3565:	4c 89 ff             	mov    %r15,%rdi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3568:	45 31 f6             	xor    %r14d,%r14d
    356b:	4c 8d 25 da 4e 00 00 	lea    0x4eda(%rip),%r12        # 844c <_IO_stdin_used+0x44c>
    3572:	e8 e9 ed ff ff       	call   2360 <fclose@plt>
    3577:	48 8d 3d 8c 4e 00 00 	lea    0x4e8c(%rip),%rdi        # 840a <_IO_stdin_used+0x40a>
    357e:	4c 89 f5             	mov    %r14,%rbp
    3581:	e8 aa ed ff ff       	call   2330 <puts@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    3586:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    358a:	89 ea                	mov    %ebp,%edx
    358c:	48 8d 35 92 4e 00 00 	lea    0x4e92(%rip),%rsi        # 8425 <_IO_stdin_used+0x425>
    3593:	bf 01 00 00 00       	mov    $0x1,%edi
    3598:	31 c0                	xor    %eax,%eax
    359a:	48 8d 1c ed 00 00 00 00 	lea    0x0(,%rbp,8),%rbx
    35a2:	44 8d 6c 2d 00       	lea    0x0(%rbp,%rbp,1),%r13d
    35a7:	45 31 ff             	xor    %r15d,%r15d
    35aa:	e8 01 ef ff ff       	call   24b0 <__printf_chk@plt>
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    35af:	48 29 eb             	sub    %rbp,%rbx
    35b2:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    35b7:	48 c1 e3 06          	shl    $0x6,%rbx
    35bb:	48 01 c3             	add    %rax,%rbx
      int x = (k * threads_per_group) + d;
    35be:	43 8d 0c 2f          	lea    (%r15,%r13,1),%ecx
    35c2:	44 89 fa             	mov    %r15d,%edx
    35c5:	48 8d 35 63 4e 00 00 	lea    0x4e63(%rip),%rsi        # 842f <_IO_stdin_used+0x42f>
    35cc:	31 c0                	xor    %eax,%eax
    35ce:	bf 01 00 00 00       	mov    $0x1,%edi
    35d3:	45 31 f6             	xor    %r14d,%r14d
    35d6:	e8 d5 ee ff ff       	call   24b0 <__printf_chk@plt>
    35db:	44 89 6c 24 10       	mov    %r13d,0x10(%rsp)
    35e0:	4c 89 f1             	mov    %r14,%rcx
    35e3:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    35e8:	48 89 dd             	mov    %rbx,%rbp
    35eb:	89 ca                	mov    %ecx,%edx
    35ed:	48 8d 35 4d 4e 00 00 	lea    0x4e4d(%rip),%rsi        # 8441 <_IO_stdin_used+0x441>
    35f4:	bf 01 00 00 00       	mov    $0x1,%edi
    35f9:	31 c0                	xor    %eax,%eax
    35fb:	48 89 0c 24          	mov    %rcx,(%rsp)
    35ff:	45 31 ed             	xor    %r13d,%r13d
    3602:	e8 a9 ee ff ff       	call   24b0 <__printf_chk@plt>
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3607:	48 8b 1c 24          	mov    (%rsp),%rbx
    360b:	48 c1 e3 09          	shl    $0x9,%rbx
    360f:	eb 33                	jmp    3644 <main+0xfd4>
    3611:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    3618:	83 ff 01             	cmp    $0x1,%edi
    361b:	0f 84 aa 00 00 00    	je     36cb <main+0x105b>
    3621:	44 8b 86 b4 00 00 00 	mov    0xb4(%rsi),%r8d
    3628:	44 89 f2             	mov    %r14d,%edx
    362b:	4c 89 e6             	mov    %r12,%rsi
    362e:	31 c0                	xor    %eax,%eax
    3630:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3635:	49 83 c5 01          	add    $0x1,%r13
    3639:	e8 72 ee ff ff       	call   24b0 <__printf_chk@plt>
    363e:	49 83 fd 06          	cmp    $0x6,%r13
    3642:	74 52                	je     3696 <main+0x1026>
          char * mailbox_kind = calloc(100, sizeof(char));
    3644:	be 01 00 00 00       	mov    $0x1,%esi
    3649:	bf 64 00 00 00       	mov    $0x64,%edi
    364e:	45 89 ee             	mov    %r13d,%r14d
    3651:	e8 aa ed ff ff       	call   2400 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3656:	4c 8b 45 38          	mov    0x38(%rbp),%r8
          char * mailbox_kind = calloc(100, sizeof(char));
    365a:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    365d:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
    3662:	49 8b b4 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rsi
    366a:	48 c1 e0 07          	shl    $0x7,%rax
    366e:	48 01 c6             	add    %rax,%rsi
    3671:	8b be b0 00 00 00    	mov    0xb0(%rsi),%edi
    3677:	83 ff 02             	cmp    $0x2,%edi
    367a:	75 9c                	jne    3618 <main+0xfa8>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    367c:	48 bf 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rdi
    3686:	48 89 39             	mov    %rdi,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3689:	49 03 84 18 70 01 00 00 	add    0x170(%r8,%rbx,1),%rax
    3691:	48 89 c6             	mov    %rax,%rsi
    3694:	eb 8b                	jmp    3621 <main+0xfb1>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3696:	48 8b 0c 24          	mov    (%rsp),%rcx
    369a:	48 83 c1 01          	add    $0x1,%rcx
    369e:	48 83 f9 03          	cmp    $0x3,%rcx
    36a2:	0f 85 43 ff ff ff    	jne    35eb <main+0xf7b>
    for (int d = 0 ; d < threads_per_group ; d++) {
    36a8:	48 89 eb             	mov    %rbp,%rbx
    36ab:	44 8b 6c 24 10       	mov    0x10(%rsp),%r13d
    36b0:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    36b5:	48 81 c3 e0 00 00 00 	add    $0xe0,%rbx
    36bc:	45 85 ff             	test   %r15d,%r15d
    36bf:	75 27                	jne    36e8 <main+0x1078>
    36c1:	44 8b 7c 24 08       	mov    0x8(%rsp),%r15d
    36c6:	e9 f3 fe ff ff       	jmp    35be <main+0xf4e>
    36cb:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    36d1:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    36d8:	49 03 84 18 70 01 00 00 	add    0x170(%r8,%rbx,1),%rax
    36e0:	48 89 c6             	mov    %rax,%rsi
    36e3:	e9 39 ff ff ff       	jmp    3621 <main+0xfb1>
  for (int k = 0 ; k < group_count ; k++) {
    36e8:	48 83 c5 01          	add    $0x1,%rbp
    36ec:	48 83 fd 03          	cmp    $0x3,%rbp
    36f0:	0f 85 94 fe ff ff    	jne    358a <main+0xf1a>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    36f6:	ba 07 00 00 00       	mov    $0x7,%edx
    36fb:	48 8d 35 65 4d 00 00 	lea    0x4d65(%rip),%rsi        # 8467 <_IO_stdin_used+0x467>
    3702:	bf 01 00 00 00       	mov    $0x1,%edi
    3707:	31 c0                	xor    %eax,%eax
    3709:	e8 a2 ed ff ff       	call   24b0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    370e:	be 08 00 00 00       	mov    $0x8,%esi
    3713:	bf 02 00 00 00       	mov    $0x2,%edi
    3718:	e8 e3 ec ff ff       	call   2400 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    371d:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3722:	be 38 00 00 00       	mov    $0x38,%esi
    3727:	bf 0a 00 00 00       	mov    $0xa,%edi
    my_thread_data[0] = &thread_data[x]; 
    372c:	4c 8d ad 20 06 00 00 	lea    0x620(%rbp),%r13
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3733:	48 89 68 08          	mov    %rbp,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3737:	4c 8d a5 e0 00 00 00 	lea    0xe0(%rbp),%r12
    thread_data[x].threads = my_thread_data;
    373e:	48 89 85 38 06 00 00 	mov    %rax,0x638(%rbp)
    my_thread_data[0] = &thread_data[x]; 
    3745:	4c 89 28             	mov    %r13,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3748:	48 8b 45 38          	mov    0x38(%rbp),%rax
    thread_data[x].thread_count = 2;
    374c:	c7 85 48 06 00 00 02 00 00 00 	movl   $0x2,0x648(%rbp)
    thread_data[x].thread_index = 0;
    3756:	c7 85 24 06 00 00 00 00 00 00 	movl   $0x0,0x624(%rbp)
    thread_data[x].task_count = total_barrier_count;
    3760:	c7 85 60 06 00 00 03 00 00 00 	movl   $0x3,0x660(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    376a:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3774:	48 8b 85 18 01 00 00 	mov    0x118(%rbp),%rax
    377b:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3785:	e8 76 ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    378a:	be 38 00 00 00       	mov    $0x38,%esi
    378f:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3794:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3798:	e8 63 ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    379d:	be 38 00 00 00       	mov    $0x38,%esi
    37a2:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37a7:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37aa:	e8 51 ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37af:	be 38 00 00 00       	mov    $0x38,%esi
    37b4:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37b9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37be:	e8 3d ec ff ff       	call   2400 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37c3:	be 08 00 00 00       	mov    $0x8,%esi
    37c8:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37cd:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37d2:	e8 29 ec ff ff       	call   2400 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    37d7:	be 08 00 00 00       	mov    $0x8,%esi
    37dc:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
    37e1:	c7 85 4c 05 00 00 00 00 00 00 	movl   $0x0,0x54c(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37eb:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    37ee:	48 8b 05 43 55 00 00 	mov    0x5543(%rip),%rax        # 8d38 <_IO_stdin_used+0xd38>
    37f5:	48 89 85 80 05 00 00 	mov    %rax,0x580(%rbp)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    37fc:	e8 ff eb ff ff       	call   2400 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3801:	48 8d 95 c0 01 00 00 	lea    0x1c0(%rbp),%rdx
    3808:	48 89 ef             	mov    %rbp,%rdi
    380b:	48 8d 8d 40 05 00 00 	lea    0x540(%rbp),%rcx
    3812:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3816:	48 8d 95 a0 02 00 00 	lea    0x2a0(%rbp),%rdx
    381d:	48 8d 35 52 4c 00 00 	lea    0x4c52(%rip),%rsi        # 8476 <_IO_stdin_used+0x476>
    3824:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3828:	48 8d 95 80 03 00 00 	lea    0x380(%rbp),%rdx
    382f:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3833:	48 8d 95 60 04 00 00 	lea    0x460(%rbp),%rdx
    383a:	48 89 28             	mov    %rbp,(%rax)
    383d:	48 8d ad 00 07 00 00 	lea    0x700(%rbp),%rbp
    3844:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3848:	48 8d 97 e0 07 00 00 	lea    0x7e0(%rdi),%rdx
    384f:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3853:	4c 89 68 38          	mov    %r13,0x38(%rax)
    3857:	48 89 50 48          	mov    %rdx,0x48(%rax)
    385b:	ba 06 00 00 00       	mov    $0x6,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3860:	48 89 87 58 05 00 00 	mov    %rax,0x558(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    3867:	4c 89 60 08          	mov    %r12,0x8(%rax)
    386b:	48 89 68 40          	mov    %rbp,0x40(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    386f:	48 8b 05 ca 54 00 00 	mov    0x54ca(%rip),%rax        # 8d40 <_IO_stdin_used+0xd40>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3876:	c7 87 70 05 00 00 06 00 00 00 	movl   $0x6,0x570(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3880:	48 89 87 68 05 00 00 	mov    %rax,0x568(%rdi)
    3887:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3889:	c7 87 44 05 00 00 00 00 00 00 	movl   $0x0,0x544(%rdi)
    3893:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
    3898:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    389d:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    38a2:	e8 09 ec ff ff       	call   24b0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38a7:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    38ac:	49 8d b6 50 01 00 00 	lea    0x150(%r14),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    38b3:	45 31 f6             	xor    %r14d,%r14d
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38b6:	48 8d 15 f3 0d 00 00 	lea    0xdf3(%rip),%rdx        # 46b0 <timer_thread>
    38bd:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    38c1:	e8 0a ec ff ff       	call   24d0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    38c6:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    38cb:	4c 89 ee             	mov    %r13,%rsi
    38ce:	48 89 d9             	mov    %rbx,%rcx
    38d1:	48 8b 04 24          	mov    (%rsp),%rax
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38d5:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    38da:	4c 89 64 24 28       	mov    %r12,0x28(%rsp)
    38df:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    38e5:	48 89 6c 24 30       	mov    %rbp,0x30(%rsp)
    38ea:	45 89 d5             	mov    %r10d,%r13d
    38ed:	44 89 7c 24 18       	mov    %r15d,0x18(%rsp)
    38f2:	49 89 c7             	mov    %rax,%r15
    for (int d = 0 ; d < threads_per_group ; d++) {
    38f5:	48 89 4c 24 48       	mov    %rcx,0x48(%rsp)
    38fa:	47 8d 24 36          	lea    (%r14,%r14,1),%r12d
    38fe:	48 89 cd             	mov    %rcx,%rbp
    3901:	48 89 d3             	mov    %rdx,%rbx
    3904:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
    3909:	4c 89 3c 24          	mov    %r15,(%rsp)
    390d:	4c 89 7c 24 40       	mov    %r15,0x40(%rsp)
    3912:	49 89 f7             	mov    %rsi,%r15
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3915:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    391c:	44 89 e2             	mov    %r12d,%edx
    391f:	44 89 f1             	mov    %r14d,%ecx
    3922:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    3924:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    392b:	48 8d 35 fe 4e 00 00 	lea    0x4efe(%rip),%rsi        # 8830 <_IO_stdin_used+0x830>
    3932:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    3937:	41 83 c4 01          	add    $0x1,%r12d
    393b:	e8 70 eb ff ff       	call   24b0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3940:	48 8b 34 24          	mov    (%rsp),%rsi
    3944:	48 89 d9             	mov    %rbx,%rcx
    3947:	48 89 ef             	mov    %rbp,%rdi
    394a:	48 8d 15 ff 28 00 00 	lea    0x28ff(%rip),%rdx        # 6250 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3951:	48 81 c3 e0 00 00 00 	add    $0xe0,%rbx
    3958:	48 83 c5 08          	add    $0x8,%rbp
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    395c:	e8 6f eb ff ff       	call   24d0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3961:	48 8b 53 d0          	mov    -0x30(%rbx),%rdx
    3965:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
    3969:	be 08 00 00 00       	mov    $0x8,%esi
    396e:	e8 ad e9 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3973:	48 83 04 24 38       	addq   $0x38,(%rsp)
    3978:	45 39 e5             	cmp    %r12d,%r13d
    397b:	75 98                	jne    3915 <main+0x12a5>
  for (int k = 0 ; k < group_count ; k++) {
    397d:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    3982:	4c 89 fe             	mov    %r15,%rsi
    3985:	41 83 c6 01          	add    $0x1,%r14d
    3989:	41 83 c5 02          	add    $0x2,%r13d
    398d:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
    3992:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    3997:	48 83 c1 10          	add    $0x10,%rcx
    399b:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    39a2:	49 83 c7 70          	add    $0x70,%r15
    39a6:	41 83 fe 03          	cmp    $0x3,%r14d
    39aa:	0f 85 45 ff ff ff    	jne    38f5 <main+0x1285>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    39b0:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    39b5:	48 8b 05 8c 53 00 00 	mov    0x538c(%rip),%rax        # 8d48 <_IO_stdin_used+0xd48>
    thread_data[x].type = IO;
    39bc:	49 89 f5             	mov    %rsi,%r13

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39bf:	bf 01 00 00 00       	mov    $0x1,%edi
    39c4:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    39c9:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    39ce:	4c 8b 64 24 28       	mov    0x28(%rsp),%r12
    39d3:	41 c7 86 2c 06 00 00 02 00 00 00 	movl   $0x2,0x62c(%r14)
    39de:	44 8b 7c 24 18       	mov    0x18(%rsp),%r15d
    thread_data[x].task_count = 0;
    39e3:	49 89 86 60 06 00 00 	mov    %rax,0x660(%r14)
    thread_data[x].type = IO;
    39ea:	48 8b 6c 24 30       	mov    0x30(%rsp),%rbp
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39ef:	e8 0c ea ff ff       	call   2400 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    39f4:	be 00 08 00 00       	mov    $0x800,%esi
    39f9:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39fb:	49 89 86 78 06 00 00 	mov    %rax,0x678(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a02:	e8 19 eb ff ff       	call   2520 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a07:	be 08 00 00 00       	mov    $0x8,%esi
    3a0c:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a11:	41 89 86 80 06 00 00 	mov    %eax,0x680(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a18:	e8 e3 e9 ff ff       	call   2400 <calloc@plt>
    3a1d:	ba 07 00 00 00       	mov    $0x7,%edx
    3a22:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3a27:	41 c7 86 48 06 00 00 02 00 00 00 	movl   $0x2,0x648(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3a32:	4c 89 30             	mov    %r14,(%rax)
    3a35:	48 8d 35 58 4a 00 00 	lea    0x4a58(%rip),%rsi        # 8494 <_IO_stdin_used+0x494>
    thread_data[x].threads = my_thread_data;
    3a3c:	49 89 86 38 06 00 00 	mov    %rax,0x638(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3a43:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3a47:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3a49:	41 c7 86 24 06 00 00 07 00 00 00 	movl   $0x7,0x624(%r14)
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a54:	41 be 08 00 00 00    	mov    $0x8,%r14d
    3a5a:	e8 51 ea ff ff       	call   24b0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3a5f:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3a64:	4c 89 e9             	mov    %r13,%rcx
    3a67:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3a6b:	48 8d 15 ee 1f 00 00 	lea    0x1fee(%rip),%rdx        # 5a60 <io_thread>
    3a72:	4c 8d 6b 40          	lea    0x40(%rbx),%r13
    3a76:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3a7d:	e8 4e ea ff ff       	call   24d0 <pthread_create@plt>
    3a82:	ba 08 00 00 00       	mov    $0x8,%edx
    3a87:	48 8d 35 1d 4a 00 00 	lea    0x4a1d(%rip),%rsi        # 84ab <_IO_stdin_used+0x4ab>
    3a8e:	31 c0                	xor    %eax,%eax
    3a90:	bf 01 00 00 00       	mov    $0x1,%edi
    3a95:	e8 16 ea ff ff       	call   24b0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a9a:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3a9f:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    3aa5:	48 89 04 24          	mov    %rax,(%rsp)
    3aa9:	44 89 f2             	mov    %r14d,%edx
    3aac:	48 8d 35 0e 4a 00 00 	lea    0x4a0e(%rip),%rsi        # 84c1 <_IO_stdin_used+0x4c1>
    3ab3:	bf 01 00 00 00       	mov    $0x1,%edi
    3ab8:	31 c0                	xor    %eax,%eax
    3aba:	e8 f1 e9 ff ff       	call   24b0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3abf:	be 08 00 00 00       	mov    $0x8,%esi
    3ac4:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3ac9:	48 8b 05 78 52 00 00 	mov    0x5278(%rip),%rax        # 8d48 <_IO_stdin_used+0xd48>
    thread_data[x].type = EXTERNAL;
    3ad0:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    thread_data[x].task_count = 0;
    3ad7:	48 89 45 40          	mov    %rax,0x40(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3adb:	e8 20 e9 ff ff       	call   2400 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3ae0:	48 8b bc 24 b0 00 00 00 	mov    0xb0(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3ae8:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3aed:	c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3af7:	48 89 45 50          	mov    %rax,0x50(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3afb:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3afe:	bf 02 00 00 00       	mov    $0x2,%edi
    3b03:	e8 f8 e8 ff ff       	call   2400 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3b08:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b0d:	48 89 e9             	mov    %rbp,%rcx
    3b10:	4c 89 ef             	mov    %r13,%rdi
    thread_data[x].threads = my_thread_data;
    3b13:	48 89 45 18          	mov    %rax,0x18(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b17:	48 8d 15 82 0a 00 00 	lea    0xa82(%rip),%rdx        # 45a0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b1e:	49 83 c5 08          	add    $0x8,%r13
    3b22:	48 81 c5 e0 00 00 00 	add    $0xe0,%rbp
      my_thread_data[n] = &thread_data[n]; 
    3b29:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b2c:	48 8b 34 24          	mov    (%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3b30:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3b34:	48 8b 05 ed 51 00 00 	mov    0x51ed(%rip),%rax        # 8d28 <_IO_stdin_used+0xd28>
    thread_data[x].thread_index = x;
    3b3b:	44 89 b5 24 ff ff ff 	mov    %r14d,-0xdc(%rbp)
    thread_data[x].thread_count = thread_count;
    3b42:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b49:	e8 82 e9 ff ff       	call   24d0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b4e:	48 83 04 24 38       	addq   $0x38,(%rsp)
    3b53:	48 83 84 24 b0 00 00 00 10 	addq   $0x10,0xb0(%rsp)
    3b5c:	41 83 fe 08          	cmp    $0x8,%r14d
    3b60:	75 47                	jne    3ba9 <main+0x1539>
    3b62:	41 be 09 00 00 00    	mov    $0x9,%r14d
    3b68:	e9 3c ff ff ff       	jmp    3aa9 <main+0x1439>
        other = (x + 1) % total_threads;
    3b6d:	44 8b 64 24 18       	mov    0x18(%rsp),%r12d
        my_thread_data[1] = &thread_data[other]; 
    3b72:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3b77:	48 89 5c 24 40       	mov    %rbx,0x40(%rsp)
    3b7c:	45 31 c0             	xor    %r8d,%r8d
    3b7f:	4a 8d 14 e5 00 00 00 00 	lea    0x0(,%r12,8),%rdx
        other = (x + 1) % total_threads;
    3b87:	45 89 e5             	mov    %r12d,%r13d
        my_thread_data[1] = &thread_data[other]; 
    3b8a:	4c 29 e2             	sub    %r12,%rdx
    3b8d:	48 c1 e2 05          	shl    $0x5,%rdx
    3b91:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    3b94:	4c 89 c8             	mov    %r9,%rax
    3b97:	e9 e9 ee ff ff       	jmp    2a85 <main+0x415>
            CPU_SET(j, sendercpu);
    3b9c:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
    3ba4:	e9 71 ef ff ff       	jmp    2b1a <main+0x4aa>
    3ba9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3bae:	48 8d 2d 29 49 00 00 	lea    0x4929(%rip),%rbp        # 84de <_IO_stdin_used+0x4de>
    3bb5:	4c 8d 68 04          	lea    0x4(%rax),%r13
    3bb9:	4c 8d a0 c4 08 00 00 	lea    0x8c4(%rax),%r12
    3bc0:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    3bc4:	41 8b 55 00          	mov    0x0(%r13),%edx
    3bc8:	48 89 ee             	mov    %rbp,%rsi
    3bcb:	bf 01 00 00 00       	mov    $0x1,%edi
    3bd0:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3bd2:	49 81 c5 e0 00 00 00 	add    $0xe0,%r13
    3bd9:	e8 d2 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bde:	4d 39 ec             	cmp    %r13,%r12
    3be1:	75 dd                	jne    3bc0 <main+0x1550>
    3be3:	48 8d 3d 07 49 00 00 	lea    0x4907(%rip),%rdi        # 84f1 <_IO_stdin_used+0x4f1>
    3bea:	45 31 ed             	xor    %r13d,%r13d
    3bed:	4c 8d a4 24 e0 00 00 00 	lea    0xe0(%rsp),%r12
    3bf5:	e8 36 e7 ff ff       	call   2330 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3bfa:	48 8d 2d 0e 49 00 00 	lea    0x490e(%rip),%rbp        # 850f <_IO_stdin_used+0x50f>
    void * result; 
    pthread_join(thread[x], &result);
    3c01:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    3c05:	4c 89 e6             	mov    %r12,%rsi
    3c08:	e8 53 e9 ff ff       	call   2560 <pthread_join@plt>
    3c0d:	44 89 ea             	mov    %r13d,%edx
    3c10:	48 89 ee             	mov    %rbp,%rsi
    3c13:	bf 01 00 00 00       	mov    $0x1,%edi
    3c18:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3c1a:	49 83 c5 01          	add    $0x1,%r13
    3c1e:	e8 8d e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c23:	49 83 fd 0a          	cmp    $0xa,%r13
    3c27:	75 d8                	jne    3c01 <main+0x1591>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c29:	be 08 00 00 00       	mov    $0x8,%esi
    3c2e:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3c33:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c35:	e8 c6 e7 ff ff       	call   2400 <calloc@plt>
    3c3a:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3c3f:	48 89 c5             	mov    %rax,%rbp
    3c42:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c44:	49 89 d1             	mov    %rdx,%r9
    3c47:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c4a:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3c4e:	45 85 d2             	test   %r10d,%r10d
    3c51:	0f 8e a9 00 00 00    	jle    3d00 <main+0x1690>
    3c57:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3c5b:	4d 63 c2             	movslq %r10d,%r8
    3c5e:	48 63 cb             	movslq %ebx,%rcx
    3c61:	49 c1 e0 09          	shl    $0x9,%r8
    3c65:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    3c6a:	49 01 f8             	add    %rdi,%r8
    3c6d:	0f 1f 00             	nopl   (%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c70:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c77:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3c7e:	48 83 c6 60          	add    $0x60,%rsi
    3c82:	f3 0f 7e a1 80 01 00 00 	movq   0x180(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c8a:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3c8e:	f3 0f 7e 99 00 03 00 00 	movq   0x300(%rcx),%xmm3
    3c96:	f3 0f 7e 91 80 04 00 00 	movq   0x480(%rcx),%xmm2
    3c9e:	f3 0f 7e 89 00 06 00 00 	movq   0x600(%rcx),%xmm1
    3ca6:	0f 16 a1 00 02 00 00 	movhps 0x200(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3cad:	f3 0f 7e 81 80 07 00 00 	movq   0x780(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3cb5:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    3cbc:	0f 16 99 80 03 00 00 	movhps 0x380(%rcx),%xmm3
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3cc3:	0f 16 91 00 05 00 00 	movhps 0x500(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3cca:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3cce:	0f 16 89 80 06 00 00 	movhps 0x680(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3cd5:	0f 16 81 00 08 00 00 	movhps 0x800(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3cdc:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3ce0:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3ce4:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3ce8:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3cec:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3cf0:	4c 39 c7             	cmp    %r8,%rdi
    3cf3:	0f 85 77 ff ff ff    	jne    3c70 <main+0x1600>
    3cf9:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3cfd:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3d00:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    3d07:	45 85 db             	test   %r11d,%r11d
    3d0a:	75 08                	jne    3d14 <main+0x16a4>
    3d0c:	45 89 fb             	mov    %r15d,%r11d
    3d0f:	e9 36 ff ff ff       	jmp    3c4a <main+0x15da>
  for (int k = 0 ; k < group_count ; k++) {
    3d14:	83 c0 02             	add    $0x2,%eax
    3d17:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    3d1e:	83 f8 06             	cmp    $0x6,%eax
    3d21:	0f 85 1d ff ff ff    	jne    3c44 <main+0x15d4>
    3d27:	48 8d 3d f5 47 00 00 	lea    0x47f5(%rip),%rdi        # 8523 <_IO_stdin_used+0x523>
    3d2e:	e8 fd e5 ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3d33:	48 8d 35 c5 46 00 00 	lea    0x46c5(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3d3a:	48 8d 3d fa 47 00 00 	lea    0x47fa(%rip),%rdi        # 853b <_IO_stdin_used+0x53b>
    3d41:	e8 aa e7 ff ff       	call   24f0 <fopen@plt>
    3d46:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas2_size; x++) {
    3d49:	85 db                	test   %ebx,%ebx
    3d4b:	7e 73                	jle    3dc0 <main+0x1750>
    3d4d:	48 63 db             	movslq %ebx,%rbx
    3d50:	49 89 ef             	mov    %rbp,%r15
    3d53:	4c 8d 35 84 46 00 00 	lea    0x4684(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    3d5a:	48 8d 6c dd 00       	lea    0x0(%rbp,%rbx,8),%rbp
    3d5f:	4c 8d 2d bc 46 00 00 	lea    0x46bc(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    char * c = calloc(250, sizeof(char));
    3d66:	be 01 00 00 00       	mov    $0x1,%esi
    3d6b:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3d70:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    3d74:	e8 87 e6 ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3d79:	4c 89 f1             	mov    %r14,%rcx
    3d7c:	ba fa 00 00 00       	mov    $0xfa,%edx
    3d81:	be 01 00 00 00       	mov    $0x1,%esi
    3d86:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3d89:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3d8d:	48 89 df             	mov    %rbx,%rdi
    3d90:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3d97:	31 c0                	xor    %eax,%eax
    3d99:	e8 02 e8 ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3d9e:	48 89 da             	mov    %rbx,%rdx
    3da1:	4c 89 ee             	mov    %r13,%rsi
    3da4:	bf 01 00 00 00       	mov    $0x1,%edi
    3da9:	31 c0                	xor    %eax,%eax
    3dab:	e8 00 e7 ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3db0:	4c 89 e6             	mov    %r12,%rsi
    3db3:	48 89 df             	mov    %rbx,%rdi
    3db6:	e8 05 e6 ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3dbb:	49 39 ef             	cmp    %rbp,%r15
    3dbe:	75 a6                	jne    3d66 <main+0x16f6>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3dc0:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    3dca:	4c 89 e7             	mov    %r12,%rdi
  long received = 0;
    3dcd:	31 db                	xor    %ebx,%ebx
  fclose(m2);
    3dcf:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
    3dd5:	e8 86 e5 ff ff       	call   2360 <fclose@plt>
  long times_sent = 0;
    3dda:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  long sents = 0;
    3de3:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long sends = 0;
    3dec:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long ingests = 0;
    3df5:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
  long total = 0;
    3dfe:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  int datas2_size = 0; 
    3e07:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    3e0f:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    3e14:	4c 8b b4 24 98 00 00 00 	mov    0x98(%rsp),%r14
    3e1c:	45 89 e5             	mov    %r12d,%r13d
    3e1f:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    3e24:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
      int x = (k * threads_per_group) + d;
    3e29:	44 89 e8             	mov    %r13d,%eax
    3e2c:	41 83 c5 01          	add    $0x1,%r13d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3e30:	bf 0a 00 00 00       	mov    $0xa,%edi
        other = abs(x - 1) % total_threads;
    3e35:	41 f6 c5 01          	test   $0x1,%r13b
    3e39:	8d 50 02             	lea    0x2(%rax),%edx
    3e3c:	0f 44 c2             	cmove  %edx,%eax
    3e3f:	4c 63 e0             	movslq %eax,%r12
    3e42:	e8 c9 e4 ff ff       	call   2310 <putchar@plt>
    3e47:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3e4c:	bf 01 00 00 00       	mov    $0x1,%edi
    3e51:	48 8d 35 ec 46 00 00 	lea    0x46ec(%rip),%rsi        # 8544 <_IO_stdin_used+0x544>
    3e58:	48 8b 10             	mov    (%rax),%rdx
    3e5b:	31 c0                	xor    %eax,%eax
    3e5d:	e8 4e e6 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e62:	41 8b 56 40          	mov    0x40(%r14),%edx
    3e66:	85 d2                	test   %edx,%edx
    3e68:	0f 8e 77 05 00 00    	jle    43e5 <main+0x1d75>
    3e6e:	48 63 ca             	movslq %edx,%rcx
    3e71:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    3e75:	31 d2                	xor    %edx,%edx
    3e77:	48 c1 e1 09          	shl    $0x9,%rcx
    3e7b:	48 01 c1             	add    %rax,%rcx
    3e7e:	66 90                	xchg   %ax,%ax
        v += thread_data[me].tasks[n].v;
    3e80:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e87:	48 05 00 02 00 00    	add    $0x200,%rax
    3e8d:	48 39 c8             	cmp    %rcx,%rax
    3e90:	75 ee                	jne    3e80 <main+0x1810>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3e92:	4a 8d 04 e5 00 00 00 00 	lea    0x0(,%r12,8),%rax
    3e9a:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3e9f:	4c 29 e0             	sub    %r12,%rax
    3ea2:	48 c1 e0 05          	shl    $0x5,%rax
    3ea6:	48 01 f8             	add    %rdi,%rax
    3ea9:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3ead:	85 c9                	test   %ecx,%ecx
    3eaf:	7e 21                	jle    3ed2 <main+0x1862>
    3eb1:	48 8b 40 38          	mov    0x38(%rax),%rax
    3eb5:	48 c1 e1 09          	shl    $0x9,%rcx
    3eb9:	48 01 c1             	add    %rax,%rcx
    3ebc:	0f 1f 40 00          	nopl   0x0(%rax)
        v += thread_data[other].tasks[n].v;
    3ec0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3ec7:	48 05 00 02 00 00    	add    $0x200,%rax
    3ecd:	48 39 c8             	cmp    %rcx,%rax
    3ed0:	75 ee                	jne    3ec0 <main+0x1850>
    3ed2:	48 8d 35 80 46 00 00 	lea    0x4680(%rip),%rsi        # 8559 <_IO_stdin_used+0x559>
    3ed9:	bf 01 00 00 00       	mov    $0x1,%edi
    3ede:	31 c0                	xor    %eax,%eax
    3ee0:	e8 cb e5 ff ff       	call   24b0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3ee5:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3eea:	bf 01 00 00 00       	mov    $0x1,%edi
    3eef:	48 8d 35 6a 49 00 00 	lea    0x496a(%rip),%rsi        # 8860 <_IO_stdin_used+0x860>
    3ef6:	48 8b 08             	mov    (%rax),%rcx
    3ef9:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3f03:	48 f7 e9             	imul   %rcx
    3f06:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3f0a:	31 c0                	xor    %eax,%eax
    3f0c:	48 d1 fa             	sar    %rdx
    3f0f:	48 29 ca             	sub    %rcx,%rdx
    3f12:	e8 99 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3f17:	bf 0a 00 00 00       	mov    $0xa,%edi
    3f1c:	e8 ef e3 ff ff       	call   2310 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3f21:	45 8b 66 40          	mov    0x40(%r14),%r12d
    3f25:	45 85 e4             	test   %r12d,%r12d
    3f28:	0f 8e 60 01 00 00    	jle    408e <main+0x1a1e>
    3f2e:	4c 8b 5c 24 28       	mov    0x28(%rsp),%r11
    3f33:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3f38:	44 89 2c 24          	mov    %r13d,(%rsp)
    3f3c:	31 d2                	xor    %edx,%edx
    3f3e:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3f43:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    3f48:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    3f4d:	0f 1f 00             	nopl   (%rax)
        total += thread_data[x].tasks[n].n;
    3f50:	49 8b 46 38          	mov    0x38(%r14),%rax
    3f54:	49 89 d1             	mov    %rdx,%r9
        times_sent += thread_data[x].tasks[n].message->times_sent ;
    3f57:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    3f5c:	41 89 d5             	mov    %edx,%r13d
        total += thread_data[x].tasks[n].n;
    3f5f:	49 c1 e1 09          	shl    $0x9,%r9
        times_sent += thread_data[x].tasks[n].message->times_sent ;
    3f63:	45 31 e4             	xor    %r12d,%r12d
        total += thread_data[x].tasks[n].n;
    3f66:	4c 01 c8             	add    %r9,%rax
        times_sent += thread_data[x].tasks[n].message->times_sent ;
    3f69:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        total += thread_data[x].tasks[n].n;
    3f6e:	4c 03 98 08 01 00 00 	add    0x108(%rax),%r11
        ingests += thread_data[x].tasks[n].ingest_count;
    3f75:	4c 03 90 68 01 00 00 	add    0x168(%rax),%r10
        sends += thread_data[x].tasks[n].sends;
    3f7c:	48 03 88 78 01 00 00 	add    0x178(%rax),%rcx
        times_sent += thread_data[x].tasks[n].message->times_sent ;
    3f83:	48 8b 80 88 01 00 00 	mov    0x188(%rax),%rax
    3f8a:	4c 89 5c 24 10       	mov    %r11,0x10(%rsp)
    3f8f:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    3f94:	48 03 70 20          	add    0x20(%rax),%rsi
    3f98:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    3f9d:	48 89 74 24 28       	mov    %rsi,0x28(%rsp)
    3fa2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3fa8:	8b 14 24             	mov    (%rsp),%edx
    3fab:	45 89 e0             	mov    %r12d,%r8d
    3fae:	44 89 e9             	mov    %r13d,%ecx
    3fb1:	48 8d 35 ae 45 00 00 	lea    0x45ae(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    3fb8:	bf 01 00 00 00       	mov    $0x1,%edi
    3fbd:	31 c0                	xor    %eax,%eax
    3fbf:	e8 ec e4 ff ff       	call   24b0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fc4:	49 8b 56 38          	mov    0x38(%r14),%rdx
    3fc8:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
    3fcc:	45 89 e0             	mov    %r12d,%r8d
    3fcf:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3fd4:	48 c1 e0 07          	shl    $0x7,%rax
    3fd8:	48 83 ec 08          	sub    $0x8,%rsp
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3fdc:	49 83 c4 01          	add    $0x1,%r12
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fe0:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    3fe8:	48 8b 38             	mov    (%rax),%rdi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3feb:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3ff2:	48 8b 87 10 03 00 00 	mov    0x310(%rdi),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3ff9:	48 8b 96 08 03 00 00 	mov    0x308(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4000:	48 8b b6 10 03 00 00 	mov    0x310(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4007:	48 8b 8f 08 03 00 00 	mov    0x308(%rdi),%rcx
    400e:	bf 01 00 00 00       	mov    $0x1,%edi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    4013:	48 01 c3             	add    %rax,%rbx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4016:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4019:	49 01 cf             	add    %rcx,%r15
    401c:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4020:	48 01 f3             	add    %rsi,%rbx
    4023:	50                   	push   %rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4024:	49 01 d7             	add    %rdx,%r15
    4027:	8b 54 24 10          	mov    0x10(%rsp),%edx
    402b:	44 89 e9             	mov    %r13d,%ecx
    402e:	48 8d 35 4b 48 00 00 	lea    0x484b(%rip),%rsi        # 8880 <_IO_stdin_used+0x880>
    4035:	31 c0                	xor    %eax,%eax
    4037:	e8 74 e4 ff ff       	call   24b0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    403c:	41 5a                	pop    %r10
    403e:	41 5b                	pop    %r11
    4040:	49 83 fc 06          	cmp    $0x6,%r12
    4044:	0f 85 5e ff ff ff    	jne    3fa8 <main+0x1938>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    404a:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    404f:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    4054:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    4059:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    405e:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    4063:	48 83 c2 01          	add    $0x1,%rdx
    4067:	41 39 56 40          	cmp    %edx,0x40(%r14)
    406b:	0f 8f df fe ff ff    	jg     3f50 <main+0x18e0>
    4071:	4c 89 5c 24 28       	mov    %r11,0x28(%rsp)
    4076:	44 8b 2c 24          	mov    (%rsp),%r13d
    407a:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    407f:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    4084:	48 89 74 24 30       	mov    %rsi,0x30(%rsp)
    4089:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    408e:	45 31 ff             	xor    %r15d,%r15d
    4091:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    4099:	4c 8d 25 00 48 00 00 	lea    0x4800(%rip),%r12        # 88a0 <_IO_stdin_used+0x8a0>
    40a0:	7e 5e                	jle    4100 <main+0x1a90>
    40a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    40a8:	49 8b 86 90 00 00 00 	mov    0x90(%r14),%rax
    40af:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    40b3:	48 83 ec 08          	sub    $0x8,%rsp
    40b7:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    40bc:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    40c0:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    40c4:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    40c8:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    40cc:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    40cf:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    40d3:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    40d6:	48 f7 e5             	mul    %rbp
    40d9:	8b 49 20             	mov    0x20(%rcx),%ecx
    40dc:	56                   	push   %rsi
    40dd:	31 c0                	xor    %eax,%eax
    40df:	4c 89 e6             	mov    %r12,%rsi
    40e2:	48 c1 ea 12          	shr    $0x12,%rdx
    40e6:	49 89 d1             	mov    %rdx,%r9
    40e9:	ba 02 00 00 00       	mov    $0x2,%edx
    40ee:	e8 bd e3 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    40f3:	41 58                	pop    %r8
    40f5:	41 59                	pop    %r9
    40f7:	4d 39 be a0 00 00 00 	cmp    %r15,0xa0(%r14)
    40fe:	7f a8                	jg     40a8 <main+0x1a38>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4100:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    4107:	85 d2                	test   %edx,%edx
    4109:	0f 8e 01 01 00 00    	jle    4210 <main+0x1ba0>
    410f:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4114:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4118:	45 31 ff             	xor    %r15d,%r15d
    411b:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    4120:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    4124:	44 89 fb             	mov    %r15d,%ebx
    4127:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    412f:	8b 30                	mov    (%rax),%esi
    4131:	85 f6                	test   %esi,%esi
    4133:	0f 8e c0 00 00 00    	jle    41f9 <main+0x1b89>
    4139:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    413e:	31 d2                	xor    %edx,%edx
    4140:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4144:	49 89 f8             	mov    %rdi,%r8
    4147:	48 89 d7             	mov    %rdx,%rdi
    414a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4150:	49 89 fc             	mov    %rdi,%r12
    4153:	45 31 ff             	xor    %r15d,%r15d
    4156:	49 c1 e4 08          	shl    $0x8,%r12
    415a:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    415e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4164:	85 d2                	test   %edx,%edx
    4166:	7e 76                	jle    41de <main+0x1b6e>
    4168:	48 89 3c 24          	mov    %rdi,(%rsp)
    416c:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4170:	4c 89 f9             	mov    %r15,%rcx
    4173:	48 83 ec 08          	sub    $0x8,%rsp
    4177:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    417c:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4180:	48 c1 e1 05          	shl    $0x5,%rcx
    4184:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    418b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    418f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    4193:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4196:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    419a:	4c 2b 01             	sub    (%rcx),%r8
    419d:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    419e:	48 f7 e5             	mul    %rbp
    41a1:	89 d9                	mov    %ebx,%ecx
    41a3:	48 8d 35 46 47 00 00 	lea    0x4746(%rip),%rsi        # 88f0 <_IO_stdin_used+0x8f0>
    41aa:	31 c0                	xor    %eax,%eax
    41ac:	48 c1 ea 12          	shr    $0x12,%rdx
    41b0:	49 89 d1             	mov    %rdx,%r9
    41b3:	ba 02 00 00 00       	mov    $0x2,%edx
    41b8:	e8 f3 e2 ff ff       	call   24b0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    41bd:	4d 8b 46 50          	mov    0x50(%r14),%r8
    41c1:	5e                   	pop    %rsi
    41c2:	5f                   	pop    %rdi
    41c3:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    41c7:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    41cb:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    41cf:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    41d6:	7f 98                	jg     4170 <main+0x1b00>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    41d8:	48 8b 3c 24          	mov    (%rsp),%rdi
    41dc:	8b 32                	mov    (%rdx),%esi
    41de:	48 83 c7 01          	add    $0x1,%rdi
    41e2:	39 fe                	cmp    %edi,%esi
    41e4:	0f 8f 66 ff ff ff    	jg     4150 <main+0x1ae0>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    41ea:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    41ef:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    41f6:	4c 89 c7             	mov    %r8,%rdi
    41f9:	49 83 c7 01          	add    $0x1,%r15
    41fd:	44 39 fa             	cmp    %r15d,%edx
    4200:	0f 8f 1a ff ff ff    	jg     4120 <main+0x1ab0>
    4206:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    420b:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    4210:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    4216:	49 81 c6 e0 00 00 00 	add    $0xe0,%r14
    421d:	44 39 6c 24 48       	cmp    %r13d,0x48(%rsp)
    4222:	0f 85 01 fc ff ff    	jne    3e29 <main+0x17b9>
  for (int k = 0 ; k < group_count ; k++) {
    4228:	48 83 84 24 80 00 00 00 30 	addq   $0x30,0x80(%rsp)
    4231:	44 8b 44 24 48       	mov    0x48(%rsp),%r8d
    4236:	48 81 84 24 98 00 00 00 c0 01 00 00 	addq   $0x1c0,0x98(%rsp)
    4242:	41 83 f8 05          	cmp    $0x5,%r8d
    4246:	74 08                	je     4250 <main+0x1be0>
    4248:	45 89 c4             	mov    %r8d,%r12d
    424b:	e9 b7 fb ff ff       	jmp    3e07 <main+0x1797>
    4250:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    4255:	bf 01 00 00 00       	mov    $0x1,%edi
    425a:	31 c0                	xor    %eax,%eax
    425c:	49 89 df             	mov    %rbx,%r15
    425f:	48 8d 35 10 43 00 00 	lea    0x4310(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    4266:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4270:	4c 89 f2             	mov    %r14,%rdx
    4273:	e8 38 e2 ff ff       	call   24b0 <__printf_chk@plt>
    4278:	bf 0a 00 00 00       	mov    $0xa,%edi
    427d:	e8 8e e0 ff ff       	call   2310 <putchar@plt>
    4282:	48 8b bc 24 90 00 00 00 	mov    0x90(%rsp),%rdi
    428a:	48 8d 35 b7 46 00 00 	lea    0x46b7(%rip),%rsi        # 8948 <_IO_stdin_used+0x948>
    4291:	31 c0                	xor    %eax,%eax
    4293:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    4297:	bf 01 00 00 00       	mov    $0x1,%edi
    429c:	e8 0f e2 ff ff       	call   24b0 <__printf_chk@plt>
    42a1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    42a6:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    42ab:	48 8d 35 be 46 00 00 	lea    0x46be(%rip),%rsi        # 8970 <_IO_stdin_used+0x970>
    42b2:	48 f7 eb             	imul   %rbx
    42b5:	48 c1 ff 3f          	sar    $0x3f,%rdi
    42b9:	31 c0                	xor    %eax,%eax
    42bb:	48 d1 fa             	sar    %rdx
    42be:	48 29 fa             	sub    %rdi,%rdx
    42c1:	bf 01 00 00 00       	mov    $0x1,%edi
    42c6:	e8 e5 e1 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    42cb:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    42d0:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    42d5:	48 8d 35 c4 46 00 00 	lea    0x46c4(%rip),%rsi        # 89a0 <_IO_stdin_used+0x9a0>
    42dc:	48 f7 eb             	imul   %rbx
    42df:	48 c1 ff 3f          	sar    $0x3f,%rdi
    42e3:	31 c0                	xor    %eax,%eax
    42e5:	48 d1 fa             	sar    %rdx
    42e8:	48 29 fa             	sub    %rdi,%rdx
    42eb:	bf 01 00 00 00       	mov    $0x1,%edi
    42f0:	e8 bb e1 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    42f5:	4c 89 f0             	mov    %r14,%rax
    42f8:	bf 01 00 00 00       	mov    $0x1,%edi
    42fd:	48 8d 35 cc 46 00 00 	lea    0x46cc(%rip),%rsi        # 89d0 <_IO_stdin_used+0x9d0>
    4304:	48 f7 eb             	imul   %rbx
    4307:	4c 89 f0             	mov    %r14,%rax
    430a:	48 c1 f8 3f          	sar    $0x3f,%rax
    430e:	48 d1 fa             	sar    %rdx
    4311:	48 29 c2             	sub    %rax,%rdx
    4314:	31 c0                	xor    %eax,%eax
    4316:	e8 95 e1 ff ff       	call   24b0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    431b:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4320:	bf 01 00 00 00       	mov    $0x1,%edi
    4325:	48 8d 35 5e 42 00 00 	lea    0x425e(%rip),%rsi        # 858a <_IO_stdin_used+0x58a>
    432c:	48 f7 eb             	imul   %rbx
    432f:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4334:	48 c1 f8 3f          	sar    $0x3f,%rax
    4338:	48 d1 fa             	sar    %rdx
    433b:	48 29 c2             	sub    %rax,%rdx
    433e:	31 c0                	xor    %eax,%eax
    4340:	48 89 d5             	mov    %rdx,%rbp
    4343:	e8 68 e1 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
    4348:	4c 89 f8             	mov    %r15,%rax
    434b:	bf 01 00 00 00       	mov    $0x1,%edi
    4350:	48 8d 35 99 46 00 00 	lea    0x4699(%rip),%rsi        # 89f0 <_IO_stdin_used+0x9f0>
    4357:	48 f7 eb             	imul   %rbx
    435a:	4c 89 f8             	mov    %r15,%rax
    435d:	48 c1 f8 3f          	sar    $0x3f,%rax
    4361:	48 89 d3             	mov    %rdx,%rbx
    4364:	48 d1 fb             	sar    %rbx
    4367:	48 29 c3             	sub    %rax,%rbx
    436a:	31 c0                	xor    %eax,%eax
    436c:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    436f:	48 29 eb             	sub    %rbp,%rbx
    4372:	e8 39 e1 ff ff       	call   24b0 <__printf_chk@plt>
    4377:	48 89 da             	mov    %rbx,%rdx
    437a:	bf 01 00 00 00       	mov    $0x1,%edi
    437f:	31 c0                	xor    %eax,%eax
    4381:	48 8d 35 1e 42 00 00 	lea    0x421e(%rip),%rsi        # 85a6 <_IO_stdin_used+0x5a6>
    4388:	e8 23 e1 ff ff       	call   24b0 <__printf_chk@plt>
    438d:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    4392:	48 8d 35 1d 42 00 00 	lea    0x421d(%rip),%rsi        # 85b6 <_IO_stdin_used+0x5b6>
    4399:	31 c0                	xor    %eax,%eax
    439b:	bf 01 00 00 00       	mov    $0x1,%edi
    43a0:	48 89 da             	mov    %rbx,%rdx
    43a3:	e8 08 e1 ff ff       	call   24b0 <__printf_chk@plt>
    43a8:	31 c0                	xor    %eax,%eax
    43aa:	48 89 da             	mov    %rbx,%rdx
    43ad:	bf 01 00 00 00       	mov    $0x1,%edi
    43b2:	48 8d 35 15 42 00 00 	lea    0x4215(%rip),%rsi        # 85ce <_IO_stdin_used+0x5ce>
    43b9:	e8 f2 e0 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Message times sent %ld\n", times_sent);
  printf("Message times received %ld\n", times_sent);
  return 0;

}
    43be:	48 8b 84 24 e8 00 00 00 	mov    0xe8(%rsp),%rax
    43c6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    43cf:	75 25                	jne    43f6 <main+0x1d86>
    43d1:	48 81 c4 f8 00 00 00 	add    $0xf8,%rsp
    43d8:	31 c0                	xor    %eax,%eax
    43da:	5b                   	pop    %rbx
    43db:	5d                   	pop    %rbp
    43dc:	41 5c                	pop    %r12
    43de:	41 5d                	pop    %r13
    43e0:	41 5e                	pop    %r14
    43e2:	41 5f                	pop    %r15
    43e4:	c3                   	ret
      long v = 0;
    43e5:	31 d2                	xor    %edx,%edx
    43e7:	e9 a6 fa ff ff       	jmp    3e92 <main+0x1822>
            exit(1);
    43ec:	bf 01 00 00 00       	mov    $0x1,%edi
    43f1:	e8 1a e1 ff ff       	call   2510 <exit@plt>
}
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
int do_protected_write(struct BarrierTask *data) {
    44f0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    44f4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    44fb:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    44ff:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4507:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    450b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    450f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4516:	48 85 c9             	test   %rcx,%rcx
    4519:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4520:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4524:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4528:	31 c0                	xor    %eax,%eax
    452a:	c3                   	ret
    452b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004530 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4530:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4534:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    453b:	85 c9                	test   %ecx,%ecx
    453d:	7e 4f                	jle    458e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    453f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4546:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    454d:	48 c1 e1 09          	shl    $0x9,%rcx
    4551:	48 8b 50 18          	mov    0x18(%rax),%rdx
    4555:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    4559:	48 8b 70 38          	mov    0x38(%rax),%rsi
    455d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    455f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4563:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4568:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4570:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4578:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    4583:	48 05 00 02 00 00    	add    $0x200,%rax
    4589:	48 39 c1             	cmp    %rax,%rcx
    458c:	75 da                	jne    4568 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    458e:	0f ae f8             	sfence
}
    4591:	31 c0                	xor    %eax,%eax
    4593:	c3                   	ret
    4594:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    459f:	90                   	nop

00000000000045a0 <external_thread>:
void * external_thread(void *arg) {
    45a0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    45a4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    45a8:	0f 85 fb 00 00 00    	jne    46a9 <external_thread+0x109>
void * external_thread(void *arg) {
    45ae:	41 57                	push   %r15
    45b0:	49 89 ff             	mov    %rdi,%r15
    45b3:	41 56                	push   %r14
    45b5:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    45b7:	4c 8d 2d 46 3a 00 00 	lea    0x3a46(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    45be:	41 54                	push   %r12
    45c0:	55                   	push   %rbp
    45c1:	53                   	push   %rbx
    45c2:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    45c6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    45cc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    45d0:	85 c9                	test   %ecx,%ecx
    45d2:	7e 6e                	jle    4642 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
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
				if (data->buffers[b]->buffer[x].available == 0) {
    45fb:	48 89 dd             	mov    %rbx,%rbp
    45fe:	48 c1 e5 08          	shl    $0x8,%rbp
    4602:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4606:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    460d:	45 85 c0             	test   %r8d,%r8d
    4610:	74 36                	je     4648 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4612:	48 83 c3 01          	add    $0x1,%rbx
    4616:	39 da                	cmp    %ebx,%edx
    4618:	7f e1                	jg     45fb <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    461a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4621:	49 83 c4 01          	add    $0x1,%r12
    4625:	44 39 e1             	cmp    %r12d,%ecx
    4628:	7f b6                	jg     45e0 <external_thread+0x40>
  while (data->running == 1) {
    462a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    462f:	74 9f                	je     45d0 <external_thread+0x30>
}
    4631:	48 83 c4 08          	add    $0x8,%rsp
    4635:	31 c0                	xor    %eax,%eax
    4637:	5b                   	pop    %rbx
    4638:	5d                   	pop    %rbp
    4639:	41 5c                	pop    %r12
    463b:	41 5d                	pop    %r13
    463d:	41 5e                	pop    %r14
    463f:	41 5f                	pop    %r15
    4641:	c3                   	ret
  while (data->running == 1) {
    4642:	eb fe                	jmp    4642 <external_thread+0xa2>
    4644:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    4648:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    464b:	48 8b 06             	mov    (%rsi),%rax
    464e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4652:	48 01 ef             	add    %rbp,%rdi
    4655:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    465c:	48 c1 e6 05          	shl    $0x5,%rsi
    4660:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4667:	bf 04 00 00 00       	mov    $0x4,%edi
    466c:	e8 df dc ff ff       	call   2350 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4671:	49 8b 47 50          	mov    0x50(%r15),%rax
    4675:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    4679:	48 8b 40 08          	mov    0x8(%rax),%rax
    467d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    4688:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    468b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    468f:	48 83 c3 01          	add    $0x1,%rbx
    4693:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4697:	48 8b 06             	mov    (%rsi),%rax
    469a:	8b 10                	mov    (%rax),%edx
    469c:	39 da                	cmp    %ebx,%edx
    469e:	0f 8f 53 ff ff ff    	jg     45f7 <external_thread+0x57>
    46a4:	e9 71 ff ff ff       	jmp    461a <external_thread+0x7a>
}
    46a9:	31 c0                	xor    %eax,%eax
    46ab:	c3                   	ret
    46ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000046b0 <timer_thread>:
void* timer_thread(void *arg) {
    46b0:	f3 0f 1e fa          	endbr64
    46b4:	41 57                	push   %r15
    46b6:	48 8d 35 53 39 00 00 	lea    0x3953(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    46bd:	41 56                	push   %r14
    46bf:	49 89 fe             	mov    %rdi,%r14
    46c2:	41 55                	push   %r13
    46c4:	41 54                	push   %r12
    46c6:	55                   	push   %rbp
    46c7:	53                   	push   %rbx
    46c8:	48 83 ec 68          	sub    $0x68,%rsp
    46cc:	8b 57 04             	mov    0x4(%rdi),%edx
    46cf:	bf 01 00 00 00       	mov    $0x1,%edi
    46d4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    46dd:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    46e2:	31 c0                	xor    %eax,%eax
    46e4:	e8 c7 dd ff ff       	call   24b0 <__printf_chk@plt>
  struct timespec preempt = {
    46e9:	66 0f 6f 05 1f 45 00 00 	movdqa 0x451f(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    46f1:	ba 88 13 00 00       	mov    $0x1388,%edx
    46f6:	31 c0                	xor    %eax,%eax
    46f8:	48 8d 35 23 39 00 00 	lea    0x3923(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    46ff:	bf 01 00 00 00       	mov    $0x1,%edi
    4704:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    4709:	e8 a2 dd ff ff       	call   24b0 <__printf_chk@plt>
  while (data->running && n < times) {
    470e:	41 8b 5e 44          	mov    0x44(%r14),%ebx
    4712:	85 db                	test   %ebx,%ebx
    4714:	0f 84 9c 00 00 00    	je     47b6 <timer_thread+0x106>
  int n = 0;
    471a:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    471d:	31 db                	xor    %ebx,%ebx
    471f:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    y++;
    4724:	31 ed                	xor    %ebp,%ebp
    4726:	4c 8d 64 24 20       	lea    0x20(%rsp),%r12
    nanosleep(&preempt , &rem2);
    472b:	4c 89 e7             	mov    %r12,%rdi
    472e:	4c 89 ee             	mov    %r13,%rsi
    n++;
    4731:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    4735:	e8 66 dc ff ff       	call   23a0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    473a:	49 63 46 30          	movslq 0x30(%r14),%rax
    y++;
    473e:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4741:	85 c0                	test   %eax,%eax
    4743:	7e 4a                	jle    478f <timer_thread+0xdf>
    4745:	49 8b 4e 18          	mov    0x18(%r14),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4749:	4c 63 c3             	movslq %ebx,%r8
    474c:	49 c1 e0 09          	shl    $0x9,%r8
    4750:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4754:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count - 1;
    4758:	48 8b 19             	mov    (%rcx),%rbx
    475b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    475d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1;
    4761:	99                   	cltd
    4762:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4765:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1;
    4769:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    476c:	48 63 d2             	movslq %edx,%rdx
    476f:	48 c1 e2 09          	shl    $0x9,%rdx
    4773:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    477e:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    478a:	49 39 c9             	cmp    %rcx,%r9
    478d:	75 c9                	jne    4758 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    478f:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4792:	49 8b 46 18          	mov    0x18(%r14),%rax
  while (data->running && n < times) {
    4796:	41 8b 4e 44          	mov    0x44(%r14),%ecx
    y++;
    479a:	89 fb                	mov    %edi,%ebx
    if (y >= data->threads[0]->task_count) {
    479c:	48 8b 00             	mov    (%rax),%rax
    y++;
    479f:	39 78 40             	cmp    %edi,0x40(%rax)
    47a2:	0f 4e dd             	cmovle %ebp,%ebx
  while (data->running && n < times) {
    47a5:	85 c9                	test   %ecx,%ecx
    47a7:	74 0d                	je     47b6 <timer_thread+0x106>
    47a9:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    47b0:	0f 85 75 ff ff ff    	jne    472b <timer_thread+0x7b>
    47b6:	48 8d 3d 7b 38 00 00 	lea    0x387b(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    47bd:	e8 6e db ff ff       	call   2330 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    47c2:	49 63 56 30          	movslq 0x30(%r14),%rdx
    47c6:	85 d2                	test   %edx,%edx
    47c8:	7e 6b                	jle    4835 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    47ca:	49 63 46 40          	movslq 0x40(%r14),%rax
    47ce:	85 c0                	test   %eax,%eax
    47d0:	7e 63                	jle    4835 <timer_thread+0x185>
    47d2:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    47d6:	4d 8b 46 18          	mov    0x18(%r14),%r8
    47da:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    47e2:	31 c9                	xor    %ecx,%ecx
    47e4:	48 89 c6             	mov    %rax,%rsi
    47e7:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    47eb:	48 8b 40 38          	mov    0x38(%rax),%rax
    47ef:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    47f3:	f7 c6 00 02 00 00    	test   $0x200,%esi
    47f9:	74 15                	je     4810 <timer_thread+0x160>
    47fb:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4805:	48 05 00 02 00 00    	add    $0x200,%rax
    480b:	48 39 c2             	cmp    %rax,%rdx
    480e:	74 1c                	je     482c <timer_thread+0x17c>
      data->threads[x]->tasks[y].sending = 0;
    4810:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    481a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4820:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4827:	48 39 c2             	cmp    %rax,%rdx
    482a:	75 e4                	jne    4810 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    482c:	48 83 c1 08          	add    $0x8,%rcx
    4830:	48 39 cf             	cmp    %rcx,%rdi
    4833:	75 b2                	jne    47e7 <timer_thread+0x137>
  asm volatile ("mfence" ::: "memory");
    4835:	0f ae f0             	mfence
  struct timespec drain = {
    4838:	66 0f 6f 05 e0 43 00 00 	movdqa 0x43e0(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4840:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4845:	49 63 46 28          	movslq 0x28(%r14),%rax
    y++;
    4849:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    484c:	85 c0                	test   %eax,%eax
    484e:	7e 47                	jle    4897 <timer_thread+0x1e7>
    4850:	49 8b 4e 18          	mov    0x18(%r14),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4854:	4c 63 c3             	movslq %ebx,%r8
    4857:	49 c1 e0 09          	shl    $0x9,%r8
    485b:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    485f:	90                   	nop
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4860:	48 8b 19             	mov    (%rcx),%rbx
    4863:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    4865:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4869:	99                   	cltd
    486a:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    486d:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4871:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    4874:	48 63 d2             	movslq %edx,%rdx
    4877:	48 c1 e2 09          	shl    $0x9,%rdx
    487b:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4886:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4892:	49 39 c9             	cmp    %rcx,%r9
    4895:	75 c9                	jne    4860 <timer_thread+0x1b0>
    asm volatile ("mfence" ::: "memory");
    4897:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    489a:	49 8b 76 18          	mov    0x18(%r14),%rsi
    y++;
    489e:	31 db                	xor    %ebx,%ebx
    if (y >= data->threads[0]->task_count) {
    48a0:	48 8b 06             	mov    (%rsi),%rax
    y++;
    48a3:	39 78 40             	cmp    %edi,0x40(%rax)
    48a6:	0f 4f df             	cmovg  %edi,%ebx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48a9:	41 8b 7e 30          	mov    0x30(%r14),%edi
    48ad:	85 ff                	test   %edi,%edi
    48af:	0f 8e c7 01 00 00    	jle    4a7c <timer_thread+0x3cc>
    int all_empty = 1;
    48b5:	89 5c 24 0c          	mov    %ebx,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48b9:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    48bc:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    48c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    48c8:	45 31 e4             	xor    %r12d,%r12d
    48cb:	44 89 eb             	mov    %r13d,%ebx
    48ce:	4a 8d 2c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbp
    48d6:	44 89 e6             	mov    %r12d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    48d9:	85 ff                	test   %edi,%edi
    48db:	0f 8e bf 00 00 00    	jle    49a0 <timer_thread+0x2f0>
    48e1:	4d 89 e2             	mov    %r12,%r10
      y = 0;
    48e4:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    48e6:	45 31 c0             	xor    %r8d,%r8d
    48e9:	49 c1 e2 09          	shl    $0x9,%r10
    48ed:	0f 1f 00             	nopl   (%rax)
          if (x == k) { continue; }
    48f0:	45 39 e8             	cmp    %r13d,%r8d
    48f3:	74 3c                	je     4931 <timer_thread+0x281>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    48f5:	49 8b 56 18          	mov    0x18(%r14),%rdx
    48f9:	48 8b 14 2a          	mov    (%rdx,%rbp,1),%rdx
    48fd:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4901:	4a 8b 8c 12 70 01 00 00 	mov    0x170(%rdx,%r10,1),%rcx
    4909:	48 01 c1             	add    %rax,%rcx
    490c:	48 89 ca             	mov    %rcx,%rdx
    490f:	48 8b 09             	mov    (%rcx),%rcx
    4912:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    4919:	4c 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9
    4920:	4c 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11
    4927:	4d 85 c9             	test   %r9,%r9
    492a:	7f 24                	jg     4950 <timer_thread+0x2a0>
    492c:	4d 85 db             	test   %r11,%r11
    492f:	7f 1f                	jg     4950 <timer_thread+0x2a0>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4931:	41 83 c0 01          	add    $0x1,%r8d
    4935:	48 05 80 01 00 00    	add    $0x180,%rax
    493b:	44 39 c7             	cmp    %r8d,%edi
    493e:	75 b0                	jne    48f0 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    4940:	49 83 fc 01          	cmp    $0x1,%r12
    4944:	74 5a                	je     49a0 <timer_thread+0x2f0>
    4946:	49 83 c4 01          	add    $0x1,%r12
    494a:	44 89 e6             	mov    %r12d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    494d:	eb 92                	jmp    48e1 <timer_thread+0x231>
    494f:	90                   	nop
    4950:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    4956:	48 83 ec 08          	sub    $0x8,%rsp
    495a:	bf 01 00 00 00       	mov    $0x1,%edi
    495f:	89 da                	mov    %ebx,%edx
    4961:	50                   	push   %rax
    4962:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    4968:	89 f1                	mov    %esi,%ecx
    496a:	48 8d 35 ec 36 00 00 	lea    0x36ec(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    4971:	50                   	push   %rax
    4972:	31 c0                	xor    %eax,%eax
    4974:	41 53                	push   %r11
    4976:	e8 35 db ff ff       	call   24b0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    497b:	41 8b 7e 30          	mov    0x30(%r14),%edi
      for (int y = 0 ; y < 2 ; y++) {
    497f:	48 83 c4 20          	add    $0x20,%rsp
    4983:	49 83 fc 01          	cmp    $0x1,%r12
    4987:	0f 84 83 00 00 00    	je     4a10 <timer_thread+0x360>
    498d:	49 83 c4 01          	add    $0x1,%r12
    4991:	45 31 ff             	xor    %r15d,%r15d
    4994:	44 89 e6             	mov    %r12d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4997:	85 ff                	test   %edi,%edi
    4999:	0f 8f 42 ff ff ff    	jg     48e1 <timer_thread+0x231>
    499f:	90                   	nop
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    49a0:	49 83 c5 01          	add    $0x1,%r13
    49a4:	44 39 ef             	cmp    %r13d,%edi
    49a7:	0f 8f 1b ff ff ff    	jg     48c8 <timer_thread+0x218>
    49ad:	8b 5c 24 0c          	mov    0xc(%rsp),%ebx
    for (int k = 0 ; k < data->my_thread_count; k++) {
    49b1:	85 ff                	test   %edi,%edi
    49b3:	7e 38                	jle    49ed <timer_thread+0x33d>
    49b5:	31 ed                	xor    %ebp,%ebp
    int all_waited = 1;
    49b7:	bf 01 00 00 00       	mov    $0x1,%edi
    49bc:	49 8b 76 18          	mov    0x18(%r14),%rsi
    49c0:	41 8b 56 40          	mov    0x40(%r14),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    49c4:	48 8b 04 ee          	mov    (%rsi,%rbp,8),%rax
    49c8:	48 8b 40 38          	mov    0x38(%rax),%rax
    49cc:	8b 88 9c 01 00 00    	mov    0x19c(%rax),%ecx
    49d2:	39 d1                	cmp    %edx,%ecx
    49d4:	7c 7a                	jl     4a50 <timer_thread+0x3a0>
    49d6:	8b 80 9c 03 00 00    	mov    0x39c(%rax),%eax
    49dc:	39 d0                	cmp    %edx,%eax
    49de:	7c 48                	jl     4a28 <timer_thread+0x378>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    49e0:	48 83 c5 01          	add    $0x1,%rbp
    49e4:	41 39 6e 30          	cmp    %ebp,0x30(%r14)
    49e8:	7f da                	jg     49c4 <timer_thread+0x314>
    49ea:	41 21 ff             	and    %edi,%r15d
    if (all_empty == 1 && all_waited == 1) {
    49ed:	45 85 ff             	test   %r15d,%r15d
    49f0:	0f 85 86 00 00 00    	jne    4a7c <timer_thread+0x3cc>
      nanosleep(&drain , &drainrem);
    49f6:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    49fb:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    4a00:	e8 9b d9 ff ff       	call   23a0 <nanosleep@plt>
    4a05:	e9 3b fe ff ff       	jmp    4845 <timer_thread+0x195>
    4a0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4a10:	49 83 c5 01          	add    $0x1,%r13
    4a14:	45 31 ff             	xor    %r15d,%r15d
    4a17:	44 39 ef             	cmp    %r13d,%edi
    4a1a:	0f 8f a8 fe ff ff    	jg     48c8 <timer_thread+0x218>
    4a20:	eb 8b                	jmp    49ad <timer_thread+0x2fd>
    4a22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a28:	89 c2                	mov    %eax,%edx
    4a2a:	bf 01 00 00 00       	mov    $0x1,%edi
    4a2f:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4a31:	48 83 c5 01          	add    $0x1,%rbp
    4a35:	48 8d 35 c9 38 00 00 	lea    0x38c9(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4a3c:	e8 6f da ff ff       	call   24b0 <__printf_chk@plt>
          all_waited = 0; 
    4a41:	31 ff                	xor    %edi,%edi
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4a43:	41 39 6e 30          	cmp    %ebp,0x30(%r14)
    4a47:	0f 8f 6f ff ff ff    	jg     49bc <timer_thread+0x30c>
    4a4d:	eb 9b                	jmp    49ea <timer_thread+0x33a>
    4a4f:	90                   	nop
    4a50:	89 ca                	mov    %ecx,%edx
    4a52:	48 8d 35 ac 38 00 00 	lea    0x38ac(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4a59:	bf 01 00 00 00       	mov    $0x1,%edi
    4a5e:	31 c0                	xor    %eax,%eax
    4a60:	e8 4b da ff ff       	call   24b0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4a65:	49 8b 76 18          	mov    0x18(%r14),%rsi
    4a69:	41 8b 56 40          	mov    0x40(%r14),%edx
          all_waited = 0; 
    4a6d:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4a6f:	48 8b 04 ee          	mov    (%rsi,%rbp,8),%rax
    4a73:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a77:	e9 5a ff ff ff       	jmp    49d6 <timer_thread+0x326>
    4a7c:	48 8d 3d d1 35 00 00 	lea    0x35d1(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4a83:	e8 a8 d8 ff ff       	call   2330 <puts@plt>
  while (data->running) {
    4a88:	41 8b 56 44          	mov    0x44(%r14),%edx
    4a8c:	85 d2                	test   %edx,%edx
    4a8e:	0f 84 eb 00 00 00    	je     4b7f <timer_thread+0x4cf>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4a94:	41 8b 46 2c          	mov    0x2c(%r14),%eax
    4a98:	31 db                	xor    %ebx,%ebx
    4a9a:	48 8d 2d d9 35 00 00 	lea    0x35d9(%rip),%rbp        # 807a <_IO_stdin_used+0x7a>
    4aa1:	4c 8d 25 ed 35 00 00 	lea    0x35ed(%rip),%r12        # 8095 <_IO_stdin_used+0x95>
    4aa8:	85 c0                	test   %eax,%eax
    4aaa:	7e 38                	jle    4ae4 <timer_thread+0x434>
    4aac:	0f 1f 40 00          	nopl   0x0(%rax)
    4ab0:	31 c0                	xor    %eax,%eax
    4ab2:	89 da                	mov    %ebx,%edx
    4ab4:	48 89 ee             	mov    %rbp,%rsi
    4ab7:	bf 01 00 00 00       	mov    $0x1,%edi
    4abc:	e8 ef d9 ff ff       	call   24b0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4ac1:	49 8b 46 18          	mov    0x18(%r14),%rax
    4ac5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4ac9:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4acd:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4ad4:	0f 84 d2 00 00 00    	je     4bac <timer_thread+0x4fc>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4ada:	48 83 c3 01          	add    $0x1,%rbx
    4ade:	41 39 5e 2c          	cmp    %ebx,0x2c(%r14)
    4ae2:	7f cc                	jg     4ab0 <timer_thread+0x400>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4ae4:	49 63 56 30          	movslq 0x30(%r14),%rdx
    4ae8:	85 d2                	test   %edx,%edx
    4aea:	7e 7c                	jle    4b68 <timer_thread+0x4b8>
      for (int y = 0 ; y < data->task_count ; y++) {
    4aec:	41 8b 46 40          	mov    0x40(%r14),%eax
    4af0:	85 c0                	test   %eax,%eax
    4af2:	7e 74                	jle    4b68 <timer_thread+0x4b8>
    4af4:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4af7:	4d 8b 46 18          	mov    0x18(%r14),%r8
    4afb:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4b03:	31 c9                	xor    %ecx,%ecx
    4b05:	48 c1 e6 09          	shl    $0x9,%rsi
    4b09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4b10:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4b14:	48 8b 40 38          	mov    0x38(%rax),%rax
    4b18:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4b1c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4b22:	74 1c                	je     4b40 <timer_thread+0x490>
    4b24:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4b2e:	48 05 00 02 00 00    	add    $0x200,%rax
    4b34:	48 39 d0             	cmp    %rdx,%rax
    4b37:	74 26                	je     4b5f <timer_thread+0x4af>
    4b39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4b40:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4b4a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4b50:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4b5a:	48 39 d0             	cmp    %rdx,%rax
    4b5d:	75 e1                	jne    4b40 <timer_thread+0x490>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4b5f:	48 83 c1 08          	add    $0x8,%rcx
    4b63:	48 39 cf             	cmp    %rcx,%rdi
    4b66:	75 a8                	jne    4b10 <timer_thread+0x460>
    asm volatile ("mfence" ::: "memory");
    4b68:	0f ae f0             	mfence
    4b6b:	48 8d 3d 35 35 00 00 	lea    0x3535(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4b72:	e8 b9 d7 ff ff       	call   2330 <puts@plt>
    data->running = 0;
    4b77:	41 c7 46 44 00 00 00 00 	movl   $0x0,0x44(%r14)
    4b7f:	48 8d 3d 28 35 00 00 	lea    0x3528(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4b86:	e8 a5 d7 ff ff       	call   2330 <puts@plt>
}
    4b8b:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    4b90:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b99:	75 41                	jne    4bdc <timer_thread+0x52c>
    4b9b:	48 83 c4 68          	add    $0x68,%rsp
    4b9f:	31 c0                	xor    %eax,%eax
    4ba1:	5b                   	pop    %rbx
    4ba2:	5d                   	pop    %rbp
    4ba3:	41 5c                	pop    %r12
    4ba5:	41 5d                	pop    %r13
    4ba7:	41 5e                	pop    %r14
    4ba9:	41 5f                	pop    %r15
    4bab:	c3                   	ret
    4bac:	4c 89 e7             	mov    %r12,%rdi
    4baf:	e8 7c d7 ff ff       	call   2330 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4bb4:	49 8b 46 18          	mov    0x18(%r14),%rax
    4bb8:	be 01 00 00 00       	mov    $0x1,%esi
    4bbd:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4bc1:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4bc5:	8b 78 60             	mov    0x60(%rax),%edi
    4bc8:	e8 93 d8 ff ff       	call   2460 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4bcd:	41 39 5e 2c          	cmp    %ebx,0x2c(%r14)
    4bd1:	0f 8f d9 fe ff ff    	jg     4ab0 <timer_thread+0x400>
    4bd7:	e9 08 ff ff ff       	jmp    4ae4 <timer_thread+0x434>
}
    4bdc:	e8 9f d7 ff ff       	call   2380 <__stack_chk_fail@plt>
    4be1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4bec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bf0 <minf>:
int minf(int a, int b) {
    4bf0:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    4bf4:	39 f7                	cmp    %esi,%edi
    4bf6:	89 f0                	mov    %esi,%eax
    4bf8:	0f 4e c7             	cmovle %edi,%eax
}
    4bfb:	c3                   	ret
    4bfc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c00 <maxf>:
int maxf(int a, int b) {
    4c00:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    4c04:	39 f7                	cmp    %esi,%edi
    4c06:	89 f0                	mov    %esi,%eax
    4c08:	0f 4d c7             	cmovge %edi,%eax
}
    4c0b:	c3                   	ret
    4c0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c10 <strtolower>:
void strtolower(char *str) {
    4c10:	f3 0f 1e fa          	endbr64
    4c14:	55                   	push   %rbp
    4c15:	53                   	push   %rbx
    4c16:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    4c1a:	48 0f be 1f          	movsbq (%rdi),%rbx
    4c1e:	84 db                	test   %bl,%bl
    4c20:	74 24                	je     4c46 <strtolower+0x36>
    4c22:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4c25:	e8 66 d9 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4c2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4c30:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4c33:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4c37:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4c3a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    4c3d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4c42:	84 db                	test   %bl,%bl
    4c44:	75 ea                	jne    4c30 <strtolower+0x20>
}
    4c46:	48 83 c4 08          	add    $0x8,%rsp
    4c4a:	5b                   	pop    %rbx
    4c4b:	5d                   	pop    %rbp
    4c4c:	c3                   	ret
    4c4d:	0f 1f 00             	nopl   (%rax)

0000000000004c50 <zh_malloc>:
void *zh_malloc(size_t size) {
    4c50:	f3 0f 1e fa          	endbr64
    4c54:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4c58:	e8 13 d8 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4c5d:	48 85 c0             	test   %rax,%rax
    4c60:	74 05                	je     4c67 <zh_malloc+0x17>
}
    4c62:	48 83 c4 08          	add    $0x8,%rsp
    4c66:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4c67:	48 8b 0d b2 63 00 00 	mov    0x63b2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4c6e:	ba 28 00 00 00       	mov    $0x28,%edx
    4c73:	be 01 00 00 00       	mov    $0x1,%esi
    4c78:	48 8d 3d 71 39 00 00 	lea    0x3971(%rip),%rdi        # 85f0 <_IO_stdin_used+0x5f0>
    4c7f:	e8 ac d8 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    4c84:	bf 01 00 00 00       	mov    $0x1,%edi
    4c89:	e8 82 d8 ff ff       	call   2510 <exit@plt>
    4c8e:	66 90                	xchg   %ax,%ax

0000000000004c90 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4c90:	f3 0f 1e fa          	endbr64
    4c94:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4c95:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4c9a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4c9d:	e8 0e d7 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    4ca2:	48 85 c0             	test   %rax,%rax
    4ca5:	74 11                	je     4cb8 <get_filename_ext+0x28>
    4ca7:	48 39 c3             	cmp    %rax,%rbx
    4caa:	74 0c                	je     4cb8 <get_filename_ext+0x28>
    return dot + 1;
    4cac:	48 83 c0 01          	add    $0x1,%rax
}
    4cb0:	5b                   	pop    %rbx
    4cb1:	c3                   	ret
    4cb2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4cb8:	48 8d 05 37 34 00 00 	lea    0x3437(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4cbf:	5b                   	pop    %rbx
    4cc0:	c3                   	ret
    4cc1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4ccc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004cd0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4cd0:	f3 0f 1e fa          	endbr64
    4cd4:	41 55                	push   %r13
    4cd6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4cd9:	48 89 fe             	mov    %rdi,%rsi
    4cdc:	41 54                	push   %r12
    4cde:	55                   	push   %rbp
    4cdf:	48 89 d5             	mov    %rdx,%rbp
    4ce2:	ba 00 04 00 00       	mov    $0x400,%edx
    4ce7:	53                   	push   %rbx
    4ce8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4cef:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4cf8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4d00:	31 c0                	xor    %eax,%eax
    4d02:	49 89 e4             	mov    %rsp,%r12
    4d05:	4c 89 e7             	mov    %r12,%rdi
    4d08:	e8 83 d7 ff ff       	call   2490 <__strcpy_chk@plt>
    for (; *str; ++str)
    4d0d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4d12:	84 db                	test   %bl,%bl
    4d14:	74 24                	je     4d3a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4d16:	e8 75 d8 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4d1b:	48 8b 08             	mov    (%rax),%rcx
    4d1e:	4c 89 e0             	mov    %r12,%rax
    4d21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4d28:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4d2b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4d2f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4d32:	48 0f be 18          	movsbq (%rax),%rbx
    4d36:	84 db                	test   %bl,%bl
    4d38:	75 ee                	jne    4d28 <send_headers+0x58>
    void *buf = malloc(size);
    4d3a:	bf 11 00 00 00       	mov    $0x11,%edi
    4d3f:	e8 2c d7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4d44:	48 85 c0             	test   %rax,%rax
    4d47:	0f 84 7e 04 00 00    	je     51cb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4d4d:	66 0f 6f 05 db 3e 00 00 	movdqa 0x3edb(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    iov[0].iov_base = zh_malloc(slen);
    4d55:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4d59:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4d5e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4d66:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4d6a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4d6d:	e8 fe d6 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4d72:	48 85 c0             	test   %rax,%rax
    4d75:	0f 84 50 04 00 00    	je     51cb <send_headers+0x4fb>
    4d7b:	66 0f 6f 05 bd 3e 00 00 	movdqa 0x3ebd(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    iov[1].iov_base = zh_malloc(slen);
    4d83:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4d87:	4c 89 e7             	mov    %r12,%rdi
    4d8a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4d94:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4d9c:	0f 11 00             	movups %xmm0,(%rax)
    4d9f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4da3:	be 2e 00 00 00       	mov    $0x2e,%esi
    4da8:	e8 03 d6 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    4dad:	48 85 c0             	test   %rax,%rax
    4db0:	0f 84 ea 02 00 00    	je     50a0 <send_headers+0x3d0>
    4db6:	4c 39 e0             	cmp    %r12,%rax
    4db9:	0f 84 e1 02 00 00    	je     50a0 <send_headers+0x3d0>
    return dot + 1;
    4dbf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4dc3:	48 8d 3d fa 32 00 00 	lea    0x32fa(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4dca:	48 89 de             	mov    %rbx,%rsi
    4dcd:	e8 3e d6 ff ff       	call   2410 <strcmp@plt>
    4dd2:	85 c0                	test   %eax,%eax
    4dd4:	75 20                	jne    4df6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4dd6:	66 0f 6f 05 72 3e 00 00 	movdqa 0x3e72(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4dde:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4de6:	66 0f 6f 05 72 3e 00 00 	movdqa 0x3e72(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    4dee:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4df6:	48 89 de             	mov    %rbx,%rsi
    4df9:	48 8d 3d c8 32 00 00 	lea    0x32c8(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4e00:	e8 0b d6 ff ff       	call   2410 <strcmp@plt>
    4e05:	85 c0                	test   %eax,%eax
    4e07:	75 20                	jne    4e29 <send_headers+0x159>
    4e09:	66 0f 6f 05 3f 3e 00 00 	movdqa 0x3e3f(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4e11:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e19:	66 0f 6f 05 3f 3e 00 00 	movdqa 0x3e3f(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    4e21:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4e29:	48 89 de             	mov    %rbx,%rsi
    4e2c:	48 8d 3d 9a 32 00 00 	lea    0x329a(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4e33:	e8 d8 d5 ff ff       	call   2410 <strcmp@plt>
    4e38:	85 c0                	test   %eax,%eax
    4e3a:	0f 84 10 02 00 00    	je     5050 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4e40:	48 89 de             	mov    %rbx,%rsi
    4e43:	48 8d 3d 87 32 00 00 	lea    0x3287(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4e4a:	e8 c1 d5 ff ff       	call   2410 <strcmp@plt>
    4e4f:	85 c0                	test   %eax,%eax
    4e51:	0f 84 a9 02 00 00    	je     5100 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4e57:	48 89 de             	mov    %rbx,%rsi
    4e5a:	48 8d 3d 74 32 00 00 	lea    0x3274(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4e61:	e8 aa d5 ff ff       	call   2410 <strcmp@plt>
    4e66:	85 c0                	test   %eax,%eax
    4e68:	0f 84 6a 02 00 00    	je     50d8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4e6e:	48 89 de             	mov    %rbx,%rsi
    4e71:	48 8d 3d a0 32 00 00 	lea    0x32a0(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4e78:	e8 93 d5 ff ff       	call   2410 <strcmp@plt>
    4e7d:	85 c0                	test   %eax,%eax
    4e7f:	0f 84 2b 02 00 00    	je     50b0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4e85:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4e88:	0f 84 52 01 00 00    	je     4fe0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4e8e:	48 89 de             	mov    %rbx,%rsi
    4e91:	48 8d 3d 41 32 00 00 	lea    0x3241(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4e98:	e8 73 d5 ff ff       	call   2410 <strcmp@plt>
    4e9d:	85 c0                	test   %eax,%eax
    4e9f:	0f 84 ab 02 00 00    	je     5150 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4ea5:	48 89 de             	mov    %rbx,%rsi
    4ea8:	48 8d 3d 2e 32 00 00 	lea    0x322e(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4eaf:	e8 5c d5 ff ff       	call   2410 <strcmp@plt>
    4eb4:	85 c0                	test   %eax,%eax
    4eb6:	0f 84 6c 02 00 00    	je     5128 <send_headers+0x458>
    slen = strlen(send_buffer);
    4ebc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4ec4:	4c 89 e7             	mov    %r12,%rdi
    4ec7:	e8 a4 d4 ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    4ecc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4ecf:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4ed2:	e8 99 d5 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4ed7:	48 85 c0             	test   %rax,%rax
    4eda:	0f 84 eb 02 00 00    	je     51cb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4ee0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4ee4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ee8:	83 fb 08             	cmp    $0x8,%ebx
    4eeb:	0f 83 3f 01 00 00    	jae    5030 <send_headers+0x360>
    4ef1:	f6 c3 04             	test   $0x4,%bl
    4ef4:	0f 85 7b 02 00 00    	jne    5175 <send_headers+0x4a5>
    4efa:	85 db                	test   %ebx,%ebx
    4efc:	74 13                	je     4f11 <send_headers+0x241>
    4efe:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4f06:	88 10                	mov    %dl,(%rax)
    4f08:	f6 c3 02             	test   $0x2,%bl
    4f0b:	0f 85 96 02 00 00    	jne    51a7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4f11:	4d 89 e8             	mov    %r13,%r8
    4f14:	48 8d 0d c6 31 00 00 	lea    0x31c6(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4f1b:	4c 89 e7             	mov    %r12,%rdi
    4f1e:	31 c0                	xor    %eax,%eax
    4f20:	ba 00 04 00 00       	mov    $0x400,%edx
    4f25:	be 01 00 00 00       	mov    $0x1,%esi
    4f2a:	e8 71 d6 ff ff       	call   25a0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4f2f:	4c 89 e7             	mov    %r12,%rdi
    4f32:	e8 39 d4 ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    4f37:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4f3a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4f3d:	e8 2e d5 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4f42:	48 85 c0             	test   %rax,%rax
    4f45:	0f 84 80 02 00 00    	je     51cb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4f4b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4f4f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4f53:	83 fb 08             	cmp    $0x8,%ebx
    4f56:	0f 83 1c 01 00 00    	jae    5078 <send_headers+0x3a8>
    4f5c:	f6 c3 04             	test   $0x4,%bl
    4f5f:	0f 85 29 02 00 00    	jne    518e <send_headers+0x4be>
    4f65:	85 db                	test   %ebx,%ebx
    4f67:	74 13                	je     4f7c <send_headers+0x2ac>
    4f69:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4f71:	88 10                	mov    %dl,(%rax)
    4f73:	f6 c3 02             	test   $0x2,%bl
    4f76:	0f 85 3d 02 00 00    	jne    51b9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f7c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4f81:	bf 02 00 00 00       	mov    $0x2,%edi
    4f86:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4f8e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4f96:	e8 d5 d4 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4f9b:	48 85 c0             	test   %rax,%rax
    4f9e:	0f 84 27 02 00 00    	je     51cb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4fa4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4fac:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4fb0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4fb8:	66 89 10             	mov    %dx,(%rax)
}
    4fbb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4fc3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4fcc:	0f 85 20 02 00 00    	jne    51f2 <send_headers+0x522>
    4fd2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4fd9:	5b                   	pop    %rbx
    4fda:	5d                   	pop    %rbp
    4fdb:	41 5c                	pop    %r12
    4fdd:	41 5d                	pop    %r13
    4fdf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4fe0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4fe4:	0f 85 a4 fe ff ff    	jne    4e8e <send_headers+0x1be>
    4fea:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4fee:	0f 85 9a fe ff ff    	jne    4e8e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ff4:	66 0f 6f 05 b4 3c 00 00 	movdqa 0x3cb4(%rip),%xmm0        # 8cb0 <_IO_stdin_used+0xcb0>
    4ffc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    5006:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    500e:	66 0f 6f 05 aa 3c 00 00 	movdqa 0x3caa(%rip),%xmm0        # 8cc0 <_IO_stdin_used+0xcc0>
    5016:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    501e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    5026:	e9 63 fe ff ff       	jmp    4e8e <send_headers+0x1be>
    502b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5030:	89 da                	mov    %ebx,%edx
    5032:	48 89 c7             	mov    %rax,%rdi
    5035:	4c 89 e6             	mov    %r12,%rsi
    5038:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    503d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5042:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5045:	c1 e9 03             	shr    $0x3,%ecx
    5048:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    504b:	e9 c1 fe ff ff       	jmp    4f11 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5050:	66 0f 6f 05 f8 3b 00 00 	movdqa 0x3bf8(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5058:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5060:	66 0f 6f 05 08 3c 00 00 	movdqa 0x3c08(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    5068:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5070:	e9 cb fd ff ff       	jmp    4e40 <send_headers+0x170>
    5075:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5078:	89 da                	mov    %ebx,%edx
    507a:	48 89 c7             	mov    %rax,%rdi
    507d:	4c 89 e6             	mov    %r12,%rsi
    5080:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    5085:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    508a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    508d:	c1 e9 03             	shr    $0x3,%ecx
    5090:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    5093:	e9 e4 fe ff ff       	jmp    4f7c <send_headers+0x2ac>
    5098:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    50a0:	48 8d 1d 4f 30 00 00 	lea    0x304f(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    50a7:	e9 94 fd ff ff       	jmp    4e40 <send_headers+0x170>
    50ac:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    50b0:	66 0f 6f 05 d8 3b 00 00 	movdqa 0x3bd8(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    50b8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50c0:	66 0f 6f 05 d8 3b 00 00 	movdqa 0x3bd8(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    50c8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    50d0:	e9 b0 fd ff ff       	jmp    4e85 <send_headers+0x1b5>
    50d5:	0f 1f 00             	nopl   (%rax)
    50d8:	66 0f 6f 05 b0 3b 00 00 	movdqa 0x3bb0(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    50e0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50e8:	66 0f 6f 05 b0 3b 00 00 	movdqa 0x3bb0(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    50f0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    50f8:	e9 71 fd ff ff       	jmp    4e6e <send_headers+0x19e>
    50fd:	0f 1f 00             	nopl   (%rax)
    5100:	66 0f 6f 05 48 3b 00 00 	movdqa 0x3b48(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5108:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5110:	66 0f 6f 05 68 3b 00 00 	movdqa 0x3b68(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    5118:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5120:	e9 32 fd ff ff       	jmp    4e57 <send_headers+0x187>
    5125:	0f 1f 00             	nopl   (%rax)
    5128:	66 0f 6f 05 60 3b 00 00 	movdqa 0x3b60(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    5130:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5138:	66 0f 6f 05 a0 3b 00 00 	movdqa 0x3ba0(%rip),%xmm0        # 8ce0 <_IO_stdin_used+0xce0>
    5140:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5148:	e9 6f fd ff ff       	jmp    4ebc <send_headers+0x1ec>
    514d:	0f 1f 00             	nopl   (%rax)
    5150:	66 0f 6f 05 38 3b 00 00 	movdqa 0x3b38(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    5158:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5160:	66 0f 6f 05 68 3b 00 00 	movdqa 0x3b68(%rip),%xmm0        # 8cd0 <_IO_stdin_used+0xcd0>
    5168:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5170:	e9 30 fd ff ff       	jmp    4ea5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5175:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    517c:	89 db                	mov    %ebx,%ebx
    517e:	89 10                	mov    %edx,(%rax)
    5180:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5185:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5189:	e9 83 fd ff ff       	jmp    4f11 <send_headers+0x241>
    518e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5195:	89 db                	mov    %ebx,%ebx
    5197:	89 10                	mov    %edx,(%rax)
    5199:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    519e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    51a2:	e9 d5 fd ff ff       	jmp    4f7c <send_headers+0x2ac>
    51a7:	89 db                	mov    %ebx,%ebx
    51a9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    51af:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    51b4:	e9 58 fd ff ff       	jmp    4f11 <send_headers+0x241>
    51b9:	89 db                	mov    %ebx,%ebx
    51bb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    51c1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    51c6:	e9 b1 fd ff ff       	jmp    4f7c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    51cb:	48 8b 0d 4e 5e 00 00 	mov    0x5e4e(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    51d2:	ba 28 00 00 00       	mov    $0x28,%edx
    51d7:	be 01 00 00 00       	mov    $0x1,%esi
    51dc:	48 8d 3d 0d 34 00 00 	lea    0x340d(%rip),%rdi        # 85f0 <_IO_stdin_used+0x5f0>
    51e3:	e8 48 d3 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    51e8:	bf 01 00 00 00       	mov    $0x1,%edi
    51ed:	e8 1e d3 ff ff       	call   2510 <exit@plt>
}
    51f2:	e8 89 d1 ff ff       	call   2380 <__stack_chk_fail@plt>
    51f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005200 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5200:	f3 0f 1e fa          	endbr64
    5204:	41 55                	push   %r13
    5206:	49 89 d5             	mov    %rdx,%r13
    5209:	41 54                	push   %r12
    520b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    520e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5211:	55                   	push   %rbp
    5212:	53                   	push   %rbx
    5213:	48 89 f3             	mov    %rsi,%rbx
    5216:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    521a:	e8 51 d2 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    521f:	48 85 c0             	test   %rax,%rax
    5222:	74 6b                	je     528f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    5224:	4c 89 e7             	mov    %r12,%rdi
    5227:	48 89 c5             	mov    %rax,%rbp
    522a:	31 f6                	xor    %esi,%esi
    522c:	31 c0                	xor    %eax,%eax
    522e:	e8 ad d2 ff ff       	call   24e0 <open@plt>
    5233:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    5236:	85 c0                	test   %eax,%eax
    5238:	0f 88 98 d3 ff ff    	js     25d6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    523e:	48 89 da             	mov    %rbx,%rdx
    5241:	48 89 ee             	mov    %rbp,%rsi
    5244:	89 c7                	mov    %eax,%edi
    5246:	e8 a5 d1 ff ff       	call   23f0 <read@plt>
    if (ret < file_size) {
    524b:	48 98                	cltq
    524d:	48 39 d8             	cmp    %rbx,%rax
    5250:	7c 1e                	jl     5270 <copy_file_contents+0x70>
    close(fd);
    5252:	44 89 e7             	mov    %r12d,%edi
    5255:	e8 76 d1 ff ff       	call   23d0 <close@plt>
    iov->iov_base = buf;
    525a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    525e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    5262:	48 83 c4 08          	add    $0x8,%rsp
    5266:	5b                   	pop    %rbx
    5267:	5d                   	pop    %rbp
    5268:	41 5c                	pop    %r12
    526a:	41 5d                	pop    %r13
    526c:	c3                   	ret
    526d:	0f 1f 00             	nopl   (%rax)
    5270:	48 8b 0d a9 5d 00 00 	mov    0x5da9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5277:	ba 1a 00 00 00       	mov    $0x1a,%edx
    527c:	be 01 00 00 00       	mov    $0x1,%esi
    5281:	48 8d 3d 6f 2e 00 00 	lea    0x2e6f(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    5288:	e8 a3 d2 ff ff       	call   2530 <fwrite@plt>
    528d:	eb c3                	jmp    5252 <copy_file_contents+0x52>
    528f:	48 8b 0d 8a 5d 00 00 	mov    0x5d8a(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5296:	ba 28 00 00 00       	mov    $0x28,%edx
    529b:	be 01 00 00 00       	mov    $0x1,%esi
    52a0:	48 8d 3d 49 33 00 00 	lea    0x3349(%rip),%rdi        # 85f0 <_IO_stdin_used+0x5f0>
    52a7:	e8 84 d2 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    52ac:	bf 01 00 00 00       	mov    $0x1,%edi
    52b1:	e8 5a d2 ff ff       	call   2510 <exit@plt>
    52b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000052c0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    52c0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    52c4:	8b 46 44             	mov    0x44(%rsi),%eax
    52c7:	48 89 fa             	mov    %rdi,%rdx
    52ca:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    52cd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    52d3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    52d6:	48 8b 07             	mov    (%rdi),%rax
    52d9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    52dc:	f6 c1 02             	test   $0x2,%cl
    52df:	74 00                	je     52e1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    52e1:	89 f0                	mov    %esi,%eax
    52e3:	44 29 c0             	sub    %r8d,%eax
    52e6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    52e9:	0f 82 f3 d2 ff ff    	jb     25e2 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    52ef:	c1 e9 0a             	shr    $0xa,%ecx
    52f2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52f6:	8b 47 44             	mov    0x44(%rdi),%eax
    52f9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    52fc:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    52ff:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5302:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    5305:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5309:	d3 e0                	shl    %cl,%eax
    530b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    530e:	48 c1 e0 06          	shl    $0x6,%rax
    5312:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    5316:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    531c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    531f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    5323:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5329:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5331:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    5335:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    5338:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    533f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5347:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    534b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    534f:	e8 3c d0 ff ff       	call   2390 <io_uring_submit@plt>
}
    5354:	31 c0                	xor    %eax,%eax
    5356:	48 83 c4 08          	add    $0x8,%rsp
    535a:	c3                   	ret
    535b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005360 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    5360:	f3 0f 1e fa          	endbr64
    5364:	41 55                	push   %r13
    5366:	41 89 fd             	mov    %edi,%r13d
    5369:	41 54                	push   %r12
    536b:	55                   	push   %rbp
    536c:	53                   	push   %rbx
    536d:	48 89 f3             	mov    %rsi,%rbx
    5370:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    5374:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5377:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    537d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    5380:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5383:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5385:	f6 c1 02             	test   $0x2,%cl
    5388:	74 00                	je     538a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    538a:	89 c2                	mov    %eax,%edx
    538c:	29 f2                	sub    %esi,%edx
    538e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5391:	0f 82 5b d2 ff ff    	jb     25f2 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5397:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    539a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    539d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    53a0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    53a5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53a8:	23 6b 58             	and    0x58(%rbx),%ebp
    53ab:	d3 e5                	shl    %cl,%ebp
    53ad:	48 c1 e5 06          	shl    $0x6,%rbp
    53b1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    53b5:	e8 b6 d0 ff ff       	call   2470 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    53ba:	be 01 00 00 00       	mov    $0x1,%esi
    53bf:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    53c4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    53c7:	e8 34 d0 ff ff       	call   2400 <calloc@plt>
    req->client_socket = client_socket;
    53cc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    53d1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    53d5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    53d8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    53dd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    53e2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    53eb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    53f3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    53f7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    53fb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    5402:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    540a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    540e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    5416:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    541e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    5422:	e8 69 cf ff ff       	call   2390 <io_uring_submit@plt>
}
    5427:	48 83 c4 08          	add    $0x8,%rsp
    542b:	31 c0                	xor    %eax,%eax
    542d:	5b                   	pop    %rbx
    542e:	5d                   	pop    %rbp
    542f:	41 5c                	pop    %r12
    5431:	41 5d                	pop    %r13
    5433:	c3                   	ret
    5434:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    543f:	90                   	nop

0000000000005440 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5440:	f3 0f 1e fa          	endbr64
    5444:	41 56                	push   %r14
    5446:	41 89 f6             	mov    %esi,%r14d
    5449:	41 55                	push   %r13
    544b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    544e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5453:	41 54                	push   %r12
    5455:	55                   	push   %rbp
    5456:	48 89 d5             	mov    %rdx,%rbp
    5459:	53                   	push   %rbx
    void *buf = malloc(size);
    545a:	e8 11 d0 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    545f:	48 85 c0             	test   %rax,%rax
    5462:	0f 84 dd 00 00 00    	je     5545 <_send_static_string_content+0x105>
    5468:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    546b:	4c 89 ef             	mov    %r13,%rdi
    546e:	e8 fd ce ff ff       	call   2370 <strlen@plt>
    req->iovec_count = 1;
    5473:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    547a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    547e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    5481:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    5484:	e8 e7 cf ff ff       	call   2470 <malloc@plt>
    5489:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    548c:	48 85 c0             	test   %rax,%rax
    548f:	0f 84 b0 00 00 00    	je     5545 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    5495:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5499:	4c 89 e2             	mov    %r12,%rdx
    549c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    549f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    54a3:	e8 98 cf ff ff       	call   2440 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    54a8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    54ab:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    54b1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    54b4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    54b8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    54ba:	f6 c1 02             	test   $0x2,%cl
    54bd:	0f 85 7d 00 00 00    	jne    5540 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    54c3:	89 d0                	mov    %edx,%eax
    54c5:	29 f0                	sub    %esi,%eax
    54c7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    54ca:	0f 82 2c d1 ff ff    	jb     25fc <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    54d0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    54d3:	8b 45 44             	mov    0x44(%rbp),%eax
    54d6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    54d9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    54dc:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    54df:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    54e2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    54e8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    54ec:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    54ee:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    54f1:	48 89 ef             	mov    %rbp,%rdi
    54f4:	48 c1 e0 06          	shl    $0x6,%rax
    54f8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    54fc:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    54ff:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    5503:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5509:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5511:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5515:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5518:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    551f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5527:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    552b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    552f:	5b                   	pop    %rbx
    5530:	5d                   	pop    %rbp
    5531:	41 5c                	pop    %r12
    5533:	41 5d                	pop    %r13
    5535:	41 5e                	pop    %r14
    io_uring_submit(ring);
    5537:	e9 54 ce ff ff       	jmp    2390 <io_uring_submit@plt>
    553c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    5540:	e9 7e ff ff ff       	jmp    54c3 <_send_static_string_content+0x83>
    5545:	48 8b 0d d4 5a 00 00 	mov    0x5ad4(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    554c:	ba 28 00 00 00       	mov    $0x28,%edx
    5551:	be 01 00 00 00       	mov    $0x1,%esi
    5556:	48 8d 3d 93 30 00 00 	lea    0x3093(%rip),%rdi        # 85f0 <_IO_stdin_used+0x5f0>
    555d:	e8 ce cf ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5562:	bf 01 00 00 00       	mov    $0x1,%edi
    5567:	e8 a4 cf ff ff       	call   2510 <exit@plt>
    556c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005570 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    5570:	f3 0f 1e fa          	endbr64
    5574:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5577:	89 fe                	mov    %edi,%esi
    5579:	48 8b 3d 98 5a 00 00 	mov    0x5a98(%rip),%rdi        # b018 <unimplemented_content>
    5580:	e9 bb fe ff ff       	jmp    5440 <_send_static_string_content>
    5585:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005590 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5590:	f3 0f 1e fa          	endbr64
    5594:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5597:	89 fe                	mov    %edi,%esi
    5599:	48 8b 3d 70 5a 00 00 	mov    0x5a70(%rip),%rdi        # b010 <http_404_content>
    55a0:	e9 9b fe ff ff       	jmp    5440 <_send_static_string_content>
    55a5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000055b0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    55b0:	f3 0f 1e fa          	endbr64
    55b4:	41 56                	push   %r14
    55b6:	41 55                	push   %r13
    55b8:	49 89 d5             	mov    %rdx,%r13
    55bb:	41 54                	push   %r12
    55bd:	41 89 f4             	mov    %esi,%r12d
    55c0:	55                   	push   %rbp
    55c1:	48 89 fd             	mov    %rdi,%rbp
    55c4:	53                   	push   %rbx
    55c5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    55cc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    55d5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    55dd:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    55df:	e8 8c cd ff ff       	call   2370 <strlen@plt>
    55e4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    55e9:	48 89 c3             	mov    %rax,%rbx
    55ec:	0f 84 b6 00 00 00    	je     56a8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55f2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55f7:	48 89 ee             	mov    %rbp,%rsi
    55fa:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    55fe:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5603:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    560b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5613:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    561e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5626:	e8 f5 cd ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    562b:	48 89 e6             	mov    %rsp,%rsi
    562e:	4c 89 f7             	mov    %r14,%rdi
    5631:	e8 fa cd ff ff       	call   2430 <stat@plt>
    5636:	83 f8 ff             	cmp    $0xffffffff,%eax
    5639:	0f 84 d3 00 00 00    	je     5712 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    563f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5643:	25 00 f0 00 00       	and    $0xf000,%eax
    5648:	3d 00 80 00 00       	cmp    $0x8000,%eax
    564d:	0f 84 f5 00 00 00    	je     5748 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    5653:	48 8b 3d b6 59 00 00 	mov    0x59b6(%rip),%rdi        # b010 <http_404_content>
    565a:	4c 89 ea             	mov    %r13,%rdx
    565d:	44 89 e6             	mov    %r12d,%esi
    5660:	e8 db fd ff ff       	call   5440 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5665:	4c 89 f2             	mov    %r14,%rdx
    5668:	bf 01 00 00 00       	mov    $0x1,%edi
    566d:	31 c0                	xor    %eax,%eax
    566f:	48 8d 35 d1 2a 00 00 	lea    0x2ad1(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5676:	e8 35 ce ff ff       	call   24b0 <__printf_chk@plt>
}
    567b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5683:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    568c:	0f 85 20 01 00 00    	jne    57b2 <handle_get_method+0x202>
    5692:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5699:	5b                   	pop    %rbx
    569a:	5d                   	pop    %rbp
    569b:	41 5c                	pop    %r12
    569d:	41 5d                	pop    %r13
    569f:	41 5e                	pop    %r14
    56a1:	c3                   	ret
    56a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    56a8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    56ad:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    56b5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    56ba:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    56bd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    56c5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    56c8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    56d0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    56db:	e8 40 cd ff ff       	call   2420 <__memcpy_chk@plt>
    56e0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    56e5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    56ea:	48 8d 35 21 2a 00 00 	lea    0x2a21(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    56f1:	48 29 d9             	sub    %rbx,%rcx
    56f4:	ba 0b 00 00 00       	mov    $0xb,%edx
    56f9:	e8 22 cd ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    56fe:	48 89 e6             	mov    %rsp,%rsi
    5701:	4c 89 f7             	mov    %r14,%rdi
    5704:	e8 27 cd ff ff       	call   2430 <stat@plt>
    5709:	83 f8 ff             	cmp    $0xffffffff,%eax
    570c:	0f 85 2d ff ff ff    	jne    563f <handle_get_method+0x8f>
    5712:	4c 89 f2             	mov    %r14,%rdx
    5715:	48 89 e9             	mov    %rbp,%rcx
    5718:	48 8d 35 fe 29 00 00 	lea    0x29fe(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    571f:	31 c0                	xor    %eax,%eax
    5721:	bf 01 00 00 00       	mov    $0x1,%edi
    5726:	e8 85 cd ff ff       	call   24b0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    572b:	48 8b 3d de 58 00 00 	mov    0x58de(%rip),%rdi        # b010 <http_404_content>
    5732:	4c 89 ea             	mov    %r13,%rdx
    5735:	44 89 e6             	mov    %r12d,%esi
    5738:	e8 03 fd ff ff       	call   5440 <_send_static_string_content>
}
    573d:	e9 39 ff ff ff       	jmp    567b <handle_get_method+0xcb>
    5742:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5748:	bf 70 00 00 00       	mov    $0x70,%edi
    574d:	e8 1e cd ff ff       	call   2470 <malloc@plt>
    5752:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5755:	48 85 c0             	test   %rax,%rax
    5758:	74 5d                	je     57b7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    575a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    575e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5763:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5767:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    576a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5771:	e8 5a f5 ff ff       	call   4cd0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5776:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    577b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    577f:	4c 89 f7             	mov    %r14,%rdi
    5782:	e8 79 fa ff ff       	call   5200 <copy_file_contents>
    5787:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    578c:	4c 89 f2             	mov    %r14,%rdx
    578f:	31 c0                	xor    %eax,%eax
    5791:	48 8d 35 9d 29 00 00 	lea    0x299d(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    5798:	bf 01 00 00 00       	mov    $0x1,%edi
    579d:	e8 0e cd ff ff       	call   24b0 <__printf_chk@plt>
            add_write_request(req, ring);
    57a2:	4c 89 ee             	mov    %r13,%rsi
    57a5:	48 89 df             	mov    %rbx,%rdi
    57a8:	e8 13 fb ff ff       	call   52c0 <add_write_request>
    57ad:	e9 c9 fe ff ff       	jmp    567b <handle_get_method+0xcb>
}
    57b2:	e8 c9 cb ff ff       	call   2380 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    57b7:	48 8b 0d 62 58 00 00 	mov    0x5862(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    57be:	ba 28 00 00 00       	mov    $0x28,%edx
    57c3:	be 01 00 00 00       	mov    $0x1,%esi
    57c8:	48 8d 3d 21 2e 00 00 	lea    0x2e21(%rip),%rdi        # 85f0 <_IO_stdin_used+0x5f0>
    57cf:	e8 5c cd ff ff       	call   2530 <fwrite@plt>
        exit(1);
    57d4:	bf 01 00 00 00       	mov    $0x1,%edi
    57d9:	e8 32 cd ff ff       	call   2510 <exit@plt>
    57de:	66 90                	xchg   %ax,%ax

00000000000057e0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    57e0:	f3 0f 1e fa          	endbr64
    57e4:	41 57                	push   %r15
    57e6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    57e8:	4c 8d 35 bd 28 00 00 	lea    0x28bd(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    57ef:	41 55                	push   %r13
    57f1:	49 89 d5             	mov    %rdx,%r13
    57f4:	41 54                	push   %r12
    57f6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    57f9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    57fc:	55                   	push   %rbp
    57fd:	53                   	push   %rbx
    57fe:	48 83 ec 18          	sub    $0x18,%rsp
    5802:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    580b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5810:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5812:	49 89 e7             	mov    %rsp,%r15
    5815:	4c 89 fa             	mov    %r15,%rdx
    5818:	e8 c3 cb ff ff       	call   23e0 <strtok_r@plt>
    for (; *str; ++str)
    581d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5821:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5824:	84 db                	test   %bl,%bl
    5826:	74 1d                	je     5845 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5828:	e8 63 cd ff ff       	call   2590 <__ctype_tolower_loc@plt>
    582d:	48 89 ea             	mov    %rbp,%rdx
    5830:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    5833:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    5837:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    583a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    583d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5841:	84 db                	test   %bl,%bl
    5843:	75 eb                	jne    5830 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5845:	4c 89 fa             	mov    %r15,%rdx
    5848:	4c 89 f6             	mov    %r14,%rsi
    584b:	31 ff                	xor    %edi,%edi
    584d:	e8 8e cb ff ff       	call   23e0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5852:	48 8d 35 01 29 00 00 	lea    0x2901(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    5859:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    585c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    585f:	e8 ac cb ff ff       	call   2410 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5864:	4c 89 ea             	mov    %r13,%rdx
    5867:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    586a:	85 c0                	test   %eax,%eax
    586c:	75 2a                	jne    5898 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    586e:	48 89 df             	mov    %rbx,%rdi
    5871:	e8 3a fd ff ff       	call   55b0 <handle_get_method>
}
    5876:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    587b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5884:	75 20                	jne    58a6 <handle_http_method+0xc6>
    5886:	48 83 c4 18          	add    $0x18,%rsp
    588a:	5b                   	pop    %rbx
    588b:	5d                   	pop    %rbp
    588c:	41 5c                	pop    %r12
    588e:	41 5d                	pop    %r13
    5890:	41 5e                	pop    %r14
    5892:	41 5f                	pop    %r15
    5894:	c3                   	ret
    5895:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5898:	48 8b 3d 79 57 00 00 	mov    0x5779(%rip),%rdi        # b018 <unimplemented_content>
    589f:	e8 9c fb ff ff       	call   5440 <_send_static_string_content>
}
    58a4:	eb d0                	jmp    5876 <handle_http_method+0x96>
    58a6:	e8 d5 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    58ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000058b0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    58b0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    58b4:	85 d2                	test   %edx,%edx
    58b6:	7e 38                	jle    58f0 <get_line+0x40>
    58b8:	48 63 d2             	movslq %edx,%rdx
    58bb:	48 83 c7 01          	add    $0x1,%rdi
    58bf:	48 01 f2             	add    %rsi,%rdx
    58c2:	eb 11                	jmp    58d5 <get_line+0x25>
    58c4:	0f 1f 40 00          	nopl   0x0(%rax)
    58c8:	48 83 c6 01          	add    $0x1,%rsi
    58cc:	48 83 c7 01          	add    $0x1,%rdi
    58d0:	48 39 d6             	cmp    %rdx,%rsi
    58d3:	74 1b                	je     58f0 <get_line+0x40>
        dest[i] = src[i];
    58d5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    58d9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    58db:	3c 0d                	cmp    $0xd,%al
    58dd:	75 e9                	jne    58c8 <get_line+0x18>
    58df:	80 3f 0a             	cmpb   $0xa,(%rdi)
    58e2:	75 e4                	jne    58c8 <get_line+0x18>
            dest[i] = '\0';
    58e4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    58e7:	31 c0                	xor    %eax,%eax
    58e9:	c3                   	ret
    58ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    58f0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    58f5:	c3                   	ret
    58f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005900 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5900:	f3 0f 1e fa          	endbr64
    5904:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    590b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    590f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5918:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5920:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5922:	49 89 e2             	mov    %rsp,%r10
    5925:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    592d:	4c 89 d0             	mov    %r10,%rax
    5930:	eb 13                	jmp    5945 <handle_client_request+0x45>
    5932:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5938:	48 83 c0 01          	add    $0x1,%rax
    593c:	48 83 c1 01          	add    $0x1,%rcx
    5940:	4c 39 c8             	cmp    %r9,%rax
    5943:	74 4b                	je     5990 <handle_client_request+0x90>
        dest[i] = src[i];
    5945:	44 0f b6 01          	movzbl (%rcx),%r8d
    5949:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    594c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5950:	75 e6                	jne    5938 <handle_client_request+0x38>
    5952:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5956:	75 e0                	jne    5938 <handle_client_request+0x38>
            dest[i] = '\0';
    5958:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    595b:	8b 47 08             	mov    0x8(%rdi),%eax
    595e:	48 89 f2             	mov    %rsi,%rdx
    5961:	4c 89 d7             	mov    %r10,%rdi
    5964:	89 c6                	mov    %eax,%esi
    5966:	e8 75 fe ff ff       	call   57e0 <handle_http_method>
}
    596b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5973:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    597c:	75 39                	jne    59b7 <handle_client_request+0xb7>
    597e:	31 c0                	xor    %eax,%eax
    5980:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5987:	c3                   	ret
    5988:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5990:	48 8b 0d 89 56 00 00 	mov    0x5689(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5997:	ba 12 00 00 00       	mov    $0x12,%edx
    599c:	be 01 00 00 00       	mov    $0x1,%esi
    59a1:	48 8d 3d b6 27 00 00 	lea    0x27b6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    59a8:	e8 83 cb ff ff       	call   2530 <fwrite@plt>
        exit(1);
    59ad:	bf 01 00 00 00       	mov    $0x1,%edi
    59b2:	e8 59 cb ff ff       	call   2510 <exit@plt>
}
    59b7:	e8 c4 c9 ff ff       	call   2380 <__stack_chk_fail@plt>
    59bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000059c0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    59c0:	f3 0f 1e fa          	endbr64
    59c4:	55                   	push   %rbp
    59c5:	53                   	push   %rbx
    59c6:	48 89 cb             	mov    %rcx,%rbx
    59c9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    59cd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    59d0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    59d3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    59d9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    59dc:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    59df:	f6 c1 02             	test   $0x2,%cl
    59e2:	74 00                	je     59e4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    59e4:	41 89 c0             	mov    %eax,%r8d
    59e7:	45 29 c8             	sub    %r9d,%r8d
    59ea:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    59ee:	0f 82 18 cc ff ff    	jb     260c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    59f4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    59f7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    59fa:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    59fd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5a00:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5a03:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a07:	d3 e5                	shl    %cl,%ebp
    5a09:	48 c1 e5 06          	shl    $0x6,%rbp
    5a0d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5a11:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5a14:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5a19:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5a20:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5a24:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5a28:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5a30:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5a38:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5a3c:	e8 2f ca ff ff       	call   2470 <malloc@plt>
  io_uring_submit(ring);
    5a41:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5a44:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    5a4a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    5a4e:	48 83 c4 08          	add    $0x8,%rsp
    5a52:	5b                   	pop    %rbx
    5a53:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5a54:	e9 37 c9 ff ff       	jmp    2390 <io_uring_submit@plt>
    5a59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005a60 <io_thread>:
void* io_thread(void *arg) {
    5a60:	f3 0f 1e fa          	endbr64
    5a64:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a66:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5a68:	41 56                	push   %r14
    5a6a:	41 55                	push   %r13
    5a6c:	41 54                	push   %r12
    5a6e:	55                   	push   %rbp
    5a6f:	48 89 fd             	mov    %rdi,%rbp
    5a72:	53                   	push   %rbx
    5a73:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    5a7a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5a83:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    5a8b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a8f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5a94:	bf 00 01 00 00       	mov    $0x100,%edi
    5a99:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    5a9c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5aa0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5aa5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5aaa:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    5aaf:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5ab4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    5abc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5ac1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5ac9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5ace:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5ad6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5adb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5ae3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5ae8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5af0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5af5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    5afd:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5b05:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5b0d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5b15:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5b1d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5b25:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5b2d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5b35:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5b3d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5b45:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5b4d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5b54:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5b5c:	e8 ef c8 ff ff       	call   2450 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5b61:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5b65:	31 f6                	xor    %esi,%esi
    5b67:	e8 e4 c9 ff ff       	call   2550 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5b6c:	31 d2                	xor    %edx,%edx
    5b6e:	be 01 00 00 00       	mov    $0x1,%esi
    5b73:	bf 02 00 00 00       	mov    $0x2,%edi
    5b78:	e8 33 ca ff ff       	call   25b0 <socket@plt>
  if (sock == -1)
    5b7d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5b80:	0f 84 c8 ca ff ff    	je     264e <io_thread.cold+0x38>
  if (setsockopt(sock,
    5b86:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5b8b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5b91:	89 c7                	mov    %eax,%edi
    5b93:	41 89 c4             	mov    %eax,%r12d
    5b96:	ba 02 00 00 00       	mov    $0x2,%edx
    5b9b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5ba0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5ba8:	e8 93 c7 ff ff       	call   2340 <setsockopt@plt>
    5bad:	85 c0                	test   %eax,%eax
    5baf:	0f 88 6d ca ff ff    	js     2622 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5bb5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    5bba:	ba 10 00 00 00       	mov    $0x10,%edx
    5bbf:	44 89 e7             	mov    %r12d,%edi
    5bc2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5bcb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5bd3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    5bdb:	e8 e0 c8 ff ff       	call   24c0 <bind@plt>
    5be0:	85 c0                	test   %eax,%eax
    5be2:	0f 88 72 ca ff ff    	js     265a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5be8:	be 0a 00 00 00       	mov    $0xa,%esi
    5bed:	44 89 e7             	mov    %r12d,%edi
    5bf0:	e8 8b c8 ff ff       	call   2480 <listen@plt>
    5bf5:	85 c0                	test   %eax,%eax
    5bf7:	0f 88 31 ca ff ff    	js     262e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5bfd:	ba db 18 00 00       	mov    $0x18db,%edx
    5c02:	48 8d 35 9a 25 00 00 	lea    0x259a(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5c09:	bf 01 00 00 00       	mov    $0x1,%edi
    5c0e:	31 c0                	xor    %eax,%eax
    5c10:	e8 9b c8 ff ff       	call   24b0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5c15:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5c1a:	48 89 d9             	mov    %rbx,%rcx
    5c1d:	44 89 e7             	mov    %r12d,%edi
    5c20:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5c25:	48 89 c6             	mov    %rax,%rsi
    5c28:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5c2d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5c32:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5c3a:	e8 81 fd ff ff       	call   59c0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5c3f:	bf 01 00 00 00       	mov    $0x1,%edi
    5c44:	be 10 00 00 00       	mov    $0x10,%esi
    5c49:	e8 b2 c7 ff ff       	call   2400 <calloc@plt>
    void *buf = malloc(size);
    5c4e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5c53:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5c56:	e8 15 c8 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5c5b:	48 85 c0             	test   %rax,%rax
    5c5e:	0f 84 ae 04 00 00    	je     6112 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5c64:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5c68:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5c6f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5c76:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5c7e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5c81:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5c86:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5c88:	f6 c1 02             	test   $0x2,%cl
    5c8b:	0f 85 0f 04 00 00    	jne    60a0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5c91:	89 d0                	mov    %edx,%eax
    5c93:	29 f0                	sub    %esi,%eax
    5c95:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5c9c:	0f 82 a2 c9 ff ff    	jb     2644 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5ca2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5ca5:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5ca9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5cad:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5cb0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5cb7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5cba:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5cc1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5cc8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5cca:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5ccd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5cd2:	48 c1 e0 06          	shl    $0x6,%rax
    5cd6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5cde:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5ce4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5ce7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5cef:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5cf3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5cfb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5d03:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5d07:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5d0b:	e8 80 c6 ff ff       	call   2390 <io_uring_submit@plt>
  while (data->running == 1) {
    5d10:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5d14:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5d19:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5d21:	0f 85 d7 01 00 00    	jne    5efe <io_thread+0x49e>
    5d27:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5d2c:	4d 89 ce             	mov    %r9,%r14
    5d2f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5d34:	0f 1f 40 00          	nopl   0x0(%rax)
    5d38:	48 8d 3d 7a 24 00 00 	lea    0x247a(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5d3f:	e8 ec c5 ff ff       	call   2330 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5d44:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5d4b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5d52:	c1 e9 0b             	shr    $0xb,%ecx
    5d55:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5d58:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5d60:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5d62:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5d6a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5d6c:	39 d0                	cmp    %edx,%eax
    5d6e:	74 36                	je     5da6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5d70:	89 f8                	mov    %edi,%eax
    5d72:	21 d0                	and    %edx,%eax
    5d74:	d3 e0                	shl    %cl,%eax
    5d76:	48 c1 e0 04          	shl    $0x4,%rax
    5d7a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5d82:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5d8a:	0f 85 a8 01 00 00    	jne    5f38 <io_thread+0x4d8>
    5d90:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5d94:	0f 85 0e 03 00 00    	jne    60a8 <io_thread+0x648>
			if (cqe->res < 0)
    5d9a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5d9d:	83 c2 01             	add    $0x1,%edx
    5da0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5da2:	85 c0                	test   %eax,%eax
    5da4:	79 b2                	jns    5d58 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5da6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5daf:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5db0:	45 31 c0             	xor    %r8d,%r8d
    5db3:	31 d2                	xor    %edx,%edx
    5db5:	b9 01 00 00 00       	mov    $0x1,%ecx
    5dba:	4c 89 f6             	mov    %r14,%rsi
    5dbd:	48 89 df             	mov    %rbx,%rdi
    5dc0:	e8 db c6 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5dc5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5dc8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5dcd:	48 83 38 01          	cmpq   $0x1,(%rax)
    5dd1:	0f 84 e1 02 00 00    	je     60b8 <io_thread+0x658>
    5dd7:	48 8d 3d 01 24 00 00 	lea    0x2401(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5dde:	e8 4d c5 ff ff       	call   2330 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5de3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5de8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5deb:	45 85 ff             	test   %r15d,%r15d
    5dee:	0f 88 22 c8 ff ff    	js     2616 <io_thread.cold>
      if (cqe->res < 0) {
    5df4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5df7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    5dfb:	85 c0                	test   %eax,%eax
    5dfd:	0f 88 d5 02 00 00    	js     60d8 <io_thread+0x678>
      switch (req->event_type) {
    5e03:	41 83 f8 01          	cmp    $0x1,%r8d
    5e07:	0f 84 7b 01 00 00    	je     5f88 <io_thread+0x528>
    5e0d:	41 83 f8 02          	cmp    $0x2,%r8d
    5e11:	0f 84 a1 01 00 00    	je     5fb8 <io_thread+0x558>
    5e17:	45 85 c0             	test   %r8d,%r8d
    5e1a:	0f 85 50 01 00 00    	jne    5f70 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5e20:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5e25:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5e2a:	48 89 d9             	mov    %rbx,%rcx
    5e2d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5e31:	e8 8a fb ff ff       	call   59c0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5e36:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5e3b:	48 89 de             	mov    %rbx,%rsi
    5e3e:	8b 78 08             	mov    0x8(%rax),%edi
    5e41:	e8 1a f5 ff ff       	call   5360 <add_read_request>
              free(req);
    5e46:	4c 89 e7             	mov    %r12,%rdi
    5e49:	e8 b2 c4 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5e4e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5e53:	48 85 c0             	test   %rax,%rax
    5e56:	0f 85 14 01 00 00    	jne    5f70 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    5e5c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5e63:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5e6a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5e6d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5e72:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5e74:	f6 c1 02             	test   $0x2,%cl
    5e77:	74 00                	je     5e79 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5e79:	89 d0                	mov    %edx,%eax
    5e7b:	29 f0                	sub    %esi,%eax
    5e7d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5e84:	0f 82 b0 c7 ff ff    	jb     263a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5e8a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5e8d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5e92:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5e96:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e99:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5ea0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5ea3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5eaa:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5eb1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5eb3:	8b 55 60             	mov    0x60(%rbp),%edx
    5eb6:	48 c1 e0 06          	shl    $0x6,%rax
    5eba:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5ec2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5ec8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5ecb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5ed3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5ed7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5edf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5ee7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5eeb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5eef:	e8 9c c4 ff ff       	call   2390 <io_uring_submit@plt>
  while (data->running == 1) {
    5ef4:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5ef8:	0f 84 3a fe ff ff    	je     5d38 <io_thread+0x2d8>
    5efe:	48 8d 3d 13 23 00 00 	lea    0x2313(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5f05:	e8 26 c4 ff ff       	call   2330 <puts@plt>
}
    5f0a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5f12:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5f1b:	0f 85 18 02 00 00    	jne    6139 <io_thread+0x6d9>
    5f21:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5f28:	31 c0                	xor    %eax,%eax
    5f2a:	5b                   	pop    %rbx
    5f2b:	5d                   	pop    %rbp
    5f2c:	41 5c                	pop    %r12
    5f2e:	41 5d                	pop    %r13
    5f30:	41 5e                	pop    %r14
    5f32:	41 5f                	pop    %r15
    5f34:	c3                   	ret
    5f35:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5f38:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5f3d:	48 85 c0             	test   %rax,%rax
    5f40:	0f 84 6a fe ff ff    	je     5db0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5f46:	48 83 38 01          	cmpq   $0x1,(%rax)
    5f4a:	0f 84 68 01 00 00    	je     60b8 <io_thread+0x658>
    5f50:	48 8d 3d 88 22 00 00 	lea    0x2288(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5f57:	e8 d4 c3 ff ff       	call   2330 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5f5c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5f61:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5f64:	e9 8b fe ff ff       	jmp    5df4 <io_thread+0x394>
    5f69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5f70:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5f78:	8b 02                	mov    (%rdx),%eax
    5f7a:	83 c0 01             	add    $0x1,%eax
    5f7d:	89 02                	mov    %eax,(%rdx)
}
    5f7f:	e9 d8 fe ff ff       	jmp    5e5c <io_thread+0x3fc>
    5f84:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5f88:	85 c0                	test   %eax,%eax
    5f8a:	75 74                	jne    6000 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5f8c:	48 8b 0d 8d 50 00 00 	mov    0x508d(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5f93:	ba 0f 00 00 00       	mov    $0xf,%edx
    5f98:	be 01 00 00 00       	mov    $0x1,%esi
    5f9d:	48 8d 3d 64 22 00 00 	lea    0x2264(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5fa4:	e8 87 c5 ff ff       	call   2530 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5fa9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5fae:	e9 a0 fe ff ff       	jmp    5e53 <io_thread+0x3f3>
    5fb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5fb8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5fbd:	45 31 ff             	xor    %r15d,%r15d
    5fc0:	85 c0                	test   %eax,%eax
    5fc2:	7e 20                	jle    5fe4 <io_thread+0x584>
    5fc4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5fc8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5fcb:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5fcf:	48 c1 e0 04          	shl    $0x4,%rax
    5fd3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5fd8:	e8 23 c3 ff ff       	call   2300 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5fdd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5fe2:	7f e4                	jg     5fc8 <io_thread+0x568>
              close(req->client_socket);
    5fe4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5fe9:	e8 e2 c3 ff ff       	call   23d0 <close@plt>
              free(req);
    5fee:	4c 89 e7             	mov    %r12,%rdi
    5ff1:	e8 0a c3 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5ff6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5ffb:	e9 53 fe ff ff       	jmp    5e53 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    6000:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    6005:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    600a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    6012:	eb 11                	jmp    6025 <io_thread+0x5c5>
    6014:	0f 1f 40 00          	nopl   0x0(%rax)
    6018:	48 83 c0 01          	add    $0x1,%rax
    601c:	48 83 c2 01          	add    $0x1,%rdx
    6020:	48 39 c6             	cmp    %rax,%rsi
    6023:	74 4b                	je     6070 <io_thread+0x610>
        dest[i] = src[i];
    6025:	0f b6 0a             	movzbl (%rdx),%ecx
    6028:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    602a:	80 f9 0d             	cmp    $0xd,%cl
    602d:	75 e9                	jne    6018 <io_thread+0x5b8>
    602f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    6033:	75 e3                	jne    6018 <io_thread+0x5b8>
            dest[i] = '\0';
    6035:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    6038:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    603d:	48 89 da             	mov    %rbx,%rdx
    6040:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    6045:	e8 96 f7 ff ff       	call   57e0 <handle_http_method>
              free(req->iov[0].iov_base);
    604a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    604f:	e8 ac c2 ff ff       	call   2300 <free@plt>
              free(req);
    6054:	4c 89 e7             	mov    %r12,%rdi
    6057:	e8 a4 c2 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    605c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    6061:	e9 ed fd ff ff       	jmp    5e53 <io_thread+0x3f3>
    6066:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6070:	48 8b 0d a9 4f 00 00 	mov    0x4fa9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6077:	ba 12 00 00 00       	mov    $0x12,%edx
    607c:	be 01 00 00 00       	mov    $0x1,%esi
    6081:	48 8d 3d d6 20 00 00 	lea    0x20d6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6088:	e8 a3 c4 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    608d:	bf 01 00 00 00       	mov    $0x1,%edi
    6092:	e8 79 c4 ff ff       	call   2510 <exit@plt>
    6097:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    60a0:	e9 ec fb ff ff       	jmp    5c91 <io_thread+0x231>
    60a5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    60a8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    60ad:	e9 94 fe ff ff       	jmp    5f46 <io_thread+0x4e6>
    60b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    60b8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    60c0:	48 8d 3d 04 21 00 00 	lea    0x2104(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    60c7:	8b 02                	mov    (%rdx),%eax
    60c9:	83 c0 01             	add    $0x1,%eax
    60cc:	89 02                	mov    %eax,(%rdx)
    60ce:	e8 5d c2 ff ff       	call   2330 <puts@plt>
    60d3:	e9 26 fe ff ff       	jmp    5efe <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    60d8:	f7 d8                	neg    %eax
    60da:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    60df:	89 c7                	mov    %eax,%edi
    60e1:	e8 8a c4 ff ff       	call   2570 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    60e6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    60eb:	be 01 00 00 00       	mov    $0x1,%esi
    60f0:	48 8b 3d 29 4f 00 00 	mov    0x4f29(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    60f7:	48 89 c1             	mov    %rax,%rcx
    60fa:	48 8d 15 1f 25 00 00 	lea    0x251f(%rip),%rdx        # 8620 <_IO_stdin_used+0x620>
    6101:	31 c0                	xor    %eax,%eax
    6103:	e8 38 c4 ff ff       	call   2540 <__fprintf_chk@plt>
          exit(1);
    6108:	bf 01 00 00 00       	mov    $0x1,%edi
    610d:	e8 fe c3 ff ff       	call   2510 <exit@plt>
    6112:	48 8b 0d 07 4f 00 00 	mov    0x4f07(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6119:	ba 28 00 00 00       	mov    $0x28,%edx
    611e:	be 01 00 00 00       	mov    $0x1,%esi
    6123:	48 8d 3d c6 24 00 00 	lea    0x24c6(%rip),%rdi        # 85f0 <_IO_stdin_used+0x5f0>
    612a:	e8 01 c4 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    612f:	bf 01 00 00 00       	mov    $0x1,%edi
    6134:	e8 d7 c3 ff ff       	call   2510 <exit@plt>
}
    6139:	e8 42 c2 ff ff       	call   2380 <__stack_chk_fail@plt>
    613e:	66 90                	xchg   %ax,%ax

0000000000006140 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    6140:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6144:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    614b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    6151:	85 c9                	test   %ecx,%ecx
    6153:	0f 8e ea 00 00 00    	jle    6243 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    6159:	41 56                	push   %r14
    615b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    615d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    6160:	41 54                	push   %r12
    6162:	49 89 fc             	mov    %rdi,%r12
    6165:	55                   	push   %rbp
    6166:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6167:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    616b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6170:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    6174:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    617c:	31 db                	xor    %ebx,%ebx
    617e:	8b 10                	mov    (%rax),%edx
    6180:	85 d2                	test   %edx,%edx
    6182:	7e 26                	jle    61aa <barriered_work_ingest+0x6a>
    6184:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    6188:	48 89 dd             	mov    %rbx,%rbp
    618b:	48 c1 e5 08          	shl    $0x8,%rbp
    618f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    6193:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    619a:	74 24                	je     61c0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    619c:	48 83 c3 01          	add    $0x1,%rbx
    61a0:	39 da                	cmp    %ebx,%edx
    61a2:	7f e4                	jg     6188 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    61a4:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    61aa:	49 83 c5 01          	add    $0x1,%r13
    61ae:	44 39 e9             	cmp    %r13d,%ecx
    61b1:	7f bd                	jg     6170 <barriered_work_ingest+0x30>
}
    61b3:	5b                   	pop    %rbx
    61b4:	31 c0                	xor    %eax,%eax
    61b6:	5d                   	pop    %rbp
    61b7:	41 5c                	pop    %r12
    61b9:	41 5d                	pop    %r13
    61bb:	41 5e                	pop    %r14
    61bd:	c3                   	ret
    61be:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    61c0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    61c9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    61d0:	bf 04 00 00 00       	mov    $0x4,%edi
    61d5:	48 c1 e6 05          	shl    $0x5,%rsi
    61d9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    61e0:	48 83 c6 10          	add    $0x10,%rsi
    61e4:	e8 67 c1 ff ff       	call   2350 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    61e9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    61f1:	48 8b 40 50          	mov    0x50(%rax),%rax
    61f5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    61f9:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    61fd:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6207:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    620d:	83 c0 01             	add    $0x1,%eax
    6210:	99                   	cltd
    6211:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    6217:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    621d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6220:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    6228:	48 83 c3 01          	add    $0x1,%rbx
    622c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6230:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    6234:	8b 10                	mov    (%rax),%edx
    6236:	39 da                	cmp    %ebx,%edx
    6238:	0f 8f 46 ff ff ff    	jg     6184 <barriered_work_ingest+0x44>
    623e:	e9 61 ff ff ff       	jmp    61a4 <barriered_work_ingest+0x64>
}
    6243:	31 c0                	xor    %eax,%eax
    6245:	c3                   	ret
    6246:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006250 <barriered_thread>:
void* barriered_thread(void *arg) {
    6250:	f3 0f 1e fa          	endbr64
    6254:	41 56                	push   %r14
    6256:	41 55                	push   %r13
    6258:	41 54                	push   %r12
  int t = 0;
    625a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    625d:	55                   	push   %rbp
  int waiting = 0;
    625e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    6260:	53                   	push   %rbx
    6261:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    6264:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6268:	0f 85 74 02 00 00    	jne    64e2 <barriered_thread+0x292>
    if (t >= data->task_count) {
    626e:	8b 43 40             	mov    0x40(%rbx),%eax
    6271:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6278:	41 39 c4             	cmp    %eax,%r12d
    627b:	0f 8d 6f 01 00 00    	jge    63f0 <barriered_thread+0x1a0>
    6281:	49 63 fc             	movslq %r12d,%rdi
    6284:	48 c1 e7 09          	shl    $0x9,%rdi
    6288:	49 89 fd             	mov    %rdi,%r13
    628b:	eb 32                	jmp    62bf <barriered_thread+0x6f>
    628d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    6290:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6294:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6298:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    629c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    62a0:	4c 01 ef             	add    %r13,%rdi
    62a3:	e8 98 fe ff ff       	call   6140 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    62a8:	8b 43 40             	mov    0x40(%rbx),%eax
    62ab:	41 83 c4 01          	add    $0x1,%r12d
    62af:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    62b6:	44 39 e0             	cmp    %r12d,%eax
    62b9:	0f 8e 19 02 00 00    	jle    64d8 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    62bf:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    62c3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    62c7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    62ce:	75 c0                	jne    6290 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    62d0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    62d4:	83 e8 01             	sub    $0x1,%eax
    62d7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    62dc:	45 85 e4             	test   %r12d,%r12d
    62df:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    62e2:	45 85 c0             	test   %r8d,%r8d
    62e5:	0f 8e 2d 01 00 00    	jle    6418 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    62eb:	48 63 c8             	movslq %eax,%rcx
    62ee:	48 8b 43 18          	mov    0x18(%rbx),%rax
    62f2:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    62f5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    62fb:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    6302:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    6306:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    6309:	45 31 f6             	xor    %r14d,%r14d
    630c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6310:	48 8b 10             	mov    (%rax),%rdx
    6313:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6317:	49 01 cb             	add    %rcx,%r11
    631a:	4c 89 da             	mov    %r11,%rdx
    631d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6324:	75 04                	jne    632a <barriered_thread+0xda>
            arrived++;
    6326:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    632a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6330:	75 04                	jne    6336 <barriered_thread+0xe6>
            prearrive++;
    6332:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6336:	48 83 c0 08          	add    $0x8,%rax
    633a:	48 39 c6             	cmp    %rax,%rsi
    633d:	75 d1                	jne    6310 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    633f:	45 85 d2             	test   %r10d,%r10d
    6342:	0f 84 c0 00 00 00    	je     6408 <barriered_thread+0x1b8>
    6348:	45 39 d0             	cmp    %r10d,%r8d
    634b:	0f 84 b7 00 00 00    	je     6408 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    6351:	45 85 f6             	test   %r14d,%r14d
    6354:	74 0a                	je     6360 <barriered_thread+0x110>
    6356:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    635a:	0f 85 ae 01 00 00    	jne    650e <barriered_thread+0x2be>
    6360:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    6364:	4c 01 ea             	add    %r13,%rdx
    6367:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    636e:	45 85 e4             	test   %r12d,%r12d
    6371:	75 14                	jne    6387 <barriered_thread+0x137>
    6373:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    637a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6381:	0f 8c 69 01 00 00    	jl     64f0 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6387:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    638b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    638f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6399:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    639d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    63a1:	4c 01 ef             	add    %r13,%rdi
    63a4:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    63aa:	48 8b 43 38          	mov    0x38(%rbx),%rax
    63ae:	4c 01 e8             	add    %r13,%rax
    63b1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    63b8:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    63bb:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    63c0:	83 e8 01             	sub    $0x1,%eax
    63c3:	44 39 e0             	cmp    %r12d,%eax
    63c6:	0f 84 a4 00 00 00    	je     6470 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    63cc:	0f ae f8             	sfence
          if (waiting == 0) {
    63cf:	85 ed                	test   %ebp,%ebp
    63d1:	0f 84 d1 00 00 00    	je     64a8 <barriered_thread+0x258>
        int arrived = 0; 
    63d7:	bd 01 00 00 00       	mov    $0x1,%ebp
    63dc:	e9 c7 fe ff ff       	jmp    62a8 <barriered_thread+0x58>
  while (data->running == 1) {
    63e1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    63e5:	0f 85 f7 00 00 00    	jne    64e2 <barriered_thread+0x292>
    63eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    63f0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    63f8:	85 c0                	test   %eax,%eax
    63fa:	7e e5                	jle    63e1 <barriered_thread+0x191>
    63fc:	45 31 e4             	xor    %r12d,%r12d
    63ff:	e9 7d fe ff ff       	jmp    6281 <barriered_thread+0x31>
    6404:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6408:	83 fd 01             	cmp    $0x1,%ebp
    640b:	74 1b                	je     6428 <barriered_thread+0x1d8>
        int arrived = 0; 
    640d:	31 ed                	xor    %ebp,%ebp
    640f:	e9 3d ff ff ff       	jmp    6351 <barriered_thread+0x101>
    6414:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6418:	83 fd 01             	cmp    $0x1,%ebp
    641b:	0f 85 43 ff ff ff    	jne    6364 <barriered_thread+0x114>
        int arrived = 0; 
    6421:	45 31 f6             	xor    %r14d,%r14d
    6424:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6428:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    642f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    6434:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6436:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    643a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6441:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6446:	e8 05 bf ff ff       	call   2350 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    644b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6452:	48 83 c0 01          	add    $0x1,%rax
    6456:	48 99                	cqto
    6458:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    645f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    6466:	e9 e6 fe ff ff       	jmp    6351 <barriered_thread+0x101>
    646b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6470:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6477:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    647e:	0f 8d 48 ff ff ff    	jge    63cc <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    6484:	48 c1 e6 04          	shl    $0x4,%rsi
    6488:	bf 04 00 00 00       	mov    $0x4,%edi
    648d:	48 03 73 70          	add    0x70(%rbx),%rsi
    6491:	e8 ba be ff ff       	call   2350 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6496:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    649e:	e9 29 ff ff ff       	jmp    63cc <barriered_thread+0x17c>
    64a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    64a8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    64af:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    64b4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    64b8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    64bf:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    64c3:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    64c7:	e8 84 be ff ff       	call   2350 <clock_gettime@plt>
            waiting = 1;
    64cc:	e9 06 ff ff ff       	jmp    63d7 <barriered_thread+0x187>
    64d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    64d8:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    64dc:	0f 84 96 fd ff ff    	je     6278 <barriered_thread+0x28>
}
    64e2:	5b                   	pop    %rbx
    64e3:	31 c0                	xor    %eax,%eax
    64e5:	5d                   	pop    %rbp
    64e6:	41 5c                	pop    %r12
    64e8:	41 5d                	pop    %r13
    64ea:	41 5e                	pop    %r14
    64ec:	c3                   	ret
    64ed:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    64f0:	48 c1 e6 04          	shl    $0x4,%rsi
    64f4:	bf 04 00 00 00       	mov    $0x4,%edi
    64f9:	48 03 73 68          	add    0x68(%rbx),%rsi
    64fd:	e8 4e be ff ff       	call   2350 <clock_gettime@plt>
          data->tasks[t].available = 0;
    6502:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6506:	4c 01 ea             	add    %r13,%rdx
    6509:	e9 79 fe ff ff       	jmp    6387 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    650e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6512:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6516:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    651a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    651e:	4c 01 ef             	add    %r13,%rdi
    6521:	e8 1a fc ff ff       	call   6140 <barriered_work_ingest>
          break;
    6526:	e9 39 fd ff ff       	jmp    6264 <barriered_thread+0x14>
    652b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006530 <receive>:
int receive(struct BarrierTask *data) {
    6530:	f3 0f 1e fa          	endbr64
    6534:	41 57                	push   %r15
    6536:	41 56                	push   %r14
    6538:	41 55                	push   %r13
    653a:	41 54                	push   %r12
    653c:	55                   	push   %rbp
    653d:	53                   	push   %rbx
    653e:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6542:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    6549:	45 85 f6             	test   %r14d,%r14d
    654c:	0f 8e 3f 01 00 00    	jle    6691 <receive+0x161>
    if (n == data->thread->real_thread_index) { continue; }
    6552:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    6559:	48 89 fe             	mov    %rdi,%rsi
    655c:	45 31 e4             	xor    %r12d,%r12d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    655f:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    6561:	49 63 6f 08          	movslq 0x8(%r15),%rbp
    6565:	49 89 ed             	mov    %rbp,%r13
    6568:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6570:	41 39 dd             	cmp    %ebx,%r13d
    6573:	0f 84 05 01 00 00    	je     667e <receive+0x14e>
    struct Data *me = data->mailboxes[n].lower;
    6579:	48 8b 86 70 01 00 00 	mov    0x170(%rsi),%rax
    6580:	4a 8b 0c 20          	mov    (%rax,%r12,1),%rcx
    if (me->available_reading == 1) {
    6584:	8b 81 00 02 00 00    	mov    0x200(%rcx),%eax
    658a:	83 f8 01             	cmp    $0x1,%eax
    658d:	74 11                	je     65a0 <receive+0x70>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    658f:	83 b9 18 03 00 00 02 	cmpl   $0x2,0x318(%rcx)
    6596:	75 08                	jne    65a0 <receive+0x70>
    6598:	85 c0                	test   %eax,%eax
    659a:	0f 84 de 00 00 00    	je     667e <receive+0x14e>
    for (; me->messages_count > 0 ; ) {
    65a0:	48 8b b9 80 00 00 00 	mov    0x80(%rcx),%rdi
    65a7:	48 85 ff             	test   %rdi,%rdi
    65aa:	0f 8e b0 00 00 00    	jle    6660 <receive+0x130>
    65b0:	4c 8b 8e 78 01 00 00 	mov    0x178(%rsi),%r9
    65b7:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    65be:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      me->messages[x]->times_received++;
    65c2:	4c 8b 19             	mov    (%rcx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    65c5:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    65c9:	49 01 f9             	add    %rdi,%r9
    65cc:	49 01 f8             	add    %rdi,%r8
    65cf:	48 03 b9 10 03 00 00 	add    0x310(%rcx),%rdi
    65d6:	eb 0e                	jmp    65e6 <receive+0xb6>
    65d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (; me->messages_count > 0 ; ) {
    65e0:	48 83 e8 01          	sub    $0x1,%rax
    65e4:	72 7a                	jb     6660 <receive+0x130>
      data->sends++;
    65e6:	4c 89 ca             	mov    %r9,%rdx
      me->messages_count--;
    65e9:	48 89 81 80 00 00 00 	mov    %rax,0x80(%rcx)
      data->sends++;
    65f0:	48 29 c2             	sub    %rax,%rdx
    65f3:	48 89 96 78 01 00 00 	mov    %rdx,0x178(%rsi)
      data->n++;
    65fa:	4c 89 c2             	mov    %r8,%rdx
    65fd:	48 29 c2             	sub    %rax,%rdx
    6600:	48 89 96 08 01 00 00 	mov    %rdx,0x108(%rsi)
      me->received++;
    6607:	48 89 fa             	mov    %rdi,%rdx
    660a:	48 29 c2             	sub    %rax,%rdx
    660d:	48 89 91 10 03 00 00 	mov    %rdx,0x310(%rcx)
      me->messages[x]->times_received++;
    6614:	48 63 d0             	movslq %eax,%rdx
    6617:	49 8b 14 d3          	mov    (%r11,%rdx,8),%rdx
    661b:	48 83 42 28 01       	addq   $0x1,0x28(%rdx)
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    6620:	4c 39 52 10          	cmp    %r10,0x10(%rdx)
    6624:	75 ba                	jne    65e0 <receive+0xb0>
    6626:	48 39 6a 08          	cmp    %rbp,0x8(%rdx)
    662a:	75 b4                	jne    65e0 <receive+0xb0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    662c:	49 63 47 04          	movslq 0x4(%r15),%rax
    6630:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6632:	bf 01 00 00 00       	mov    $0x1,%edi
    6637:	ba 01 00 00 00       	mov    $0x1,%edx
    663c:	48 8d 35 05 20 00 00 	lea    0x2005(%rip),%rsi        # 8648 <_IO_stdin_used+0x648>
    6643:	48 39 e8             	cmp    %rbp,%rax
    6646:	0f 94 c1             	sete   %cl
    6649:	31 c0                	xor    %eax,%eax
    664b:	e8 60 be ff ff       	call   24b0 <__printf_chk@plt>
        exit(1);
    6650:	bf 01 00 00 00       	mov    $0x1,%edi
    6655:	e8 b6 be ff ff       	call   2510 <exit@plt>
    665a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      me->available_reading = 0;
    6660:	c7 81 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rcx)
      me->finished_reading = 1;
    666a:	c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rcx)
      me->available_sending = 1;
    6674:	c7 81 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rcx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    667e:	83 c3 01             	add    $0x1,%ebx
    6681:	49 81 c4 80 01 00 00 	add    $0x180,%r12
    6688:	44 39 f3             	cmp    %r14d,%ebx
    668b:	0f 85 df fe ff ff    	jne    6570 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    6691:	0f ae f8             	sfence
}
    6694:	48 83 c4 08          	add    $0x8,%rsp
    6698:	31 c0                	xor    %eax,%eax
    669a:	5b                   	pop    %rbx
    669b:	5d                   	pop    %rbp
    669c:	41 5c                	pop    %r12
    669e:	41 5d                	pop    %r13
    66a0:	41 5e                	pop    %r14
    66a2:	41 5f                	pop    %r15
    66a4:	c3                   	ret
    66a5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000066b0 <sendm>:
int sendm(struct BarrierTask *data) {
    66b0:	f3 0f 1e fa          	endbr64
    66b4:	41 57                	push   %r15
    66b6:	41 56                	push   %r14
    66b8:	41 55                	push   %r13
    66ba:	41 54                	push   %r12
    66bc:	55                   	push   %rbp
    66bd:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    66be:	8b 8f 40 01 00 00    	mov    0x140(%rdi),%ecx
    66c4:	85 c9                	test   %ecx,%ecx
    66c6:	0f 8e d4 00 00 00    	jle    67a0 <sendm+0xf0>
    66cc:	48 89 fa             	mov    %rdi,%rdx
    66cf:	31 c0                	xor    %eax,%eax
    66d1:	31 ff                	xor    %edi,%edi
    66d3:	eb 26                	jmp    66fb <sendm+0x4b>
    66d5:	0f 1f 00             	nopl   (%rax)
    66d8:	48 c7 86 00 01 00 00 00 00 00 00 	movq   $0x0,0x100(%rsi)
    66e3:	8b 8a 40 01 00 00    	mov    0x140(%rdx),%ecx
    66e9:	83 c0 01             	add    $0x1,%eax
    66ec:	48 81 c7 80 01 00 00 	add    $0x180,%rdi
    66f3:	39 c8                	cmp    %ecx,%eax
    66f5:	0f 8d a5 00 00 00    	jge    67a0 <sendm+0xf0>
        if (n == data->thread->real_thread_index) { continue; }
    66fb:	4c 8b a2 28 01 00 00 	mov    0x128(%rdx),%r12
    6702:	41 39 44 24 08       	cmp    %eax,0x8(%r12)
    6707:	74 e0                	je     66e9 <sendm+0x39>
        struct Data *them = data->mailboxes[n].higher;
    6709:	48 8b b2 70 01 00 00 	mov    0x170(%rdx),%rsi
    6710:	48 01 fe             	add    %rdi,%rsi
        data->mailboxes[n].counter++;
    6713:	48 8b 9e 00 01 00 00 	mov    0x100(%rsi),%rbx
        struct Data *them = data->mailboxes[n].higher;
    671a:	4c 8b 86 80 00 00 00 	mov    0x80(%rsi),%r8
        data->mailboxes[n].counter++;
    6721:	48 8d 4b 01          	lea    0x1(%rbx),%rcx
        if (data->mailboxes[n].counter > limit) {
    6725:	48 83 f9 02          	cmp    $0x2,%rcx
    6729:	7f ad                	jg     66d8 <sendm+0x28>
    672b:	48 89 8e 00 01 00 00 	mov    %rcx,0x100(%rsi)
        if (data->mailboxes[n].counter < limit) {
    6732:	75 54                	jne    6788 <sendm+0xd8>
        if (them->messages_count > 0) {
    6734:	4d 8b 98 80 00 00 00 	mov    0x80(%r8),%r11
    673b:	4d 85 db             	test   %r11,%r11
    673e:	7f 48                	jg     6788 <sendm+0xd8>
        if (them->available_sending == 1) {
    6740:	41 8b 88 00 01 00 00 	mov    0x100(%r8),%ecx
    6747:	83 f9 01             	cmp    $0x1,%ecx
    674a:	74 0e                	je     675a <sendm+0xaa>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    674c:	41 83 b8 18 03 00 00 02 	cmpl   $0x2,0x318(%r8)
    6754:	75 04                	jne    675a <sendm+0xaa>
    6756:	85 c9                	test   %ecx,%ecx
    6758:	74 2e                	je     6788 <sendm+0xd8>
        if (data->sending == 1) {
    675a:	83 ba 80 01 00 00 01 	cmpl   $0x1,0x180(%rdx)
    6761:	74 4d                	je     67b0 <sendm+0x100>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter >= limit) {
    6763:	83 be b0 00 00 00 02 	cmpl   $0x2,0xb0(%rsi)
    676a:	75 1c                	jne    6788 <sendm+0xd8>
          data->mailboxes[n].counter = 0;
    676c:	48 c7 86 00 01 00 00 00 00 00 00 	movq   $0x0,0x100(%rsi)
          data->thread->have_foreign = 1;
    6777:	41 c7 84 24 d8 00 00 00 01 00 00 00 	movl   $0x1,0xd8(%r12)
    6783:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6788:	8b 8a 40 01 00 00    	mov    0x140(%rdx),%ecx
    678e:	83 c0 01             	add    $0x1,%eax
    6791:	48 81 c7 80 01 00 00 	add    $0x180,%rdi
    6798:	39 c8                	cmp    %ecx,%eax
    679a:	0f 8c 5b ff ff ff    	jl     66fb <sendm+0x4b>
      asm volatile ("sfence" ::: "memory");
    67a0:	0f ae f8             	sfence
}
    67a3:	31 c0                	xor    %eax,%eax
    67a5:	5b                   	pop    %rbx
    67a6:	5d                   	pop    %rbp
    67a7:	41 5c                	pop    %r12
    67a9:	41 5d                	pop    %r13
    67ab:	41 5e                	pop    %r14
    67ad:	41 5f                	pop    %r15
    67af:	c3                   	ret
          for (; them->messages_count < min;) {
    67b0:	49 63 a8 88 00 00 00 	movslq 0x88(%r8),%rbp
    67b7:	49 39 eb             	cmp    %rbp,%r11
    67ba:	7d 70                	jge    682c <sendm+0x17c>
            them->messages[them->messages_count++] = data->message; 
    67bc:	4d 8b 28             	mov    (%r8),%r13
    67bf:	4c 8b ba 08 01 00 00 	mov    0x108(%rdx),%r15
    67c6:	4d 8b b0 08 03 00 00 	mov    0x308(%r8),%r14
    67cd:	4f 8d 54 dd 00       	lea    0x0(%r13,%r11,8),%r10
    67d2:	49 8d 5c ed 00       	lea    0x0(%r13,%rbp,8),%rbx
    67d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    67e0:	48 8b 8a 88 01 00 00 	mov    0x188(%rdx),%rcx
          for (; them->messages_count < min;) {
    67e7:	49 83 c2 08          	add    $0x8,%r10
            data->message->times_sent++;
    67eb:	4c 8b 49 20          	mov    0x20(%rcx),%r9
            them->messages[them->messages_count++] = data->message; 
    67ef:	49 89 4a f8          	mov    %rcx,-0x8(%r10)
            data->message->times_sent++;
    67f3:	49 83 c1 01          	add    $0x1,%r9
    67f7:	4c 89 49 20          	mov    %r9,0x20(%rcx)
          for (; them->messages_count < min;) {
    67fb:	49 39 da             	cmp    %rbx,%r10
    67fe:	75 e0                	jne    67e0 <sendm+0x130>
    6800:	48 89 eb             	mov    %rbp,%rbx
    6803:	4c 29 db             	sub    %r11,%rbx
    6806:	4d 8d 14 1f          	lea    (%r15,%rbx,1),%r10
    680a:	4c 89 92 08 01 00 00 	mov    %r10,0x108(%rdx)
    6811:	4d 8d 14 1e          	lea    (%r14,%rbx,1),%r10
    6815:	4d 89 90 08 03 00 00 	mov    %r10,0x308(%r8)
    681c:	49 89 a8 80 00 00 00 	mov    %rbp,0x80(%r8)
    6823:	49 89 4c ed f8       	mov    %rcx,-0x8(%r13,%rbp,8)
    6828:	4c 89 49 20          	mov    %r9,0x20(%rcx)
          them->available_sending = 0;
    682c:	41 c7 80 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r8)
          them->available_reading = 1;
    6837:	41 c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%r8)
          them->available_receiving = 1;
    6842:	41 c7 80 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r8)
    684d:	e9 11 ff ff ff       	jmp    6763 <sendm+0xb3>
    6852:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    685d:	0f 1f 00             	nopl   (%rax)

0000000000006860 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6860:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6864:	85 f6                	test   %esi,%esi
    6866:	74 18                	je     6880 <mailboxkind+0x20>
  return NULL;
    6868:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    686a:	83 fe 01             	cmp    $0x1,%esi
    686d:	74 01                	je     6870 <mailboxkind+0x10>
}
    686f:	c3                   	ret
    return mailbox->higher;
    6870:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
}
    6877:	c3                   	ret
    6878:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    return mailbox->lower;
    6880:	48 8b 07             	mov    (%rdi),%rax
    6883:	c3                   	ret
    6884:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    688f:	90                   	nop

0000000000006890 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    6890:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6894:	85 d2                	test   %edx,%edx
    6896:	75 08                	jne    68a0 <setmailboxkind+0x10>
    mailbox->lower = data;
    6898:	48 89 37             	mov    %rsi,(%rdi)
}
    689b:	31 c0                	xor    %eax,%eax
    689d:	c3                   	ret
    689e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    68a0:	83 fa 01             	cmp    $0x1,%edx
    68a3:	74 13                	je     68b8 <setmailboxkind+0x28>
  if (kind == 2) {
    68a5:	83 fa 02             	cmp    $0x2,%edx
    68a8:	75 1e                	jne    68c8 <setmailboxkind+0x38>
    mailbox->pending_lower = data;
    68aa:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
}
    68b1:	31 c0                	xor    %eax,%eax
    68b3:	c3                   	ret
    68b4:	0f 1f 40 00          	nopl   0x0(%rax)
    mailbox->higher = data;
    68b8:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
}
    68bf:	31 c0                	xor    %eax,%eax
    68c1:	c3                   	ret
    68c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (kind == 3) {
    68c8:	83 fa 03             	cmp    $0x3,%edx
    68cb:	75 ce                	jne    689b <setmailboxkind+0xb>
    mailbox->pending_higher = data;
    68cd:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
}
    68d4:	31 c0                	xor    %eax,%eax
    68d6:	c3                   	ret
    68d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000068e0 <fswap>:
int fswap(struct BarrierTask *data) {
    68e0:	f3 0f 1e fa          	endbr64
          int y = (k * data->thread->threads_per_group) + data->thread_index;
    68e4:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    68eb:	8b 97 94 01 00 00    	mov    0x194(%rdi),%edx
    68f1:	8b 8f 30 01 00 00    	mov    0x130(%rdi),%ecx
      int t = data->task_index;
    68f7:	48 63 77 04          	movslq 0x4(%rdi),%rsi
          int y = (k * data->thread->threads_per_group) + data->thread_index;
    68fb:	49 63 80 c4 00 00 00 	movslq 0xc4(%r8),%rax
    6902:	0f af d0             	imul   %eax,%edx
    6905:	01 d1                	add    %edx,%ecx
          for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6907:	85 c0                	test   %eax,%eax
    6909:	0f 8e 0c 01 00 00    	jle    6a1b <fswap+0x13b>
            int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    690f:	48 63 c9             	movslq %ecx,%rcx
int fswap(struct BarrierTask *data) {
    6912:	41 56                	push   %r14
    6914:	48 63 d2             	movslq %edx,%rdx
            int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6917:	48 c1 e6 09          	shl    $0x9,%rsi
int fswap(struct BarrierTask *data) {
    691b:	41 55                	push   %r13
    691d:	48 01 d0             	add    %rdx,%rax
    6920:	41 54                	push   %r12
    6922:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
    6926:	55                   	push   %rbp
    6927:	49 c1 e4 07          	shl    $0x7,%r12
    692b:	53                   	push   %rbx
            int next_task = abs((t + 1) % (data->thread_count));
    692c:	44 8b 8f 34 01 00 00 	mov    0x134(%rdi),%r9d
            int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6933:	48 8d 3c cd 00 00 00 00 	lea    0x0(,%rcx,8),%rdi
                int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    693b:	48 8d 1c 49          	lea    (%rcx,%rcx,2),%rbx
            int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    693f:	4d 8b 50 20          	mov    0x20(%r8),%r10
    6943:	48 29 cf             	sub    %rcx,%rdi
    6946:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
                int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    694e:	48 c1 e3 07          	shl    $0x7,%rbx
            int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6952:	48 c1 e7 05          	shl    $0x5,%rdi
    6956:	48 29 d1             	sub    %rdx,%rcx
    6959:	49 8b 6c 3a 38       	mov    0x38(%r10,%rdi,1),%rbp
    695e:	48 c1 e1 05          	shl    $0x5,%rcx
    6962:	48 8d 3c 52          	lea    (%rdx,%rdx,2),%rdi
    6966:	49 01 ca             	add    %rcx,%r10
    6969:	48 c1 e7 07          	shl    $0x7,%rdi
    696d:	4c 8b ac 35 70 01 00 00 	mov    0x170(%rbp,%rsi,1),%r13
    6975:	eb 1c                	jmp    6993 <fswap+0xb3>
    6977:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6980:	48 81 c7 80 01 00 00 	add    $0x180,%rdi
    6987:	49 81 c2 e0 00 00 00 	add    $0xe0,%r10
    698e:	49 39 fc             	cmp    %rdi,%r12
    6991:	74 7d                	je     6a10 <fswap+0x130>
            if (kind == MAILBOX_FRIEND) {
    6993:	41 83 bc 3d b0 00 00 00 01 	cmpl   $0x1,0xb0(%r13,%rdi,1)
    699c:	75 e2                	jne    6980 <fswap+0xa0>
                int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    699e:	4d 8b 42 38          	mov    0x38(%r10),%r8
                 for (int nn = 0 ; nn < data->thread_count; nn++) {
    69a2:	45 85 c9             	test   %r9d,%r9d
    69a5:	7e d9                	jle    6980 <fswap+0xa0>
    69a7:	49 81 c0 70 01 00 00 	add    $0x170,%r8
    69ae:	31 c9                	xor    %ecx,%ecx
                  int next_task = abs((nn + 1) % (data->thread_count));
    69b0:	83 c1 01             	add    $0x1,%ecx
                  struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    69b3:	49 8b 30             	mov    (%r8),%rsi
                 for (int nn = 0 ; nn < data->thread_count; nn++) {
    69b6:	49 81 c0 00 02 00 00 	add    $0x200,%r8
                  int next_task = abs((nn + 1) % (data->thread_count));
    69bd:	89 c8                	mov    %ecx,%eax
    69bf:	99                   	cltd
                  struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    69c0:	48 01 de             	add    %rbx,%rsi
                  int next_task = abs((nn + 1) % (data->thread_count));
    69c3:	41 f7 f9             	idiv   %r9d
    mailbox->lower = data;
    69c6:	4c 8b b6 80 00 00 00 	mov    0x80(%rsi),%r14
    return mailbox->lower;
    69cd:	4c 8b 1e             	mov    (%rsi),%r11
                  struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    69d0:	48 63 d2             	movslq %edx,%rdx
    69d3:	48 c1 e2 09          	shl    $0x9,%rdx
    69d7:	48 8b 84 15 70 01 00 00 	mov    0x170(%rbp,%rdx,1),%rax
    69df:	48 01 f8             	add    %rdi,%rax
    return mailbox->lower;
    69e2:	48 8b 10             	mov    (%rax),%rdx
    mailbox->lower = data;
    69e5:	4c 89 30             	mov    %r14,(%rax)
    69e8:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    mailbox->higher = data;
    69ef:	48 89 96 80 00 00 00 	mov    %rdx,0x80(%rsi)
    mailbox->lower = data;
    69f6:	4c 89 36             	mov    %r14,(%rsi)
    mailbox->higher = data;
    69f9:	4c 89 98 80 00 00 00 	mov    %r11,0x80(%rax)
                 for (int nn = 0 ; nn < data->thread_count; nn++) {
    6a00:	41 39 c9             	cmp    %ecx,%r9d
    6a03:	75 ab                	jne    69b0 <fswap+0xd0>
    6a05:	e9 76 ff ff ff       	jmp    6980 <fswap+0xa0>
    6a0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
}
    6a10:	5b                   	pop    %rbx
    6a11:	31 c0                	xor    %eax,%eax
    6a13:	5d                   	pop    %rbp
    6a14:	41 5c                	pop    %r12
    6a16:	41 5d                	pop    %r13
    6a18:	41 5e                	pop    %r14
    6a1a:	c3                   	ret
    6a1b:	31 c0                	xor    %eax,%eax
    6a1d:	c3                   	ret
    6a1e:	66 90                	xchg   %ax,%ax

0000000000006a20 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6a20:	f3 0f 1e fa          	endbr64
    6a24:	41 57                	push   %r15
    6a26:	41 56                	push   %r14
    6a28:	41 55                	push   %r13
    6a2a:	41 54                	push   %r12
    6a2c:	55                   	push   %rbp
    6a2d:	53                   	push   %rbx
    6a2e:	48 89 fb             	mov    %rdi,%rbx
    6a31:	48 83 ec 58          	sub    $0x58,%rsp
        int t = data->task_index;
    6a35:	44 8b 67 04          	mov    0x4(%rdi),%r12d
  if (data->thread_index == data->task_index) {
    6a39:	44 39 a7 30 01 00 00 	cmp    %r12d,0x130(%rdi)
    6a40:	74 6e                	je     6ab0 <barriered_work+0x90>
    receive(data);
    6a42:	e8 e9 fa ff ff       	call   6530 <receive>
    fswap(data); 
    6a47:	48 89 df             	mov    %rbx,%rdi
    6a4a:	e8 91 fe ff ff       	call   68e0 <fswap>
    receive(data);
    6a4f:	48 89 df             	mov    %rbx,%rdi
    6a52:	e8 d9 fa ff ff       	call   6530 <receive>
    while (data->scheduled == 1) {
    6a57:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6a5e:	75 14                	jne    6a74 <barriered_work+0x54>
      data->n++;
    6a60:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    6a68:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6a6b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6a72:	74 ec                	je     6a60 <barriered_work+0x40>
    sendm(data);
    6a74:	48 89 df             	mov    %rbx,%rdi
    6a77:	e8 34 fc ff ff       	call   66b0 <sendm>
  if (t == data->thread_count - 1) {
    6a7c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6a82:	83 e8 01             	sub    $0x1,%eax
    6a85:	44 39 e0             	cmp    %r12d,%eax
    6a88:	0f 84 bd 03 00 00    	je     6e4b <barriered_work+0x42b>
  data->swap = 0;
    6a8e:	c7 83 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbx)
  asm volatile ("sfence" ::: "memory");
    6a98:	0f ae f8             	sfence
}
    6a9b:	48 83 c4 58          	add    $0x58,%rsp
    6a9f:	31 c0                	xor    %eax,%eax
    6aa1:	5b                   	pop    %rbx
    6aa2:	5d                   	pop    %rbp
    6aa3:	41 5c                	pop    %r12
    6aa5:	41 5d                	pop    %r13
    6aa7:	41 5e                	pop    %r14
    6aa9:	41 5f                	pop    %r15
    6aab:	c3                   	ret
    6aac:	0f 1f 40 00          	nopl   0x0(%rax)
    receive(data);
    6ab0:	e8 7b fa ff ff       	call   6530 <receive>
        if (data->thread->have_foreign == 1) {
    6ab5:	4c 8b b3 28 01 00 00 	mov    0x128(%rbx),%r14
    6abc:	41 83 be d8 00 00 00 01 	cmpl   $0x1,0xd8(%r14)
    6ac4:	0f 85 8e 02 00 00    	jne    6d58 <barriered_work+0x338>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6aca:	44 8b bb 40 01 00 00 	mov    0x140(%rbx),%r15d
          data->thread->have_foreign = 0;
    6ad1:	41 c7 86 d8 00 00 00 00 00 00 00 	movl   $0x0,0xd8(%r14)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6adc:	45 85 ff             	test   %r15d,%r15d
    6adf:	0f 8e 73 02 00 00    	jle    6d58 <barriered_work+0x338>
              int next_task = abs((t + 1) % (data->thread_count));
    6ae5:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
        int b = data->thread->real_thread_index;
    6aeb:	41 8b 56 08          	mov    0x8(%r14),%edx
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6aef:	31 f6                	xor    %esi,%esi
    6af1:	45 31 c0             	xor    %r8d,%r8d
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6af4:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
              int next_task = abs((t + 1) % (data->thread_count));
    6afc:	89 44 24 24          	mov    %eax,0x24(%rsp)
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6b00:	49 63 c4             	movslq %r12d,%rax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6b03:	41 89 d3             	mov    %edx,%r11d
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6b06:	48 c1 e0 09          	shl    $0x9,%rax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6b0a:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6b0f:	49 89 c5             	mov    %rax,%r13
    6b12:	48 63 c2             	movslq %edx,%rax
    6b15:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    6b1d:	48 29 c1             	sub    %rax,%rcx
    6b20:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    6b24:	48 c1 e1 05          	shl    $0x5,%rcx
    6b28:	48 c1 e0 07          	shl    $0x7,%rax
    6b2c:	48 89 cd             	mov    %rcx,%rbp
    6b2f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6b34:	48 89 d9             	mov    %rbx,%rcx
    6b37:	eb 27                	jmp    6b60 <barriered_work+0x140>
    6b39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6b40:	83 44 24 0c 01       	addl   $0x1,0xc(%rsp)
    6b45:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    6b49:	49 81 c0 80 01 00 00 	add    $0x180,%r8
    6b50:	48 81 c6 e0 00 00 00 	add    $0xe0,%rsi
    6b57:	44 39 f8             	cmp    %r15d,%eax
    6b5a:	0f 84 f0 01 00 00    	je     6d50 <barriered_work+0x330>
              if (y == b) { continue; }
    6b60:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    6b64:	41 39 c3             	cmp    %eax,%r11d
    6b67:	74 d7                	je     6b40 <barriered_work+0x120>
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6b69:	49 8b 56 20          	mov    0x20(%r14),%rdx
    6b6d:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    6b72:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    6b76:	44 8b 88 98 01 00 00 	mov    0x198(%rax),%r9d
    6b7d:	45 85 c9             	test   %r9d,%r9d
    6b80:	75 be                	jne    6b40 <barriered_work+0x120>
    6b82:	4c 8b 4c 2a 38       	mov    0x38(%rdx,%rbp,1),%r9
    6b87:	4b 8d 14 29          	lea    (%r9,%r13,1),%rdx
    6b8b:	44 8b 92 98 01 00 00 	mov    0x198(%rdx),%r10d
    6b92:	45 85 d2             	test   %r10d,%r10d
    6b95:	75 a9                	jne    6b40 <barriered_work+0x120>
    6b97:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    6b9e:	42 83 bc 02 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r8,1)
    6ba7:	75 97                	jne    6b40 <barriered_work+0x120>
    6ba9:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6bb0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    6bb5:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    6bbd:	75 81                	jne    6b40 <barriered_work+0x120>
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6bbf:	48 63 44 24 24       	movslq 0x24(%rsp),%rax
    6bc4:	85 c0                	test   %eax,%eax
    6bc6:	0f 8e 74 ff ff ff    	jle    6b40 <barriered_work+0x120>
    6bcc:	48 89 c2             	mov    %rax,%rdx
    6bcf:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
    6bd4:	41 bc 70 01 00 00    	mov    $0x170,%r12d
    6bda:	48 c1 e2 09          	shl    $0x9,%rdx
    6bde:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    6be3:	48 89 74 24 40       	mov    %rsi,0x40(%rsp)
    6be8:	48 8d 9a 98 01 00 00 	lea    0x198(%rdx),%rbx
    6bef:	48 89 54 24 48       	mov    %rdx,0x48(%rsp)
    6bf4:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    6bf9:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    6bfe:	44 89 5c 24 38       	mov    %r11d,0x38(%rsp)
    6c03:	44 8b 5c 24 24       	mov    0x24(%rsp),%r11d
    6c08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                      int next_task = abs((nn + 1) % data->thread_count);
    6c10:	41 83 c2 01          	add    $0x1,%r10d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6c14:	4b 8b 34 21          	mov    (%r9,%r12,1),%rsi
                      int next_task = abs((nn + 1) % data->thread_count);
    6c18:	44 89 d0             	mov    %r10d,%eax
    6c1b:	99                   	cltd
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6c1c:	4c 01 c6             	add    %r8,%rsi
                      int next_task = abs((nn + 1) % data->thread_count);
    6c1f:	41 f7 fb             	idiv   %r11d
    return mailbox->lower;
    6c22:	4c 8b 36             	mov    (%rsi),%r14
    6c25:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    mailbox->lower = data;
    6c2a:	4c 8b b6 80 00 00 00 	mov    0x80(%rsi),%r14
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6c31:	48 63 d2             	movslq %edx,%rdx
    6c34:	48 c1 e2 09          	shl    $0x9,%rdx
    6c38:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    6c40:	4c 01 e8             	add    %r13,%rax
    return mailbox->lower;
    6c43:	4c 8b 38             	mov    (%rax),%r15
    return mailbox->higher;
    6c46:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    mailbox->lower = data;
    6c4d:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    6c50:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    6c55:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    mailbox->lower = data;
    6c5c:	48 89 16             	mov    %rdx,(%rsi)
    mailbox->higher = data;
    6c5f:	4c 89 be 80 00 00 00 	mov    %r15,0x80(%rsi)
    6c66:	be 98 01 00 00       	mov    $0x198,%esi
    6c6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
    6c70:	41 c7 04 31 01 00 00 00 	movl   $0x1,(%r9,%rsi,1)
                        data->thread->all_threads[t2].tasks[jj].swap = 1;
    6c78:	c7 04 37 01 00 00 00 	movl   $0x1,(%rdi,%rsi,1)
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
    6c7f:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    6c86:	48 39 f3             	cmp    %rsi,%rbx
    6c89:	75 e5                	jne    6c70 <barriered_work+0x250>
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6c8b:	4a 8b 34 27          	mov    (%rdi,%r12,1),%rsi
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6c8f:	48 8b 00             	mov    (%rax),%rax
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    6c92:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6c9d:	49 81 c4 00 02 00 00 	add    $0x200,%r12
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6ca4:	4a 8b b4 2e 80 00 00 00 	mov    0x80(%rsi,%r13,1),%rsi
    6cac:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6cb6:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6cc0:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6cca:	45 39 d3             	cmp    %r10d,%r11d
    6ccd:	0f 85 3d ff ff ff    	jne    6c10 <barriered_work+0x1f0>
    6cd3:	48 8b 54 24 48       	mov    0x48(%rsp),%rdx
    6cd8:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    6cdd:	b8 70 01 00 00       	mov    $0x170,%eax
    6ce2:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    6ce7:	44 8b 5c 24 38       	mov    0x38(%rsp),%r11d
    6cec:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
    6cf1:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    6cf6:	48 8d 9a 70 01 00 00 	lea    0x170(%rdx),%rbx
    6cfd:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    6d02:	eb 13                	jmp    6d17 <barriered_work+0x2f7>
    6d04:	0f 1f 40 00          	nopl   0x0(%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6d08:	48 05 00 02 00 00    	add    $0x200,%rax
    6d0e:	48 39 c3             	cmp    %rax,%rbx
    6d11:	0f 84 29 fe ff ff    	je     6b40 <barriered_work+0x120>
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6d17:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    6d1b:	4d 8b 14 01          	mov    (%r9,%rax,1),%r10
    6d1f:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    6d23:	4b 39 14 02          	cmp    %rdx,(%r10,%r8,1)
    6d27:	75 df                	jne    6d08 <barriered_work+0x2e8>
    6d29:	bf 01 00 00 00       	mov    $0x1,%edi
    6d2e:	48 8d 35 f6 14 00 00 	lea    0x14f6(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6d35:	31 c0                	xor    %eax,%eax
    6d37:	e8 74 b7 ff ff       	call   24b0 <__printf_chk@plt>
                          exit(1);
    6d3c:	bf 01 00 00 00       	mov    $0x1,%edi
    6d41:	e8 ca b7 ff ff       	call   2510 <exit@plt>
    6d46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6d50:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    6d55:	48 89 cb             	mov    %rcx,%rbx
     fswap(data);
    6d58:	48 89 df             	mov    %rbx,%rdi
    6d5b:	e8 80 fb ff ff       	call   68e0 <fswap>
      receive(data);
    6d60:	48 89 df             	mov    %rbx,%rdi
    6d63:	e8 c8 f7 ff ff       	call   6530 <receive>
      asm volatile ("sfence" ::: "memory");
    6d68:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6d6b:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6d72:	31 ff                	xor    %edi,%edi
    6d74:	48 c1 e6 05          	shl    $0x5,%rsi
    6d78:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6d7f:	e8 cc b5 ff ff       	call   2350 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6d84:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    6d8b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    6d92:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6d96:	8b 4a 10             	mov    0x10(%rdx),%ecx
    6d99:	8d 69 01             	lea    0x1(%rcx),%ebp
    6d9c:	89 6a 10             	mov    %ebp,0x10(%rdx)
    while (data->scheduled == 1) {
    6d9f:	75 58                	jne    6df9 <barriered_work+0x3d9>
    6da1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6da8:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    6daf:	48 8b 40 18          	mov    0x18(%rax),%rax
    6db3:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
      data->n++;
    6db7:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6dbf:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6dc3:	48 c1 e7 09          	shl    $0x9,%rdi
    6dc7:	48 03 78 38          	add    0x38(%rax),%rdi
    6dcb:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    6dd1:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6dd4:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    6ddb:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    6de2:	74 c4                	je     6da8 <barriered_work+0x388>
    if (modcount != data->thread->protected_state->modcount) {
    6de4:	48 8b 40 48          	mov    0x48(%rax),%rax
    6de8:	3b 68 10             	cmp    0x10(%rax),%ebp
    6deb:	74 0c                	je     6df9 <barriered_work+0x3d9>
    6ded:	48 8d 3d 52 14 00 00 	lea    0x1452(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6df4:	e8 37 b5 ff ff       	call   2330 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6df9:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6e00:	31 ff                	xor    %edi,%edi
    6e02:	48 c1 e6 05          	shl    $0x5,%rsi
    6e06:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6e0d:	48 83 c6 10          	add    $0x10,%rsi
    6e11:	e8 3a b5 ff ff       	call   2350 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6e16:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    sendm(data);
    6e1d:	48 89 df             	mov    %rbx,%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6e20:	48 83 c0 01          	add    $0x1,%rax
    6e24:	48 99                	cqto
    6e26:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6e2d:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    sendm(data);
    6e34:	e8 77 f8 ff ff       	call   66b0 <sendm>
  if (t == data->thread_count - 1) {
    6e39:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6e3f:	83 e8 01             	sub    $0x1,%eax
    6e42:	44 39 e0             	cmp    %r12d,%eax
    6e45:	0f 85 43 fc ff ff    	jne    6a8e <barriered_work+0x6e>
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6e4b:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    6e52:	85 d2                	test   %edx,%edx
    6e54:	0f 8e 34 fc ff ff    	jle    6a8e <barriered_work+0x6e>
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6e5a:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    6e61:	48 c1 e2 09          	shl    $0x9,%rdx
    6e65:	48 63 71 08          	movslq 0x8(%rcx),%rsi
    6e69:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
    6e71:	48 29 f0             	sub    %rsi,%rax
    6e74:	48 c1 e0 05          	shl    $0x5,%rax
    6e78:	48 03 41 20          	add    0x20(%rcx),%rax
    6e7c:	48 8b 40 38          	mov    0x38(%rax),%rax
    6e80:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    6e84:	80 e6 02             	and    $0x2,%dh
    6e87:	74 17                	je     6ea0 <barriered_work+0x480>
    6e89:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6e90:	48 05 00 02 00 00    	add    $0x200,%rax
    6e96:	48 39 c8             	cmp    %rcx,%rax
    6e99:	0f 84 ef fb ff ff    	je     6a8e <barriered_work+0x6e>
    6e9f:	90                   	nop
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6ea0:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
    6ea7:	83 80 9c 03 00 00 01 	addl   $0x1,0x39c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6eae:	48 05 00 04 00 00    	add    $0x400,%rax
    6eb4:	48 39 c8             	cmp    %rcx,%rax
    6eb7:	75 e7                	jne    6ea0 <barriered_work+0x480>
    6eb9:	e9 d0 fb ff ff       	jmp    6a8e <barriered_work+0x6e>
    6ebe:	66 90                	xchg   %ax,%ax

0000000000006ec0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6ec0:	f3 0f 1e fa          	endbr64
    6ec4:	53                   	push   %rbx
    6ec5:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6ec8:	e8 73 f2 ff ff       	call   6140 <barriered_work_ingest>
  barriered_work(data);
    6ecd:	48 89 df             	mov    %rbx,%rdi
}
    6ed0:	5b                   	pop    %rbx
  barriered_work(data);
    6ed1:	e9 4a fb ff ff       	jmp    6a20 <barriered_work>
    6ed6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006ee0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6ee0:	f3 0f 1e fa          	endbr64
}
    6ee4:	31 c0                	xor    %eax,%eax
    6ee6:	c3                   	ret
    6ee7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006ef0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6ef0:	f3 0f 1e fa          	endbr64
    6ef4:	31 c0                	xor    %eax,%eax
    6ef6:	c3                   	ret
    6ef7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006f00 <after>:
int after(struct timespec left, struct timespec right) {
    6f00:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6f04:	31 c0                	xor    %eax,%eax
    6f06:	48 39 d7             	cmp    %rdx,%rdi
    6f09:	7e 08                	jle    6f13 <after+0x13>
    6f0b:	31 c0                	xor    %eax,%eax
    6f0d:	48 39 ce             	cmp    %rcx,%rsi
    6f10:	0f 9f c0             	setg   %al
}
    6f13:	c3                   	ret
    6f14:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6f1f:	90                   	nop

0000000000006f20 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6f20:	f3 0f 1e fa          	endbr64
    6f24:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6f29:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    6f2e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f30:	48 39 d7             	cmp    %rdx,%rdi
    6f33:	7f 18                	jg     6f4d <within+0x2d>
    6f35:	4d 39 d8             	cmp    %r11,%r8
    6f38:	0f 9e c2             	setle  %dl
    6f3b:	48 39 ce             	cmp    %rcx,%rsi
    6f3e:	0f 9e c0             	setle  %al
    6f41:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6f43:	31 c0                	xor    %eax,%eax
    6f45:	4d 39 d1             	cmp    %r10,%r9
    6f48:	0f 9e c0             	setle  %al
    6f4b:	21 d0                	and    %edx,%eax
}
    6f4d:	c3                   	ret
    6f4e:	66 90                	xchg   %ax,%ax

0000000000006f50 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6f50:	f3 0f 1e fa          	endbr64
    6f54:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6f59:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6f5e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6f63:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6f68:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6f6d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6f72:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6f77:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6f7c:	48 39 fe             	cmp    %rdi,%rsi
    6f7f:	7d 2f                	jge    6fb0 <overlap+0x60>
    6f81:	48 39 ca             	cmp    %rcx,%rdx
    6f84:	7d 62                	jge    6fe8 <overlap+0x98>
    6f86:	4d 39 da             	cmp    %r11,%r10
    6f89:	7d 0e                	jge    6f99 <overlap+0x49>
    return 1;
    6f8b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6f90:	4d 39 c1             	cmp    %r8,%r9
    6f93:	0f 8c 7f 00 00 00    	jl     7018 <overlap+0xc8>
  return 0;
    6f99:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f9b:	4d 39 c1             	cmp    %r8,%r9
    6f9e:	7f 4c                	jg     6fec <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6fa0:	31 c0                	xor    %eax,%eax
    6fa2:	4d 39 da             	cmp    %r11,%r10
    6fa5:	0f 9e c0             	setle  %al
    6fa8:	c3                   	ret
    6fa9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6fb0:	7e 4e                	jle    7000 <overlap+0xb0>
    6fb2:	48 39 ca             	cmp    %rcx,%rdx
    6fb5:	7f 39                	jg     6ff0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6fb7:	75 31                	jne    6fea <overlap+0x9a>
    6fb9:	4d 39 c1             	cmp    %r8,%r9
    6fbc:	7c 2c                	jl     6fea <overlap+0x9a>
    return 1;
    6fbe:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6fc3:	4d 39 da             	cmp    %r11,%r10
    6fc6:	7d 24                	jge    6fec <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6fc8:	48 39 ca             	cmp    %rcx,%rdx
    6fcb:	0f 94 c2             	sete   %dl
    6fce:	48 39 fe             	cmp    %rdi,%rsi
    6fd1:	0f 94 c0             	sete   %al
    6fd4:	21 c2                	and    %eax,%edx
    6fd6:	31 c0                	xor    %eax,%eax
    6fd8:	4d 39 c1             	cmp    %r8,%r9
    6fdb:	0f 94 c0             	sete   %al
    6fde:	21 d0                	and    %edx,%eax
    6fe0:	c3                   	ret
    6fe1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6fe8:	74 af                	je     6f99 <overlap+0x49>
  return 0;
    6fea:	31 c0                	xor    %eax,%eax
}
    6fec:	c3                   	ret
    6fed:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6ff0:	4d 39 da             	cmp    %r11,%r10
    6ff3:	7e c4                	jle    6fb9 <overlap+0x69>
    return 1;
    6ff5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6ffa:	4d 39 c1             	cmp    %r8,%r9
    6ffd:	7e ba                	jle    6fb9 <overlap+0x69>
    6fff:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7000:	48 39 ca             	cmp    %rcx,%rdx
    7003:	7c 94                	jl     6f99 <overlap+0x49>
    7005:	4d 39 c1             	cmp    %r8,%r9
    7008:	7d b4                	jge    6fbe <overlap+0x6e>
    700a:	48 39 ca             	cmp    %rcx,%rdx
    700d:	74 91                	je     6fa0 <overlap+0x50>
    700f:	eb d9                	jmp    6fea <overlap+0x9a>
    7011:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7018:	c3                   	ret
    7019:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007020 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    7020:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    7024:	85 f6                	test   %esi,%esi
    7026:	0f 8e 44 03 00 00    	jle    7370 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    702c:	41 57                	push   %r15
    702e:	41 89 f7             	mov    %esi,%r15d
    7031:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    7033:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    7036:	41 55                	push   %r13
    7038:	41 54                	push   %r12
    703a:	55                   	push   %rbp
    703b:	53                   	push   %rbx
    703c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    7040:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    7044:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    7049:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    704e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    7051:	45 39 e6             	cmp    %r12d,%r14d
    7054:	0f 84 4e 02 00 00    	je     72a8 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    705a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    705f:	8b 50 08             	mov    0x8(%rax),%edx
    7062:	85 d2                	test   %edx,%edx
    7064:	0f 8e 3e 02 00 00    	jle    72a8 <verify+0x288>
    706a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    706f:	31 c9                	xor    %ecx,%ecx
    7071:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    7076:	31 c0                	xor    %eax,%eax
    7078:	44 89 f2             	mov    %r14d,%edx
    707b:	bf 01 00 00 00       	mov    $0x1,%edi
    7080:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    7085:	48 8d 35 ca 11 00 00 	lea    0x11ca(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    708c:	e8 1f b4 ff ff       	call   24b0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    7091:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7096:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    709b:	8b 40 08             	mov    0x8(%rax),%eax
    709e:	85 c0                	test   %eax,%eax
    70a0:	0f 8e e6 01 00 00    	jle    728c <verify+0x26c>
    70a6:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    70a9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    70ae:	31 db                	xor    %ebx,%ebx
    70b0:	48 c1 e0 09          	shl    $0x9,%rax
    70b4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    70b9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    70be:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    70c3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    70c8:	4c 8b 20             	mov    (%rax),%r12
    70cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    70d0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    70d5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    70da:	49 89 de             	mov    %rbx,%r14
    70dd:	48 8d 35 87 11 00 00 	lea    0x1187(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    70e4:	49 c1 e6 09          	shl    $0x9,%r14
    70e8:	bf 01 00 00 00       	mov    $0x1,%edi
    70ed:	48 8b 45 00          	mov    0x0(%rbp),%rax
    70f1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    70f9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    70fe:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    7106:	31 c0                	xor    %eax,%eax
    7108:	e8 a3 b3 ff ff       	call   24b0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    710d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7112:	4c 8b 20             	mov    (%rax),%r12
    7115:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    711e:	0f 8e 47 01 00 00    	jle    726b <verify+0x24b>
    7124:	4c 03 75 00          	add    0x0(%rbp),%r14
    7128:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    712d:	ba 01 00 00 00       	mov    $0x1,%edx
    7132:	4d 89 f5             	mov    %r14,%r13
    7135:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    713c:	4d 85 f6             	test   %r14,%r14
    713f:	0f 8e 21 01 00 00    	jle    7266 <verify+0x246>
    7145:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    7148:	48 89 d5             	mov    %rdx,%rbp
    714b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7150:	31 db                	xor    %ebx,%ebx
    7152:	4d 89 f2             	mov    %r14,%r10
    7155:	48 c1 e5 05          	shl    $0x5,%rbp
    7159:	48 83 ed 20          	sub    $0x20,%rbp
    715d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    7161:	49 89 ee             	mov    %rbp,%r14
    7164:	48 89 dd             	mov    %rbx,%rbp
    7167:	48 89 d3             	mov    %rdx,%rbx
    716a:	eb 31                	jmp    719d <verify+0x17d>
    716c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    7170:	4c 39 c2             	cmp    %r8,%rdx
    7173:	0f 8d 57 01 00 00    	jge    72d0 <verify+0x2b0>
    7179:	4c 39 df             	cmp    %r11,%rdi
    717c:	7e 05                	jle    7183 <verify+0x163>
    717e:	49 39 c1             	cmp    %rax,%r9
    7181:	7c 75                	jl     71f8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7183:	4c 39 df             	cmp    %r11,%rdi
    7186:	0f 8d ab 01 00 00    	jge    7337 <verify+0x317>
    718c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7190:	48 83 c5 01          	add    $0x1,%rbp
    7194:	49 39 ea             	cmp    %rbp,%r10
    7197:	0f 8e a9 00 00 00    	jle    7246 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    719d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    71a4:	48 89 e8             	mov    %rbp,%rax
    71a7:	48 c1 e0 05          	shl    $0x5,%rax
    71ab:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    71b2:	4c 01 f2             	add    %r14,%rdx
    71b5:	48 8b 08             	mov    (%rax),%rcx
    71b8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    71bc:	48 8b 32             	mov    (%rdx),%rsi
    71bf:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    71c3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    71c7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    71cb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    71cf:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    71d3:	48 39 f1             	cmp    %rsi,%rcx
    71d6:	7c 98                	jl     7170 <verify+0x150>
    71d8:	0f 8e 42 01 00 00    	jle    7320 <verify+0x300>
    71de:	4c 39 c2             	cmp    %r8,%rdx
    71e1:	0f 8f f9 00 00 00    	jg     72e0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71e7:	75 a7                	jne    7190 <verify+0x170>
    71e9:	4c 39 df             	cmp    %r11,%rdi
    71ec:	7f a2                	jg     7190 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    71ee:	49 39 c1             	cmp    %rax,%r9
    71f1:	7c 9d                	jl     7190 <verify+0x170>
    71f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    71f8:	49 89 c1             	mov    %rax,%r9
    71fb:	48 89 f9             	mov    %rdi,%rcx
    71fe:	48 89 f2             	mov    %rsi,%rdx
    7201:	bf 01 00 00 00       	mov    $0x1,%edi
    7206:	48 8d 35 63 14 00 00 	lea    0x1463(%rip),%rsi        # 8670 <_IO_stdin_used+0x670>
    720d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    720f:	48 83 c5 01          	add    $0x1,%rbp
    7213:	e8 98 b2 ff ff       	call   24b0 <__printf_chk@plt>
    7218:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    721d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    7222:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7225:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    722a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7231:	4c 8b 20             	mov    (%rax),%r12
    7234:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7239:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    723d:	49 39 ea             	cmp    %rbp,%r10
    7240:	0f 8f 57 ff ff ff    	jg     719d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7246:	48 89 da             	mov    %rbx,%rdx
    7249:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7250:	7d 14                	jge    7266 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7252:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7259:	48 83 c2 01          	add    $0x1,%rdx
    725d:	4d 85 f6             	test   %r14,%r14
    7260:	0f 8f e2 fe ff ff    	jg     7148 <verify+0x128>
    7266:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    726b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7270:	48 83 c3 01          	add    $0x1,%rbx
    7274:	39 58 08             	cmp    %ebx,0x8(%rax)
    7277:	0f 8f 53 fe ff ff    	jg     70d0 <verify+0xb0>
    727d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    7282:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    7287:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    728c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7291:	48 83 c1 01          	add    $0x1,%rcx
    7295:	39 48 08             	cmp    %ecx,0x8(%rax)
    7298:	0f 8f d8 fd ff ff    	jg     7076 <verify+0x56>
    729e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    72a3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    72a8:	48 81 44 24 10 e0 00 00 00 	addq   $0xe0,0x10(%rsp)
    72b1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    72b6:	41 39 c7             	cmp    %eax,%r15d
    72b9:	0f 84 86 00 00 00    	je     7345 <verify+0x325>
    72bf:	41 89 c4             	mov    %eax,%r12d
    72c2:	e9 8a fd ff ff       	jmp    7051 <verify+0x31>
    72c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    72d0:	0f 85 ba fe ff ff    	jne    7190 <verify+0x170>
    72d6:	e9 a8 fe ff ff       	jmp    7183 <verify+0x163>
    72db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    72e0:	49 39 c1             	cmp    %rax,%r9
    72e3:	7e 09                	jle    72ee <verify+0x2ce>
    72e5:	4c 39 df             	cmp    %r11,%rdi
    72e8:	0f 8c 0a ff ff ff    	jl     71f8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    72ee:	4c 39 df             	cmp    %r11,%rdi
    72f1:	0f 8f 99 fe ff ff    	jg     7190 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    72f7:	49 39 c1             	cmp    %rax,%r9
    72fa:	0f 8d f8 fe ff ff    	jge    71f8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7300:	48 39 f1             	cmp    %rsi,%rcx
    7303:	0f 85 87 fe ff ff    	jne    7190 <verify+0x170>
    7309:	4c 39 c2             	cmp    %r8,%rdx
    730c:	0f 85 7e fe ff ff    	jne    7190 <verify+0x170>
    7312:	4c 39 df             	cmp    %r11,%rdi
    7315:	0f 84 dd fe ff ff    	je     71f8 <verify+0x1d8>
    731b:	e9 70 fe ff ff       	jmp    7190 <verify+0x170>
    7320:	4c 39 c2             	cmp    %r8,%rdx
    7323:	0f 8c 5a fe ff ff    	jl     7183 <verify+0x163>
    7329:	4c 39 df             	cmp    %r11,%rdi
    732c:	7e c9                	jle    72f7 <verify+0x2d7>
    732e:	4c 39 c2             	cmp    %r8,%rdx
    7331:	0f 85 59 fe ff ff    	jne    7190 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7337:	49 39 c1             	cmp    %rax,%r9
    733a:	0f 8f 50 fe ff ff    	jg     7190 <verify+0x170>
    7340:	e9 b3 fe ff ff       	jmp    71f8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    7345:	48 81 44 24 18 e0 00 00 00 	addq   $0xe0,0x18(%rsp)
    734e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7352:	45 39 e6             	cmp    %r12d,%r14d
    7355:	74 08                	je     735f <verify+0x33f>
    7357:	41 89 c6             	mov    %eax,%r14d
    735a:	e9 ea fc ff ff       	jmp    7049 <verify+0x29>
}
    735f:	48 83 c4 58          	add    $0x58,%rsp
    7363:	31 c0                	xor    %eax,%eax
    7365:	5b                   	pop    %rbx
    7366:	5d                   	pop    %rbp
    7367:	41 5c                	pop    %r12
    7369:	41 5d                	pop    %r13
    736b:	41 5e                	pop    %r14
    736d:	41 5f                	pop    %r15
    736f:	c3                   	ret
    7370:	31 c0                	xor    %eax,%eax
    7372:	c3                   	ret

Disassembly of section .fini:

0000000000007374 <_fini>:
    7374:	f3 0f 1e fa          	endbr64
    7378:	48 83 ec 08          	sub    $0x8,%rsp
    737c:	48 83 c4 08          	add    $0x8,%rsp
    7380:	c3                   	ret
