
multibarrier-evented4-fswap:     file format elf64-x86-64


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
    282d:	be e0 00 00 00       	mov    $0xe0,%esi
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
    2914:	48 89 c5             	mov    %rax,%rbp
    2917:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
    291e:	49 89 c6             	mov    %rax,%r14
    2921:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    2928:	be 00 01 00 00       	mov    $0x100,%esi
    292d:	bf 01 00 00 00       	mov    $0x1,%edi
    2932:	49 83 c6 10          	add    $0x10,%r14
    2936:	e8 c5 fa ff ff       	call   2400 <calloc@plt>
    293b:	be 20 00 00 00       	mov    $0x20,%esi
    2940:	bf 64 00 00 00       	mov    $0x64,%edi
    2945:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    2949:	49 89 c4             	mov    %rax,%r12
    294c:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    2956:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
    2960:	e8 9b fa ff ff       	call   2400 <calloc@plt>
    2965:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
    296d:	4c 39 f3             	cmp    %r14,%rbx
    2970:	75 af                	jne    2921 <main+0x2b1>
    2972:	48 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%rsi
    297a:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    297f:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    2987:	45 31 f6             	xor    %r14d,%r14d
    298a:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
    2992:	45 31 e4             	xor    %r12d,%r12d
    2995:	45 89 f7             	mov    %r14d,%r15d
    2998:	48 89 b4 24 90 00 00 00 	mov    %rsi,0x90(%rsp)
    29a0:	48 89 9c 24 a8 00 00 00 	mov    %rbx,0xa8(%rsp)
    29a8:	c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rsp)
    29b3:	48 63 84 24 80 00 00 00 	movslq 0x80(%rsp),%rax
    29bb:	44 89 bc 24 84 00 00 00 	mov    %r15d,0x84(%rsp)
    29c3:	49 89 d9             	mov    %rbx,%r9
    29c6:	48 89 9c 24 e0 00 00 00 	mov    %rbx,0xe0(%rsp)
    29ce:	48 c1 e0 04          	shl    $0x4,%rax
    29d2:	48 89 b4 24 c8 00 00 00 	mov    %rsi,0xc8(%rsp)
    29da:	48 01 e8             	add    %rbp,%rax
    29dd:	48 89 ac 24 e8 00 00 00 	mov    %rbp,0xe8(%rsp)
    29e5:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    29ea:	43 8d 04 3f          	lea    (%r15,%r15,1),%eax
    29ee:	8d 78 01             	lea    0x1(%rax),%edi
    29f1:	83 c0 03             	add    $0x3,%eax
    29f4:	89 7c 24 20          	mov    %edi,0x20(%rsp)
    29f8:	89 84 24 9c 00 00 00 	mov    %eax,0x9c(%rsp)
    29ff:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
    2a04:	8b 94 24 84 00 00 00 	mov    0x84(%rsp),%edx
    2a0b:	48 8d 35 0e 5d 00 00 	lea    0x5d0e(%rip),%rsi        # 8720 <_IO_stdin_used+0x720>
    2a12:	31 c0                	xor    %eax,%eax
    2a14:	bf 01 00 00 00       	mov    $0x1,%edi
    2a19:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2a1e:	45 8d 7e ff          	lea    -0x1(%r14),%r15d
    2a22:	44 89 f9             	mov    %r15d,%ecx
    2a25:	e8 86 fa ff ff       	call   24b0 <__printf_chk@plt>
    2a2a:	be 08 00 00 00       	mov    $0x8,%esi
    2a2f:	bf 02 00 00 00       	mov    $0x2,%edi
    2a34:	e8 c7 f9 ff ff       	call   2400 <calloc@plt>
    2a39:	be 80 00 00 00       	mov    $0x80,%esi
    2a3e:	bf 01 00 00 00       	mov    $0x1,%edi
    2a43:	48 89 c3             	mov    %rax,%rbx
    2a46:	e8 b5 f9 ff ff       	call   2400 <calloc@plt>
    2a4b:	45 89 f8             	mov    %r15d,%r8d
    2a4e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2a53:	41 83 e0 01          	and    $0x1,%r8d
    2a57:	48 89 c5             	mov    %rax,%rbp
    2a5a:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2a5f:	0f 84 59 11 00 00    	je     3bbe <main+0x154e>
    2a65:	45 89 f5             	mov    %r14d,%r13d
    2a68:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    2a6d:	41 8d 55 fe          	lea    -0x2(%r13),%edx
    2a71:	48 8d 04 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rax
    2a79:	49 89 d6             	mov    %rdx,%r14
    2a7c:	48 29 d0             	sub    %rdx,%rax
    2a7f:	4c 89 ca             	mov    %r9,%rdx
    2a82:	48 c1 e0 05          	shl    $0x5,%rax
    2a86:	48 01 f0             	add    %rsi,%rax
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
    2af6:	0f 87 f1 10 00 00    	ja     3bed <main+0x157d>
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
    2c47:	be 80 01 00 00       	mov    $0x180,%esi
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
    2cb4:	49 81 c5 80 01 00 00 	add    $0x180,%r13
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
    2d0a:	be 80 03 00 00       	mov    $0x380,%esi
    2d0f:	bf 03 00 00 00       	mov    $0x3,%edi
    2d14:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2d19:	e8 e2 f6 ff ff       	call   2400 <calloc@plt>
    2d1e:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2d22:	44 89 f2             	mov    %r14d,%edx
    2d25:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
    2d30:	49 89 c1             	mov    %rax,%r9
    2d33:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
    2d39:	48 8d 35 60 5a 00 00 	lea    0x5a60(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
    2d40:	bf 01 00 00 00       	mov    $0x1,%edi
    2d45:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
    2d4f:	89 98 1c 03 00 00    	mov    %ebx,0x31c(%rax)
    2d55:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
    2d5c:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    2d61:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
    2d68:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2d6f:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    2d76:	8b 44 24 70          	mov    0x70(%rsp),%eax
    2d7a:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
    2d81:	41 83 c4 02          	add    $0x2,%r12d
    2d85:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
    2d90:	89 c1                	mov    %eax,%ecx
    2d92:	41 89 99 9c 06 00 00 	mov    %ebx,0x69c(%r9)
    2d99:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
    2da0:	45 89 b1 a4 06 00 00 	mov    %r14d,0x6a4(%r9)
    2da7:	4d 89 4d 00          	mov    %r9,0x0(%r13)
    2dab:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
    2db6:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
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
    2e04:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
    2e0b:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
    2e13:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
    2e1b:	e9 90 fe ff ff       	jmp    2cb0 <main+0x640>
    2e20:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    2e24:	49 89 c5             	mov    %rax,%r13
    2e27:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
    2e2c:	eb 17                	jmp    2e45 <main+0x7d5>
    2e2e:	66 90                	xchg   %ax,%ax
    2e30:	41 83 c6 01          	add    $0x1,%r14d
    2e34:	49 81 c5 80 01 00 00 	add    $0x180,%r13
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
    2e8a:	be 80 03 00 00       	mov    $0x380,%esi
    2e8f:	bf 03 00 00 00       	mov    $0x3,%edi
    2e94:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    2e99:	e8 62 f5 ff ff       	call   2400 <calloc@plt>
    2e9e:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2ea2:	44 89 f2             	mov    %r14d,%edx
    2ea5:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
    2eb0:	49 89 c1             	mov    %rax,%r9
    2eb3:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
    2eb9:	48 8d 35 e0 58 00 00 	lea    0x58e0(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
    2ec0:	bf 01 00 00 00       	mov    $0x1,%edi
    2ec5:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
    2ecf:	89 98 1c 03 00 00    	mov    %ebx,0x31c(%rax)
    2ed5:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
    2edc:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    2ee1:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
    2ee8:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2eef:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    2ef6:	8b 84 24 98 00 00 00 	mov    0x98(%rsp),%eax
    2efd:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
    2f04:	41 83 c4 02          	add    $0x2,%r12d
    2f08:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
    2f13:	89 c1                	mov    %eax,%ecx
    2f15:	41 89 99 9c 06 00 00 	mov    %ebx,0x69c(%r9)
    2f1c:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
    2f23:	45 89 b1 a4 06 00 00 	mov    %r14d,0x6a4(%r9)
    2f2a:	4d 89 4d 00          	mov    %r9,0x0(%r13)
    2f2e:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
    2f39:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
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
    2f87:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
    2f8e:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
    2f96:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
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
    3013:	be 80 03 00 00       	mov    $0x380,%esi
    3018:	bf 03 00 00 00       	mov    $0x3,%edi
    301d:	48 89 c5             	mov    %rax,%rbp
    3020:	e8 db f3 ff ff       	call   2400 <calloc@plt>
    3025:	be 80 03 00 00       	mov    $0x380,%esi
    302a:	bf 03 00 00 00       	mov    $0x3,%edi
    302f:	49 89 c6             	mov    %rax,%r14
    3032:	e8 c9 f3 ff ff       	call   2400 <calloc@plt>
    3037:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
    303c:	41 8d 74 24 01       	lea    0x1(%r12),%esi
    3041:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    3046:	66 0f 6f 35 72 5c 00 00 	movdqa 0x5c72(%rip),%xmm6        # 8cc0 <_IO_stdin_used+0xcc0>
    304e:	4d 89 75 00          	mov    %r14,0x0(%r13)
    3052:	41 89 b6 a8 06 00 00 	mov    %esi,0x6a8(%r14)
    3059:	49 8d b6 80 03 00 00 	lea    0x380(%r14),%rsi
    3060:	45 89 a6 28 03 00 00 	mov    %r12d,0x328(%r14)
    3067:	41 83 c4 02          	add    $0x2,%r12d
    306b:	41 c7 86 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r14)
    3076:	45 89 be 1c 03 00 00 	mov    %r15d,0x31c(%r14)
    307d:	45 89 86 20 03 00 00 	mov    %r8d,0x320(%r14)
    3084:	41 89 9e 24 03 00 00 	mov    %ebx,0x324(%r14)
    308b:	41 c7 86 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r14)
    3096:	45 89 be 9c 06 00 00 	mov    %r15d,0x69c(%r14)
    309d:	45 89 86 a0 06 00 00 	mov    %r8d,0x6a0(%r14)
    30a4:	41 89 9e a4 06 00 00 	mov    %ebx,0x6a4(%r14)
    30ab:	4d 89 b5 a0 00 00 00 	mov    %r14,0xa0(%r13)
    30b2:	49 89 b5 80 00 00 00 	mov    %rsi,0x80(%r13)
    30b9:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
    30c4:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
    30cf:	41 c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r14)
    30da:	41 c7 86 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r14)
    30e5:	49 89 b5 a8 00 00 00 	mov    %rsi,0xa8(%r13)
    30ec:	41 c7 85 b0 00 00 00 02 00 00 00 	movl   $0x2,0xb0(%r13)
    30f7:	4c 89 30             	mov    %r14,(%rax)
    30fa:	48 89 70 08          	mov    %rsi,0x8(%rax)
    30fe:	49 89 85 98 00 00 00 	mov    %rax,0x98(%r13)
    3105:	41 c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r14)
    3110:	41 c7 86 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r14)
    311b:	49 89 16             	mov    %rdx,(%r14)
    311e:	49 89 ae 80 03 00 00 	mov    %rbp,0x380(%r14)
    3125:	41 c7 86 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r14)
    3130:	41 c7 86 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r14)
    313b:	41 0f 29 b6 80 00 00 00 	movaps %xmm6,0x80(%r14)
    3143:	41 0f 29 b6 00 04 00 00 	movaps %xmm6,0x400(%r14)
    314b:	83 c3 01             	add    $0x1,%ebx
    314e:	49 81 c5 80 01 00 00 	add    $0x180,%r13
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
    31ed:	44 89 ba 94 01 00 00 	mov    %r15d,0x194(%rdx)
    31f4:	89 82 98 01 00 00    	mov    %eax,0x198(%rdx)
    31fa:	83 c0 01             	add    $0x1,%eax
    31fd:	89 44 24 38          	mov    %eax,0x38(%rsp)
    3201:	8d 45 01             	lea    0x1(%rbp),%eax
    3204:	83 e0 01             	and    $0x1,%eax
    3207:	c7 02 41 00 00 00    	movl   $0x41,(%rdx)
    320d:	89 82 90 01 00 00    	mov    %eax,0x190(%rdx)
    3213:	4c 89 92 88 01 00 00 	mov    %r10,0x188(%rdx)
    321a:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
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
    329a:	c7 82 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rdx)
    32a4:	4c 89 aa 44 01 00 00 	mov    %r13,0x144(%rdx)
    32ab:	0f 11 82 34 01 00 00 	movups %xmm0,0x134(%rdx)
    32b2:	83 fd 01             	cmp    $0x1,%ebp
    32b5:	0f 84 31 02 00 00    	je     34ec <main+0xe7c>
    32bb:	85 ed                	test   %ebp,%ebp
    32bd:	0f 84 11 02 00 00    	je     34d4 <main+0xe64>
    32c3:	4c 8b 4c 24 50       	mov    0x50(%rsp),%r9
    32c8:	48 8d 05 81 38 00 00 	lea    0x3881(%rip),%rax        # 6b50 <barriered_work>
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
    3317:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    331e:	49 89 81 70 ff ff ff 	mov    %rax,-0x90(%r9)
    3325:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    332a:	83 84 24 80 00 00 00 01 	addl   $0x1,0x80(%rsp)
    3332:	48 8b 00             	mov    (%rax),%rax
    3335:	48 89 5c 24 68       	mov    %rbx,0x68(%rsp)
    333a:	41 c7 86 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r14)
    3345:	49 89 86 28 05 00 00 	mov    %rax,0x528(%r14)
    334c:	41 c7 86 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r14)
    3357:	41 c7 86 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r14)
    3362:	41 8b 81 24 ff ff ff 	mov    -0xdc(%r9),%eax
    3369:	41 0f 11 be 18 05 00 00 	movups %xmm7,0x518(%r14)
    3371:	41 89 86 30 05 00 00 	mov    %eax,0x530(%r14)
    3378:	8b 44 24 20          	mov    0x20(%rsp),%eax
    337c:	41 c7 86 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r14)
    3387:	4d 89 ae 44 05 00 00 	mov    %r13,0x544(%r14)
    338e:	39 84 24 9c 00 00 00 	cmp    %eax,0x9c(%rsp)
    3395:	0f 85 64 f6 ff ff    	jne    29ff <main+0x38f>
    339b:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
    33a3:	48 8b 9c 24 e0 00 00 00 	mov    0xe0(%rsp),%rbx
    33ab:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    33b3:	48 8b ac 24 e8 00 00 00 	mov    0xe8(%rsp),%rbp
    33bb:	41 83 c7 01          	add    $0x1,%r15d
    33bf:	48 81 c3 c0 01 00 00 	add    $0x1c0,%rbx
    33c6:	48 83 c6 18          	add    $0x18,%rsi
    33ca:	41 83 ff 03          	cmp    $0x3,%r15d
    33ce:	0f 85 df f5 ff ff    	jne    29b3 <main+0x343>
    33d4:	be 08 00 00 00       	mov    $0x8,%esi
    33d9:	bf 00 04 00 00       	mov    $0x400,%edi
    33de:	45 31 e4             	xor    %r12d,%r12d
    33e1:	e8 1a f0 ff ff       	call   2400 <calloc@plt>
    33e6:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    33eb:	48 89 c5             	mov    %rax,%rbp
    33ee:	31 c0                	xor    %eax,%eax
    33f0:	49 89 d1             	mov    %rdx,%r9
    33f3:	31 db                	xor    %ebx,%ebx
    33f5:	45 8b 51 40          	mov    0x40(%r9),%r10d
    33f9:	45 85 d2             	test   %r10d,%r10d
    33fc:	0f 8e af 00 00 00    	jle    34b1 <main+0xe41>
    3402:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3406:	4d 63 c2             	movslq %r10d,%r8
    3409:	49 63 cc             	movslq %r12d,%rcx
    340c:	49 c1 e0 09          	shl    $0x9,%r8
    3410:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    3415:	49 01 f8             	add    %rdi,%r8
    3418:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    3420:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
    3427:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    342e:	48 83 c6 60          	add    $0x60,%rsi
    3432:	f3 0f 7e a1 80 01 00 00 	movq   0x180(%rcx),%xmm4
    343a:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    343e:	f3 0f 7e 99 00 03 00 00 	movq   0x300(%rcx),%xmm3
    3446:	f3 0f 7e 91 80 04 00 00 	movq   0x480(%rcx),%xmm2
    344e:	f3 0f 7e 89 00 06 00 00 	movq   0x600(%rcx),%xmm1
    3456:	0f 16 a1 00 02 00 00 	movhps 0x200(%rcx),%xmm4
    345d:	f3 0f 7e 81 80 07 00 00 	movq   0x780(%rcx),%xmm0
    3465:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    346c:	0f 16 99 80 03 00 00 	movhps 0x380(%rcx),%xmm3
    3473:	0f 16 91 00 05 00 00 	movhps 0x500(%rcx),%xmm2
    347a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    347e:	0f 16 89 80 06 00 00 	movhps 0x680(%rcx),%xmm1
    3485:	0f 16 81 00 08 00 00 	movhps 0x800(%rcx),%xmm0
    348c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3490:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3494:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3498:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    349c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    34a0:	49 39 f8             	cmp    %rdi,%r8
    34a3:	0f 85 77 ff ff ff    	jne    3420 <main+0xdb0>
    34a9:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    34ad:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    34b1:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    34b8:	85 db                	test   %ebx,%ebx
    34ba:	75 3e                	jne    34fa <main+0xe8a>
    34bc:	bb 01 00 00 00       	mov    $0x1,%ebx
    34c1:	e9 2f ff ff ff       	jmp    33f5 <main+0xd85>
    34c6:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    34ca:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    34cf:	e9 db fa ff ff       	jmp    2faf <main+0x93f>
    34d4:	48 8d 05 15 3b 00 00 	lea    0x3b15(%rip),%rax        # 6ff0 <barriered_work_ingest_andwork>
    34db:	bd 01 00 00 00       	mov    $0x1,%ebp
    34e0:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
    34e7:	e9 58 f7 ff ff       	jmp    2c44 <main+0x5d4>
    34ec:	48 8d 05 5d 36 00 00 	lea    0x365d(%rip),%rax        # 6b50 <barriered_work>
    34f3:	bd 02 00 00 00       	mov    $0x2,%ebp
    34f8:	eb e6                	jmp    34e0 <main+0xe70>
    34fa:	83 c0 02             	add    $0x2,%eax
    34fd:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    3504:	83 f8 06             	cmp    $0x6,%eax
    3507:	0f 85 e3 fe ff ff    	jne    33f0 <main+0xd80>
    350d:	48 8d 3d d6 4e 00 00 	lea    0x4ed6(%rip),%rdi        # 83ea <_IO_stdin_used+0x3ea>
    3514:	e8 17 ee ff ff       	call   2330 <puts@plt>
    3519:	48 8d 35 df 4e 00 00 	lea    0x4edf(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3520:	48 8d 3d da 4e 00 00 	lea    0x4eda(%rip),%rdi        # 8401 <_IO_stdin_used+0x401>
    3527:	e8 c4 ef ff ff       	call   24f0 <fopen@plt>
    352c:	49 89 c7             	mov    %rax,%r15
    352f:	45 85 e4             	test   %r12d,%r12d
    3532:	7e 77                	jle    35ab <main+0xf3b>
    3534:	4d 63 e4             	movslq %r12d,%r12
    3537:	4c 8d 35 a0 4e 00 00 	lea    0x4ea0(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    353e:	4c 8d 2d dd 4e 00 00 	lea    0x4edd(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    3545:	4a 8d 44 e5 00       	lea    0x0(%rbp,%r12,8),%rax
    354a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    354f:	be 01 00 00 00       	mov    $0x1,%esi
    3554:	bf fa 00 00 00       	mov    $0xfa,%edi
    3559:	48 83 c5 08          	add    $0x8,%rbp
    355d:	e8 9e ee ff ff       	call   2400 <calloc@plt>
    3562:	4c 89 f1             	mov    %r14,%rcx
    3565:	ba fa 00 00 00       	mov    $0xfa,%edx
    356a:	be 01 00 00 00       	mov    $0x1,%esi
    356f:	49 89 c4             	mov    %rax,%r12
    3572:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    3576:	4c 89 e7             	mov    %r12,%rdi
    3579:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3580:	31 c0                	xor    %eax,%eax
    3582:	e8 19 f0 ff ff       	call   25a0 <__sprintf_chk@plt>
    3587:	4c 89 e2             	mov    %r12,%rdx
    358a:	4c 89 ee             	mov    %r13,%rsi
    358d:	bf 01 00 00 00       	mov    $0x1,%edi
    3592:	31 c0                	xor    %eax,%eax
    3594:	e8 17 ef ff ff       	call   24b0 <__printf_chk@plt>
    3599:	4c 89 fe             	mov    %r15,%rsi
    359c:	4c 89 e7             	mov    %r12,%rdi
    359f:	e8 1c ee ff ff       	call   23c0 <fputs@plt>
    35a4:	48 39 6c 24 08       	cmp    %rbp,0x8(%rsp)
    35a9:	75 a4                	jne    354f <main+0xedf>
    35ab:	4c 89 ff             	mov    %r15,%rdi
    35ae:	45 31 f6             	xor    %r14d,%r14d
    35b1:	4c 8d 25 94 4e 00 00 	lea    0x4e94(%rip),%r12        # 844c <_IO_stdin_used+0x44c>
    35b8:	e8 a3 ed ff ff       	call   2360 <fclose@plt>
    35bd:	48 8d 3d 46 4e 00 00 	lea    0x4e46(%rip),%rdi        # 840a <_IO_stdin_used+0x40a>
    35c4:	4c 89 f5             	mov    %r14,%rbp
    35c7:	e8 64 ed ff ff       	call   2330 <puts@plt>
    35cc:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    35d0:	89 ea                	mov    %ebp,%edx
    35d2:	48 8d 35 4c 4e 00 00 	lea    0x4e4c(%rip),%rsi        # 8425 <_IO_stdin_used+0x425>
    35d9:	bf 01 00 00 00       	mov    $0x1,%edi
    35de:	31 c0                	xor    %eax,%eax
    35e0:	48 8d 1c ed 00 00 00 00 	lea    0x0(,%rbp,8),%rbx
    35e8:	44 8d 6c 2d 00       	lea    0x0(%rbp,%rbp,1),%r13d
    35ed:	45 31 ff             	xor    %r15d,%r15d
    35f0:	e8 bb ee ff ff       	call   24b0 <__printf_chk@plt>
    35f5:	48 29 eb             	sub    %rbp,%rbx
    35f8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    35fd:	48 c1 e3 06          	shl    $0x6,%rbx
    3601:	48 01 c3             	add    %rax,%rbx
    3604:	43 8d 0c 2f          	lea    (%r15,%r13,1),%ecx
    3608:	44 89 fa             	mov    %r15d,%edx
    360b:	48 8d 35 1d 4e 00 00 	lea    0x4e1d(%rip),%rsi        # 842f <_IO_stdin_used+0x42f>
    3612:	31 c0                	xor    %eax,%eax
    3614:	bf 01 00 00 00       	mov    $0x1,%edi
    3619:	45 31 f6             	xor    %r14d,%r14d
    361c:	e8 8f ee ff ff       	call   24b0 <__printf_chk@plt>
    3621:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
    3626:	4c 89 f1             	mov    %r14,%rcx
    3629:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    362e:	48 89 dd             	mov    %rbx,%rbp
    3631:	89 ca                	mov    %ecx,%edx
    3633:	48 8d 35 07 4e 00 00 	lea    0x4e07(%rip),%rsi        # 8441 <_IO_stdin_used+0x441>
    363a:	bf 01 00 00 00       	mov    $0x1,%edi
    363f:	31 c0                	xor    %eax,%eax
    3641:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    3646:	45 31 ed             	xor    %r13d,%r13d
    3649:	e8 62 ee ff ff       	call   24b0 <__printf_chk@plt>
    364e:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    3653:	48 c1 e3 09          	shl    $0x9,%rbx
    3657:	eb 33                	jmp    368c <main+0x101c>
    3659:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3660:	83 ff 01             	cmp    $0x1,%edi
    3663:	0f 84 ab 00 00 00    	je     3714 <main+0x10a4>
    3669:	44 8b 86 b4 00 00 00 	mov    0xb4(%rsi),%r8d
    3670:	44 89 f2             	mov    %r14d,%edx
    3673:	4c 89 e6             	mov    %r12,%rsi
    3676:	31 c0                	xor    %eax,%eax
    3678:	bf 01 00 00 00       	mov    $0x1,%edi
    367d:	49 83 c5 01          	add    $0x1,%r13
    3681:	e8 2a ee ff ff       	call   24b0 <__printf_chk@plt>
    3686:	49 83 fd 06          	cmp    $0x6,%r13
    368a:	74 52                	je     36de <main+0x106e>
    368c:	be 01 00 00 00       	mov    $0x1,%esi
    3691:	bf 64 00 00 00       	mov    $0x64,%edi
    3696:	45 89 ee             	mov    %r13d,%r14d
    3699:	e8 62 ed ff ff       	call   2400 <calloc@plt>
    369e:	4c 8b 45 38          	mov    0x38(%rbp),%r8
    36a2:	48 89 c1             	mov    %rax,%rcx
    36a5:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
    36aa:	49 8b b4 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rsi
    36b2:	48 c1 e0 07          	shl    $0x7,%rax
    36b6:	48 01 c6             	add    %rax,%rsi
    36b9:	8b be b0 00 00 00    	mov    0xb0(%rsi),%edi
    36bf:	83 ff 02             	cmp    $0x2,%edi
    36c2:	75 9c                	jne    3660 <main+0xff0>
    36c4:	48 bf 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rdi
    36ce:	48 89 39             	mov    %rdi,(%rcx)
    36d1:	49 03 84 18 70 01 00 00 	add    0x170(%r8,%rbx,1),%rax
    36d9:	48 89 c6             	mov    %rax,%rsi
    36dc:	eb 8b                	jmp    3669 <main+0xff9>
    36de:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    36e3:	48 83 c1 01          	add    $0x1,%rcx
    36e7:	48 83 f9 03          	cmp    $0x3,%rcx
    36eb:	0f 85 40 ff ff ff    	jne    3631 <main+0xfc1>
    36f1:	48 89 eb             	mov    %rbp,%rbx
    36f4:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    36f9:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    36fe:	48 81 c3 e0 00 00 00 	add    $0xe0,%rbx
    3705:	45 85 ff             	test   %r15d,%r15d
    3708:	75 27                	jne    3731 <main+0x10c1>
    370a:	44 8b 7c 24 10       	mov    0x10(%rsp),%r15d
    370f:	e9 f0 fe ff ff       	jmp    3604 <main+0xf94>
    3714:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    371a:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    3721:	49 03 84 18 70 01 00 00 	add    0x170(%r8,%rbx,1),%rax
    3729:	48 89 c6             	mov    %rax,%rsi
    372c:	e9 38 ff ff ff       	jmp    3669 <main+0xff9>
    3731:	48 83 c5 01          	add    $0x1,%rbp
    3735:	48 83 fd 03          	cmp    $0x3,%rbp
    3739:	0f 85 91 fe ff ff    	jne    35d0 <main+0xf60>
    373f:	ba 07 00 00 00       	mov    $0x7,%edx
    3744:	48 8d 35 1c 4d 00 00 	lea    0x4d1c(%rip),%rsi        # 8467 <_IO_stdin_used+0x467>
    374b:	bf 01 00 00 00       	mov    $0x1,%edi
    3750:	31 c0                	xor    %eax,%eax
    3752:	e8 59 ed ff ff       	call   24b0 <__printf_chk@plt>
    3757:	be 08 00 00 00       	mov    $0x8,%esi
    375c:	bf 02 00 00 00       	mov    $0x2,%edi
    3761:	e8 9a ec ff ff       	call   2400 <calloc@plt>
    3766:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
    376b:	be 38 00 00 00       	mov    $0x38,%esi
    3770:	bf 0a 00 00 00       	mov    $0xa,%edi
    3775:	4c 8d ad 20 06 00 00 	lea    0x620(%rbp),%r13
    377c:	48 89 68 08          	mov    %rbp,0x8(%rax)
    3780:	4c 8d a5 e0 00 00 00 	lea    0xe0(%rbp),%r12
    3787:	48 89 85 38 06 00 00 	mov    %rax,0x638(%rbp)
    378e:	4c 89 28             	mov    %r13,(%rax)
    3791:	48 8b 45 38          	mov    0x38(%rbp),%rax
    3795:	c7 85 48 06 00 00 02 00 00 00 	movl   $0x2,0x648(%rbp)
    379f:	c7 85 24 06 00 00 00 00 00 00 	movl   $0x0,0x624(%rbp)
    37a9:	c7 85 60 06 00 00 03 00 00 00 	movl   $0x3,0x660(%rbp)
    37b3:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    37bd:	48 8b 85 18 01 00 00 	mov    0x118(%rbp),%rax
    37c4:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    37ce:	e8 2d ec ff ff       	call   2400 <calloc@plt>
    37d3:	be 38 00 00 00       	mov    $0x38,%esi
    37d8:	bf 0a 00 00 00       	mov    $0xa,%edi
    37dd:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    37e2:	e8 19 ec ff ff       	call   2400 <calloc@plt>
    37e7:	be 38 00 00 00       	mov    $0x38,%esi
    37ec:	bf 0a 00 00 00       	mov    $0xa,%edi
    37f1:	49 89 c6             	mov    %rax,%r14
    37f4:	e8 07 ec ff ff       	call   2400 <calloc@plt>
    37f9:	be 38 00 00 00       	mov    $0x38,%esi
    37fe:	bf 0a 00 00 00       	mov    $0xa,%edi
    3803:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3808:	e8 f3 eb ff ff       	call   2400 <calloc@plt>
    380d:	be 08 00 00 00       	mov    $0x8,%esi
    3812:	bf 0a 00 00 00       	mov    $0xa,%edi
    3817:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    381c:	e8 df eb ff ff       	call   2400 <calloc@plt>
    3821:	be 08 00 00 00       	mov    $0x8,%esi
    3826:	bf 0a 00 00 00       	mov    $0xa,%edi
    382b:	c7 85 4c 05 00 00 00 00 00 00 	movl   $0x0,0x54c(%rbp)
    3835:	48 89 c3             	mov    %rax,%rbx
    3838:	48 8b 05 b9 54 00 00 	mov    0x54b9(%rip),%rax        # 8cf8 <_IO_stdin_used+0xcf8>
    383f:	48 89 85 80 05 00 00 	mov    %rax,0x580(%rbp)
    3846:	e8 b5 eb ff ff       	call   2400 <calloc@plt>
    384b:	48 8d 95 c0 01 00 00 	lea    0x1c0(%rbp),%rdx
    3852:	48 89 ef             	mov    %rbp,%rdi
    3855:	48 8d 8d 40 05 00 00 	lea    0x540(%rbp),%rcx
    385c:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3860:	48 8d 95 a0 02 00 00 	lea    0x2a0(%rbp),%rdx
    3867:	48 8d 35 08 4c 00 00 	lea    0x4c08(%rip),%rsi        # 8476 <_IO_stdin_used+0x476>
    386e:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3872:	48 8d 95 80 03 00 00 	lea    0x380(%rbp),%rdx
    3879:	48 89 50 20          	mov    %rdx,0x20(%rax)
    387d:	48 8d 95 60 04 00 00 	lea    0x460(%rbp),%rdx
    3884:	48 89 28             	mov    %rbp,(%rax)
    3887:	48 8d ad 00 07 00 00 	lea    0x700(%rbp),%rbp
    388e:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3892:	48 8d 97 e0 07 00 00 	lea    0x7e0(%rdi),%rdx
    3899:	48 89 48 30          	mov    %rcx,0x30(%rax)
    389d:	4c 89 68 38          	mov    %r13,0x38(%rax)
    38a1:	48 89 50 48          	mov    %rdx,0x48(%rax)
    38a5:	ba 06 00 00 00       	mov    $0x6,%edx
    38aa:	48 89 87 58 05 00 00 	mov    %rax,0x558(%rdi)
    38b1:	4c 89 60 08          	mov    %r12,0x8(%rax)
    38b5:	48 89 68 40          	mov    %rbp,0x40(%rax)
    38b9:	48 8b 05 40 54 00 00 	mov    0x5440(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
    38c0:	c7 87 70 05 00 00 06 00 00 00 	movl   $0x6,0x570(%rdi)
    38ca:	48 89 87 68 05 00 00 	mov    %rax,0x568(%rdi)
    38d1:	31 c0                	xor    %eax,%eax
    38d3:	c7 87 44 05 00 00 00 00 00 00 	movl   $0x0,0x544(%rdi)
    38dd:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
    38e2:	bf 01 00 00 00       	mov    $0x1,%edi
    38e7:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    38ec:	e8 bf eb ff ff       	call   24b0 <__printf_chk@plt>
    38f1:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    38f6:	49 8d b6 50 01 00 00 	lea    0x150(%r14),%rsi
    38fd:	45 31 f6             	xor    %r14d,%r14d
    3900:	48 8d 15 f9 0d 00 00 	lea    0xdf9(%rip),%rdx        # 4700 <timer_thread>
    3907:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    390b:	e8 c0 eb ff ff       	call   24d0 <pthread_create@plt>
    3910:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    3915:	4c 89 ee             	mov    %r13,%rsi
    3918:	48 89 d9             	mov    %rbx,%rcx
    391b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3920:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3925:	4c 89 64 24 30       	mov    %r12,0x30(%rsp)
    392a:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3930:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    3935:	45 89 d5             	mov    %r10d,%r13d
    3938:	44 89 7c 24 20       	mov    %r15d,0x20(%rsp)
    393d:	49 89 c7             	mov    %rax,%r15
    3940:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    3945:	47 8d 24 36          	lea    (%r14,%r14,1),%r12d
    3949:	48 89 cd             	mov    %rcx,%rbp
    394c:	48 89 d3             	mov    %rdx,%rbx
    394f:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
    3954:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    3959:	4c 89 7c 24 48       	mov    %r15,0x48(%rsp)
    395e:	49 89 f7             	mov    %rsi,%r15
    3961:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    3968:	44 89 e2             	mov    %r12d,%edx
    396b:	44 89 f1             	mov    %r14d,%ecx
    396e:	31 c0                	xor    %eax,%eax
    3970:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    3977:	48 8d 35 7a 4e 00 00 	lea    0x4e7a(%rip),%rsi        # 87f8 <_IO_stdin_used+0x7f8>
    397e:	bf 01 00 00 00       	mov    $0x1,%edi
    3983:	41 83 c4 01          	add    $0x1,%r12d
    3987:	e8 24 eb ff ff       	call   24b0 <__printf_chk@plt>
    398c:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3991:	48 89 d9             	mov    %rbx,%rcx
    3994:	48 89 ef             	mov    %rbp,%rdi
    3997:	48 8d 15 02 29 00 00 	lea    0x2902(%rip),%rdx        # 62a0 <barriered_thread>
    399e:	48 81 c3 e0 00 00 00 	add    $0xe0,%rbx
    39a5:	48 83 c5 08          	add    $0x8,%rbp
    39a9:	e8 22 eb ff ff       	call   24d0 <pthread_create@plt>
    39ae:	48 8b 53 d0          	mov    -0x30(%rbx),%rdx
    39b2:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
    39b6:	be 08 00 00 00       	mov    $0x8,%esi
    39bb:	e8 60 e9 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    39c0:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    39c6:	45 39 e5             	cmp    %r12d,%r13d
    39c9:	75 96                	jne    3961 <main+0x12f1>
    39cb:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    39d0:	4c 89 fe             	mov    %r15,%rsi
    39d3:	41 83 c6 01          	add    $0x1,%r14d
    39d7:	41 83 c5 02          	add    $0x2,%r13d
    39db:	4c 8b 7c 24 48       	mov    0x48(%rsp),%r15
    39e0:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    39e5:	48 83 c1 10          	add    $0x10,%rcx
    39e9:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    39f0:	49 83 c7 70          	add    $0x70,%r15
    39f4:	41 83 fe 03          	cmp    $0x3,%r14d
    39f8:	0f 85 42 ff ff ff    	jne    3940 <main+0x12d0>
    39fe:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3a03:	48 8b 05 fe 52 00 00 	mov    0x52fe(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    3a0a:	49 89 f5             	mov    %rsi,%r13
    3a0d:	bf 01 00 00 00       	mov    $0x1,%edi
    3a12:	be d8 00 00 00       	mov    $0xd8,%esi
    3a17:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    3a1c:	4c 8b 64 24 30       	mov    0x30(%rsp),%r12
    3a21:	41 c7 86 2c 06 00 00 02 00 00 00 	movl   $0x2,0x62c(%r14)
    3a2c:	44 8b 7c 24 20       	mov    0x20(%rsp),%r15d
    3a31:	49 89 86 60 06 00 00 	mov    %rax,0x660(%r14)
    3a38:	48 8b 6c 24 40       	mov    0x40(%rsp),%rbp
    3a3d:	e8 be e9 ff ff       	call   2400 <calloc@plt>
    3a42:	be 00 08 00 00       	mov    $0x800,%esi
    3a47:	31 ff                	xor    %edi,%edi
    3a49:	49 89 86 78 06 00 00 	mov    %rax,0x678(%r14)
    3a50:	e8 cb ea ff ff       	call   2520 <eventfd@plt>
    3a55:	be 08 00 00 00       	mov    $0x8,%esi
    3a5a:	bf 02 00 00 00       	mov    $0x2,%edi
    3a5f:	41 89 86 80 06 00 00 	mov    %eax,0x680(%r14)
    3a66:	e8 95 e9 ff ff       	call   2400 <calloc@plt>
    3a6b:	ba 07 00 00 00       	mov    $0x7,%edx
    3a70:	bf 01 00 00 00       	mov    $0x1,%edi
    3a75:	41 c7 86 48 06 00 00 02 00 00 00 	movl   $0x2,0x648(%r14)
    3a80:	4c 89 30             	mov    %r14,(%rax)
    3a83:	48 8d 35 0a 4a 00 00 	lea    0x4a0a(%rip),%rsi        # 8494 <_IO_stdin_used+0x494>
    3a8a:	49 89 86 38 06 00 00 	mov    %rax,0x638(%r14)
    3a91:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3a95:	31 c0                	xor    %eax,%eax
    3a97:	41 c7 86 24 06 00 00 07 00 00 00 	movl   $0x7,0x624(%r14)
    3aa2:	41 be 08 00 00 00    	mov    $0x8,%r14d
    3aa8:	e8 03 ea ff ff       	call   24b0 <__printf_chk@plt>
    3aad:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3ab2:	4c 89 e9             	mov    %r13,%rcx
    3ab5:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3ab9:	48 8d 15 f0 1f 00 00 	lea    0x1ff0(%rip),%rdx        # 5ab0 <io_thread>
    3ac0:	4c 8d 6b 40          	lea    0x40(%rbx),%r13
    3ac4:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3acb:	e8 00 ea ff ff       	call   24d0 <pthread_create@plt>
    3ad0:	ba 08 00 00 00       	mov    $0x8,%edx
    3ad5:	48 8d 35 cf 49 00 00 	lea    0x49cf(%rip),%rsi        # 84ab <_IO_stdin_used+0x4ab>
    3adc:	31 c0                	xor    %eax,%eax
    3ade:	bf 01 00 00 00       	mov    $0x1,%edi
    3ae3:	e8 c8 e9 ff ff       	call   24b0 <__printf_chk@plt>
    3ae8:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3aed:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    3af3:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3af8:	44 89 f2             	mov    %r14d,%edx
    3afb:	48 8d 35 bf 49 00 00 	lea    0x49bf(%rip),%rsi        # 84c1 <_IO_stdin_used+0x4c1>
    3b02:	bf 01 00 00 00       	mov    $0x1,%edi
    3b07:	31 c0                	xor    %eax,%eax
    3b09:	e8 a2 e9 ff ff       	call   24b0 <__printf_chk@plt>
    3b0e:	be 08 00 00 00       	mov    $0x8,%esi
    3b13:	bf 01 00 00 00       	mov    $0x1,%edi
    3b18:	48 8b 05 e9 51 00 00 	mov    0x51e9(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    3b1f:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    3b26:	48 89 45 40          	mov    %rax,0x40(%rbp)
    3b2a:	e8 d1 e8 ff ff       	call   2400 <calloc@plt>
    3b2f:	48 8b bc 24 c0 00 00 00 	mov    0xc0(%rsp),%rdi
    3b37:	be 08 00 00 00       	mov    $0x8,%esi
    3b3c:	c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbp)
    3b46:	48 89 45 50          	mov    %rax,0x50(%rbp)
    3b4a:	48 89 38             	mov    %rdi,(%rax)
    3b4d:	bf 02 00 00 00       	mov    $0x2,%edi
    3b52:	e8 a9 e8 ff ff       	call   2400 <calloc@plt>
    3b57:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    3b5c:	48 89 e9             	mov    %rbp,%rcx
    3b5f:	4c 89 ef             	mov    %r13,%rdi
    3b62:	48 89 45 18          	mov    %rax,0x18(%rbp)
    3b66:	48 8d 15 33 0a 00 00 	lea    0xa33(%rip),%rdx        # 45a0 <external_thread>
    3b6d:	49 83 c5 08          	add    $0x8,%r13
    3b71:	48 81 c5 e0 00 00 00 	add    $0xe0,%rbp
    3b78:	48 89 30             	mov    %rsi,(%rax)
    3b7b:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3b80:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3b84:	48 8b 05 5d 51 00 00 	mov    0x515d(%rip),%rax        # 8ce8 <_IO_stdin_used+0xce8>
    3b8b:	44 89 b5 24 ff ff ff 	mov    %r14d,-0xdc(%rbp)
    3b92:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
    3b99:	e8 32 e9 ff ff       	call   24d0 <pthread_create@plt>
    3b9e:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3ba4:	48 83 84 24 c0 00 00 00 10 	addq   $0x10,0xc0(%rsp)
    3bad:	41 83 fe 08          	cmp    $0x8,%r14d
    3bb1:	75 47                	jne    3bfa <main+0x158a>
    3bb3:	41 be 09 00 00 00    	mov    $0x9,%r14d
    3bb9:	e9 3a ff ff ff       	jmp    3af8 <main+0x1488>
    3bbe:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
    3bc3:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3bc8:	48 89 5c 24 48       	mov    %rbx,0x48(%rsp)
    3bcd:	45 31 c0             	xor    %r8d,%r8d
    3bd0:	4a 8d 14 ed 00 00 00 00 	lea    0x0(,%r13,8),%rdx
    3bd8:	45 89 ee             	mov    %r13d,%r14d
    3bdb:	4c 29 ea             	sub    %r13,%rdx
    3bde:	48 c1 e2 05          	shl    $0x5,%rdx
    3be2:	48 01 c2             	add    %rax,%rdx
    3be5:	4c 89 c8             	mov    %r9,%rax
    3be8:	e9 a5 ee ff ff       	jmp    2a92 <main+0x422>
    3bed:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
    3bf5:	e9 2a ef ff ff       	jmp    2b24 <main+0x4b4>
    3bfa:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3bff:	48 8d 2d d8 48 00 00 	lea    0x48d8(%rip),%rbp        # 84de <_IO_stdin_used+0x4de>
    3c06:	4c 8d 68 04          	lea    0x4(%rax),%r13
    3c0a:	4c 8d a0 c4 08 00 00 	lea    0x8c4(%rax),%r12
    3c11:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    3c15:	41 8b 55 00          	mov    0x0(%r13),%edx
    3c19:	48 89 ee             	mov    %rbp,%rsi
    3c1c:	bf 01 00 00 00       	mov    $0x1,%edi
    3c21:	31 c0                	xor    %eax,%eax
    3c23:	49 81 c5 e0 00 00 00 	add    $0xe0,%r13
    3c2a:	e8 81 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c2f:	4d 39 ec             	cmp    %r13,%r12
    3c32:	75 dd                	jne    3c11 <main+0x15a1>
    3c34:	48 8d 3d b6 48 00 00 	lea    0x48b6(%rip),%rdi        # 84f1 <_IO_stdin_used+0x4f1>
    3c3b:	45 31 ed             	xor    %r13d,%r13d
    3c3e:	4c 8d a4 24 f0 00 00 00 	lea    0xf0(%rsp),%r12
    3c46:	e8 e5 e6 ff ff       	call   2330 <puts@plt>
    3c4b:	48 8d 2d bd 48 00 00 	lea    0x48bd(%rip),%rbp        # 850f <_IO_stdin_used+0x50f>
    3c52:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    3c56:	4c 89 e6             	mov    %r12,%rsi
    3c59:	e8 02 e9 ff ff       	call   2560 <pthread_join@plt>
    3c5e:	44 89 ea             	mov    %r13d,%edx
    3c61:	48 89 ee             	mov    %rbp,%rsi
    3c64:	bf 01 00 00 00       	mov    $0x1,%edi
    3c69:	31 c0                	xor    %eax,%eax
    3c6b:	49 83 c5 01          	add    $0x1,%r13
    3c6f:	e8 3c e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c74:	49 83 fd 0a          	cmp    $0xa,%r13
    3c78:	75 d8                	jne    3c52 <main+0x15e2>
    3c7a:	be 08 00 00 00       	mov    $0x8,%esi
    3c7f:	bf 00 04 00 00       	mov    $0x400,%edi
    3c84:	31 db                	xor    %ebx,%ebx
    3c86:	e8 75 e7 ff ff       	call   2400 <calloc@plt>
    3c8b:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3c90:	48 89 c5             	mov    %rax,%rbp
    3c93:	31 c0                	xor    %eax,%eax
    3c95:	49 89 d1             	mov    %rdx,%r9
    3c98:	45 31 db             	xor    %r11d,%r11d
    3c9b:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3c9f:	45 85 d2             	test   %r10d,%r10d
    3ca2:	0f 8e a8 00 00 00    	jle    3d50 <main+0x16e0>
    3ca8:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3cac:	4d 63 c2             	movslq %r10d,%r8
    3caf:	48 63 cb             	movslq %ebx,%rcx
    3cb2:	49 c1 e0 09          	shl    $0x9,%r8
    3cb6:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    3cbb:	49 01 f8             	add    %rdi,%r8
    3cbe:	66 90                	xchg   %ax,%ax
    3cc0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
    3cc7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3cce:	48 83 c6 60          	add    $0x60,%rsi
    3cd2:	f3 0f 7e a1 80 01 00 00 	movq   0x180(%rcx),%xmm4
    3cda:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3cde:	f3 0f 7e 99 00 03 00 00 	movq   0x300(%rcx),%xmm3
    3ce6:	f3 0f 7e 91 80 04 00 00 	movq   0x480(%rcx),%xmm2
    3cee:	f3 0f 7e 89 00 06 00 00 	movq   0x600(%rcx),%xmm1
    3cf6:	0f 16 a1 00 02 00 00 	movhps 0x200(%rcx),%xmm4
    3cfd:	f3 0f 7e 81 80 07 00 00 	movq   0x780(%rcx),%xmm0
    3d05:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    3d0c:	0f 16 99 80 03 00 00 	movhps 0x380(%rcx),%xmm3
    3d13:	0f 16 91 00 05 00 00 	movhps 0x500(%rcx),%xmm2
    3d1a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3d1e:	0f 16 89 80 06 00 00 	movhps 0x680(%rcx),%xmm1
    3d25:	0f 16 81 00 08 00 00 	movhps 0x800(%rcx),%xmm0
    3d2c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3d30:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3d34:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3d38:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3d3c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    3d40:	4c 39 c7             	cmp    %r8,%rdi
    3d43:	0f 85 77 ff ff ff    	jne    3cc0 <main+0x1650>
    3d49:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3d4d:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    3d50:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    3d57:	45 85 db             	test   %r11d,%r11d
    3d5a:	75 08                	jne    3d64 <main+0x16f4>
    3d5c:	45 89 fb             	mov    %r15d,%r11d
    3d5f:	e9 37 ff ff ff       	jmp    3c9b <main+0x162b>
    3d64:	83 c0 02             	add    $0x2,%eax
    3d67:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    3d6e:	83 f8 06             	cmp    $0x6,%eax
    3d71:	0f 85 1e ff ff ff    	jne    3c95 <main+0x1625>
    3d77:	48 8d 3d a5 47 00 00 	lea    0x47a5(%rip),%rdi        # 8523 <_IO_stdin_used+0x523>
    3d7e:	e8 ad e5 ff ff       	call   2330 <puts@plt>
    3d83:	48 8d 35 75 46 00 00 	lea    0x4675(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3d8a:	48 8d 3d aa 47 00 00 	lea    0x47aa(%rip),%rdi        # 853b <_IO_stdin_used+0x53b>
    3d91:	e8 5a e7 ff ff       	call   24f0 <fopen@plt>
    3d96:	49 89 c4             	mov    %rax,%r12
    3d99:	85 db                	test   %ebx,%ebx
    3d9b:	7e 73                	jle    3e10 <main+0x17a0>
    3d9d:	48 63 db             	movslq %ebx,%rbx
    3da0:	49 89 ef             	mov    %rbp,%r15
    3da3:	4c 8d 35 34 46 00 00 	lea    0x4634(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    3daa:	48 8d 6c dd 00       	lea    0x0(%rbp,%rbx,8),%rbp
    3daf:	4c 8d 2d 6c 46 00 00 	lea    0x466c(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    3db6:	be 01 00 00 00       	mov    $0x1,%esi
    3dbb:	bf fa 00 00 00       	mov    $0xfa,%edi
    3dc0:	49 83 c7 08          	add    $0x8,%r15
    3dc4:	e8 37 e6 ff ff       	call   2400 <calloc@plt>
    3dc9:	4c 89 f1             	mov    %r14,%rcx
    3dcc:	ba fa 00 00 00       	mov    $0xfa,%edx
    3dd1:	be 01 00 00 00       	mov    $0x1,%esi
    3dd6:	48 89 c3             	mov    %rax,%rbx
    3dd9:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3ddd:	48 89 df             	mov    %rbx,%rdi
    3de0:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3de7:	31 c0                	xor    %eax,%eax
    3de9:	e8 b2 e7 ff ff       	call   25a0 <__sprintf_chk@plt>
    3dee:	48 89 da             	mov    %rbx,%rdx
    3df1:	4c 89 ee             	mov    %r13,%rsi
    3df4:	bf 01 00 00 00       	mov    $0x1,%edi
    3df9:	31 c0                	xor    %eax,%eax
    3dfb:	e8 b0 e6 ff ff       	call   24b0 <__printf_chk@plt>
    3e00:	4c 89 e6             	mov    %r12,%rsi
    3e03:	48 89 df             	mov    %rbx,%rdi
    3e06:	e8 b5 e5 ff ff       	call   23c0 <fputs@plt>
    3e0b:	49 39 ef             	cmp    %rbp,%r15
    3e0e:	75 a6                	jne    3db6 <main+0x1746>
    3e10:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
    3e1a:	4c 89 e7             	mov    %r12,%rdi
    3e1d:	31 db                	xor    %ebx,%ebx
    3e1f:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
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
    3eda:	4a 8d 04 e5 00 00 00 00 	lea    0x0(,%r12,8),%rax
    3ee2:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3ee7:	4c 29 e0             	sub    %r12,%rax
    3eea:	48 c1 e0 05          	shl    $0x5,%rax
    3eee:	48 01 f8             	add    %rdi,%rax
    3ef1:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3ef5:	85 c9                	test   %ecx,%ecx
    3ef7:	7e 21                	jle    3f1a <main+0x18aa>
    3ef9:	48 8b 40 38          	mov    0x38(%rax),%rax
    3efd:	48 c1 e1 09          	shl    $0x9,%rcx
    3f01:	48 01 c1             	add    %rax,%rcx
    3f04:	0f 1f 40 00          	nopl   0x0(%rax)
    3f08:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3f0f:	48 05 00 02 00 00    	add    $0x200,%rax
    3f15:	48 39 c8             	cmp    %rcx,%rax
    3f18:	75 ee                	jne    3f08 <main+0x1898>
    3f1a:	48 8d 35 38 46 00 00 	lea    0x4638(%rip),%rsi        # 8559 <_IO_stdin_used+0x559>
    3f21:	bf 01 00 00 00       	mov    $0x1,%edi
    3f26:	31 c0                	xor    %eax,%eax
    3f28:	e8 83 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3f2d:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3f32:	bf 01 00 00 00       	mov    $0x1,%edi
    3f37:	48 8d 35 ea 48 00 00 	lea    0x48ea(%rip),%rsi        # 8828 <_IO_stdin_used+0x828>
    3f3e:	48 8b 08             	mov    (%rax),%rcx
    3f41:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3f4b:	48 f7 e9             	imul   %rcx
    3f4e:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3f52:	31 c0                	xor    %eax,%eax
    3f54:	48 d1 fa             	sar    %rdx
    3f57:	48 29 ca             	sub    %rcx,%rdx
    3f5a:	e8 51 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3f5f:	bf 0a 00 00 00       	mov    $0xa,%edi
    3f64:	e8 a7 e3 ff ff       	call   2310 <putchar@plt>
    3f69:	45 8b 66 40          	mov    0x40(%r14),%r12d
    3f6d:	45 85 e4             	test   %r12d,%r12d
    3f70:	0f 8e 48 01 00 00    	jle    40be <main+0x1a4e>
    3f76:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    3f7b:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    3f80:	31 d2                	xor    %edx,%edx
    3f82:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3f87:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3f8c:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    3f91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3f98:	49 8b 46 38          	mov    0x38(%r14),%rax
    3f9c:	49 89 d1             	mov    %rdx,%r9
    3f9f:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    3fa4:	41 89 d5             	mov    %edx,%r13d
    3fa7:	49 c1 e1 09          	shl    $0x9,%r9
    3fab:	45 31 e4             	xor    %r12d,%r12d
    3fae:	4c 01 c8             	add    %r9,%rax
    3fb1:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    3fb6:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
    3fbd:	48 03 88 68 01 00 00 	add    0x168(%rax),%rcx
    3fc4:	48 03 b0 78 01 00 00 	add    0x178(%rax),%rsi
    3fcb:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    3fd0:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    3fd5:	48 89 74 24 28       	mov    %rsi,0x28(%rsp)
    3fda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3fe0:	8b 54 24 08          	mov    0x8(%rsp),%edx
    3fe4:	45 89 e0             	mov    %r12d,%r8d
    3fe7:	44 89 e9             	mov    %r13d,%ecx
    3fea:	bf 01 00 00 00       	mov    $0x1,%edi
    3fef:	48 8d 35 70 45 00 00 	lea    0x4570(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    3ff6:	31 c0                	xor    %eax,%eax
    3ff8:	e8 b3 e4 ff ff       	call   24b0 <__printf_chk@plt>
    3ffd:	49 8b 56 38          	mov    0x38(%r14),%rdx
    4001:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
    4005:	45 89 e0             	mov    %r12d,%r8d
    4008:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    400d:	48 c1 e0 07          	shl    $0x7,%rax
    4011:	48 83 ec 08          	sub    $0x8,%rsp
    4015:	49 83 c4 01          	add    $0x1,%r12
    4019:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    4021:	48 8b 38             	mov    (%rax),%rdi
    4024:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    402b:	48 8b 87 10 03 00 00 	mov    0x310(%rdi),%rax
    4032:	48 8b 96 08 03 00 00 	mov    0x308(%rsi),%rdx
    4039:	48 8b b6 10 03 00 00 	mov    0x310(%rsi),%rsi
    4040:	48 8b 8f 08 03 00 00 	mov    0x308(%rdi),%rcx
    4047:	bf 01 00 00 00       	mov    $0x1,%edi
    404c:	48 01 c3             	add    %rax,%rbx
    404f:	48 01 f0             	add    %rsi,%rax
    4052:	49 01 cf             	add    %rcx,%r15
    4055:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
    4059:	48 01 f3             	add    %rsi,%rbx
    405c:	50                   	push   %rax
    405d:	49 01 d7             	add    %rdx,%r15
    4060:	8b 54 24 18          	mov    0x18(%rsp),%edx
    4064:	44 89 e9             	mov    %r13d,%ecx
    4067:	48 8d 35 da 47 00 00 	lea    0x47da(%rip),%rsi        # 8848 <_IO_stdin_used+0x848>
    406e:	31 c0                	xor    %eax,%eax
    4070:	e8 3b e4 ff ff       	call   24b0 <__printf_chk@plt>
    4075:	41 5a                	pop    %r10
    4077:	41 5b                	pop    %r11
    4079:	49 83 fc 06          	cmp    $0x6,%r12
    407d:	0f 85 5d ff ff ff    	jne    3fe0 <main+0x1970>
    4083:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    4088:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    408d:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    4092:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    4097:	48 83 c2 01          	add    $0x1,%rdx
    409b:	41 39 56 40          	cmp    %edx,0x40(%r14)
    409f:	0f 8f f3 fe ff ff    	jg     3f98 <main+0x1928>
    40a5:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    40aa:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    40af:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    40b4:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    40b9:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    40be:	45 31 ff             	xor    %r15d,%r15d
    40c1:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    40c9:	4c 8d 25 98 47 00 00 	lea    0x4798(%rip),%r12        # 8868 <_IO_stdin_used+0x868>
    40d0:	7e 5e                	jle    4130 <main+0x1ac0>
    40d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    40d8:	49 8b 86 90 00 00 00 	mov    0x90(%r14),%rax
    40df:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    40e3:	48 83 ec 08          	sub    $0x8,%rsp
    40e7:	bf 01 00 00 00       	mov    $0x1,%edi
    40ec:	49 83 c7 01          	add    $0x1,%r15
    40f0:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    40f4:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    40f8:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    40fc:	48 89 f0             	mov    %rsi,%rax
    40ff:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    4103:	4c 2b 01             	sub    (%rcx),%r8
    4106:	48 f7 e5             	mul    %rbp
    4109:	8b 49 20             	mov    0x20(%rcx),%ecx
    410c:	56                   	push   %rsi
    410d:	31 c0                	xor    %eax,%eax
    410f:	4c 89 e6             	mov    %r12,%rsi
    4112:	48 c1 ea 12          	shr    $0x12,%rdx
    4116:	49 89 d1             	mov    %rdx,%r9
    4119:	ba 02 00 00 00       	mov    $0x2,%edx
    411e:	e8 8d e3 ff ff       	call   24b0 <__printf_chk@plt>
    4123:	41 58                	pop    %r8
    4125:	41 59                	pop    %r9
    4127:	4d 39 be a0 00 00 00 	cmp    %r15,0xa0(%r14)
    412e:	7f a8                	jg     40d8 <main+0x1a68>
    4130:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    4137:	85 d2                	test   %edx,%edx
    4139:	0f 8e 02 01 00 00    	jle    4241 <main+0x1bd1>
    413f:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
    4144:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4148:	45 31 ff             	xor    %r15d,%r15d
    414b:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
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
    4247:	49 81 c6 e0 00 00 00 	add    $0xe0,%r14
    424e:	44 39 6c 24 48       	cmp    %r13d,0x48(%rsp)
    4253:	0f 85 17 fc ff ff    	jne    3e70 <main+0x1800>
    4259:	48 83 84 24 90 00 00 00 30 	addq   $0x30,0x90(%rsp)
    4262:	44 8b 44 24 48       	mov    0x48(%rsp),%r8d
    4267:	48 81 84 24 a8 00 00 00 c0 01 00 00 	addq   $0x1c0,0xa8(%rsp)
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
    45a4:	41 57                	push   %r15
    45a6:	41 56                	push   %r14
    45a8:	49 89 fe             	mov    %rdi,%r14
    45ab:	41 55                	push   %r13
    45ad:	4c 8d 2d 50 3a 00 00 	lea    0x3a50(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
    45b4:	41 54                	push   %r12
    45b6:	55                   	push   %rbp
    45b7:	53                   	push   %rbx
    45b8:	48 83 ec 48          	sub    $0x48,%rsp
    45bc:	66 0f 6f 05 0c 46 00 00 	movdqa 0x460c(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    45c4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    45cd:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    45d2:	31 c0                	xor    %eax,%eax
    45d4:	48 8d 44 24 20       	lea    0x20(%rsp),%rax
    45d9:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    45dd:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    45e2:	48 8d 44 24 10       	lea    0x10(%rsp),%rax
    45e7:	48 89 04 24          	mov    %rax,(%rsp)
    45eb:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    45f0:	75 7d                	jne    466f <external_thread+0xcf>
    45f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    45f8:	48 8b 3c 24          	mov    (%rsp),%rdi
    45fc:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    4601:	e8 9a dd ff ff       	call   23a0 <nanosleep@plt>
    4606:	41 8b be bc 00 00 00 	mov    0xbc(%r14),%edi
    460d:	85 ff                	test   %edi,%edi
    460f:	7e 57                	jle    4668 <external_thread+0xc8>
    4611:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    4615:	45 31 e4             	xor    %r12d,%r12d
    4618:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4620:	4e 8d 3c e5 00 00 00 00 	lea    0x0(,%r12,8),%r15
    4628:	31 db                	xor    %ebx,%ebx
    462a:	4f 8d 04 39          	lea    (%r9,%r15,1),%r8
    462e:	49 8b 00             	mov    (%r8),%rax
    4631:	8b 30                	mov    (%rax),%esi
    4633:	85 f6                	test   %esi,%esi
    4635:	7e 28                	jle    465f <external_thread+0xbf>
    4637:	48 8b 78 08          	mov    0x8(%rax),%rdi
    463b:	48 89 dd             	mov    %rbx,%rbp
    463e:	48 c1 e5 08          	shl    $0x8,%rbp
    4642:	48 8d 04 2f          	lea    (%rdi,%rbp,1),%rax
    4646:	8b 90 80 00 00 00    	mov    0x80(%rax),%edx
    464c:	85 d2                	test   %edx,%edx
    464e:	74 40                	je     4690 <external_thread+0xf0>
    4650:	48 83 c3 01          	add    $0x1,%rbx
    4654:	39 de                	cmp    %ebx,%esi
    4656:	7f e3                	jg     463b <external_thread+0x9b>
    4658:	41 8b be bc 00 00 00 	mov    0xbc(%r14),%edi
    465f:	49 83 c4 01          	add    $0x1,%r12
    4663:	44 39 e7             	cmp    %r12d,%edi
    4666:	7f b8                	jg     4620 <external_thread+0x80>
    4668:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    466d:	74 89                	je     45f8 <external_thread+0x58>
    466f:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4674:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    467d:	75 72                	jne    46f1 <external_thread+0x151>
    467f:	48 83 c4 48          	add    $0x48,%rsp
    4683:	31 c0                	xor    %eax,%eax
    4685:	5b                   	pop    %rbx
    4686:	5d                   	pop    %rbp
    4687:	41 5c                	pop    %r12
    4689:	41 5d                	pop    %r13
    468b:	41 5e                	pop    %r14
    468d:	41 5f                	pop    %r15
    468f:	c3                   	ret
    4690:	4c 89 28             	mov    %r13,(%rax)
    4693:	49 8b 00             	mov    (%r8),%rax
    4696:	bf 04 00 00 00       	mov    $0x4,%edi
    469b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    469f:	48 01 ea             	add    %rbp,%rdx
    46a2:	48 63 b2 94 00 00 00 	movslq 0x94(%rdx),%rsi
    46a9:	48 c1 e6 05          	shl    $0x5,%rsi
    46ad:	48 03 b2 88 00 00 00 	add    0x88(%rdx),%rsi
    46b4:	e8 97 dc ff ff       	call   2350 <clock_gettime@plt>
    46b9:	49 8b 46 50          	mov    0x50(%r14),%rax
    46bd:	4a 8b 04 38          	mov    (%rax,%r15,1),%rax
    46c1:	48 8b 40 08          	mov    0x8(%rax),%rax
    46c5:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
    46d0:	0f ae f8             	sfence
    46d3:	4d 8b 4e 50          	mov    0x50(%r14),%r9
    46d7:	48 83 c3 01          	add    $0x1,%rbx
    46db:	4f 8d 04 39          	lea    (%r9,%r15,1),%r8
    46df:	49 8b 00             	mov    (%r8),%rax
    46e2:	8b 30                	mov    (%rax),%esi
    46e4:	39 de                	cmp    %ebx,%esi
    46e6:	0f 8f 4b ff ff ff    	jg     4637 <external_thread+0x97>
    46ec:	e9 67 ff ff ff       	jmp    4658 <external_thread+0xb8>
    46f1:	e8 8a dc ff ff       	call   2380 <__stack_chk_fail@plt>
    46f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004700 <timer_thread>:
    4700:	f3 0f 1e fa          	endbr64
    4704:	41 57                	push   %r15
    4706:	48 8d 35 03 39 00 00 	lea    0x3903(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    470d:	41 56                	push   %r14
    470f:	49 89 fe             	mov    %rdi,%r14
    4712:	41 55                	push   %r13
    4714:	41 54                	push   %r12
    4716:	55                   	push   %rbp
    4717:	53                   	push   %rbx
    4718:	48 83 ec 68          	sub    $0x68,%rsp
    471c:	8b 57 04             	mov    0x4(%rdi),%edx
    471f:	bf 01 00 00 00       	mov    $0x1,%edi
    4724:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    472d:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    4732:	31 c0                	xor    %eax,%eax
    4734:	e8 77 dd ff ff       	call   24b0 <__printf_chk@plt>
    4739:	66 0f 6f 05 8f 44 00 00 	movdqa 0x448f(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4741:	ba 88 13 00 00       	mov    $0x1388,%edx
    4746:	31 c0                	xor    %eax,%eax
    4748:	48 8d 35 d3 38 00 00 	lea    0x38d3(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    474f:	bf 01 00 00 00       	mov    $0x1,%edi
    4754:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    4759:	e8 52 dd ff ff       	call   24b0 <__printf_chk@plt>
    475e:	41 8b 5e 44          	mov    0x44(%r14),%ebx
    4762:	85 db                	test   %ebx,%ebx
    4764:	0f 84 9c 00 00 00    	je     4806 <timer_thread+0x106>
    476a:	45 31 ff             	xor    %r15d,%r15d
    476d:	31 db                	xor    %ebx,%ebx
    476f:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    4774:	31 ed                	xor    %ebp,%ebp
    4776:	4c 8d 64 24 20       	lea    0x20(%rsp),%r12
    477b:	4c 89 e7             	mov    %r12,%rdi
    477e:	4c 89 ee             	mov    %r13,%rsi
    4781:	41 83 c7 01          	add    $0x1,%r15d
    4785:	e8 16 dc ff ff       	call   23a0 <nanosleep@plt>
    478a:	49 63 46 30          	movslq 0x30(%r14),%rax
    478e:	8d 7b 01             	lea    0x1(%rbx),%edi
    4791:	85 c0                	test   %eax,%eax
    4793:	7e 4a                	jle    47df <timer_thread+0xdf>
    4795:	49 8b 4e 18          	mov    0x18(%r14),%rcx
    4799:	4c 63 c3             	movslq %ebx,%r8
    479c:	49 c1 e0 09          	shl    $0x9,%r8
    47a0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    47a4:	0f 1f 40 00          	nopl   0x0(%rax)
    47a8:	48 8b 19             	mov    (%rcx),%rbx
    47ab:	89 f8                	mov    %edi,%eax
    47ad:	48 83 c1 08          	add    $0x8,%rcx
    47b1:	99                   	cltd
    47b2:	f7 7b 40             	idivl  0x40(%rbx)
    47b5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    47b9:	83 ea 01             	sub    $0x1,%edx
    47bc:	48 63 d2             	movslq %edx,%rdx
    47bf:	48 c1 e2 09          	shl    $0x9,%rdx
    47c3:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    47ce:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    47da:	49 39 c9             	cmp    %rcx,%r9
    47dd:	75 c9                	jne    47a8 <timer_thread+0xa8>
    47df:	0f ae f0             	mfence
    47e2:	49 8b 46 18          	mov    0x18(%r14),%rax
    47e6:	41 8b 4e 44          	mov    0x44(%r14),%ecx
    47ea:	89 fb                	mov    %edi,%ebx
    47ec:	48 8b 00             	mov    (%rax),%rax
    47ef:	39 78 40             	cmp    %edi,0x40(%rax)
    47f2:	0f 4e dd             	cmovle %ebp,%ebx
    47f5:	85 c9                	test   %ecx,%ecx
    47f7:	74 0d                	je     4806 <timer_thread+0x106>
    47f9:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    4800:	0f 85 75 ff ff ff    	jne    477b <timer_thread+0x7b>
    4806:	48 8d 3d 2b 38 00 00 	lea    0x382b(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    480d:	e8 1e db ff ff       	call   2330 <puts@plt>
    4812:	49 63 56 30          	movslq 0x30(%r14),%rdx
    4816:	85 d2                	test   %edx,%edx
    4818:	7e 6b                	jle    4885 <timer_thread+0x185>
    481a:	49 63 46 40          	movslq 0x40(%r14),%rax
    481e:	85 c0                	test   %eax,%eax
    4820:	7e 63                	jle    4885 <timer_thread+0x185>
    4822:	48 c1 e0 09          	shl    $0x9,%rax
    4826:	4d 8b 46 18          	mov    0x18(%r14),%r8
    482a:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4832:	31 c9                	xor    %ecx,%ecx
    4834:	48 89 c6             	mov    %rax,%rsi
    4837:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    483b:	48 8b 40 38          	mov    0x38(%rax),%rax
    483f:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4843:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4849:	74 15                	je     4860 <timer_thread+0x160>
    484b:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    4855:	48 05 00 02 00 00    	add    $0x200,%rax
    485b:	48 39 c2             	cmp    %rax,%rdx
    485e:	74 1c                	je     487c <timer_thread+0x17c>
    4860:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    486a:	48 05 00 04 00 00    	add    $0x400,%rax
    4870:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    4877:	48 39 c2             	cmp    %rax,%rdx
    487a:	75 e4                	jne    4860 <timer_thread+0x160>
    487c:	48 83 c1 08          	add    $0x8,%rcx
    4880:	48 39 cf             	cmp    %rcx,%rdi
    4883:	75 b2                	jne    4837 <timer_thread+0x137>
    4885:	0f ae f0             	mfence
    4888:	66 0f 6f 05 50 43 00 00 	movdqa 0x4350(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4890:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    4895:	49 63 46 28          	movslq 0x28(%r14),%rax
    4899:	8d 7b 01             	lea    0x1(%rbx),%edi
    489c:	85 c0                	test   %eax,%eax
    489e:	7e 47                	jle    48e7 <timer_thread+0x1e7>
    48a0:	49 8b 4e 18          	mov    0x18(%r14),%rcx
    48a4:	4c 63 c3             	movslq %ebx,%r8
    48a7:	49 c1 e0 09          	shl    $0x9,%r8
    48ab:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    48af:	90                   	nop
    48b0:	48 8b 19             	mov    (%rcx),%rbx
    48b3:	89 f8                	mov    %edi,%eax
    48b5:	48 83 c1 08          	add    $0x8,%rcx
    48b9:	99                   	cltd
    48ba:	f7 7b 40             	idivl  0x40(%rbx)
    48bd:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    48c1:	83 ea 01             	sub    $0x1,%edx
    48c4:	48 63 d2             	movslq %edx,%rdx
    48c7:	48 c1 e2 09          	shl    $0x9,%rdx
    48cb:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    48d6:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    48e2:	49 39 c9             	cmp    %rcx,%r9
    48e5:	75 c9                	jne    48b0 <timer_thread+0x1b0>
    48e7:	0f ae f0             	mfence
    48ea:	49 8b 76 18          	mov    0x18(%r14),%rsi
    48ee:	31 db                	xor    %ebx,%ebx
    48f0:	48 8b 06             	mov    (%rsi),%rax
    48f3:	39 78 40             	cmp    %edi,0x40(%rax)
    48f6:	0f 4f df             	cmovg  %edi,%ebx
    48f9:	41 8b 7e 30          	mov    0x30(%r14),%edi
    48fd:	85 ff                	test   %edi,%edi
    48ff:	0f 8e c7 01 00 00    	jle    4acc <timer_thread+0x3cc>
    4905:	89 5c 24 0c          	mov    %ebx,0xc(%rsp)
    4909:	45 31 ed             	xor    %r13d,%r13d
    490c:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    4912:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4918:	45 31 e4             	xor    %r12d,%r12d
    491b:	44 89 eb             	mov    %r13d,%ebx
    491e:	4a 8d 2c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbp
    4926:	44 89 e6             	mov    %r12d,%esi
    4929:	85 ff                	test   %edi,%edi
    492b:	0f 8e bf 00 00 00    	jle    49f0 <timer_thread+0x2f0>
    4931:	4d 89 e2             	mov    %r12,%r10
    4934:	31 c0                	xor    %eax,%eax
    4936:	45 31 c0             	xor    %r8d,%r8d
    4939:	49 c1 e2 09          	shl    $0x9,%r10
    493d:	0f 1f 00             	nopl   (%rax)
    4940:	45 39 e8             	cmp    %r13d,%r8d
    4943:	74 3c                	je     4981 <timer_thread+0x281>
    4945:	49 8b 56 18          	mov    0x18(%r14),%rdx
    4949:	48 8b 14 2a          	mov    (%rdx,%rbp,1),%rdx
    494d:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4951:	4a 8b 8c 12 70 01 00 00 	mov    0x170(%rdx,%r10,1),%rcx
    4959:	48 01 c1             	add    %rax,%rcx
    495c:	48 89 ca             	mov    %rcx,%rdx
    495f:	48 8b 09             	mov    (%rcx),%rcx
    4962:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    4969:	4c 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9
    4970:	4c 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11
    4977:	4d 85 c9             	test   %r9,%r9
    497a:	7f 24                	jg     49a0 <timer_thread+0x2a0>
    497c:	4d 85 db             	test   %r11,%r11
    497f:	7f 1f                	jg     49a0 <timer_thread+0x2a0>
    4981:	41 83 c0 01          	add    $0x1,%r8d
    4985:	48 05 80 01 00 00    	add    $0x180,%rax
    498b:	44 39 c7             	cmp    %r8d,%edi
    498e:	75 b0                	jne    4940 <timer_thread+0x240>
    4990:	49 83 fc 01          	cmp    $0x1,%r12
    4994:	74 5a                	je     49f0 <timer_thread+0x2f0>
    4996:	49 83 c4 01          	add    $0x1,%r12
    499a:	44 89 e6             	mov    %r12d,%esi
    499d:	eb 92                	jmp    4931 <timer_thread+0x231>
    499f:	90                   	nop
    49a0:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    49a6:	48 83 ec 08          	sub    $0x8,%rsp
    49aa:	bf 01 00 00 00       	mov    $0x1,%edi
    49af:	89 da                	mov    %ebx,%edx
    49b1:	50                   	push   %rax
    49b2:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    49b8:	89 f1                	mov    %esi,%ecx
    49ba:	48 8d 35 9c 36 00 00 	lea    0x369c(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    49c1:	50                   	push   %rax
    49c2:	31 c0                	xor    %eax,%eax
    49c4:	41 53                	push   %r11
    49c6:	e8 e5 da ff ff       	call   24b0 <__printf_chk@plt>
    49cb:	41 8b 7e 30          	mov    0x30(%r14),%edi
    49cf:	48 83 c4 20          	add    $0x20,%rsp
    49d3:	49 83 fc 01          	cmp    $0x1,%r12
    49d7:	0f 84 83 00 00 00    	je     4a60 <timer_thread+0x360>
    49dd:	49 83 c4 01          	add    $0x1,%r12
    49e1:	45 31 ff             	xor    %r15d,%r15d
    49e4:	44 89 e6             	mov    %r12d,%esi
    49e7:	85 ff                	test   %edi,%edi
    49e9:	0f 8f 42 ff ff ff    	jg     4931 <timer_thread+0x231>
    49ef:	90                   	nop
    49f0:	49 83 c5 01          	add    $0x1,%r13
    49f4:	44 39 ef             	cmp    %r13d,%edi
    49f7:	0f 8f 1b ff ff ff    	jg     4918 <timer_thread+0x218>
    49fd:	8b 5c 24 0c          	mov    0xc(%rsp),%ebx
    4a01:	85 ff                	test   %edi,%edi
    4a03:	7e 38                	jle    4a3d <timer_thread+0x33d>
    4a05:	31 ed                	xor    %ebp,%ebp
    4a07:	bf 01 00 00 00       	mov    $0x1,%edi
    4a0c:	49 8b 76 18          	mov    0x18(%r14),%rsi
    4a10:	41 8b 56 40          	mov    0x40(%r14),%edx
    4a14:	48 8b 04 ee          	mov    (%rsi,%rbp,8),%rax
    4a18:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a1c:	8b 88 9c 01 00 00    	mov    0x19c(%rax),%ecx
    4a22:	39 d1                	cmp    %edx,%ecx
    4a24:	7c 7a                	jl     4aa0 <timer_thread+0x3a0>
    4a26:	8b 80 9c 03 00 00    	mov    0x39c(%rax),%eax
    4a2c:	39 d0                	cmp    %edx,%eax
    4a2e:	7c 48                	jl     4a78 <timer_thread+0x378>
    4a30:	48 83 c5 01          	add    $0x1,%rbp
    4a34:	41 39 6e 30          	cmp    %ebp,0x30(%r14)
    4a38:	7f da                	jg     4a14 <timer_thread+0x314>
    4a3a:	41 21 ff             	and    %edi,%r15d
    4a3d:	45 85 ff             	test   %r15d,%r15d
    4a40:	0f 85 86 00 00 00    	jne    4acc <timer_thread+0x3cc>
    4a46:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    4a4b:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    4a50:	e8 4b d9 ff ff       	call   23a0 <nanosleep@plt>
    4a55:	e9 3b fe ff ff       	jmp    4895 <timer_thread+0x195>
    4a5a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a60:	49 83 c5 01          	add    $0x1,%r13
    4a64:	45 31 ff             	xor    %r15d,%r15d
    4a67:	44 39 ef             	cmp    %r13d,%edi
    4a6a:	0f 8f a8 fe ff ff    	jg     4918 <timer_thread+0x218>
    4a70:	eb 8b                	jmp    49fd <timer_thread+0x2fd>
    4a72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a78:	89 c2                	mov    %eax,%edx
    4a7a:	bf 01 00 00 00       	mov    $0x1,%edi
    4a7f:	31 c0                	xor    %eax,%eax
    4a81:	48 83 c5 01          	add    $0x1,%rbp
    4a85:	48 8d 35 79 38 00 00 	lea    0x3879(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4a8c:	e8 1f da ff ff       	call   24b0 <__printf_chk@plt>
    4a91:	31 ff                	xor    %edi,%edi
    4a93:	41 39 6e 30          	cmp    %ebp,0x30(%r14)
    4a97:	0f 8f 6f ff ff ff    	jg     4a0c <timer_thread+0x30c>
    4a9d:	eb 9b                	jmp    4a3a <timer_thread+0x33a>
    4a9f:	90                   	nop
    4aa0:	89 ca                	mov    %ecx,%edx
    4aa2:	48 8d 35 5c 38 00 00 	lea    0x385c(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4aa9:	bf 01 00 00 00       	mov    $0x1,%edi
    4aae:	31 c0                	xor    %eax,%eax
    4ab0:	e8 fb d9 ff ff       	call   24b0 <__printf_chk@plt>
    4ab5:	49 8b 76 18          	mov    0x18(%r14),%rsi
    4ab9:	41 8b 56 40          	mov    0x40(%r14),%edx
    4abd:	31 ff                	xor    %edi,%edi
    4abf:	48 8b 04 ee          	mov    (%rsi,%rbp,8),%rax
    4ac3:	48 8b 40 38          	mov    0x38(%rax),%rax
    4ac7:	e9 5a ff ff ff       	jmp    4a26 <timer_thread+0x326>
    4acc:	48 8d 3d 81 35 00 00 	lea    0x3581(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4ad3:	e8 58 d8 ff ff       	call   2330 <puts@plt>
    4ad8:	41 8b 56 44          	mov    0x44(%r14),%edx
    4adc:	85 d2                	test   %edx,%edx
    4ade:	0f 84 eb 00 00 00    	je     4bcf <timer_thread+0x4cf>
    4ae4:	41 8b 46 2c          	mov    0x2c(%r14),%eax
    4ae8:	31 db                	xor    %ebx,%ebx
    4aea:	48 8d 2d 89 35 00 00 	lea    0x3589(%rip),%rbp        # 807a <_IO_stdin_used+0x7a>
    4af1:	4c 8d 25 9d 35 00 00 	lea    0x359d(%rip),%r12        # 8095 <_IO_stdin_used+0x95>
    4af8:	85 c0                	test   %eax,%eax
    4afa:	7e 38                	jle    4b34 <timer_thread+0x434>
    4afc:	0f 1f 40 00          	nopl   0x0(%rax)
    4b00:	31 c0                	xor    %eax,%eax
    4b02:	89 da                	mov    %ebx,%edx
    4b04:	48 89 ee             	mov    %rbp,%rsi
    4b07:	bf 01 00 00 00       	mov    $0x1,%edi
    4b0c:	e8 9f d9 ff ff       	call   24b0 <__printf_chk@plt>
    4b11:	49 8b 46 18          	mov    0x18(%r14),%rax
    4b15:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4b19:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
    4b1d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
    4b24:	0f 84 d2 00 00 00    	je     4bfc <timer_thread+0x4fc>
    4b2a:	48 83 c3 01          	add    $0x1,%rbx
    4b2e:	41 39 5e 2c          	cmp    %ebx,0x2c(%r14)
    4b32:	7f cc                	jg     4b00 <timer_thread+0x400>
    4b34:	49 63 56 30          	movslq 0x30(%r14),%rdx
    4b38:	85 d2                	test   %edx,%edx
    4b3a:	7e 7c                	jle    4bb8 <timer_thread+0x4b8>
    4b3c:	41 8b 46 40          	mov    0x40(%r14),%eax
    4b40:	85 c0                	test   %eax,%eax
    4b42:	7e 74                	jle    4bb8 <timer_thread+0x4b8>
    4b44:	48 63 f0             	movslq %eax,%rsi
    4b47:	4d 8b 46 18          	mov    0x18(%r14),%r8
    4b4b:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4b53:	31 c9                	xor    %ecx,%ecx
    4b55:	48 c1 e6 09          	shl    $0x9,%rsi
    4b59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4b60:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4b64:	48 8b 40 38          	mov    0x38(%rax),%rax
    4b68:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4b6c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4b72:	74 1c                	je     4b90 <timer_thread+0x490>
    4b74:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4b7e:	48 05 00 02 00 00    	add    $0x200,%rax
    4b84:	48 39 d0             	cmp    %rdx,%rax
    4b87:	74 26                	je     4baf <timer_thread+0x4af>
    4b89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4b90:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4b9a:	48 05 00 04 00 00    	add    $0x400,%rax
    4ba0:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
    4baa:	48 39 d0             	cmp    %rdx,%rax
    4bad:	75 e1                	jne    4b90 <timer_thread+0x490>
    4baf:	48 83 c1 08          	add    $0x8,%rcx
    4bb3:	48 39 cf             	cmp    %rcx,%rdi
    4bb6:	75 a8                	jne    4b60 <timer_thread+0x460>
    4bb8:	0f ae f0             	mfence
    4bbb:	48 8d 3d e5 34 00 00 	lea    0x34e5(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4bc2:	e8 69 d7 ff ff       	call   2330 <puts@plt>
    4bc7:	41 c7 46 44 00 00 00 00 	movl   $0x0,0x44(%r14)
    4bcf:	48 8d 3d d8 34 00 00 	lea    0x34d8(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4bd6:	e8 55 d7 ff ff       	call   2330 <puts@plt>
    4bdb:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    4be0:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4be9:	75 41                	jne    4c2c <timer_thread+0x52c>
    4beb:	48 83 c4 68          	add    $0x68,%rsp
    4bef:	31 c0                	xor    %eax,%eax
    4bf1:	5b                   	pop    %rbx
    4bf2:	5d                   	pop    %rbp
    4bf3:	41 5c                	pop    %r12
    4bf5:	41 5d                	pop    %r13
    4bf7:	41 5e                	pop    %r14
    4bf9:	41 5f                	pop    %r15
    4bfb:	c3                   	ret
    4bfc:	4c 89 e7             	mov    %r12,%rdi
    4bff:	e8 2c d7 ff ff       	call   2330 <puts@plt>
    4c04:	49 8b 46 18          	mov    0x18(%r14),%rax
    4c08:	be 01 00 00 00       	mov    $0x1,%esi
    4c0d:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4c11:	48 83 c3 01          	add    $0x1,%rbx
    4c15:	8b 78 60             	mov    0x60(%rax),%edi
    4c18:	e8 43 d8 ff ff       	call   2460 <eventfd_write@plt>
    4c1d:	41 39 5e 2c          	cmp    %ebx,0x2c(%r14)
    4c21:	0f 8f d9 fe ff ff    	jg     4b00 <timer_thread+0x400>
    4c27:	e9 08 ff ff ff       	jmp    4b34 <timer_thread+0x434>
    4c2c:	e8 4f d7 ff ff       	call   2380 <__stack_chk_fail@plt>
    4c31:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4c3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c40 <minf>:
    4c40:	f3 0f 1e fa          	endbr64
    4c44:	39 f7                	cmp    %esi,%edi
    4c46:	89 f0                	mov    %esi,%eax
    4c48:	0f 4e c7             	cmovle %edi,%eax
    4c4b:	c3                   	ret
    4c4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c50 <maxf>:
    4c50:	f3 0f 1e fa          	endbr64
    4c54:	39 f7                	cmp    %esi,%edi
    4c56:	89 f0                	mov    %esi,%eax
    4c58:	0f 4d c7             	cmovge %edi,%eax
    4c5b:	c3                   	ret
    4c5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c60 <strtolower>:
    4c60:	f3 0f 1e fa          	endbr64
    4c64:	55                   	push   %rbp
    4c65:	53                   	push   %rbx
    4c66:	48 83 ec 08          	sub    $0x8,%rsp
    4c6a:	48 0f be 1f          	movsbq (%rdi),%rbx
    4c6e:	84 db                	test   %bl,%bl
    4c70:	74 24                	je     4c96 <strtolower+0x36>
    4c72:	48 89 fd             	mov    %rdi,%rbp
    4c75:	e8 16 d9 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4c7a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4c80:	48 8b 10             	mov    (%rax),%rdx
    4c83:	48 83 c5 01          	add    $0x1,%rbp
    4c87:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4c8a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    4c8d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4c92:	84 db                	test   %bl,%bl
    4c94:	75 ea                	jne    4c80 <strtolower+0x20>
    4c96:	48 83 c4 08          	add    $0x8,%rsp
    4c9a:	5b                   	pop    %rbx
    4c9b:	5d                   	pop    %rbp
    4c9c:	c3                   	ret
    4c9d:	0f 1f 00             	nopl   (%rax)

0000000000004ca0 <zh_malloc>:
    4ca0:	f3 0f 1e fa          	endbr64
    4ca4:	48 83 ec 08          	sub    $0x8,%rsp
    4ca8:	e8 c3 d7 ff ff       	call   2470 <malloc@plt>
    4cad:	48 85 c0             	test   %rax,%rax
    4cb0:	74 05                	je     4cb7 <zh_malloc+0x17>
    4cb2:	48 83 c4 08          	add    $0x8,%rsp
    4cb6:	c3                   	ret
    4cb7:	48 8b 0d 62 63 00 00 	mov    0x6362(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4cbe:	ba 28 00 00 00       	mov    $0x28,%edx
    4cc3:	be 01 00 00 00       	mov    $0x1,%esi
    4cc8:	48 8d 3d e9 38 00 00 	lea    0x38e9(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    4ccf:	e8 5c d8 ff ff       	call   2530 <fwrite@plt>
    4cd4:	bf 01 00 00 00       	mov    $0x1,%edi
    4cd9:	e8 32 d8 ff ff       	call   2510 <exit@plt>
    4cde:	66 90                	xchg   %ax,%ax

0000000000004ce0 <get_filename_ext>:
    4ce0:	f3 0f 1e fa          	endbr64
    4ce4:	53                   	push   %rbx
    4ce5:	be 2e 00 00 00       	mov    $0x2e,%esi
    4cea:	48 89 fb             	mov    %rdi,%rbx
    4ced:	e8 be d6 ff ff       	call   23b0 <strrchr@plt>
    4cf2:	48 85 c0             	test   %rax,%rax
    4cf5:	74 11                	je     4d08 <get_filename_ext+0x28>
    4cf7:	48 39 c3             	cmp    %rax,%rbx
    4cfa:	74 0c                	je     4d08 <get_filename_ext+0x28>
    4cfc:	48 83 c0 01          	add    $0x1,%rax
    4d00:	5b                   	pop    %rbx
    4d01:	c3                   	ret
    4d02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d08:	48 8d 05 e7 33 00 00 	lea    0x33e7(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
    4d0f:	5b                   	pop    %rbx
    4d10:	c3                   	ret
    4d11:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4d1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004d20 <send_headers>:
    4d20:	f3 0f 1e fa          	endbr64
    4d24:	41 55                	push   %r13
    4d26:	49 89 f5             	mov    %rsi,%r13
    4d29:	48 89 fe             	mov    %rdi,%rsi
    4d2c:	41 54                	push   %r12
    4d2e:	55                   	push   %rbp
    4d2f:	48 89 d5             	mov    %rdx,%rbp
    4d32:	ba 00 04 00 00       	mov    $0x400,%edx
    4d37:	53                   	push   %rbx
    4d38:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4d3f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4d48:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4d50:	31 c0                	xor    %eax,%eax
    4d52:	49 89 e4             	mov    %rsp,%r12
    4d55:	4c 89 e7             	mov    %r12,%rdi
    4d58:	e8 33 d7 ff ff       	call   2490 <__strcpy_chk@plt>
    4d5d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4d62:	84 db                	test   %bl,%bl
    4d64:	74 24                	je     4d8a <send_headers+0x6a>
    4d66:	e8 25 d8 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4d6b:	48 8b 08             	mov    (%rax),%rcx
    4d6e:	4c 89 e0             	mov    %r12,%rax
    4d71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4d78:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    4d7b:	48 83 c0 01          	add    $0x1,%rax
    4d7f:	88 50 ff             	mov    %dl,-0x1(%rax)
    4d82:	48 0f be 18          	movsbq (%rax),%rbx
    4d86:	84 db                	test   %bl,%bl
    4d88:	75 ee                	jne    4d78 <send_headers+0x58>
    4d8a:	bf 11 00 00 00       	mov    $0x11,%edi
    4d8f:	e8 dc d6 ff ff       	call   2470 <malloc@plt>
    4d94:	48 85 c0             	test   %rax,%rax
    4d97:	0f 84 7e 04 00 00    	je     521b <send_headers+0x4fb>
    4d9d:	66 0f 6f 05 4b 3e 00 00 	movdqa 0x3e4b(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4da5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    4da9:	bf 17 00 00 00       	mov    $0x17,%edi
    4dae:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4db6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4dba:	0f 11 00             	movups %xmm0,(%rax)
    4dbd:	e8 ae d6 ff ff       	call   2470 <malloc@plt>
    4dc2:	48 85 c0             	test   %rax,%rax
    4dc5:	0f 84 50 04 00 00    	je     521b <send_headers+0x4fb>
    4dcb:	66 0f 6f 05 2d 3e 00 00 	movdqa 0x3e2d(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4dd3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    4dd7:	4c 89 e7             	mov    %r12,%rdi
    4dda:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    4de4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4dec:	0f 11 00             	movups %xmm0,(%rax)
    4def:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    4df3:	be 2e 00 00 00       	mov    $0x2e,%esi
    4df8:	e8 b3 d5 ff ff       	call   23b0 <strrchr@plt>
    4dfd:	48 85 c0             	test   %rax,%rax
    4e00:	0f 84 ea 02 00 00    	je     50f0 <send_headers+0x3d0>
    4e06:	4c 39 e0             	cmp    %r12,%rax
    4e09:	0f 84 e1 02 00 00    	je     50f0 <send_headers+0x3d0>
    4e0f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    4e13:	48 8d 3d aa 32 00 00 	lea    0x32aa(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4e1a:	48 89 de             	mov    %rbx,%rsi
    4e1d:	e8 ee d5 ff ff       	call   2410 <strcmp@plt>
    4e22:	85 c0                	test   %eax,%eax
    4e24:	75 20                	jne    4e46 <send_headers+0x126>
    4e26:	66 0f 6f 05 e2 3d 00 00 	movdqa 0x3de2(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e2e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e36:	66 0f 6f 05 e2 3d 00 00 	movdqa 0x3de2(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4e3e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4e46:	48 89 de             	mov    %rbx,%rsi
    4e49:	48 8d 3d 78 32 00 00 	lea    0x3278(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4e50:	e8 bb d5 ff ff       	call   2410 <strcmp@plt>
    4e55:	85 c0                	test   %eax,%eax
    4e57:	75 20                	jne    4e79 <send_headers+0x159>
    4e59:	66 0f 6f 05 af 3d 00 00 	movdqa 0x3daf(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e61:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e69:	66 0f 6f 05 af 3d 00 00 	movdqa 0x3daf(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4e71:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4e79:	48 89 de             	mov    %rbx,%rsi
    4e7c:	48 8d 3d 4a 32 00 00 	lea    0x324a(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4e83:	e8 88 d5 ff ff       	call   2410 <strcmp@plt>
    4e88:	85 c0                	test   %eax,%eax
    4e8a:	0f 84 10 02 00 00    	je     50a0 <send_headers+0x380>
    4e90:	48 89 de             	mov    %rbx,%rsi
    4e93:	48 8d 3d 37 32 00 00 	lea    0x3237(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4e9a:	e8 71 d5 ff ff       	call   2410 <strcmp@plt>
    4e9f:	85 c0                	test   %eax,%eax
    4ea1:	0f 84 a9 02 00 00    	je     5150 <send_headers+0x430>
    4ea7:	48 89 de             	mov    %rbx,%rsi
    4eaa:	48 8d 3d 24 32 00 00 	lea    0x3224(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4eb1:	e8 5a d5 ff ff       	call   2410 <strcmp@plt>
    4eb6:	85 c0                	test   %eax,%eax
    4eb8:	0f 84 6a 02 00 00    	je     5128 <send_headers+0x408>
    4ebe:	48 89 de             	mov    %rbx,%rsi
    4ec1:	48 8d 3d 50 32 00 00 	lea    0x3250(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4ec8:	e8 43 d5 ff ff       	call   2410 <strcmp@plt>
    4ecd:	85 c0                	test   %eax,%eax
    4ecf:	0f 84 2b 02 00 00    	je     5100 <send_headers+0x3e0>
    4ed5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4ed8:	0f 84 52 01 00 00    	je     5030 <send_headers+0x310>
    4ede:	48 89 de             	mov    %rbx,%rsi
    4ee1:	48 8d 3d f1 31 00 00 	lea    0x31f1(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4ee8:	e8 23 d5 ff ff       	call   2410 <strcmp@plt>
    4eed:	85 c0                	test   %eax,%eax
    4eef:	0f 84 ab 02 00 00    	je     51a0 <send_headers+0x480>
    4ef5:	48 89 de             	mov    %rbx,%rsi
    4ef8:	48 8d 3d de 31 00 00 	lea    0x31de(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4eff:	e8 0c d5 ff ff       	call   2410 <strcmp@plt>
    4f04:	85 c0                	test   %eax,%eax
    4f06:	0f 84 6c 02 00 00    	je     5178 <send_headers+0x458>
    4f0c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4f14:	4c 89 e7             	mov    %r12,%rdi
    4f17:	e8 54 d4 ff ff       	call   2370 <strlen@plt>
    4f1c:	48 89 c7             	mov    %rax,%rdi
    4f1f:	48 89 c3             	mov    %rax,%rbx
    4f22:	e8 49 d5 ff ff       	call   2470 <malloc@plt>
    4f27:	48 85 c0             	test   %rax,%rax
    4f2a:	0f 84 eb 02 00 00    	je     521b <send_headers+0x4fb>
    4f30:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4f34:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    4f38:	83 fb 08             	cmp    $0x8,%ebx
    4f3b:	0f 83 3f 01 00 00    	jae    5080 <send_headers+0x360>
    4f41:	f6 c3 04             	test   $0x4,%bl
    4f44:	0f 85 7b 02 00 00    	jne    51c5 <send_headers+0x4a5>
    4f4a:	85 db                	test   %ebx,%ebx
    4f4c:	74 13                	je     4f61 <send_headers+0x241>
    4f4e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4f56:	88 10                	mov    %dl,(%rax)
    4f58:	f6 c3 02             	test   $0x2,%bl
    4f5b:	0f 85 96 02 00 00    	jne    51f7 <send_headers+0x4d7>
    4f61:	4d 89 e8             	mov    %r13,%r8
    4f64:	48 8d 0d 76 31 00 00 	lea    0x3176(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4f6b:	4c 89 e7             	mov    %r12,%rdi
    4f6e:	31 c0                	xor    %eax,%eax
    4f70:	ba 00 04 00 00       	mov    $0x400,%edx
    4f75:	be 01 00 00 00       	mov    $0x1,%esi
    4f7a:	e8 21 d6 ff ff       	call   25a0 <__sprintf_chk@plt>
    4f7f:	4c 89 e7             	mov    %r12,%rdi
    4f82:	e8 e9 d3 ff ff       	call   2370 <strlen@plt>
    4f87:	48 89 c7             	mov    %rax,%rdi
    4f8a:	48 89 c3             	mov    %rax,%rbx
    4f8d:	e8 de d4 ff ff       	call   2470 <malloc@plt>
    4f92:	48 85 c0             	test   %rax,%rax
    4f95:	0f 84 80 02 00 00    	je     521b <send_headers+0x4fb>
    4f9b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    4f9f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4fa3:	83 fb 08             	cmp    $0x8,%ebx
    4fa6:	0f 83 1c 01 00 00    	jae    50c8 <send_headers+0x3a8>
    4fac:	f6 c3 04             	test   $0x4,%bl
    4faf:	0f 85 29 02 00 00    	jne    51de <send_headers+0x4be>
    4fb5:	85 db                	test   %ebx,%ebx
    4fb7:	74 13                	je     4fcc <send_headers+0x2ac>
    4fb9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4fc1:	88 10                	mov    %dl,(%rax)
    4fc3:	f6 c3 02             	test   $0x2,%bl
    4fc6:	0f 85 3d 02 00 00    	jne    5209 <send_headers+0x4e9>
    4fcc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    4fd1:	bf 02 00 00 00       	mov    $0x2,%edi
    4fd6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4fde:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4fe6:	e8 85 d4 ff ff       	call   2470 <malloc@plt>
    4feb:	48 85 c0             	test   %rax,%rax
    4fee:	0f 84 27 02 00 00    	je     521b <send_headers+0x4fb>
    4ff4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    4ffc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    5000:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    5008:	66 89 10             	mov    %dx,(%rax)
    500b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    5013:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    501c:	0f 85 20 02 00 00    	jne    5242 <send_headers+0x522>
    5022:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    5029:	5b                   	pop    %rbx
    502a:	5d                   	pop    %rbp
    502b:	41 5c                	pop    %r12
    502d:	41 5d                	pop    %r13
    502f:	c3                   	ret
    5030:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    5034:	0f 85 a4 fe ff ff    	jne    4ede <send_headers+0x1be>
    503a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    503e:	0f 85 9a fe ff ff    	jne    4ede <send_headers+0x1be>
    5044:	66 0f 6f 05 24 3c 00 00 	movdqa 0x3c24(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    504c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    5056:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    505e:	66 0f 6f 05 1a 3c 00 00 	movdqa 0x3c1a(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    5066:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    506e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    5076:	e9 63 fe ff ff       	jmp    4ede <send_headers+0x1be>
    507b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5080:	89 da                	mov    %ebx,%edx
    5082:	48 89 c7             	mov    %rax,%rdi
    5085:	4c 89 e6             	mov    %r12,%rsi
    5088:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    508d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5092:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5095:	c1 e9 03             	shr    $0x3,%ecx
    5098:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    509b:	e9 c1 fe ff ff       	jmp    4f61 <send_headers+0x241>
    50a0:	66 0f 6f 05 68 3b 00 00 	movdqa 0x3b68(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    50a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50b0:	66 0f 6f 05 78 3b 00 00 	movdqa 0x3b78(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    50b8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    50c0:	e9 cb fd ff ff       	jmp    4e90 <send_headers+0x170>
    50c5:	0f 1f 00             	nopl   (%rax)
    50c8:	89 da                	mov    %ebx,%edx
    50ca:	48 89 c7             	mov    %rax,%rdi
    50cd:	4c 89 e6             	mov    %r12,%rsi
    50d0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    50d5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    50da:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    50dd:	c1 e9 03             	shr    $0x3,%ecx
    50e0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    50e3:	e9 e4 fe ff ff       	jmp    4fcc <send_headers+0x2ac>
    50e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    50f0:	48 8d 1d ff 2f 00 00 	lea    0x2fff(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    50f7:	e9 94 fd ff ff       	jmp    4e90 <send_headers+0x170>
    50fc:	0f 1f 40 00          	nopl   0x0(%rax)
    5100:	66 0f 6f 05 48 3b 00 00 	movdqa 0x3b48(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5108:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5110:	66 0f 6f 05 48 3b 00 00 	movdqa 0x3b48(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5118:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5120:	e9 b0 fd ff ff       	jmp    4ed5 <send_headers+0x1b5>
    5125:	0f 1f 00             	nopl   (%rax)
    5128:	66 0f 6f 05 20 3b 00 00 	movdqa 0x3b20(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5130:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5138:	66 0f 6f 05 20 3b 00 00 	movdqa 0x3b20(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5140:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5148:	e9 71 fd ff ff       	jmp    4ebe <send_headers+0x19e>
    514d:	0f 1f 00             	nopl   (%rax)
    5150:	66 0f 6f 05 b8 3a 00 00 	movdqa 0x3ab8(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    5158:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5160:	66 0f 6f 05 d8 3a 00 00 	movdqa 0x3ad8(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    5168:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5170:	e9 32 fd ff ff       	jmp    4ea7 <send_headers+0x187>
    5175:	0f 1f 00             	nopl   (%rax)
    5178:	66 0f 6f 05 d0 3a 00 00 	movdqa 0x3ad0(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5180:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5188:	66 0f 6f 05 10 3b 00 00 	movdqa 0x3b10(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    5190:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5198:	e9 6f fd ff ff       	jmp    4f0c <send_headers+0x1ec>
    519d:	0f 1f 00             	nopl   (%rax)
    51a0:	66 0f 6f 05 a8 3a 00 00 	movdqa 0x3aa8(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    51a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    51b0:	66 0f 6f 05 d8 3a 00 00 	movdqa 0x3ad8(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    51b8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    51c0:	e9 30 fd ff ff       	jmp    4ef5 <send_headers+0x1d5>
    51c5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    51cc:	89 db                	mov    %ebx,%ebx
    51ce:	89 10                	mov    %edx,(%rax)
    51d0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    51d5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    51d9:	e9 83 fd ff ff       	jmp    4f61 <send_headers+0x241>
    51de:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    51e5:	89 db                	mov    %ebx,%ebx
    51e7:	89 10                	mov    %edx,(%rax)
    51e9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    51ee:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    51f2:	e9 d5 fd ff ff       	jmp    4fcc <send_headers+0x2ac>
    51f7:	89 db                	mov    %ebx,%ebx
    51f9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    51ff:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5204:	e9 58 fd ff ff       	jmp    4f61 <send_headers+0x241>
    5209:	89 db                	mov    %ebx,%ebx
    520b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    5211:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5216:	e9 b1 fd ff ff       	jmp    4fcc <send_headers+0x2ac>
    521b:	48 8b 0d fe 5d 00 00 	mov    0x5dfe(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5222:	ba 28 00 00 00       	mov    $0x28,%edx
    5227:	be 01 00 00 00       	mov    $0x1,%esi
    522c:	48 8d 3d 85 33 00 00 	lea    0x3385(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    5233:	e8 f8 d2 ff ff       	call   2530 <fwrite@plt>
    5238:	bf 01 00 00 00       	mov    $0x1,%edi
    523d:	e8 ce d2 ff ff       	call   2510 <exit@plt>
    5242:	e8 39 d1 ff ff       	call   2380 <__stack_chk_fail@plt>
    5247:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005250 <copy_file_contents>:
    5250:	f3 0f 1e fa          	endbr64
    5254:	41 55                	push   %r13
    5256:	49 89 d5             	mov    %rdx,%r13
    5259:	41 54                	push   %r12
    525b:	49 89 fc             	mov    %rdi,%r12
    525e:	48 89 f7             	mov    %rsi,%rdi
    5261:	55                   	push   %rbp
    5262:	53                   	push   %rbx
    5263:	48 89 f3             	mov    %rsi,%rbx
    5266:	48 83 ec 08          	sub    $0x8,%rsp
    526a:	e8 01 d2 ff ff       	call   2470 <malloc@plt>
    526f:	48 85 c0             	test   %rax,%rax
    5272:	74 6b                	je     52df <copy_file_contents+0x8f>
    5274:	4c 89 e7             	mov    %r12,%rdi
    5277:	48 89 c5             	mov    %rax,%rbp
    527a:	31 f6                	xor    %esi,%esi
    527c:	31 c0                	xor    %eax,%eax
    527e:	e8 5d d2 ff ff       	call   24e0 <open@plt>
    5283:	41 89 c4             	mov    %eax,%r12d
    5286:	85 c0                	test   %eax,%eax
    5288:	0f 88 48 d3 ff ff    	js     25d6 <copy_file_contents.cold>
    528e:	48 89 da             	mov    %rbx,%rdx
    5291:	48 89 ee             	mov    %rbp,%rsi
    5294:	89 c7                	mov    %eax,%edi
    5296:	e8 55 d1 ff ff       	call   23f0 <read@plt>
    529b:	48 98                	cltq
    529d:	48 39 d8             	cmp    %rbx,%rax
    52a0:	7c 1e                	jl     52c0 <copy_file_contents+0x70>
    52a2:	44 89 e7             	mov    %r12d,%edi
    52a5:	e8 26 d1 ff ff       	call   23d0 <close@plt>
    52aa:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    52ae:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    52b2:	48 83 c4 08          	add    $0x8,%rsp
    52b6:	5b                   	pop    %rbx
    52b7:	5d                   	pop    %rbp
    52b8:	41 5c                	pop    %r12
    52ba:	41 5d                	pop    %r13
    52bc:	c3                   	ret
    52bd:	0f 1f 00             	nopl   (%rax)
    52c0:	48 8b 0d 59 5d 00 00 	mov    0x5d59(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    52c7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    52cc:	be 01 00 00 00       	mov    $0x1,%esi
    52d1:	48 8d 3d 1f 2e 00 00 	lea    0x2e1f(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    52d8:	e8 53 d2 ff ff       	call   2530 <fwrite@plt>
    52dd:	eb c3                	jmp    52a2 <copy_file_contents+0x52>
    52df:	48 8b 0d 3a 5d 00 00 	mov    0x5d3a(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    52e6:	ba 28 00 00 00       	mov    $0x28,%edx
    52eb:	be 01 00 00 00       	mov    $0x1,%esi
    52f0:	48 8d 3d c1 32 00 00 	lea    0x32c1(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    52f7:	e8 34 d2 ff ff       	call   2530 <fwrite@plt>
    52fc:	bf 01 00 00 00       	mov    $0x1,%edi
    5301:	e8 0a d2 ff ff       	call   2510 <exit@plt>
    5306:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005310 <add_write_request>:
    5310:	f3 0f 1e fa          	endbr64
    5314:	8b 46 44             	mov    0x44(%rsi),%eax
    5317:	48 89 fa             	mov    %rdi,%rdx
    531a:	48 89 f7             	mov    %rsi,%rdi
    531d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    5323:	8d 70 01             	lea    0x1(%rax),%esi
    5326:	48 8b 07             	mov    (%rdi),%rax
    5329:	44 8b 00             	mov    (%rax),%r8d
    532c:	f6 c1 02             	test   $0x2,%cl
    532f:	74 00                	je     5331 <add_write_request+0x21>
    5331:	89 f0                	mov    %esi,%eax
    5333:	44 29 c0             	sub    %r8d,%eax
    5336:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5339:	0f 82 a3 d2 ff ff    	jb     25e2 <add_write_request.cold>
    533f:	c1 e9 0a             	shr    $0xa,%ecx
    5342:	48 83 ec 08          	sub    $0x8,%rsp
    5346:	8b 47 44             	mov    0x44(%rdi),%eax
    5349:	23 47 58             	and    0x58(%rdi),%eax
    534c:	83 e1 01             	and    $0x1,%ecx
    534f:	89 77 44             	mov    %esi,0x44(%rdi)
    5352:	8b 72 08             	mov    0x8(%rdx),%esi
    5355:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5359:	d3 e0                	shl    %cl,%eax
    535b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    535e:	48 c1 e0 06          	shl    $0x6,%rax
    5362:	48 03 47 38          	add    0x38(%rdi),%rax
    5366:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    536c:	89 70 04             	mov    %esi,0x4(%rax)
    536f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    5373:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    5379:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5381:	48 89 70 10          	mov    %rsi,0x10(%rax)
    5385:	89 48 18             	mov    %ecx,0x18(%rax)
    5388:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    538f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5397:	48 89 50 20          	mov    %rdx,0x20(%rax)
    539b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    539f:	e8 ec cf ff ff       	call   2390 <io_uring_submit@plt>
    53a4:	31 c0                	xor    %eax,%eax
    53a6:	48 83 c4 08          	add    $0x8,%rsp
    53aa:	c3                   	ret
    53ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000053b0 <add_read_request>:
    53b0:	f3 0f 1e fa          	endbr64
    53b4:	41 55                	push   %r13
    53b6:	41 89 fd             	mov    %edi,%r13d
    53b9:	41 54                	push   %r12
    53bb:	55                   	push   %rbp
    53bc:	53                   	push   %rbx
    53bd:	48 89 f3             	mov    %rsi,%rbx
    53c0:	48 83 ec 08          	sub    $0x8,%rsp
    53c4:	8b 46 44             	mov    0x44(%rsi),%eax
    53c7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    53cd:	48 8b 16             	mov    (%rsi),%rdx
    53d0:	83 c0 01             	add    $0x1,%eax
    53d3:	8b 32                	mov    (%rdx),%esi
    53d5:	f6 c1 02             	test   $0x2,%cl
    53d8:	74 00                	je     53da <add_read_request+0x2a>
    53da:	89 c2                	mov    %eax,%edx
    53dc:	29 f2                	sub    %esi,%edx
    53de:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    53e1:	0f 82 0b d2 ff ff    	jb     25f2 <add_read_request.cold>
    53e7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    53ea:	c1 e9 0a             	shr    $0xa,%ecx
    53ed:	89 43 44             	mov    %eax,0x44(%rbx)
    53f0:	bf 20 00 00 00       	mov    $0x20,%edi
    53f5:	83 e1 01             	and    $0x1,%ecx
    53f8:	23 6b 58             	and    0x58(%rbx),%ebp
    53fb:	d3 e5                	shl    %cl,%ebp
    53fd:	48 c1 e5 06          	shl    $0x6,%rbp
    5401:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5405:	e8 66 d0 ff ff       	call   2470 <malloc@plt>
    540a:	be 01 00 00 00       	mov    $0x1,%esi
    540f:	bf 00 20 00 00       	mov    $0x2000,%edi
    5414:	49 89 c4             	mov    %rax,%r12
    5417:	e8 e4 cf ff ff       	call   2400 <calloc@plt>
    541c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    5421:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5425:	48 89 df             	mov    %rbx,%rdi
    5428:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    542d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    5432:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    543b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    5443:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    5447:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    544b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    5452:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    545a:	48 89 45 10          	mov    %rax,0x10(%rbp)
    545e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    5466:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    546e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5472:	e8 19 cf ff ff       	call   2390 <io_uring_submit@plt>
    5477:	48 83 c4 08          	add    $0x8,%rsp
    547b:	31 c0                	xor    %eax,%eax
    547d:	5b                   	pop    %rbx
    547e:	5d                   	pop    %rbp
    547f:	41 5c                	pop    %r12
    5481:	41 5d                	pop    %r13
    5483:	c3                   	ret
    5484:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    548f:	90                   	nop

0000000000005490 <_send_static_string_content>:
    5490:	f3 0f 1e fa          	endbr64
    5494:	41 56                	push   %r14
    5496:	41 89 f6             	mov    %esi,%r14d
    5499:	41 55                	push   %r13
    549b:	49 89 fd             	mov    %rdi,%r13
    549e:	bf 20 00 00 00       	mov    $0x20,%edi
    54a3:	41 54                	push   %r12
    54a5:	55                   	push   %rbp
    54a6:	48 89 d5             	mov    %rdx,%rbp
    54a9:	53                   	push   %rbx
    54aa:	e8 c1 cf ff ff       	call   2470 <malloc@plt>
    54af:	48 85 c0             	test   %rax,%rax
    54b2:	0f 84 dd 00 00 00    	je     5595 <_send_static_string_content+0x105>
    54b8:	48 89 c3             	mov    %rax,%rbx
    54bb:	4c 89 ef             	mov    %r13,%rdi
    54be:	e8 ad ce ff ff       	call   2370 <strlen@plt>
    54c3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    54ca:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    54ce:	48 89 c7             	mov    %rax,%rdi
    54d1:	49 89 c4             	mov    %rax,%r12
    54d4:	e8 97 cf ff ff       	call   2470 <malloc@plt>
    54d9:	48 89 c7             	mov    %rax,%rdi
    54dc:	48 85 c0             	test   %rax,%rax
    54df:	0f 84 b0 00 00 00    	je     5595 <_send_static_string_content+0x105>
    54e5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    54e9:	4c 89 e2             	mov    %r12,%rdx
    54ec:	4c 89 ee             	mov    %r13,%rsi
    54ef:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    54f3:	e8 48 cf ff ff       	call   2440 <memcpy@plt>
    54f8:	8b 45 44             	mov    0x44(%rbp),%eax
    54fb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    5501:	8d 50 01             	lea    0x1(%rax),%edx
    5504:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5508:	8b 30                	mov    (%rax),%esi
    550a:	f6 c1 02             	test   $0x2,%cl
    550d:	0f 85 7d 00 00 00    	jne    5590 <_send_static_string_content+0x100>
    5513:	89 d0                	mov    %edx,%eax
    5515:	29 f0                	sub    %esi,%eax
    5517:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    551a:	0f 82 dc d0 ff ff    	jb     25fc <_send_static_string_content.cold>
    5520:	c1 e9 0a             	shr    $0xa,%ecx
    5523:	8b 45 44             	mov    0x44(%rbp),%eax
    5526:	23 45 58             	and    0x58(%rbp),%eax
    5529:	89 55 44             	mov    %edx,0x44(%rbp)
    552c:	83 e1 01             	and    $0x1,%ecx
    552f:	8b 53 04             	mov    0x4(%rbx),%edx
    5532:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    5538:	66 0f ef c0          	pxor   %xmm0,%xmm0
    553c:	d3 e0                	shl    %cl,%eax
    553e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    5541:	48 89 ef             	mov    %rbp,%rdi
    5544:	48 c1 e0 06          	shl    $0x6,%rax
    5548:	48 03 45 38          	add    0x38(%rbp),%rax
    554c:	89 48 04             	mov    %ecx,0x4(%rax)
    554f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    5553:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    5559:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5561:	48 89 48 10          	mov    %rcx,0x10(%rax)
    5565:	89 50 18             	mov    %edx,0x18(%rax)
    5568:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    556f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5577:	48 89 58 20          	mov    %rbx,0x20(%rax)
    557b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    557f:	5b                   	pop    %rbx
    5580:	5d                   	pop    %rbp
    5581:	41 5c                	pop    %r12
    5583:	41 5d                	pop    %r13
    5585:	41 5e                	pop    %r14
    5587:	e9 04 ce ff ff       	jmp    2390 <io_uring_submit@plt>
    558c:	0f 1f 40 00          	nopl   0x0(%rax)
    5590:	e9 7e ff ff ff       	jmp    5513 <_send_static_string_content+0x83>
    5595:	48 8b 0d 84 5a 00 00 	mov    0x5a84(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    559c:	ba 28 00 00 00       	mov    $0x28,%edx
    55a1:	be 01 00 00 00       	mov    $0x1,%esi
    55a6:	48 8d 3d 0b 30 00 00 	lea    0x300b(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    55ad:	e8 7e cf ff ff       	call   2530 <fwrite@plt>
    55b2:	bf 01 00 00 00       	mov    $0x1,%edi
    55b7:	e8 54 cf ff ff       	call   2510 <exit@plt>
    55bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000055c0 <handle_unimplemented_method>:
    55c0:	f3 0f 1e fa          	endbr64
    55c4:	48 89 f2             	mov    %rsi,%rdx
    55c7:	89 fe                	mov    %edi,%esi
    55c9:	48 8b 3d 48 5a 00 00 	mov    0x5a48(%rip),%rdi        # b018 <unimplemented_content>
    55d0:	e9 bb fe ff ff       	jmp    5490 <_send_static_string_content>
    55d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000055e0 <handle_http_404>:
    55e0:	f3 0f 1e fa          	endbr64
    55e4:	48 89 f2             	mov    %rsi,%rdx
    55e7:	89 fe                	mov    %edi,%esi
    55e9:	48 8b 3d 20 5a 00 00 	mov    0x5a20(%rip),%rdi        # b010 <http_404_content>
    55f0:	e9 9b fe ff ff       	jmp    5490 <_send_static_string_content>
    55f5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005600 <handle_get_method>:
    5600:	f3 0f 1e fa          	endbr64
    5604:	41 56                	push   %r14
    5606:	41 55                	push   %r13
    5608:	49 89 d5             	mov    %rdx,%r13
    560b:	41 54                	push   %r12
    560d:	41 89 f4             	mov    %esi,%r12d
    5610:	55                   	push   %rbp
    5611:	48 89 fd             	mov    %rdi,%rbp
    5614:	53                   	push   %rbx
    5615:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    561c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5625:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    562d:	31 c0                	xor    %eax,%eax
    562f:	e8 3c cd ff ff       	call   2370 <strlen@plt>
    5634:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    5639:	48 89 c3             	mov    %rax,%rbx
    563c:	0f 84 b6 00 00 00    	je     56f8 <handle_get_method+0xf8>
    5642:	b8 69 63 00 00       	mov    $0x6369,%eax
    5647:	48 89 ee             	mov    %rbp,%rsi
    564a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    564e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5653:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    565b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5663:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    566e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    5676:	e8 a5 cd ff ff       	call   2420 <__memcpy_chk@plt>
    567b:	48 89 e6             	mov    %rsp,%rsi
    567e:	4c 89 f7             	mov    %r14,%rdi
    5681:	e8 aa cd ff ff       	call   2430 <stat@plt>
    5686:	83 f8 ff             	cmp    $0xffffffff,%eax
    5689:	0f 84 d3 00 00 00    	je     5762 <handle_get_method+0x162>
    568f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5693:	25 00 f0 00 00       	and    $0xf000,%eax
    5698:	3d 00 80 00 00       	cmp    $0x8000,%eax
    569d:	0f 84 f5 00 00 00    	je     5798 <handle_get_method+0x198>
    56a3:	48 8b 3d 66 59 00 00 	mov    0x5966(%rip),%rdi        # b010 <http_404_content>
    56aa:	4c 89 ea             	mov    %r13,%rdx
    56ad:	44 89 e6             	mov    %r12d,%esi
    56b0:	e8 db fd ff ff       	call   5490 <_send_static_string_content>
    56b5:	4c 89 f2             	mov    %r14,%rdx
    56b8:	bf 01 00 00 00       	mov    $0x1,%edi
    56bd:	31 c0                	xor    %eax,%eax
    56bf:	48 8d 35 81 2a 00 00 	lea    0x2a81(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    56c6:	e8 e5 cd ff ff       	call   24b0 <__printf_chk@plt>
    56cb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    56d3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    56dc:	0f 85 20 01 00 00    	jne    5802 <handle_get_method+0x202>
    56e2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    56e9:	5b                   	pop    %rbx
    56ea:	5d                   	pop    %rbp
    56eb:	41 5c                	pop    %r12
    56ed:	41 5d                	pop    %r13
    56ef:	41 5e                	pop    %r14
    56f1:	c3                   	ret
    56f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    56f8:	ba 69 63 00 00       	mov    $0x6369,%edx
    56fd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5705:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    570a:	48 89 ee             	mov    %rbp,%rsi
    570d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    5715:	48 89 c2             	mov    %rax,%rdx
    5718:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5720:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    572b:	e8 f0 cc ff ff       	call   2420 <__memcpy_chk@plt>
    5730:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5735:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    573a:	48 8d 35 d1 29 00 00 	lea    0x29d1(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    5741:	48 29 d9             	sub    %rbx,%rcx
    5744:	ba 0b 00 00 00       	mov    $0xb,%edx
    5749:	e8 d2 cc ff ff       	call   2420 <__memcpy_chk@plt>
    574e:	48 89 e6             	mov    %rsp,%rsi
    5751:	4c 89 f7             	mov    %r14,%rdi
    5754:	e8 d7 cc ff ff       	call   2430 <stat@plt>
    5759:	83 f8 ff             	cmp    $0xffffffff,%eax
    575c:	0f 85 2d ff ff ff    	jne    568f <handle_get_method+0x8f>
    5762:	4c 89 f2             	mov    %r14,%rdx
    5765:	48 89 e9             	mov    %rbp,%rcx
    5768:	48 8d 35 ae 29 00 00 	lea    0x29ae(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    576f:	31 c0                	xor    %eax,%eax
    5771:	bf 01 00 00 00       	mov    $0x1,%edi
    5776:	e8 35 cd ff ff       	call   24b0 <__printf_chk@plt>
    577b:	48 8b 3d 8e 58 00 00 	mov    0x588e(%rip),%rdi        # b010 <http_404_content>
    5782:	4c 89 ea             	mov    %r13,%rdx
    5785:	44 89 e6             	mov    %r12d,%esi
    5788:	e8 03 fd ff ff       	call   5490 <_send_static_string_content>
    578d:	e9 39 ff ff ff       	jmp    56cb <handle_get_method+0xcb>
    5792:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5798:	bf 70 00 00 00       	mov    $0x70,%edi
    579d:	e8 ce cc ff ff       	call   2470 <malloc@plt>
    57a2:	48 89 c3             	mov    %rax,%rbx
    57a5:	48 85 c0             	test   %rax,%rax
    57a8:	74 5d                	je     5807 <handle_get_method+0x207>
    57aa:	44 89 60 08          	mov    %r12d,0x8(%rax)
    57ae:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    57b3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    57b7:	4c 89 f7             	mov    %r14,%rdi
    57ba:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    57c1:	e8 5a f5 ff ff       	call   4d20 <send_headers>
    57c6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    57cb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    57cf:	4c 89 f7             	mov    %r14,%rdi
    57d2:	e8 79 fa ff ff       	call   5250 <copy_file_contents>
    57d7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    57dc:	4c 89 f2             	mov    %r14,%rdx
    57df:	31 c0                	xor    %eax,%eax
    57e1:	48 8d 35 4d 29 00 00 	lea    0x294d(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    57e8:	bf 01 00 00 00       	mov    $0x1,%edi
    57ed:	e8 be cc ff ff       	call   24b0 <__printf_chk@plt>
    57f2:	4c 89 ee             	mov    %r13,%rsi
    57f5:	48 89 df             	mov    %rbx,%rdi
    57f8:	e8 13 fb ff ff       	call   5310 <add_write_request>
    57fd:	e9 c9 fe ff ff       	jmp    56cb <handle_get_method+0xcb>
    5802:	e8 79 cb ff ff       	call   2380 <__stack_chk_fail@plt>
    5807:	48 8b 0d 12 58 00 00 	mov    0x5812(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    580e:	ba 28 00 00 00       	mov    $0x28,%edx
    5813:	be 01 00 00 00       	mov    $0x1,%esi
    5818:	48 8d 3d 99 2d 00 00 	lea    0x2d99(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    581f:	e8 0c cd ff ff       	call   2530 <fwrite@plt>
    5824:	bf 01 00 00 00       	mov    $0x1,%edi
    5829:	e8 e2 cc ff ff       	call   2510 <exit@plt>
    582e:	66 90                	xchg   %ax,%ax

0000000000005830 <handle_http_method>:
    5830:	f3 0f 1e fa          	endbr64
    5834:	41 57                	push   %r15
    5836:	41 56                	push   %r14
    5838:	4c 8d 35 6d 28 00 00 	lea    0x286d(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
    583f:	41 55                	push   %r13
    5841:	49 89 d5             	mov    %rdx,%r13
    5844:	41 54                	push   %r12
    5846:	41 89 f4             	mov    %esi,%r12d
    5849:	4c 89 f6             	mov    %r14,%rsi
    584c:	55                   	push   %rbp
    584d:	53                   	push   %rbx
    584e:	48 83 ec 18          	sub    $0x18,%rsp
    5852:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    585b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5860:	31 c0                	xor    %eax,%eax
    5862:	49 89 e7             	mov    %rsp,%r15
    5865:	4c 89 fa             	mov    %r15,%rdx
    5868:	e8 73 cb ff ff       	call   23e0 <strtok_r@plt>
    586d:	48 0f be 18          	movsbq (%rax),%rbx
    5871:	48 89 c5             	mov    %rax,%rbp
    5874:	84 db                	test   %bl,%bl
    5876:	74 1d                	je     5895 <handle_http_method+0x65>
    5878:	e8 13 cd ff ff       	call   2590 <__ctype_tolower_loc@plt>
    587d:	48 89 ea             	mov    %rbp,%rdx
    5880:	48 8b 08             	mov    (%rax),%rcx
    5883:	48 83 c2 01          	add    $0x1,%rdx
    5887:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    588a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    588d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5891:	84 db                	test   %bl,%bl
    5893:	75 eb                	jne    5880 <handle_http_method+0x50>
    5895:	4c 89 fa             	mov    %r15,%rdx
    5898:	4c 89 f6             	mov    %r14,%rsi
    589b:	31 ff                	xor    %edi,%edi
    589d:	e8 3e cb ff ff       	call   23e0 <strtok_r@plt>
    58a2:	48 8d 35 b1 28 00 00 	lea    0x28b1(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    58a9:	48 89 ef             	mov    %rbp,%rdi
    58ac:	48 89 c3             	mov    %rax,%rbx
    58af:	e8 5c cb ff ff       	call   2410 <strcmp@plt>
    58b4:	4c 89 ea             	mov    %r13,%rdx
    58b7:	44 89 e6             	mov    %r12d,%esi
    58ba:	85 c0                	test   %eax,%eax
    58bc:	75 2a                	jne    58e8 <handle_http_method+0xb8>
    58be:	48 89 df             	mov    %rbx,%rdi
    58c1:	e8 3a fd ff ff       	call   5600 <handle_get_method>
    58c6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    58cb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    58d4:	75 20                	jne    58f6 <handle_http_method+0xc6>
    58d6:	48 83 c4 18          	add    $0x18,%rsp
    58da:	5b                   	pop    %rbx
    58db:	5d                   	pop    %rbp
    58dc:	41 5c                	pop    %r12
    58de:	41 5d                	pop    %r13
    58e0:	41 5e                	pop    %r14
    58e2:	41 5f                	pop    %r15
    58e4:	c3                   	ret
    58e5:	0f 1f 00             	nopl   (%rax)
    58e8:	48 8b 3d 29 57 00 00 	mov    0x5729(%rip),%rdi        # b018 <unimplemented_content>
    58ef:	e8 9c fb ff ff       	call   5490 <_send_static_string_content>
    58f4:	eb d0                	jmp    58c6 <handle_http_method+0x96>
    58f6:	e8 85 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    58fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005900 <get_line>:
    5900:	f3 0f 1e fa          	endbr64
    5904:	85 d2                	test   %edx,%edx
    5906:	7e 38                	jle    5940 <get_line+0x40>
    5908:	48 63 d2             	movslq %edx,%rdx
    590b:	48 83 c7 01          	add    $0x1,%rdi
    590f:	48 01 f2             	add    %rsi,%rdx
    5912:	eb 11                	jmp    5925 <get_line+0x25>
    5914:	0f 1f 40 00          	nopl   0x0(%rax)
    5918:	48 83 c6 01          	add    $0x1,%rsi
    591c:	48 83 c7 01          	add    $0x1,%rdi
    5920:	48 39 d6             	cmp    %rdx,%rsi
    5923:	74 1b                	je     5940 <get_line+0x40>
    5925:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5929:	88 06                	mov    %al,(%rsi)
    592b:	3c 0d                	cmp    $0xd,%al
    592d:	75 e9                	jne    5918 <get_line+0x18>
    592f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5932:	75 e4                	jne    5918 <get_line+0x18>
    5934:	c6 06 00             	movb   $0x0,(%rsi)
    5937:	31 c0                	xor    %eax,%eax
    5939:	c3                   	ret
    593a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5940:	b8 01 00 00 00       	mov    $0x1,%eax
    5945:	c3                   	ret
    5946:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005950 <handle_client_request>:
    5950:	f3 0f 1e fa          	endbr64
    5954:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    595b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    595f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5968:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5970:	31 c0                	xor    %eax,%eax
    5972:	49 89 e2             	mov    %rsp,%r10
    5975:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    597d:	4c 89 d0             	mov    %r10,%rax
    5980:	eb 13                	jmp    5995 <handle_client_request+0x45>
    5982:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5988:	48 83 c0 01          	add    $0x1,%rax
    598c:	48 83 c1 01          	add    $0x1,%rcx
    5990:	4c 39 c8             	cmp    %r9,%rax
    5993:	74 4b                	je     59e0 <handle_client_request+0x90>
    5995:	44 0f b6 01          	movzbl (%rcx),%r8d
    5999:	44 88 00             	mov    %r8b,(%rax)
    599c:	41 80 f8 0d          	cmp    $0xd,%r8b
    59a0:	75 e6                	jne    5988 <handle_client_request+0x38>
    59a2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    59a6:	75 e0                	jne    5988 <handle_client_request+0x38>
    59a8:	c6 00 00             	movb   $0x0,(%rax)
    59ab:	8b 47 08             	mov    0x8(%rdi),%eax
    59ae:	48 89 f2             	mov    %rsi,%rdx
    59b1:	4c 89 d7             	mov    %r10,%rdi
    59b4:	89 c6                	mov    %eax,%esi
    59b6:	e8 75 fe ff ff       	call   5830 <handle_http_method>
    59bb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    59c3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    59cc:	75 39                	jne    5a07 <handle_client_request+0xb7>
    59ce:	31 c0                	xor    %eax,%eax
    59d0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    59d7:	c3                   	ret
    59d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    59e0:	48 8b 0d 39 56 00 00 	mov    0x5639(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    59e7:	ba 12 00 00 00       	mov    $0x12,%edx
    59ec:	be 01 00 00 00       	mov    $0x1,%esi
    59f1:	48 8d 3d 66 27 00 00 	lea    0x2766(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    59f8:	e8 33 cb ff ff       	call   2530 <fwrite@plt>
    59fd:	bf 01 00 00 00       	mov    $0x1,%edi
    5a02:	e8 09 cb ff ff       	call   2510 <exit@plt>
    5a07:	e8 74 c9 ff ff       	call   2380 <__stack_chk_fail@plt>
    5a0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005a10 <add_accept_request>:
    5a10:	f3 0f 1e fa          	endbr64
    5a14:	55                   	push   %rbp
    5a15:	53                   	push   %rbx
    5a16:	48 89 cb             	mov    %rcx,%rbx
    5a19:	48 83 ec 08          	sub    $0x8,%rsp
    5a1d:	8b 41 44             	mov    0x44(%rcx),%eax
    5a20:	4c 8b 03             	mov    (%rbx),%r8
    5a23:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    5a29:	83 c0 01             	add    $0x1,%eax
    5a2c:	45 8b 08             	mov    (%r8),%r9d
    5a2f:	f6 c1 02             	test   $0x2,%cl
    5a32:	74 00                	je     5a34 <add_accept_request+0x24>
    5a34:	41 89 c0             	mov    %eax,%r8d
    5a37:	45 29 c8             	sub    %r9d,%r8d
    5a3a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    5a3e:	0f 82 c8 cb ff ff    	jb     260c <add_accept_request.cold>
    5a44:	c1 e9 0a             	shr    $0xa,%ecx
    5a47:	8b 6b 44             	mov    0x44(%rbx),%ebp
    5a4a:	23 6b 58             	and    0x58(%rbx),%ebp
    5a4d:	89 43 44             	mov    %eax,0x44(%rbx)
    5a50:	83 e1 01             	and    $0x1,%ecx
    5a53:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5a57:	d3 e5                	shl    %cl,%ebp
    5a59:	48 c1 e5 06          	shl    $0x6,%rbp
    5a5d:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5a61:	89 7d 04             	mov    %edi,0x4(%rbp)
    5a64:	bf 10 00 00 00       	mov    $0x10,%edi
    5a69:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    5a70:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    5a74:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    5a78:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    5a80:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    5a88:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5a8c:	e8 df c9 ff ff       	call   2470 <malloc@plt>
    5a91:	48 89 df             	mov    %rbx,%rdi
    5a94:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    5a9a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    5a9e:	48 83 c4 08          	add    $0x8,%rsp
    5aa2:	5b                   	pop    %rbx
    5aa3:	5d                   	pop    %rbp
    5aa4:	e9 e7 c8 ff ff       	jmp    2390 <io_uring_submit@plt>
    5aa9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005ab0 <io_thread>:
    5ab0:	f3 0f 1e fa          	endbr64
    5ab4:	41 57                	push   %r15
    5ab6:	31 d2                	xor    %edx,%edx
    5ab8:	41 56                	push   %r14
    5aba:	41 55                	push   %r13
    5abc:	41 54                	push   %r12
    5abe:	55                   	push   %rbp
    5abf:	48 89 fd             	mov    %rdi,%rbp
    5ac2:	53                   	push   %rbx
    5ac3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    5aca:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5ad3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    5adb:	48 8b 47 58          	mov    0x58(%rdi),%rax
    5adf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5ae4:	bf 00 01 00 00       	mov    $0x100,%edi
    5ae9:	48 89 de             	mov    %rbx,%rsi
    5aec:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5af0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5af5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5afa:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    5aff:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5b04:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    5b0c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5b11:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5b19:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5b1e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5b26:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5b2b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5b33:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5b38:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5b40:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5b45:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    5b4d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5b55:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5b5d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5b65:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5b6d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5b75:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5b7d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5b85:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5b8d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5b95:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5b9d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5ba4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    5bac:	e8 9f c8 ff ff       	call   2450 <io_uring_queue_init@plt>
    5bb1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5bb5:	31 f6                	xor    %esi,%esi
    5bb7:	e8 94 c9 ff ff       	call   2550 <io_uring_register_eventfd@plt>
    5bbc:	31 d2                	xor    %edx,%edx
    5bbe:	be 01 00 00 00       	mov    $0x1,%esi
    5bc3:	bf 02 00 00 00       	mov    $0x2,%edi
    5bc8:	e8 e3 c9 ff ff       	call   25b0 <socket@plt>
    5bcd:	83 f8 ff             	cmp    $0xffffffff,%eax
    5bd0:	0f 84 78 ca ff ff    	je     264e <io_thread.cold+0x38>
    5bd6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5bdb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5be1:	89 c7                	mov    %eax,%edi
    5be3:	41 89 c4             	mov    %eax,%r12d
    5be6:	ba 02 00 00 00       	mov    $0x2,%edx
    5beb:	be 01 00 00 00       	mov    $0x1,%esi
    5bf0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    5bf8:	e8 43 c7 ff ff       	call   2340 <setsockopt@plt>
    5bfd:	85 c0                	test   %eax,%eax
    5bff:	0f 88 1d ca ff ff    	js     2622 <io_thread.cold+0xc>
    5c05:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    5c0a:	ba 10 00 00 00       	mov    $0x10,%edx
    5c0f:	44 89 e7             	mov    %r12d,%edi
    5c12:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5c1b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    5c23:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
    5c2b:	e8 90 c8 ff ff       	call   24c0 <bind@plt>
    5c30:	85 c0                	test   %eax,%eax
    5c32:	0f 88 22 ca ff ff    	js     265a <io_thread.cold+0x44>
    5c38:	be 0a 00 00 00       	mov    $0xa,%esi
    5c3d:	44 89 e7             	mov    %r12d,%edi
    5c40:	e8 3b c8 ff ff       	call   2480 <listen@plt>
    5c45:	85 c0                	test   %eax,%eax
    5c47:	0f 88 e1 c9 ff ff    	js     262e <io_thread.cold+0x18>
    5c4d:	ba db 18 00 00       	mov    $0x18db,%edx
    5c52:	48 8d 35 4a 25 00 00 	lea    0x254a(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5c59:	bf 01 00 00 00       	mov    $0x1,%edi
    5c5e:	31 c0                	xor    %eax,%eax
    5c60:	e8 4b c8 ff ff       	call   24b0 <__printf_chk@plt>
    5c65:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5c6a:	48 89 d9             	mov    %rbx,%rcx
    5c6d:	44 89 e7             	mov    %r12d,%edi
    5c70:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5c75:	48 89 c6             	mov    %rax,%rsi
    5c78:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5c7d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    5c82:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    5c8a:	e8 81 fd ff ff       	call   5a10 <add_accept_request>
    5c8f:	bf 01 00 00 00       	mov    $0x1,%edi
    5c94:	be 10 00 00 00       	mov    $0x10,%esi
    5c99:	e8 62 c7 ff ff       	call   2400 <calloc@plt>
    5c9e:	bf 0a 00 00 00       	mov    $0xa,%edi
    5ca3:	49 89 c5             	mov    %rax,%r13
    5ca6:	e8 c5 c7 ff ff       	call   2470 <malloc@plt>
    5cab:	48 85 c0             	test   %rax,%rax
    5cae:	0f 84 ae 04 00 00    	je     6162 <io_thread+0x6b2>
    5cb4:	49 89 45 00          	mov    %rax,0x0(%r13)
    5cb8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5cbf:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5cc6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    5cce:	8d 50 01             	lea    0x1(%rax),%edx
    5cd1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5cd6:	8b 30                	mov    (%rax),%esi
    5cd8:	f6 c1 02             	test   $0x2,%cl
    5cdb:	0f 85 0f 04 00 00    	jne    60f0 <io_thread+0x640>
    5ce1:	89 d0                	mov    %edx,%eax
    5ce3:	29 f0                	sub    %esi,%eax
    5ce5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5cec:	0f 82 52 c9 ff ff    	jb     2644 <io_thread.cold+0x2e>
    5cf2:	c1 e9 0a             	shr    $0xa,%ecx
    5cf5:	48 8d 75 60          	lea    0x60(%rbp),%rsi
    5cf9:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5cfd:	48 89 df             	mov    %rbx,%rdi
    5d00:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5d07:	83 e1 01             	and    $0x1,%ecx
    5d0a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5d11:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5d18:	d3 e0                	shl    %cl,%eax
    5d1a:	8b 55 60             	mov    0x60(%rbp),%edx
    5d1d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5d22:	48 c1 e0 06          	shl    $0x6,%rax
    5d26:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5d2e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5d34:	89 50 04             	mov    %edx,0x4(%rax)
    5d37:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5d3f:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5d43:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5d4b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5d53:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5d57:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5d5b:	e8 30 c6 ff ff       	call   2390 <io_uring_submit@plt>
    5d60:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5d64:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5d69:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5d71:	0f 85 d7 01 00 00    	jne    5f4e <io_thread+0x49e>
    5d77:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5d7c:	4d 89 ce             	mov    %r9,%r14
    5d7f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5d84:	0f 1f 40 00          	nopl   0x0(%rax)
    5d88:	48 8d 3d 2a 24 00 00 	lea    0x242a(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5d8f:	e8 9c c5 ff ff       	call   2330 <puts@plt>
    5d94:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5d9b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    5da2:	c1 e9 0b             	shr    $0xb,%ecx
    5da5:	83 e1 01             	and    $0x1,%ecx
    5da8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5db0:	8b 00                	mov    (%rax),%eax
    5db2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5dba:	8b 16                	mov    (%rsi),%edx
    5dbc:	39 d0                	cmp    %edx,%eax
    5dbe:	74 36                	je     5df6 <io_thread+0x346>
    5dc0:	89 f8                	mov    %edi,%eax
    5dc2:	21 d0                	and    %edx,%eax
    5dc4:	d3 e0                	shl    %cl,%eax
    5dc6:	48 c1 e0 04          	shl    $0x4,%rax
    5dca:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    5dd2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5dda:	0f 85 a8 01 00 00    	jne    5f88 <io_thread+0x4d8>
    5de0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5de4:	0f 85 0e 03 00 00    	jne    60f8 <io_thread+0x648>
    5dea:	8b 40 08             	mov    0x8(%rax),%eax
    5ded:	83 c2 01             	add    $0x1,%edx
    5df0:	89 16                	mov    %edx,(%rsi)
    5df2:	85 c0                	test   %eax,%eax
    5df4:	79 b2                	jns    5da8 <io_thread+0x2f8>
    5df6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    5dff:	90                   	nop
    5e00:	45 31 c0             	xor    %r8d,%r8d
    5e03:	31 d2                	xor    %edx,%edx
    5e05:	b9 01 00 00 00       	mov    $0x1,%ecx
    5e0a:	4c 89 f6             	mov    %r14,%rsi
    5e0d:	48 89 df             	mov    %rbx,%rdi
    5e10:	e8 8b c6 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5e15:	41 89 c7             	mov    %eax,%r15d
    5e18:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5e1d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5e21:	0f 84 e1 02 00 00    	je     6108 <io_thread+0x658>
    5e27:	48 8d 3d b1 23 00 00 	lea    0x23b1(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5e2e:	e8 fd c4 ff ff       	call   2330 <puts@plt>
    5e33:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5e38:	4c 8b 22             	mov    (%rdx),%r12
    5e3b:	45 85 ff             	test   %r15d,%r15d
    5e3e:	0f 88 d2 c7 ff ff    	js     2616 <io_thread.cold>
    5e44:	8b 42 08             	mov    0x8(%rdx),%eax
    5e47:	45 8b 04 24          	mov    (%r12),%r8d
    5e4b:	85 c0                	test   %eax,%eax
    5e4d:	0f 88 d5 02 00 00    	js     6128 <io_thread+0x678>
    5e53:	41 83 f8 01          	cmp    $0x1,%r8d
    5e57:	0f 84 7b 01 00 00    	je     5fd8 <io_thread+0x528>
    5e5d:	41 83 f8 02          	cmp    $0x2,%r8d
    5e61:	0f 84 a1 01 00 00    	je     6008 <io_thread+0x558>
    5e67:	45 85 c0             	test   %r8d,%r8d
    5e6a:	0f 85 50 01 00 00    	jne    5fc0 <io_thread+0x510>
    5e70:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5e75:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5e7a:	48 89 d9             	mov    %rbx,%rcx
    5e7d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5e81:	e8 8a fb ff ff       	call   5a10 <add_accept_request>
    5e86:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5e8b:	48 89 de             	mov    %rbx,%rsi
    5e8e:	8b 78 08             	mov    0x8(%rax),%edi
    5e91:	e8 1a f5 ff ff       	call   53b0 <add_read_request>
    5e96:	4c 89 e7             	mov    %r12,%rdi
    5e99:	e8 62 c4 ff ff       	call   2300 <free@plt>
    5e9e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5ea3:	48 85 c0             	test   %rax,%rax
    5ea6:	0f 85 14 01 00 00    	jne    5fc0 <io_thread+0x510>
    5eac:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5eb3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5eba:	8d 50 01             	lea    0x1(%rax),%edx
    5ebd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5ec2:	8b 30                	mov    (%rax),%esi
    5ec4:	f6 c1 02             	test   $0x2,%cl
    5ec7:	74 00                	je     5ec9 <io_thread+0x419>
    5ec9:	89 d0                	mov    %edx,%eax
    5ecb:	29 f0                	sub    %esi,%eax
    5ecd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5ed4:	0f 82 60 c7 ff ff    	jb     263a <io_thread.cold+0x24>
    5eda:	c1 e9 0a             	shr    $0xa,%ecx
    5edd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5ee2:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5ee6:	48 89 df             	mov    %rbx,%rdi
    5ee9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5ef0:	83 e1 01             	and    $0x1,%ecx
    5ef3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5efa:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5f01:	d3 e0                	shl    %cl,%eax
    5f03:	8b 55 60             	mov    0x60(%rbp),%edx
    5f06:	48 c1 e0 06          	shl    $0x6,%rax
    5f0a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5f12:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5f18:	89 50 04             	mov    %edx,0x4(%rax)
    5f1b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5f23:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5f27:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5f2f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5f37:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5f3b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5f3f:	e8 4c c4 ff ff       	call   2390 <io_uring_submit@plt>
    5f44:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5f48:	0f 84 3a fe ff ff    	je     5d88 <io_thread+0x2d8>
    5f4e:	48 8d 3d c3 22 00 00 	lea    0x22c3(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5f55:	e8 d6 c3 ff ff       	call   2330 <puts@plt>
    5f5a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5f62:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5f6b:	0f 85 18 02 00 00    	jne    6189 <io_thread+0x6d9>
    5f71:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5f78:	31 c0                	xor    %eax,%eax
    5f7a:	5b                   	pop    %rbx
    5f7b:	5d                   	pop    %rbp
    5f7c:	41 5c                	pop    %r12
    5f7e:	41 5d                	pop    %r13
    5f80:	41 5e                	pop    %r14
    5f82:	41 5f                	pop    %r15
    5f84:	c3                   	ret
    5f85:	0f 1f 00             	nopl   (%rax)
    5f88:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    5f8d:	48 85 c0             	test   %rax,%rax
    5f90:	0f 84 6a fe ff ff    	je     5e00 <io_thread+0x350>
    5f96:	48 83 38 01          	cmpq   $0x1,(%rax)
    5f9a:	0f 84 68 01 00 00    	je     6108 <io_thread+0x658>
    5fa0:	48 8d 3d 38 22 00 00 	lea    0x2238(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5fa7:	e8 84 c3 ff ff       	call   2330 <puts@plt>
    5fac:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5fb1:	4c 8b 22             	mov    (%rdx),%r12
    5fb4:	e9 8b fe ff ff       	jmp    5e44 <io_thread+0x394>
    5fb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5fc0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5fc8:	8b 02                	mov    (%rdx),%eax
    5fca:	83 c0 01             	add    $0x1,%eax
    5fcd:	89 02                	mov    %eax,(%rdx)
    5fcf:	e9 d8 fe ff ff       	jmp    5eac <io_thread+0x3fc>
    5fd4:	0f 1f 40 00          	nopl   0x0(%rax)
    5fd8:	85 c0                	test   %eax,%eax
    5fda:	75 74                	jne    6050 <io_thread+0x5a0>
    5fdc:	48 8b 0d 3d 50 00 00 	mov    0x503d(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5fe3:	ba 0f 00 00 00       	mov    $0xf,%edx
    5fe8:	be 01 00 00 00       	mov    $0x1,%esi
    5fed:	48 8d 3d 14 22 00 00 	lea    0x2214(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5ff4:	e8 37 c5 ff ff       	call   2530 <fwrite@plt>
    5ff9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5ffe:	e9 a0 fe ff ff       	jmp    5ea3 <io_thread+0x3f3>
    6003:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6008:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    600d:	45 31 ff             	xor    %r15d,%r15d
    6010:	85 c0                	test   %eax,%eax
    6012:	7e 20                	jle    6034 <io_thread+0x584>
    6014:	0f 1f 40 00          	nopl   0x0(%rax)
    6018:	4c 89 f8             	mov    %r15,%rax
    601b:	49 83 c7 01          	add    $0x1,%r15
    601f:	48 c1 e0 04          	shl    $0x4,%rax
    6023:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    6028:	e8 d3 c2 ff ff       	call   2300 <free@plt>
    602d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    6032:	7f e4                	jg     6018 <io_thread+0x568>
    6034:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    6039:	e8 92 c3 ff ff       	call   23d0 <close@plt>
    603e:	4c 89 e7             	mov    %r12,%rdi
    6041:	e8 ba c2 ff ff       	call   2300 <free@plt>
    6046:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    604b:	e9 53 fe ff ff       	jmp    5ea3 <io_thread+0x3f3>
    6050:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    6055:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    605a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    6062:	eb 11                	jmp    6075 <io_thread+0x5c5>
    6064:	0f 1f 40 00          	nopl   0x0(%rax)
    6068:	48 83 c0 01          	add    $0x1,%rax
    606c:	48 83 c2 01          	add    $0x1,%rdx
    6070:	48 39 c6             	cmp    %rax,%rsi
    6073:	74 4b                	je     60c0 <io_thread+0x610>
    6075:	0f b6 0a             	movzbl (%rdx),%ecx
    6078:	88 08                	mov    %cl,(%rax)
    607a:	80 f9 0d             	cmp    $0xd,%cl
    607d:	75 e9                	jne    6068 <io_thread+0x5b8>
    607f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    6083:	75 e3                	jne    6068 <io_thread+0x5b8>
    6085:	c6 00 00             	movb   $0x0,(%rax)
    6088:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    608d:	48 89 da             	mov    %rbx,%rdx
    6090:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    6095:	e8 96 f7 ff ff       	call   5830 <handle_http_method>
    609a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    609f:	e8 5c c2 ff ff       	call   2300 <free@plt>
    60a4:	4c 89 e7             	mov    %r12,%rdi
    60a7:	e8 54 c2 ff ff       	call   2300 <free@plt>
    60ac:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    60b1:	e9 ed fd ff ff       	jmp    5ea3 <io_thread+0x3f3>
    60b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    60c0:	48 8b 0d 59 4f 00 00 	mov    0x4f59(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    60c7:	ba 12 00 00 00       	mov    $0x12,%edx
    60cc:	be 01 00 00 00       	mov    $0x1,%esi
    60d1:	48 8d 3d 86 20 00 00 	lea    0x2086(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    60d8:	e8 53 c4 ff ff       	call   2530 <fwrite@plt>
    60dd:	bf 01 00 00 00       	mov    $0x1,%edi
    60e2:	e8 29 c4 ff ff       	call   2510 <exit@plt>
    60e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    60f0:	e9 ec fb ff ff       	jmp    5ce1 <io_thread+0x231>
    60f5:	0f 1f 00             	nopl   (%rax)
    60f8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    60fd:	e9 94 fe ff ff       	jmp    5f96 <io_thread+0x4e6>
    6102:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6108:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    6110:	48 8d 3d b4 20 00 00 	lea    0x20b4(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    6117:	8b 02                	mov    (%rdx),%eax
    6119:	83 c0 01             	add    $0x1,%eax
    611c:	89 02                	mov    %eax,(%rdx)
    611e:	e8 0d c2 ff ff       	call   2330 <puts@plt>
    6123:	e9 26 fe ff ff       	jmp    5f4e <io_thread+0x49e>
    6128:	f7 d8                	neg    %eax
    612a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    612f:	89 c7                	mov    %eax,%edi
    6131:	e8 3a c4 ff ff       	call   2570 <strerror@plt>
    6136:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    613b:	be 01 00 00 00       	mov    $0x1,%esi
    6140:	48 8b 3d d9 4e 00 00 	mov    0x4ed9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    6147:	48 89 c1             	mov    %rax,%rcx
    614a:	48 8d 15 97 24 00 00 	lea    0x2497(%rip),%rdx        # 85e8 <_IO_stdin_used+0x5e8>
    6151:	31 c0                	xor    %eax,%eax
    6153:	e8 e8 c3 ff ff       	call   2540 <__fprintf_chk@plt>
    6158:	bf 01 00 00 00       	mov    $0x1,%edi
    615d:	e8 ae c3 ff ff       	call   2510 <exit@plt>
    6162:	48 8b 0d b7 4e 00 00 	mov    0x4eb7(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6169:	ba 28 00 00 00       	mov    $0x28,%edx
    616e:	be 01 00 00 00       	mov    $0x1,%esi
    6173:	48 8d 3d 3e 24 00 00 	lea    0x243e(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    617a:	e8 b1 c3 ff ff       	call   2530 <fwrite@plt>
    617f:	bf 01 00 00 00       	mov    $0x1,%edi
    6184:	e8 87 c3 ff ff       	call   2510 <exit@plt>
    6189:	e8 f2 c1 ff ff       	call   2380 <__stack_chk_fail@plt>
    618e:	66 90                	xchg   %ax,%ax

0000000000006190 <barriered_work_ingest>:
    6190:	f3 0f 1e fa          	endbr64
    6194:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    619b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    61a1:	85 c9                	test   %ecx,%ecx
    61a3:	0f 8e ea 00 00 00    	jle    6293 <barriered_work_ingest+0x103>
    61a9:	41 56                	push   %r14
    61ab:	41 55                	push   %r13
    61ad:	45 31 ed             	xor    %r13d,%r13d
    61b0:	41 54                	push   %r12
    61b2:	49 89 fc             	mov    %rdi,%r12
    61b5:	55                   	push   %rbp
    61b6:	53                   	push   %rbx
    61b7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    61bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    61c0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    61c4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    61cc:	31 db                	xor    %ebx,%ebx
    61ce:	8b 10                	mov    (%rax),%edx
    61d0:	85 d2                	test   %edx,%edx
    61d2:	7e 26                	jle    61fa <barriered_work_ingest+0x6a>
    61d4:	48 8b 48 08          	mov    0x8(%rax),%rcx
    61d8:	48 89 dd             	mov    %rbx,%rbp
    61db:	48 c1 e5 08          	shl    $0x8,%rbp
    61df:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    61e3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    61ea:	74 24                	je     6210 <barriered_work_ingest+0x80>
    61ec:	48 83 c3 01          	add    $0x1,%rbx
    61f0:	39 da                	cmp    %ebx,%edx
    61f2:	7f e4                	jg     61d8 <barriered_work_ingest+0x48>
    61f4:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    61fa:	49 83 c5 01          	add    $0x1,%r13
    61fe:	44 39 e9             	cmp    %r13d,%ecx
    6201:	7f bd                	jg     61c0 <barriered_work_ingest+0x30>
    6203:	5b                   	pop    %rbx
    6204:	31 c0                	xor    %eax,%eax
    6206:	5d                   	pop    %rbp
    6207:	41 5c                	pop    %r12
    6209:	41 5d                	pop    %r13
    620b:	41 5e                	pop    %r14
    620d:	c3                   	ret
    620e:	66 90                	xchg   %ax,%ax
    6210:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
    6219:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    6220:	bf 04 00 00 00       	mov    $0x4,%edi
    6225:	48 c1 e6 05          	shl    $0x5,%rsi
    6229:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    6230:	48 83 c6 10          	add    $0x10,%rsi
    6234:	e8 17 c1 ff ff       	call   2350 <clock_gettime@plt>
    6239:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    6241:	48 8b 40 50          	mov    0x50(%rax),%rax
    6245:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    6249:	48 03 68 08          	add    0x8(%rax),%rbp
    624d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    6257:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    625d:	83 c0 01             	add    $0x1,%eax
    6260:	99                   	cltd
    6261:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    6267:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
    626d:	0f ae f8             	sfence
    6270:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    6278:	48 83 c3 01          	add    $0x1,%rbx
    627c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6280:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    6284:	8b 10                	mov    (%rax),%edx
    6286:	39 da                	cmp    %ebx,%edx
    6288:	0f 8f 46 ff ff ff    	jg     61d4 <barriered_work_ingest+0x44>
    628e:	e9 61 ff ff ff       	jmp    61f4 <barriered_work_ingest+0x64>
    6293:	31 c0                	xor    %eax,%eax
    6295:	c3                   	ret
    6296:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000062a0 <barriered_thread>:
    62a0:	f3 0f 1e fa          	endbr64
    62a4:	41 56                	push   %r14
    62a6:	41 55                	push   %r13
    62a8:	41 54                	push   %r12
    62aa:	45 31 e4             	xor    %r12d,%r12d
    62ad:	55                   	push   %rbp
    62ae:	31 ed                	xor    %ebp,%ebp
    62b0:	53                   	push   %rbx
    62b1:	48 89 fb             	mov    %rdi,%rbx
    62b4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    62b8:	0f 85 74 02 00 00    	jne    6532 <barriered_thread+0x292>
    62be:	8b 43 40             	mov    0x40(%rbx),%eax
    62c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    62c8:	41 39 c4             	cmp    %eax,%r12d
    62cb:	0f 8d 6f 01 00 00    	jge    6440 <barriered_thread+0x1a0>
    62d1:	49 63 fc             	movslq %r12d,%rdi
    62d4:	48 c1 e7 09          	shl    $0x9,%rdi
    62d8:	49 89 fd             	mov    %rdi,%r13
    62db:	eb 32                	jmp    630f <barriered_thread+0x6f>
    62dd:	0f 1f 00             	nopl   (%rax)
    62e0:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    62e4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    62e8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    62ec:	48 8b 78 38          	mov    0x38(%rax),%rdi
    62f0:	4c 01 ef             	add    %r13,%rdi
    62f3:	e8 98 fe ff ff       	call   6190 <barriered_work_ingest>
    62f8:	8b 43 40             	mov    0x40(%rbx),%eax
    62fb:	41 83 c4 01          	add    $0x1,%r12d
    62ff:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    6306:	44 39 e0             	cmp    %r12d,%eax
    6309:	0f 8e 19 02 00 00    	jle    6528 <barriered_thread+0x288>
    630f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6313:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    6317:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    631e:	75 c0                	jne    62e0 <barriered_thread+0x40>
    6320:	44 8b 43 28          	mov    0x28(%rbx),%r8d
    6324:	83 e8 01             	sub    $0x1,%eax
    6327:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    632c:	45 85 e4             	test   %r12d,%r12d
    632f:	0f 4f c1             	cmovg  %ecx,%eax
    6332:	45 85 c0             	test   %r8d,%r8d
    6335:	0f 8e 2d 01 00 00    	jle    6468 <barriered_thread+0x1c8>
    633b:	48 63 c8             	movslq %eax,%rcx
    633e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6342:	49 63 d0             	movslq %r8d,%rdx
    6345:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
    634b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    6352:	48 c1 e1 09          	shl    $0x9,%rcx
    6356:	45 31 d2             	xor    %r10d,%r10d
    6359:	45 31 f6             	xor    %r14d,%r14d
    635c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6360:	48 8b 10             	mov    (%rax),%rdx
    6363:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6367:	49 01 cb             	add    %rcx,%r11
    636a:	4c 89 da             	mov    %r11,%rdx
    636d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6374:	75 04                	jne    637a <barriered_thread+0xda>
    6376:	41 83 c6 01          	add    $0x1,%r14d
    637a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6380:	75 04                	jne    6386 <barriered_thread+0xe6>
    6382:	41 83 c2 01          	add    $0x1,%r10d
    6386:	48 83 c0 08          	add    $0x8,%rax
    638a:	48 39 c6             	cmp    %rax,%rsi
    638d:	75 d1                	jne    6360 <barriered_thread+0xc0>
    638f:	45 85 d2             	test   %r10d,%r10d
    6392:	0f 84 c0 00 00 00    	je     6458 <barriered_thread+0x1b8>
    6398:	45 39 d0             	cmp    %r10d,%r8d
    639b:	0f 84 b7 00 00 00    	je     6458 <barriered_thread+0x1b8>
    63a1:	45 85 f6             	test   %r14d,%r14d
    63a4:	74 0a                	je     63b0 <barriered_thread+0x110>
    63a6:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    63aa:	0f 85 ae 01 00 00    	jne    655e <barriered_thread+0x2be>
    63b0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    63b4:	4c 01 ea             	add    %r13,%rdx
    63b7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
    63be:	45 85 e4             	test   %r12d,%r12d
    63c1:	75 14                	jne    63d7 <barriered_thread+0x137>
    63c3:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    63ca:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    63d1:	0f 8c 69 01 00 00    	jl     6540 <barriered_thread+0x2a0>
    63d7:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    63db:	48 8b 43 18          	mov    0x18(%rbx),%rax
    63df:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
    63e9:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    63ed:	48 8b 78 38          	mov    0x38(%rax),%rdi
    63f1:	4c 01 ef             	add    %r13,%rdi
    63f4:	ff 92 18 01 00 00    	call   *0x118(%rdx)
    63fa:	48 8b 43 38          	mov    0x38(%rbx),%rax
    63fe:	4c 01 e8             	add    %r13,%rax
    6401:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    6408:	8b 43 40             	mov    0x40(%rbx),%eax
    640b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
    6410:	83 e8 01             	sub    $0x1,%eax
    6413:	44 39 e0             	cmp    %r12d,%eax
    6416:	0f 84 a4 00 00 00    	je     64c0 <barriered_thread+0x220>
    641c:	0f ae f8             	sfence
    641f:	85 ed                	test   %ebp,%ebp
    6421:	0f 84 d1 00 00 00    	je     64f8 <barriered_thread+0x258>
    6427:	bd 01 00 00 00       	mov    $0x1,%ebp
    642c:	e9 c7 fe ff ff       	jmp    62f8 <barriered_thread+0x58>
    6431:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6435:	0f 85 f7 00 00 00    	jne    6532 <barriered_thread+0x292>
    643b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6440:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    6448:	85 c0                	test   %eax,%eax
    644a:	7e e5                	jle    6431 <barriered_thread+0x191>
    644c:	45 31 e4             	xor    %r12d,%r12d
    644f:	e9 7d fe ff ff       	jmp    62d1 <barriered_thread+0x31>
    6454:	0f 1f 40 00          	nopl   0x0(%rax)
    6458:	83 fd 01             	cmp    $0x1,%ebp
    645b:	74 1b                	je     6478 <barriered_thread+0x1d8>
    645d:	31 ed                	xor    %ebp,%ebp
    645f:	e9 3d ff ff ff       	jmp    63a1 <barriered_thread+0x101>
    6464:	0f 1f 40 00          	nopl   0x0(%rax)
    6468:	83 fd 01             	cmp    $0x1,%ebp
    646b:	0f 85 43 ff ff ff    	jne    63b4 <barriered_thread+0x114>
    6471:	45 31 f6             	xor    %r14d,%r14d
    6474:	0f 1f 40 00          	nopl   0x0(%rax)
    6478:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    647f:	bf 04 00 00 00       	mov    $0x4,%edi
    6484:	31 ed                	xor    %ebp,%ebp
    6486:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    648a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6491:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6496:	e8 b5 be ff ff       	call   2350 <clock_gettime@plt>
    649b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    64a2:	48 83 c0 01          	add    $0x1,%rax
    64a6:	48 99                	cqto
    64a8:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    64af:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
    64b6:	e9 e6 fe ff ff       	jmp    63a1 <barriered_thread+0x101>
    64bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    64c0:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    64c7:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    64ce:	0f 8d 48 ff ff ff    	jge    641c <barriered_thread+0x17c>
    64d4:	48 c1 e6 04          	shl    $0x4,%rsi
    64d8:	bf 04 00 00 00       	mov    $0x4,%edi
    64dd:	48 03 73 70          	add    0x70(%rbx),%rsi
    64e1:	e8 6a be ff ff       	call   2350 <clock_gettime@plt>
    64e6:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    64ee:	e9 29 ff ff ff       	jmp    641c <barriered_thread+0x17c>
    64f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    64f8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    64ff:	bf 04 00 00 00       	mov    $0x4,%edi
    6504:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6508:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    650f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6513:	44 89 66 20          	mov    %r12d,0x20(%rsi)
    6517:	e8 34 be ff ff       	call   2350 <clock_gettime@plt>
    651c:	e9 06 ff ff ff       	jmp    6427 <barriered_thread+0x187>
    6521:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6528:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    652c:	0f 84 96 fd ff ff    	je     62c8 <barriered_thread+0x28>
    6532:	5b                   	pop    %rbx
    6533:	31 c0                	xor    %eax,%eax
    6535:	5d                   	pop    %rbp
    6536:	41 5c                	pop    %r12
    6538:	41 5d                	pop    %r13
    653a:	41 5e                	pop    %r14
    653c:	c3                   	ret
    653d:	0f 1f 00             	nopl   (%rax)
    6540:	48 c1 e6 04          	shl    $0x4,%rsi
    6544:	bf 04 00 00 00       	mov    $0x4,%edi
    6549:	48 03 73 68          	add    0x68(%rbx),%rsi
    654d:	e8 fe bd ff ff       	call   2350 <clock_gettime@plt>
    6552:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6556:	4c 01 ea             	add    %r13,%rdx
    6559:	e9 79 fe ff ff       	jmp    63d7 <barriered_thread+0x137>
    655e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6562:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6566:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    656a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    656e:	4c 01 ef             	add    %r13,%rdi
    6571:	e8 1a fc ff ff       	call   6190 <barriered_work_ingest>
    6576:	e9 39 fd ff ff       	jmp    62b4 <barriered_thread+0x14>
    657b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006580 <receive>:
    6580:	f3 0f 1e fa          	endbr64
    6584:	41 57                	push   %r15
    6586:	41 56                	push   %r14
    6588:	41 55                	push   %r13
    658a:	41 54                	push   %r12
    658c:	55                   	push   %rbp
    658d:	53                   	push   %rbx
    658e:	48 83 ec 08          	sub    $0x8,%rsp
    6592:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    6599:	45 85 f6             	test   %r14d,%r14d
    659c:	0f 8e 37 01 00 00    	jle    66d9 <receive+0x159>
    65a2:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    65a9:	48 89 fe             	mov    %rdi,%rsi
    65ac:	45 31 e4             	xor    %r12d,%r12d
    65af:	31 db                	xor    %ebx,%ebx
    65b1:	49 63 6f 08          	movslq 0x8(%r15),%rbp
    65b5:	49 89 ed             	mov    %rbp,%r13
    65b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    65c0:	41 39 dd             	cmp    %ebx,%r13d
    65c3:	0f 84 fd 00 00 00    	je     66c6 <receive+0x146>
    65c9:	48 8b 86 70 01 00 00 	mov    0x170(%rsi),%rax
    65d0:	4a 8b 14 20          	mov    (%rax,%r12,1),%rdx
    65d4:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    65da:	83 f8 01             	cmp    $0x1,%eax
    65dd:	74 11                	je     65f0 <receive+0x70>
    65df:	83 ba 18 03 00 00 02 	cmpl   $0x2,0x318(%rdx)
    65e6:	75 08                	jne    65f0 <receive+0x70>
    65e8:	85 c0                	test   %eax,%eax
    65ea:	0f 84 d6 00 00 00    	je     66c6 <receive+0x146>
    65f0:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    65f7:	48 85 ff             	test   %rdi,%rdi
    65fa:	0f 8e a8 00 00 00    	jle    66a8 <receive+0x128>
    6600:	4c 8b 8e 78 01 00 00 	mov    0x178(%rsi),%r9
    6607:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    660e:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    6612:	4c 8b 1a             	mov    (%rdx),%r11
    6615:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    6619:	49 01 f9             	add    %rdi,%r9
    661c:	49 01 f8             	add    %rdi,%r8
    661f:	48 03 ba 10 03 00 00 	add    0x310(%rdx),%rdi
    6626:	eb 0e                	jmp    6636 <receive+0xb6>
    6628:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6630:	48 83 e8 01          	sub    $0x1,%rax
    6634:	72 72                	jb     66a8 <receive+0x128>
    6636:	4c 89 c9             	mov    %r9,%rcx
    6639:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
    6640:	48 29 c1             	sub    %rax,%rcx
    6643:	48 89 8e 78 01 00 00 	mov    %rcx,0x178(%rsi)
    664a:	4c 89 c1             	mov    %r8,%rcx
    664d:	48 29 c1             	sub    %rax,%rcx
    6650:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
    6657:	48 89 f9             	mov    %rdi,%rcx
    665a:	48 29 c1             	sub    %rax,%rcx
    665d:	48 89 8a 10 03 00 00 	mov    %rcx,0x310(%rdx)
    6664:	48 63 c8             	movslq %eax,%rcx
    6667:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
    666b:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    666f:	75 bf                	jne    6630 <receive+0xb0>
    6671:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    6675:	75 b9                	jne    6630 <receive+0xb0>
    6677:	49 63 47 04          	movslq 0x4(%r15),%rax
    667b:	31 c9                	xor    %ecx,%ecx
    667d:	bf 01 00 00 00       	mov    $0x1,%edi
    6682:	ba 01 00 00 00       	mov    $0x1,%edx
    6687:	48 8d 35 82 1f 00 00 	lea    0x1f82(%rip),%rsi        # 8610 <_IO_stdin_used+0x610>
    668e:	48 39 e8             	cmp    %rbp,%rax
    6691:	0f 94 c1             	sete   %cl
    6694:	31 c0                	xor    %eax,%eax
    6696:	e8 15 be ff ff       	call   24b0 <__printf_chk@plt>
    669b:	bf 01 00 00 00       	mov    $0x1,%edi
    66a0:	e8 6b be ff ff       	call   2510 <exit@plt>
    66a5:	0f 1f 00             	nopl   (%rax)
    66a8:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
    66b2:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
    66bc:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
    66c6:	83 c3 01             	add    $0x1,%ebx
    66c9:	49 81 c4 80 01 00 00 	add    $0x180,%r12
    66d0:	44 39 f3             	cmp    %r14d,%ebx
    66d3:	0f 85 e7 fe ff ff    	jne    65c0 <receive+0x40>
    66d9:	0f ae f8             	sfence
    66dc:	48 83 c4 08          	add    $0x8,%rsp
    66e0:	31 c0                	xor    %eax,%eax
    66e2:	5b                   	pop    %rbx
    66e3:	5d                   	pop    %rbp
    66e4:	41 5c                	pop    %r12
    66e6:	41 5d                	pop    %r13
    66e8:	41 5e                	pop    %r14
    66ea:	41 5f                	pop    %r15
    66ec:	c3                   	ret
    66ed:	0f 1f 00             	nopl   (%rax)

00000000000066f0 <sendm>:
    66f0:	f3 0f 1e fa          	endbr64
    66f4:	41 57                	push   %r15
    66f6:	41 56                	push   %r14
    66f8:	41 55                	push   %r13
    66fa:	41 54                	push   %r12
    66fc:	55                   	push   %rbp
    66fd:	53                   	push   %rbx
    66fe:	8b af 40 01 00 00    	mov    0x140(%rdi),%ebp
    6704:	85 ed                	test   %ebp,%ebp
    6706:	0f 8e a6 00 00 00    	jle    67b2 <sendm+0xc2>
    670c:	4c 8b a7 28 01 00 00 	mov    0x128(%rdi),%r12
    6713:	49 89 ff             	mov    %rdi,%r15
    6716:	31 c9                	xor    %ecx,%ecx
    6718:	31 c0                	xor    %eax,%eax
    671a:	45 8b 6c 24 08       	mov    0x8(%r12),%r13d
    671f:	90                   	nop
    6720:	41 39 c5             	cmp    %eax,%r13d
    6723:	74 7b                	je     67a0 <sendm+0xb0>
    6725:	49 8b 97 70 01 00 00 	mov    0x170(%r15),%rdx
    672c:	48 01 ca             	add    %rcx,%rdx
    672f:	48 8b 9a 00 01 00 00 	mov    0x100(%rdx),%rbx
    6736:	48 8b b2 80 00 00 00 	mov    0x80(%rdx),%rsi
    673d:	48 8d 7b 01          	lea    0x1(%rbx),%rdi
    6741:	48 89 ba 00 01 00 00 	mov    %rdi,0x100(%rdx)
    6748:	48 83 ff 09          	cmp    $0x9,%rdi
    674c:	7e 52                	jle    67a0 <sendm+0xb0>
    674e:	48 8b be 80 00 00 00 	mov    0x80(%rsi),%rdi
    6755:	48 85 ff             	test   %rdi,%rdi
    6758:	7f 46                	jg     67a0 <sendm+0xb0>
    675a:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
    6761:	41 83 f8 01          	cmp    $0x1,%r8d
    6765:	74 0e                	je     6775 <sendm+0x85>
    6767:	83 be 18 03 00 00 02 	cmpl   $0x2,0x318(%rsi)
    676e:	75 05                	jne    6775 <sendm+0x85>
    6770:	45 85 c0             	test   %r8d,%r8d
    6773:	74 2b                	je     67a0 <sendm+0xb0>
    6775:	41 83 bf 80 01 00 00 01 	cmpl   $0x1,0x180(%r15)
    677d:	74 49                	je     67c8 <sendm+0xd8>
    677f:	83 ba b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx)
    6786:	75 18                	jne    67a0 <sendm+0xb0>
    6788:	48 c7 82 00 01 00 00 00 00 00 00 	movq   $0x0,0x100(%rdx)
    6793:	41 c7 84 24 d8 00 00 00 01 00 00 00 	movl   $0x1,0xd8(%r12)
    679f:	90                   	nop
    67a0:	83 c0 01             	add    $0x1,%eax
    67a3:	48 81 c1 80 01 00 00 	add    $0x180,%rcx
    67aa:	39 e8                	cmp    %ebp,%eax
    67ac:	0f 85 6e ff ff ff    	jne    6720 <sendm+0x30>
    67b2:	0f ae f8             	sfence
    67b5:	31 c0                	xor    %eax,%eax
    67b7:	5b                   	pop    %rbx
    67b8:	5d                   	pop    %rbp
    67b9:	41 5c                	pop    %r12
    67bb:	41 5d                	pop    %r13
    67bd:	41 5e                	pop    %r14
    67bf:	41 5f                	pop    %r15
    67c1:	c3                   	ret
    67c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    67c8:	4c 63 9e 88 00 00 00 	movslq 0x88(%rsi),%r11
    67cf:	4c 39 df             	cmp    %r11,%rdi
    67d2:	0f 8d c2 00 00 00    	jge    689a <sendm+0x1aa>
    67d8:	49 8b 9f 08 01 00 00 	mov    0x108(%r15),%rbx
    67df:	4d 89 de             	mov    %r11,%r14
    67e2:	4c 8b 16             	mov    (%rsi),%r10
    67e5:	49 29 fe             	sub    %rdi,%r14
    67e8:	48 89 5c 24 d8       	mov    %rbx,-0x28(%rsp)
    67ed:	48 8b 9e 08 03 00 00 	mov    0x308(%rsi),%rbx
    67f4:	4d 8d 46 ff          	lea    -0x1(%r14),%r8
    67f8:	48 89 5c 24 e0       	mov    %rbx,-0x20(%rsp)
    67fd:	49 83 f8 02          	cmp    $0x2,%r8
    6801:	0f 86 39 01 00 00    	jbe    6940 <sendm+0x250>
    6807:	48 8d 1c fd 00 00 00 00 	lea    0x0(,%rdi,8),%rbx
    680f:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    6817:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    681c:	4c 01 d3             	add    %r10,%rbx
    681f:	4d 8d 87 88 01 00 00 	lea    0x188(%r15),%r8
    6826:	48 89 5c 24 d0       	mov    %rbx,-0x30(%rsp)
    682b:	4b 8d 1c 0a          	lea    (%r10,%r9,1),%rbx
    682f:	49 39 d8             	cmp    %rbx,%r8
    6832:	0f 83 88 00 00 00    	jae    68c0 <sendm+0x1d0>
    6838:	49 8d 9f 90 01 00 00 	lea    0x190(%r15),%rbx
    683f:	48 39 5c 24 d0       	cmp    %rbx,-0x30(%rsp)
    6844:	73 7a                	jae    68c0 <sendm+0x1d0>
    6846:	4c 8b 44 24 e8       	mov    -0x18(%rsp),%r8
    684b:	4b 8d 3c 0a          	lea    (%r10,%r9,1),%rdi
    684f:	4d 01 d0             	add    %r10,%r8
    6852:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6858:	4d 8b 8f 88 01 00 00 	mov    0x188(%r15),%r9
    685f:	49 83 c0 08          	add    $0x8,%r8
    6863:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
    6867:	4c 39 c7             	cmp    %r8,%rdi
    686a:	75 ec                	jne    6858 <sendm+0x168>
    686c:	0f 1f 40 00          	nopl   0x0(%rax)
    6870:	48 8b 7c 24 d8       	mov    -0x28(%rsp),%rdi
    6875:	4c 01 f7             	add    %r14,%rdi
    6878:	49 89 bf 08 01 00 00 	mov    %rdi,0x108(%r15)
    687f:	48 8b 7c 24 e0       	mov    -0x20(%rsp),%rdi
    6884:	4c 89 9e 80 00 00 00 	mov    %r11,0x80(%rsi)
    688b:	4c 01 f7             	add    %r14,%rdi
    688e:	48 89 be 08 03 00 00 	mov    %rdi,0x308(%rsi)
    6895:	4f 89 4c da f8       	mov    %r9,-0x8(%r10,%r11,8)
    689a:	c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rsi)
    68a4:	c7 86 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rsi)
    68ae:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
    68b8:	e9 c2 fe ff ff       	jmp    677f <sendm+0x8f>
    68bd:	0f 1f 00             	nopl   (%rax)
    68c0:	4c 89 f3             	mov    %r14,%rbx
    68c3:	4c 8b 44 24 d0       	mov    -0x30(%rsp),%r8
    68c8:	4d 8b 8f 88 01 00 00 	mov    0x188(%r15),%r9
    68cf:	48 d1 eb             	shr    %rbx
    68d2:	48 c1 e3 04          	shl    $0x4,%rbx
    68d6:	66 49 0f 6e c1       	movq   %r9,%xmm0
    68db:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    68e0:	4c 01 c3             	add    %r8,%rbx
    68e3:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    68e7:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    68ec:	48 8b 5c 24 e8       	mov    -0x18(%rsp),%rbx
    68f1:	83 e3 10             	and    $0x10,%ebx
    68f4:	75 64                	jne    695a <sendm+0x26a>
    68f6:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    68fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6900:	41 0f 11 00          	movups %xmm0,(%r8)
    6904:	49 83 c0 20          	add    $0x20,%r8
    6908:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
    690d:	49 39 d8             	cmp    %rbx,%r8
    6910:	75 ee                	jne    6900 <sendm+0x210>
    6912:	4d 89 f0             	mov    %r14,%r8
    6915:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6919:	49 01 f8             	add    %rdi,%r8
    691c:	41 f6 c6 01          	test   $0x1,%r14b
    6920:	0f 84 4a ff ff ff    	je     6870 <sendm+0x180>
    6926:	4d 8b 8f 88 01 00 00 	mov    0x188(%r15),%r9
    692d:	4f 89 0c c2          	mov    %r9,(%r10,%r8,8)
    6931:	e9 3a ff ff ff       	jmp    6870 <sendm+0x180>
    6936:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6940:	48 8d 1c fd 00 00 00 00 	lea    0x0(,%rdi,8),%rbx
    6948:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    6950:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    6955:	e9 ec fe ff ff       	jmp    6846 <sendm+0x156>
    695a:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    695f:	41 0f 11 00          	movups %xmm0,(%r8)
    6963:	49 83 c0 10          	add    $0x10,%r8
    6967:	49 39 d8             	cmp    %rbx,%r8
    696a:	75 94                	jne    6900 <sendm+0x210>
    696c:	eb a4                	jmp    6912 <sendm+0x222>
    696e:	66 90                	xchg   %ax,%ax

0000000000006970 <mailboxkind>:
    6970:	f3 0f 1e fa          	endbr64
    6974:	85 f6                	test   %esi,%esi
    6976:	74 18                	je     6990 <mailboxkind+0x20>
    6978:	31 c0                	xor    %eax,%eax
    697a:	83 fe 01             	cmp    $0x1,%esi
    697d:	74 01                	je     6980 <mailboxkind+0x10>
    697f:	c3                   	ret
    6980:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
    6987:	c3                   	ret
    6988:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6990:	48 8b 07             	mov    (%rdi),%rax
    6993:	c3                   	ret
    6994:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    699f:	90                   	nop

00000000000069a0 <setmailboxkind>:
    69a0:	f3 0f 1e fa          	endbr64
    69a4:	85 d2                	test   %edx,%edx
    69a6:	75 08                	jne    69b0 <setmailboxkind+0x10>
    69a8:	48 89 37             	mov    %rsi,(%rdi)
    69ab:	31 c0                	xor    %eax,%eax
    69ad:	c3                   	ret
    69ae:	66 90                	xchg   %ax,%ax
    69b0:	83 fa 01             	cmp    $0x1,%edx
    69b3:	74 13                	je     69c8 <setmailboxkind+0x28>
    69b5:	83 fa 02             	cmp    $0x2,%edx
    69b8:	75 1e                	jne    69d8 <setmailboxkind+0x38>
    69ba:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
    69c1:	31 c0                	xor    %eax,%eax
    69c3:	c3                   	ret
    69c4:	0f 1f 40 00          	nopl   0x0(%rax)
    69c8:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
    69cf:	31 c0                	xor    %eax,%eax
    69d1:	c3                   	ret
    69d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    69d8:	83 fa 03             	cmp    $0x3,%edx
    69db:	75 ce                	jne    69ab <setmailboxkind+0xb>
    69dd:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
    69e4:	31 c0                	xor    %eax,%eax
    69e6:	c3                   	ret
    69e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000069f0 <fswap>:
    69f0:	f3 0f 1e fa          	endbr64
    69f4:	4c 8b 8f 28 01 00 00 	mov    0x128(%rdi),%r9
    69fb:	8b 97 94 01 00 00    	mov    0x194(%rdi),%edx
    6a01:	8b 8f 30 01 00 00    	mov    0x130(%rdi),%ecx
    6a07:	48 63 77 04          	movslq 0x4(%rdi),%rsi
    6a0b:	49 63 81 c4 00 00 00 	movslq 0xc4(%r9),%rax
    6a12:	0f af d0             	imul   %eax,%edx
    6a15:	01 d1                	add    %edx,%ecx
    6a17:	85 c0                	test   %eax,%eax
    6a19:	0f 8e 2c 01 00 00    	jle    6b4b <fswap+0x15b>
    6a1f:	48 63 c9             	movslq %ecx,%rcx
    6a22:	41 56                	push   %r14
    6a24:	48 63 d2             	movslq %edx,%rdx
    6a27:	48 c1 e6 09          	shl    $0x9,%rsi
    6a2b:	41 55                	push   %r13
    6a2d:	4c 8d 14 49          	lea    (%rcx,%rcx,2),%r10
    6a31:	48 01 d0             	add    %rdx,%rax
    6a34:	41 54                	push   %r12
    6a36:	49 c1 e2 07          	shl    $0x7,%r10
    6a3a:	55                   	push   %rbp
    6a3b:	53                   	push   %rbx
    6a3c:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
    6a43:	48 8d 3c cd 00 00 00 00 	lea    0x0(,%rcx,8),%rdi
    6a4b:	48 8d 1c 40          	lea    (%rax,%rax,2),%rbx
    6a4f:	4d 8b 49 20          	mov    0x20(%r9),%r9
    6a53:	48 29 cf             	sub    %rcx,%rdi
    6a56:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    6a5e:	48 c1 e3 07          	shl    $0x7,%rbx
    6a62:	48 c1 e7 05          	shl    $0x5,%rdi
    6a66:	48 29 d1             	sub    %rdx,%rcx
    6a69:	4d 8b 5c 39 38       	mov    0x38(%r9,%rdi,1),%r11
    6a6e:	48 c1 e1 05          	shl    $0x5,%rcx
    6a72:	49 01 c9             	add    %rcx,%r9
    6a75:	49 8b ac 33 70 01 00 00 	mov    0x170(%r11,%rsi,1),%rbp
    6a7d:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    6a81:	48 c1 e6 07          	shl    $0x7,%rsi
    6a85:	eb 20                	jmp    6aa7 <fswap+0xb7>
    6a87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6a90:	48 81 c6 80 01 00 00 	add    $0x180,%rsi
    6a97:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    6a9e:	48 39 f3             	cmp    %rsi,%rbx
    6aa1:	0f 84 99 00 00 00    	je     6b40 <fswap+0x150>
    6aa7:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    6aaf:	75 df                	jne    6a90 <fswap+0xa0>
    6ab1:	49 8b 79 38          	mov    0x38(%r9),%rdi
    6ab5:	45 85 c0             	test   %r8d,%r8d
    6ab8:	7e d6                	jle    6a90 <fswap+0xa0>
    6aba:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    6ac1:	31 c9                	xor    %ecx,%ecx
    6ac3:	eb 58                	jmp    6b1d <fswap+0x12d>
    6ac5:	0f 1f 00             	nopl   (%rax)
    6ac8:	48 63 d2             	movslq %edx,%rdx
    6acb:	48 c1 e2 09          	shl    $0x9,%rdx
    6acf:	4d 8b ac 13 70 01 00 00 	mov    0x170(%r11,%rdx,1),%r13
    6ad7:	49 01 f5             	add    %rsi,%r13
    6ada:	4c 89 ea             	mov    %r13,%rdx
    6add:	4d 8b 6d 00          	mov    0x0(%r13),%r13
    6ae1:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    6ae9:	75 22                	jne    6b0d <fswap+0x11d>
    6aeb:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    6af2:	4c 89 32             	mov    %r14,(%rdx)
    6af5:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    6afc:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    6b03:	4c 89 30             	mov    %r14,(%rax)
    6b06:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
    6b0d:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    6b14:	41 39 c8             	cmp    %ecx,%r8d
    6b17:	0f 84 73 ff ff ff    	je     6a90 <fswap+0xa0>
    6b1d:	83 c1 01             	add    $0x1,%ecx
    6b20:	89 c8                	mov    %ecx,%eax
    6b22:	99                   	cltd
    6b23:	41 f7 f8             	idiv   %r8d
    6b26:	48 8b 07             	mov    (%rdi),%rax
    6b29:	4c 01 d0             	add    %r10,%rax
    6b2c:	4c 8b 20             	mov    (%rax),%r12
    6b2f:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    6b38:	74 8e                	je     6ac8 <fswap+0xd8>
    6b3a:	e9 51 ff ff ff       	jmp    6a90 <fswap+0xa0>
    6b3f:	90                   	nop
    6b40:	5b                   	pop    %rbx
    6b41:	31 c0                	xor    %eax,%eax
    6b43:	5d                   	pop    %rbp
    6b44:	41 5c                	pop    %r12
    6b46:	41 5d                	pop    %r13
    6b48:	41 5e                	pop    %r14
    6b4a:	c3                   	ret
    6b4b:	31 c0                	xor    %eax,%eax
    6b4d:	c3                   	ret
    6b4e:	66 90                	xchg   %ax,%ax

0000000000006b50 <barriered_work>:
    6b50:	f3 0f 1e fa          	endbr64
    6b54:	41 57                	push   %r15
    6b56:	41 56                	push   %r14
    6b58:	41 55                	push   %r13
    6b5a:	41 54                	push   %r12
    6b5c:	55                   	push   %rbp
    6b5d:	53                   	push   %rbx
    6b5e:	48 89 fb             	mov    %rdi,%rbx
    6b61:	48 83 ec 58          	sub    $0x58,%rsp
    6b65:	44 8b 67 04          	mov    0x4(%rdi),%r12d
    6b69:	44 39 a7 30 01 00 00 	cmp    %r12d,0x130(%rdi)
    6b70:	74 6e                	je     6be0 <barriered_work+0x90>
    6b72:	e8 79 fe ff ff       	call   69f0 <fswap>
    6b77:	48 89 df             	mov    %rbx,%rdi
    6b7a:	e8 01 fa ff ff       	call   6580 <receive>
    6b7f:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6b86:	75 1c                	jne    6ba4 <barriered_work+0x54>
    6b88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6b90:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6b98:	0f ae f8             	sfence
    6b9b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6ba2:	74 ec                	je     6b90 <barriered_work+0x40>
    6ba4:	48 89 df             	mov    %rbx,%rdi
    6ba7:	e8 44 fb ff ff       	call   66f0 <sendm>
    6bac:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6bb2:	83 e8 01             	sub    $0x1,%eax
    6bb5:	44 39 e0             	cmp    %r12d,%eax
    6bb8:	0f 84 bd 03 00 00    	je     6f7b <barriered_work+0x42b>
    6bbe:	c7 83 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbx)
    6bc8:	0f ae f8             	sfence
    6bcb:	48 83 c4 58          	add    $0x58,%rsp
    6bcf:	31 c0                	xor    %eax,%eax
    6bd1:	5b                   	pop    %rbx
    6bd2:	5d                   	pop    %rbp
    6bd3:	41 5c                	pop    %r12
    6bd5:	41 5d                	pop    %r13
    6bd7:	41 5e                	pop    %r14
    6bd9:	41 5f                	pop    %r15
    6bdb:	c3                   	ret
    6bdc:	0f 1f 40 00          	nopl   0x0(%rax)
    6be0:	e8 9b f9 ff ff       	call   6580 <receive>
    6be5:	4c 8b b3 28 01 00 00 	mov    0x128(%rbx),%r14
    6bec:	41 83 be d8 00 00 00 01 	cmpl   $0x1,0xd8(%r14)
    6bf4:	0f 85 8e 02 00 00    	jne    6e88 <barriered_work+0x338>
    6bfa:	44 8b bb 40 01 00 00 	mov    0x140(%rbx),%r15d
    6c01:	41 c7 86 d8 00 00 00 00 00 00 00 	movl   $0x0,0xd8(%r14)
    6c0c:	45 85 ff             	test   %r15d,%r15d
    6c0f:	0f 8e 73 02 00 00    	jle    6e88 <barriered_work+0x338>
    6c15:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6c1b:	41 8b 56 08          	mov    0x8(%r14),%edx
    6c1f:	31 f6                	xor    %esi,%esi
    6c21:	45 31 c0             	xor    %r8d,%r8d
    6c24:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
    6c2c:	89 44 24 24          	mov    %eax,0x24(%rsp)
    6c30:	49 63 c4             	movslq %r12d,%rax
    6c33:	41 89 d3             	mov    %edx,%r11d
    6c36:	48 c1 e0 09          	shl    $0x9,%rax
    6c3a:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
    6c3f:	49 89 c5             	mov    %rax,%r13
    6c42:	48 63 c2             	movslq %edx,%rax
    6c45:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    6c4d:	48 29 c1             	sub    %rax,%rcx
    6c50:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    6c54:	48 c1 e1 05          	shl    $0x5,%rcx
    6c58:	48 c1 e0 07          	shl    $0x7,%rax
    6c5c:	48 89 cd             	mov    %rcx,%rbp
    6c5f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    6c64:	48 89 d9             	mov    %rbx,%rcx
    6c67:	eb 27                	jmp    6c90 <barriered_work+0x140>
    6c69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6c70:	83 44 24 0c 01       	addl   $0x1,0xc(%rsp)
    6c75:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    6c79:	49 81 c0 80 01 00 00 	add    $0x180,%r8
    6c80:	48 81 c6 e0 00 00 00 	add    $0xe0,%rsi
    6c87:	44 39 f8             	cmp    %r15d,%eax
    6c8a:	0f 84 f0 01 00 00    	je     6e80 <barriered_work+0x330>
    6c90:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    6c94:	41 39 c3             	cmp    %eax,%r11d
    6c97:	74 d7                	je     6c70 <barriered_work+0x120>
    6c99:	49 8b 56 20          	mov    0x20(%r14),%rdx
    6c9d:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    6ca2:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    6ca6:	44 8b 88 98 01 00 00 	mov    0x198(%rax),%r9d
    6cad:	45 85 c9             	test   %r9d,%r9d
    6cb0:	75 be                	jne    6c70 <barriered_work+0x120>
    6cb2:	4c 8b 4c 2a 38       	mov    0x38(%rdx,%rbp,1),%r9
    6cb7:	4b 8d 14 29          	lea    (%r9,%r13,1),%rdx
    6cbb:	44 8b 92 98 01 00 00 	mov    0x198(%rdx),%r10d
    6cc2:	45 85 d2             	test   %r10d,%r10d
    6cc5:	75 a9                	jne    6c70 <barriered_work+0x120>
    6cc7:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    6cce:	42 83 bc 02 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r8,1)
    6cd7:	75 97                	jne    6c70 <barriered_work+0x120>
    6cd9:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6ce0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    6ce5:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    6ced:	75 81                	jne    6c70 <barriered_work+0x120>
    6cef:	48 63 44 24 24       	movslq 0x24(%rsp),%rax
    6cf4:	85 c0                	test   %eax,%eax
    6cf6:	0f 8e 74 ff ff ff    	jle    6c70 <barriered_work+0x120>
    6cfc:	48 89 c2             	mov    %rax,%rdx
    6cff:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
    6d04:	41 bc 70 01 00 00    	mov    $0x170,%r12d
    6d0a:	48 c1 e2 09          	shl    $0x9,%rdx
    6d0e:	44 89 7c 24 3c       	mov    %r15d,0x3c(%rsp)
    6d13:	48 89 74 24 40       	mov    %rsi,0x40(%rsp)
    6d18:	48 8d 9a 98 01 00 00 	lea    0x198(%rdx),%rbx
    6d1f:	48 89 54 24 48       	mov    %rdx,0x48(%rsp)
    6d24:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    6d29:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    6d2e:	44 89 5c 24 38       	mov    %r11d,0x38(%rsp)
    6d33:	44 8b 5c 24 24       	mov    0x24(%rsp),%r11d
    6d38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6d40:	41 83 c2 01          	add    $0x1,%r10d
    6d44:	4b 8b 34 21          	mov    (%r9,%r12,1),%rsi
    6d48:	44 89 d0             	mov    %r10d,%eax
    6d4b:	99                   	cltd
    6d4c:	4c 01 c6             	add    %r8,%rsi
    6d4f:	41 f7 fb             	idiv   %r11d
    6d52:	4c 8b 36             	mov    (%rsi),%r14
    6d55:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    6d5a:	4c 8b b6 80 00 00 00 	mov    0x80(%rsi),%r14
    6d61:	48 63 d2             	movslq %edx,%rdx
    6d64:	48 c1 e2 09          	shl    $0x9,%rdx
    6d68:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    6d70:	4c 01 e8             	add    %r13,%rax
    6d73:	4c 8b 38             	mov    (%rax),%r15
    6d76:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    6d7d:	4c 89 30             	mov    %r14,(%rax)
    6d80:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    6d85:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    6d8c:	48 89 16             	mov    %rdx,(%rsi)
    6d8f:	4c 89 be 80 00 00 00 	mov    %r15,0x80(%rsi)
    6d96:	be 98 01 00 00       	mov    $0x198,%esi
    6d9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6da0:	41 c7 04 31 01 00 00 00 	movl   $0x1,(%r9,%rsi,1)
    6da8:	c7 04 37 01 00 00 00 	movl   $0x1,(%rdi,%rsi,1)
    6daf:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    6db6:	48 39 f3             	cmp    %rsi,%rbx
    6db9:	75 e5                	jne    6da0 <barriered_work+0x250>
    6dbb:	4a 8b 34 27          	mov    (%rdi,%r12,1),%rsi
    6dbf:	48 8b 00             	mov    (%rax),%rax
    6dc2:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
    6dcd:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    6dd4:	4a 8b b4 2e 80 00 00 00 	mov    0x80(%rsi,%r13,1),%rsi
    6ddc:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
    6de6:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    6df0:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    6dfa:	45 39 d3             	cmp    %r10d,%r11d
    6dfd:	0f 85 3d ff ff ff    	jne    6d40 <barriered_work+0x1f0>
    6e03:	48 8b 54 24 48       	mov    0x48(%rsp),%rdx
    6e08:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    6e0d:	b8 70 01 00 00       	mov    $0x170,%eax
    6e12:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    6e17:	44 8b 5c 24 38       	mov    0x38(%rsp),%r11d
    6e1c:	44 8b 7c 24 3c       	mov    0x3c(%rsp),%r15d
    6e21:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    6e26:	48 8d 9a 70 01 00 00 	lea    0x170(%rdx),%rbx
    6e2d:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    6e32:	eb 13                	jmp    6e47 <barriered_work+0x2f7>
    6e34:	0f 1f 40 00          	nopl   0x0(%rax)
    6e38:	48 05 00 02 00 00    	add    $0x200,%rax
    6e3e:	48 39 c3             	cmp    %rax,%rbx
    6e41:	0f 84 29 fe ff ff    	je     6c70 <barriered_work+0x120>
    6e47:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    6e4b:	4d 8b 14 01          	mov    (%r9,%rax,1),%r10
    6e4f:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    6e53:	4b 39 14 02          	cmp    %rdx,(%r10,%r8,1)
    6e57:	75 df                	jne    6e38 <barriered_work+0x2e8>
    6e59:	bf 01 00 00 00       	mov    $0x1,%edi
    6e5e:	48 8d 35 c6 13 00 00 	lea    0x13c6(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6e65:	31 c0                	xor    %eax,%eax
    6e67:	e8 44 b6 ff ff       	call   24b0 <__printf_chk@plt>
    6e6c:	bf 01 00 00 00       	mov    $0x1,%edi
    6e71:	e8 9a b6 ff ff       	call   2510 <exit@plt>
    6e76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6e80:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    6e85:	48 89 cb             	mov    %rcx,%rbx
    6e88:	48 89 df             	mov    %rbx,%rdi
    6e8b:	e8 60 fb ff ff       	call   69f0 <fswap>
    6e90:	48 89 df             	mov    %rbx,%rdi
    6e93:	e8 e8 f6 ff ff       	call   6580 <receive>
    6e98:	0f ae f8             	sfence
    6e9b:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6ea2:	31 ff                	xor    %edi,%edi
    6ea4:	48 c1 e6 05          	shl    $0x5,%rsi
    6ea8:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6eaf:	e8 9c b4 ff ff       	call   2350 <clock_gettime@plt>
    6eb4:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6ebb:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6ec2:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6ec6:	8b 4a 10             	mov    0x10(%rdx),%ecx
    6ec9:	8d 69 01             	lea    0x1(%rcx),%ebp
    6ecc:	89 6a 10             	mov    %ebp,0x10(%rdx)
    6ecf:	75 58                	jne    6f29 <barriered_work+0x3d9>
    6ed1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6ed8:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    6edf:	48 8b 40 18          	mov    0x18(%rax),%rax
    6ee3:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
    6ee7:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6eef:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6ef3:	48 c1 e7 09          	shl    $0x9,%rdi
    6ef7:	48 03 78 38          	add    0x38(%rax),%rdi
    6efb:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    6f01:	0f ae f8             	sfence
    6f04:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6f0b:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6f12:	74 c4                	je     6ed8 <barriered_work+0x388>
    6f14:	48 8b 40 48          	mov    0x48(%rax),%rax
    6f18:	3b 68 10             	cmp    0x10(%rax),%ebp
    6f1b:	74 0c                	je     6f29 <barriered_work+0x3d9>
    6f1d:	48 8d 3d 22 13 00 00 	lea    0x1322(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6f24:	e8 07 b4 ff ff       	call   2330 <puts@plt>
    6f29:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6f30:	31 ff                	xor    %edi,%edi
    6f32:	48 c1 e6 05          	shl    $0x5,%rsi
    6f36:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6f3d:	48 83 c6 10          	add    $0x10,%rsi
    6f41:	e8 0a b4 ff ff       	call   2350 <clock_gettime@plt>
    6f46:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6f4d:	48 89 df             	mov    %rbx,%rdi
    6f50:	48 83 c0 01          	add    $0x1,%rax
    6f54:	48 99                	cqto
    6f56:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6f5d:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    6f64:	e8 87 f7 ff ff       	call   66f0 <sendm>
    6f69:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6f6f:	83 e8 01             	sub    $0x1,%eax
    6f72:	44 39 e0             	cmp    %r12d,%eax
    6f75:	0f 85 43 fc ff ff    	jne    6bbe <barriered_work+0x6e>
    6f7b:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    6f82:	85 d2                	test   %edx,%edx
    6f84:	0f 8e 34 fc ff ff    	jle    6bbe <barriered_work+0x6e>
    6f8a:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    6f91:	48 c1 e2 09          	shl    $0x9,%rdx
    6f95:	48 63 71 08          	movslq 0x8(%rcx),%rsi
    6f99:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
    6fa1:	48 29 f0             	sub    %rsi,%rax
    6fa4:	48 c1 e0 05          	shl    $0x5,%rax
    6fa8:	48 03 41 20          	add    0x20(%rcx),%rax
    6fac:	48 8b 40 38          	mov    0x38(%rax),%rax
    6fb0:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    6fb4:	80 e6 02             	and    $0x2,%dh
    6fb7:	74 17                	je     6fd0 <barriered_work+0x480>
    6fb9:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
    6fc0:	48 05 00 02 00 00    	add    $0x200,%rax
    6fc6:	48 39 c8             	cmp    %rcx,%rax
    6fc9:	0f 84 ef fb ff ff    	je     6bbe <barriered_work+0x6e>
    6fcf:	90                   	nop
    6fd0:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
    6fd7:	83 80 9c 03 00 00 01 	addl   $0x1,0x39c(%rax)
    6fde:	48 05 00 04 00 00    	add    $0x400,%rax
    6fe4:	48 39 c8             	cmp    %rcx,%rax
    6fe7:	75 e7                	jne    6fd0 <barriered_work+0x480>
    6fe9:	e9 d0 fb ff ff       	jmp    6bbe <barriered_work+0x6e>
    6fee:	66 90                	xchg   %ax,%ax

0000000000006ff0 <barriered_work_ingest_andwork>:
    6ff0:	f3 0f 1e fa          	endbr64
    6ff4:	53                   	push   %rbx
    6ff5:	48 89 fb             	mov    %rdi,%rbx
    6ff8:	e8 93 f1 ff ff       	call   6190 <barriered_work_ingest>
    6ffd:	48 89 df             	mov    %rbx,%rdi
    7000:	5b                   	pop    %rbx
    7001:	e9 4a fb ff ff       	jmp    6b50 <barriered_work>
    7006:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000007010 <barriered_nulltask>:
    7010:	f3 0f 1e fa          	endbr64
    7014:	31 c0                	xor    %eax,%eax
    7016:	c3                   	ret
    7017:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007020 <barriered_steal>:
    7020:	f3 0f 1e fa          	endbr64
    7024:	31 c0                	xor    %eax,%eax
    7026:	c3                   	ret
    7027:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007030 <after>:
    7030:	f3 0f 1e fa          	endbr64
    7034:	31 c0                	xor    %eax,%eax
    7036:	48 39 d7             	cmp    %rdx,%rdi
    7039:	7e 08                	jle    7043 <after+0x13>
    703b:	31 c0                	xor    %eax,%eax
    703d:	48 39 ce             	cmp    %rcx,%rsi
    7040:	0f 9f c0             	setg   %al
    7043:	c3                   	ret
    7044:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    704f:	90                   	nop

0000000000007050 <within>:
    7050:	f3 0f 1e fa          	endbr64
    7054:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    7059:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    705e:	31 c0                	xor    %eax,%eax
    7060:	48 39 d7             	cmp    %rdx,%rdi
    7063:	7f 18                	jg     707d <within+0x2d>
    7065:	4d 39 d8             	cmp    %r11,%r8
    7068:	0f 9e c2             	setle  %dl
    706b:	48 39 ce             	cmp    %rcx,%rsi
    706e:	0f 9e c0             	setle  %al
    7071:	21 c2                	and    %eax,%edx
    7073:	31 c0                	xor    %eax,%eax
    7075:	4d 39 d1             	cmp    %r10,%r9
    7078:	0f 9e c0             	setle  %al
    707b:	21 d0                	and    %edx,%eax
    707d:	c3                   	ret
    707e:	66 90                	xchg   %ax,%ax

0000000000007080 <overlap>:
    7080:	f3 0f 1e fa          	endbr64
    7084:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    7089:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    708e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    7093:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    7098:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    709d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    70a2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    70a7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    70ac:	48 39 fe             	cmp    %rdi,%rsi
    70af:	7d 2f                	jge    70e0 <overlap+0x60>
    70b1:	48 39 ca             	cmp    %rcx,%rdx
    70b4:	7d 62                	jge    7118 <overlap+0x98>
    70b6:	4d 39 da             	cmp    %r11,%r10
    70b9:	7d 0e                	jge    70c9 <overlap+0x49>
    70bb:	b8 01 00 00 00       	mov    $0x1,%eax
    70c0:	4d 39 c1             	cmp    %r8,%r9
    70c3:	0f 8c 7f 00 00 00    	jl     7148 <overlap+0xc8>
    70c9:	31 c0                	xor    %eax,%eax
    70cb:	4d 39 c1             	cmp    %r8,%r9
    70ce:	7f 4c                	jg     711c <overlap+0x9c>
    70d0:	31 c0                	xor    %eax,%eax
    70d2:	4d 39 da             	cmp    %r11,%r10
    70d5:	0f 9e c0             	setle  %al
    70d8:	c3                   	ret
    70d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    70e0:	7e 4e                	jle    7130 <overlap+0xb0>
    70e2:	48 39 ca             	cmp    %rcx,%rdx
    70e5:	7f 39                	jg     7120 <overlap+0xa0>
    70e7:	75 31                	jne    711a <overlap+0x9a>
    70e9:	4d 39 c1             	cmp    %r8,%r9
    70ec:	7c 2c                	jl     711a <overlap+0x9a>
    70ee:	b8 01 00 00 00       	mov    $0x1,%eax
    70f3:	4d 39 da             	cmp    %r11,%r10
    70f6:	7d 24                	jge    711c <overlap+0x9c>
    70f8:	48 39 ca             	cmp    %rcx,%rdx
    70fb:	0f 94 c2             	sete   %dl
    70fe:	48 39 fe             	cmp    %rdi,%rsi
    7101:	0f 94 c0             	sete   %al
    7104:	21 c2                	and    %eax,%edx
    7106:	31 c0                	xor    %eax,%eax
    7108:	4d 39 c1             	cmp    %r8,%r9
    710b:	0f 94 c0             	sete   %al
    710e:	21 d0                	and    %edx,%eax
    7110:	c3                   	ret
    7111:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7118:	74 af                	je     70c9 <overlap+0x49>
    711a:	31 c0                	xor    %eax,%eax
    711c:	c3                   	ret
    711d:	0f 1f 00             	nopl   (%rax)
    7120:	4d 39 da             	cmp    %r11,%r10
    7123:	7e c4                	jle    70e9 <overlap+0x69>
    7125:	b8 01 00 00 00       	mov    $0x1,%eax
    712a:	4d 39 c1             	cmp    %r8,%r9
    712d:	7e ba                	jle    70e9 <overlap+0x69>
    712f:	c3                   	ret
    7130:	48 39 ca             	cmp    %rcx,%rdx
    7133:	7c 94                	jl     70c9 <overlap+0x49>
    7135:	4d 39 c1             	cmp    %r8,%r9
    7138:	7d b4                	jge    70ee <overlap+0x6e>
    713a:	48 39 ca             	cmp    %rcx,%rdx
    713d:	74 91                	je     70d0 <overlap+0x50>
    713f:	eb d9                	jmp    711a <overlap+0x9a>
    7141:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7148:	c3                   	ret
    7149:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007150 <verify>:
    7150:	f3 0f 1e fa          	endbr64
    7154:	85 f6                	test   %esi,%esi
    7156:	0f 8e 44 03 00 00    	jle    74a0 <verify+0x350>
    715c:	41 57                	push   %r15
    715e:	41 89 f7             	mov    %esi,%r15d
    7161:	41 56                	push   %r14
    7163:	45 31 f6             	xor    %r14d,%r14d
    7166:	41 55                	push   %r13
    7168:	41 54                	push   %r12
    716a:	55                   	push   %rbp
    716b:	53                   	push   %rbx
    716c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    7170:	48 83 ec 58          	sub    $0x58,%rsp
    7174:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    7179:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    717e:	45 31 e4             	xor    %r12d,%r12d
    7181:	45 39 e6             	cmp    %r12d,%r14d
    7184:	0f 84 4e 02 00 00    	je     73d8 <verify+0x288>
    718a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    718f:	8b 50 08             	mov    0x8(%rax),%edx
    7192:	85 d2                	test   %edx,%edx
    7194:	0f 8e 3e 02 00 00    	jle    73d8 <verify+0x288>
    719a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    719f:	31 c9                	xor    %ecx,%ecx
    71a1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    71a6:	31 c0                	xor    %eax,%eax
    71a8:	44 89 f2             	mov    %r14d,%edx
    71ab:	bf 01 00 00 00       	mov    $0x1,%edi
    71b0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    71b5:	48 8d 35 9a 10 00 00 	lea    0x109a(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    71bc:	e8 ef b2 ff ff       	call   24b0 <__printf_chk@plt>
    71c1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    71c6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    71cb:	8b 40 08             	mov    0x8(%rax),%eax
    71ce:	85 c0                	test   %eax,%eax
    71d0:	0f 8e e6 01 00 00    	jle    73bc <verify+0x26c>
    71d6:	48 89 c8             	mov    %rcx,%rax
    71d9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    71de:	31 db                	xor    %ebx,%ebx
    71e0:	48 c1 e0 09          	shl    $0x9,%rax
    71e4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    71e9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    71ee:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    71f3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    71f8:	4c 8b 20             	mov    (%rax),%r12
    71fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7200:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    7205:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    720a:	49 89 de             	mov    %rbx,%r14
    720d:	48 8d 35 57 10 00 00 	lea    0x1057(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    7214:	49 c1 e6 09          	shl    $0x9,%r14
    7218:	bf 01 00 00 00       	mov    $0x1,%edi
    721d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    7221:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    7229:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    722e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    7236:	31 c0                	xor    %eax,%eax
    7238:	e8 73 b2 ff ff       	call   24b0 <__printf_chk@plt>
    723d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7242:	4c 8b 20             	mov    (%rax),%r12
    7245:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    724e:	0f 8e 47 01 00 00    	jle    739b <verify+0x24b>
    7254:	4c 03 75 00          	add    0x0(%rbp),%r14
    7258:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    725d:	ba 01 00 00 00       	mov    $0x1,%edx
    7262:	4d 89 f5             	mov    %r14,%r13
    7265:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    726c:	4d 85 f6             	test   %r14,%r14
    726f:	0f 8e 21 01 00 00    	jle    7396 <verify+0x246>
    7275:	0f 1f 00             	nopl   (%rax)
    7278:	48 89 d5             	mov    %rdx,%rbp
    727b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7280:	31 db                	xor    %ebx,%ebx
    7282:	4d 89 f2             	mov    %r14,%r10
    7285:	48 c1 e5 05          	shl    $0x5,%rbp
    7289:	48 83 ed 20          	sub    $0x20,%rbp
    728d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    7291:	49 89 ee             	mov    %rbp,%r14
    7294:	48 89 dd             	mov    %rbx,%rbp
    7297:	48 89 d3             	mov    %rdx,%rbx
    729a:	eb 31                	jmp    72cd <verify+0x17d>
    729c:	0f 1f 40 00          	nopl   0x0(%rax)
    72a0:	4c 39 c2             	cmp    %r8,%rdx
    72a3:	0f 8d 57 01 00 00    	jge    7400 <verify+0x2b0>
    72a9:	4c 39 df             	cmp    %r11,%rdi
    72ac:	7e 05                	jle    72b3 <verify+0x163>
    72ae:	49 39 c1             	cmp    %rax,%r9
    72b1:	7c 75                	jl     7328 <verify+0x1d8>
    72b3:	4c 39 df             	cmp    %r11,%rdi
    72b6:	0f 8d ab 01 00 00    	jge    7467 <verify+0x317>
    72bc:	0f 1f 40 00          	nopl   0x0(%rax)
    72c0:	48 83 c5 01          	add    $0x1,%rbp
    72c4:	49 39 ea             	cmp    %rbp,%r10
    72c7:	0f 8e a9 00 00 00    	jle    7376 <verify+0x226>
    72cd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    72d4:	48 89 e8             	mov    %rbp,%rax
    72d7:	48 c1 e0 05          	shl    $0x5,%rax
    72db:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    72e2:	4c 01 f2             	add    %r14,%rdx
    72e5:	48 8b 08             	mov    (%rax),%rcx
    72e8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    72ec:	48 8b 32             	mov    (%rdx),%rsi
    72ef:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    72f3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    72f7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    72fb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    72ff:	48 8b 40 18          	mov    0x18(%rax),%rax
    7303:	48 39 f1             	cmp    %rsi,%rcx
    7306:	7c 98                	jl     72a0 <verify+0x150>
    7308:	0f 8e 42 01 00 00    	jle    7450 <verify+0x300>
    730e:	4c 39 c2             	cmp    %r8,%rdx
    7311:	0f 8f f9 00 00 00    	jg     7410 <verify+0x2c0>
    7317:	75 a7                	jne    72c0 <verify+0x170>
    7319:	4c 39 df             	cmp    %r11,%rdi
    731c:	7f a2                	jg     72c0 <verify+0x170>
    731e:	49 39 c1             	cmp    %rax,%r9
    7321:	7c 9d                	jl     72c0 <verify+0x170>
    7323:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7328:	49 89 c1             	mov    %rax,%r9
    732b:	48 89 f9             	mov    %rdi,%rcx
    732e:	48 89 f2             	mov    %rsi,%rdx
    7331:	bf 01 00 00 00       	mov    $0x1,%edi
    7336:	48 8d 35 fb 12 00 00 	lea    0x12fb(%rip),%rsi        # 8638 <_IO_stdin_used+0x638>
    733d:	31 c0                	xor    %eax,%eax
    733f:	48 83 c5 01          	add    $0x1,%rbp
    7343:	e8 68 b1 ff ff       	call   24b0 <__printf_chk@plt>
    7348:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    734d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    7352:	4c 03 28             	add    (%rax),%r13
    7355:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    735a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
    7361:	4c 8b 20             	mov    (%rax),%r12
    7364:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7369:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    736d:	49 39 ea             	cmp    %rbp,%r10
    7370:	0f 8f 57 ff ff ff    	jg     72cd <verify+0x17d>
    7376:	48 89 da             	mov    %rbx,%rdx
    7379:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7380:	7d 14                	jge    7396 <verify+0x246>
    7382:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7389:	48 83 c2 01          	add    $0x1,%rdx
    738d:	4d 85 f6             	test   %r14,%r14
    7390:	0f 8f e2 fe ff ff    	jg     7278 <verify+0x128>
    7396:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    739b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    73a0:	48 83 c3 01          	add    $0x1,%rbx
    73a4:	39 58 08             	cmp    %ebx,0x8(%rax)
    73a7:	0f 8f 53 fe ff ff    	jg     7200 <verify+0xb0>
    73ad:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    73b2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    73b7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
    73bc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    73c1:	48 83 c1 01          	add    $0x1,%rcx
    73c5:	39 48 08             	cmp    %ecx,0x8(%rax)
    73c8:	0f 8f d8 fd ff ff    	jg     71a6 <verify+0x56>
    73ce:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    73d3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    73d8:	48 81 44 24 10 e0 00 00 00 	addq   $0xe0,0x10(%rsp)
    73e1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    73e6:	41 39 c7             	cmp    %eax,%r15d
    73e9:	0f 84 86 00 00 00    	je     7475 <verify+0x325>
    73ef:	41 89 c4             	mov    %eax,%r12d
    73f2:	e9 8a fd ff ff       	jmp    7181 <verify+0x31>
    73f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    7400:	0f 85 ba fe ff ff    	jne    72c0 <verify+0x170>
    7406:	e9 a8 fe ff ff       	jmp    72b3 <verify+0x163>
    740b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7410:	49 39 c1             	cmp    %rax,%r9
    7413:	7e 09                	jle    741e <verify+0x2ce>
    7415:	4c 39 df             	cmp    %r11,%rdi
    7418:	0f 8c 0a ff ff ff    	jl     7328 <verify+0x1d8>
    741e:	4c 39 df             	cmp    %r11,%rdi
    7421:	0f 8f 99 fe ff ff    	jg     72c0 <verify+0x170>
    7427:	49 39 c1             	cmp    %rax,%r9
    742a:	0f 8d f8 fe ff ff    	jge    7328 <verify+0x1d8>
    7430:	48 39 f1             	cmp    %rsi,%rcx
    7433:	0f 85 87 fe ff ff    	jne    72c0 <verify+0x170>
    7439:	4c 39 c2             	cmp    %r8,%rdx
    743c:	0f 85 7e fe ff ff    	jne    72c0 <verify+0x170>
    7442:	4c 39 df             	cmp    %r11,%rdi
    7445:	0f 84 dd fe ff ff    	je     7328 <verify+0x1d8>
    744b:	e9 70 fe ff ff       	jmp    72c0 <verify+0x170>
    7450:	4c 39 c2             	cmp    %r8,%rdx
    7453:	0f 8c 5a fe ff ff    	jl     72b3 <verify+0x163>
    7459:	4c 39 df             	cmp    %r11,%rdi
    745c:	7e c9                	jle    7427 <verify+0x2d7>
    745e:	4c 39 c2             	cmp    %r8,%rdx
    7461:	0f 85 59 fe ff ff    	jne    72c0 <verify+0x170>
    7467:	49 39 c1             	cmp    %rax,%r9
    746a:	0f 8f 50 fe ff ff    	jg     72c0 <verify+0x170>
    7470:	e9 b3 fe ff ff       	jmp    7328 <verify+0x1d8>
    7475:	48 81 44 24 18 e0 00 00 00 	addq   $0xe0,0x18(%rsp)
    747e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7482:	45 39 e6             	cmp    %r12d,%r14d
    7485:	74 08                	je     748f <verify+0x33f>
    7487:	41 89 c6             	mov    %eax,%r14d
    748a:	e9 ea fc ff ff       	jmp    7179 <verify+0x29>
    748f:	48 83 c4 58          	add    $0x58,%rsp
    7493:	31 c0                	xor    %eax,%eax
    7495:	5b                   	pop    %rbx
    7496:	5d                   	pop    %rbp
    7497:	41 5c                	pop    %r12
    7499:	41 5d                	pop    %r13
    749b:	41 5e                	pop    %r14
    749d:	41 5f                	pop    %r15
    749f:	c3                   	ret
    74a0:	31 c0                	xor    %eax,%eax
    74a2:	c3                   	ret

Disassembly of section .fini:

00000000000074a4 <_fini>:
    74a4:	f3 0f 1e fa          	endbr64
    74a8:	48 83 ec 08          	sub    $0x8,%rsp
    74ac:	48 83 c4 08          	add    $0x8,%rsp
    74b0:	c3                   	ret
