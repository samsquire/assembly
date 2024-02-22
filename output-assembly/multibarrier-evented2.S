
multibarrier-evented2:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8d 05 91 23 00 00 	lea    0x2391(%rip),%rax        # 43a0 <__gmon_start__>
    200f:	48 85 c0             	test   %rax,%rax
    2012:	74 02                	je     2016 <_init+0x16>
    2014:	ff d0                	call   *%rax
    2016:	48 83 c4 08          	add    $0x8,%rsp
    201a:	c3                   	ret

Disassembly of section .plt:

0000000000002020 <.plt>:
    2020:	ff 35 2a 8e 00 00    	push   0x8e2a(%rip)        # ae50 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 2c 8e 00 00    	jmp    *0x8e2c(%rip)        # ae58 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    22f0:	f3 0f 1e fa          	endbr64
    22f4:	68 2c 00 00 00       	push   $0x2c
    22f9:	e9 22 fd ff ff       	jmp    2020 <_init+0x20>
    22fe:	66 90                	xchg   %ax,%ax
    2300:	f3 0f 1e fa          	endbr64
    2304:	68 2d 00 00 00       	push   $0x2d
    2309:	e9 12 fd ff ff       	jmp    2020 <_init+0x20>
    230e:	66 90                	xchg   %ax,%ax

Disassembly of section .plt.got:

0000000000002310 <__cxa_finalize@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 de 8c 00 00    	jmp    *0x8cde(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000002320 <free@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 36 8b 00 00    	jmp    *0x8b36(%rip)        # ae60 <free@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <putchar@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 2e 8b 00 00    	jmp    *0x8b2e(%rip)        # ae68 <putchar@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <pthread_setaffinity_np@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 26 8b 00 00    	jmp    *0x8b26(%rip)        # ae70 <pthread_setaffinity_np@GLIBC_2.34>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <puts@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 1e 8b 00 00    	jmp    *0x8b1e(%rip)        # ae78 <puts@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <setsockopt@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 16 8b 00 00    	jmp    *0x8b16(%rip)        # ae80 <setsockopt@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <clock_gettime@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 0e 8b 00 00    	jmp    *0x8b0e(%rip)        # ae88 <clock_gettime@GLIBC_2.17>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <fclose@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 06 8b 00 00    	jmp    *0x8b06(%rip)        # ae90 <fclose@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <strlen@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 fe 8a 00 00    	jmp    *0x8afe(%rip)        # ae98 <strlen@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <__stack_chk_fail@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 f6 8a 00 00    	jmp    *0x8af6(%rip)        # aea0 <__stack_chk_fail@GLIBC_2.4>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <io_uring_submit@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 ee 8a 00 00    	jmp    *0x8aee(%rip)        # aea8 <io_uring_submit@LIBURING_2.0>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <nanosleep@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 e6 8a 00 00    	jmp    *0x8ae6(%rip)        # aeb0 <nanosleep@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <strrchr@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 de 8a 00 00    	jmp    *0x8ade(%rip)        # aeb8 <strrchr@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <fputs@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 d6 8a 00 00    	jmp    *0x8ad6(%rip)        # aec0 <fputs@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <close@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 ce 8a 00 00    	jmp    *0x8ace(%rip)        # aec8 <close@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <strtok_r@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 c6 8a 00 00    	jmp    *0x8ac6(%rip)        # aed0 <strtok_r@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <read@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 be 8a 00 00    	jmp    *0x8abe(%rip)        # aed8 <read@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <calloc@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 b6 8a 00 00    	jmp    *0x8ab6(%rip)        # aee0 <calloc@GLIBC_2.2.5>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <strcmp@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 ae 8a 00 00    	jmp    *0x8aae(%rip)        # aee8 <strcmp@GLIBC_2.2.5>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <__monstartup@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 a6 8a 00 00    	jmp    *0x8aa6(%rip)        # aef0 <__monstartup@GLIBC_2.2.5>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <__memcpy_chk@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 9e 8a 00 00    	jmp    *0x8a9e(%rip)        # aef8 <__memcpy_chk@GLIBC_2.3.4>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <stat@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 96 8a 00 00    	jmp    *0x8a96(%rip)        # af00 <stat@GLIBC_2.33>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <memcpy@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 8e 8a 00 00    	jmp    *0x8a8e(%rip)        # af08 <memcpy@GLIBC_2.14>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <io_uring_queue_init@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 86 8a 00 00    	jmp    *0x8a86(%rip)        # af10 <io_uring_queue_init@LIBURING_2.0>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <eventfd_write@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 7e 8a 00 00    	jmp    *0x8a7e(%rip)        # af18 <eventfd_write@GLIBC_2.7>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <malloc@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 76 8a 00 00    	jmp    *0x8a76(%rip)        # af20 <malloc@GLIBC_2.2.5>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <listen@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 6e 8a 00 00    	jmp    *0x8a6e(%rip)        # af28 <listen@GLIBC_2.2.5>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <__strcpy_chk@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 66 8a 00 00    	jmp    *0x8a66(%rip)        # af30 <__strcpy_chk@GLIBC_2.3.4>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <__io_uring_get_cqe@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 5e 8a 00 00    	jmp    *0x8a5e(%rip)        # af38 <__io_uring_get_cqe@LIBURING_2.0>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <__printf_chk@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 56 8a 00 00    	jmp    *0x8a56(%rip)        # af40 <__printf_chk@GLIBC_2.3.4>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <bind@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 4e 8a 00 00    	jmp    *0x8a4e(%rip)        # af48 <bind@GLIBC_2.2.5>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <pthread_create@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 46 8a 00 00    	jmp    *0x8a46(%rip)        # af50 <pthread_create@GLIBC_2.34>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <open@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 3e 8a 00 00    	jmp    *0x8a3e(%rip)        # af58 <open@GLIBC_2.2.5>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <fopen@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 36 8a 00 00    	jmp    *0x8a36(%rip)        # af60 <fopen@GLIBC_2.2.5>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <perror@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 2e 8a 00 00    	jmp    *0x8a2e(%rip)        # af68 <perror@GLIBC_2.2.5>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <__cxa_atexit@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 26 8a 00 00    	jmp    *0x8a26(%rip)        # af70 <__cxa_atexit@GLIBC_2.2.5>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <exit@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 1e 8a 00 00    	jmp    *0x8a1e(%rip)        # af78 <exit@GLIBC_2.2.5>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <eventfd@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 16 8a 00 00    	jmp    *0x8a16(%rip)        # af80 <eventfd@GLIBC_2.7>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <fwrite@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 0e 8a 00 00    	jmp    *0x8a0e(%rip)        # af88 <fwrite@GLIBC_2.2.5>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <__fprintf_chk@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 06 8a 00 00    	jmp    *0x8a06(%rip)        # af90 <__fprintf_chk@GLIBC_2.3.4>
    258a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002590 <io_uring_register_eventfd@plt>:
    2590:	f3 0f 1e fa          	endbr64
    2594:	ff 25 fe 89 00 00    	jmp    *0x89fe(%rip)        # af98 <io_uring_register_eventfd@LIBURING_2.0>
    259a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025a0 <pthread_join@plt>:
    25a0:	f3 0f 1e fa          	endbr64
    25a4:	ff 25 f6 89 00 00    	jmp    *0x89f6(%rip)        # afa0 <pthread_join@GLIBC_2.34>
    25aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025b0 <strerror@plt>:
    25b0:	f3 0f 1e fa          	endbr64
    25b4:	ff 25 ee 89 00 00    	jmp    *0x89ee(%rip)        # afa8 <strerror@GLIBC_2.2.5>
    25ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025c0 <pthread_mutex_init@plt>:
    25c0:	f3 0f 1e fa          	endbr64
    25c4:	ff 25 e6 89 00 00    	jmp    *0x89e6(%rip)        # afb0 <pthread_mutex_init@GLIBC_2.2.5>
    25ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025d0 <__ctype_tolower_loc@plt>:
    25d0:	f3 0f 1e fa          	endbr64
    25d4:	ff 25 de 89 00 00    	jmp    *0x89de(%rip)        # afb8 <__ctype_tolower_loc@GLIBC_2.3>
    25da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025e0 <__sprintf_chk@plt>:
    25e0:	f3 0f 1e fa          	endbr64
    25e4:	ff 25 d6 89 00 00    	jmp    *0x89d6(%rip)        # afc0 <__sprintf_chk@GLIBC_2.3.4>
    25ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025f0 <socket@plt>:
    25f0:	f3 0f 1e fa          	endbr64
    25f4:	ff 25 ce 89 00 00    	jmp    *0x89ce(%rip)        # afc8 <socket@GLIBC_2.2.5>
    25fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000002600 <fatal_error>:
  if (a > b) { return a; }
  if (b > a) { return b; }
  return a;
}

void fatal_error(const char *syscall) {
    2600:	f3 0f 1e fa          	endbr64
    2604:	55                   	push   %rbp
    2605:	48 89 e5             	mov    %rsp,%rbp
    2608:	ff 15 da 89 00 00    	call   *0x89da(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    perror(syscall);
    260e:	e8 1d ff ff ff       	call   2530 <perror@plt>
    exit(1);
    2613:	bf 01 00 00 00       	mov    $0x1,%edi
    2618:	e8 33 ff ff ff       	call   2550 <exit@plt>

000000000000261d <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    261d:	48 8d 3d 02 5c 00 00 	lea    0x5c02(%rip),%rdi        # 8226 <_IO_stdin_used+0x226>
    2624:	e8 d7 ff ff ff       	call   2600 <fatal_error>

0000000000002629 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    2629:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    262f:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2637:	0f 0b                	ud2

0000000000002639 <add_read_request.cold>:
    2639:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2641:	0f 0b                	ud2

0000000000002643 <_send_static_string_content.cold>:
    2643:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    2649:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2651:	0f 0b                	ud2

0000000000002653 <add_accept_request.cold>:
    2653:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    265b:	0f 0b                	ud2

000000000000265d <io_thread.cold>:
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    265d:	48 8d 3d 92 5b 00 00 	lea    0x5b92(%rip),%rdi        # 81f6 <_IO_stdin_used+0x1f6>
    2664:	e8 97 ff ff ff       	call   2600 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    2669:	48 8d 3d 0a 5b 00 00 	lea    0x5b0a(%rip),%rdi        # 817a <_IO_stdin_used+0x17a>
    2670:	e8 8b ff ff ff       	call   2600 <fatal_error>
    fatal_error("listen()");
    2675:	48 8d 3d 1e 5b 00 00 	lea    0x5b1e(%rip),%rdi        # 819a <_IO_stdin_used+0x19a>
    267c:	e8 7f ff ff ff       	call   2600 <fatal_error>
    2681:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2689:	0f 0b                	ud2
    268b:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2693:	0f 0b                	ud2
      fatal_error("socket()");
    2695:	48 8d 3d d5 5a 00 00 	lea    0x5ad5(%rip),%rdi        # 8171 <_IO_stdin_used+0x171>
    269c:	e8 5f ff ff ff       	call   2600 <fatal_error>
      fatal_error("bind()");
    26a1:	48 8d 3d eb 5a 00 00 	lea    0x5aeb(%rip),%rdi        # 8193 <_IO_stdin_used+0x193>
    26a8:	e8 53 ff ff ff       	call   2600 <fatal_error>
    26ad:	0f 1f 00             	nopl   (%rax)

00000000000026b0 <main>:
    }


  return 0;
}
int main() {
    26b0:	f3 0f 1e fa          	endbr64
    26b4:	55                   	push   %rbp
    26b5:	48 89 e5             	mov    %rsp,%rbp
    26b8:	41 57                	push   %r15
    26ba:	41 56                	push   %r14
    26bc:	41 55                	push   %r13
    26be:	41 54                	push   %r12
    26c0:	53                   	push   %rbx
    26c1:	48 81 ec 08 01 00 00 	sub    $0x108,%rsp
    26c8:	ff 15 1a 89 00 00    	call   *0x891a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    26ce:	48 8d 3d 93 5f 00 00 	lea    0x5f93(%rip),%rdi        # 8668 <_IO_stdin_used+0x668>
    26d5:	4c 8d 25 a0 5c 00 00 	lea    0x5ca0(%rip),%r12        # 837c <_IO_stdin_used+0x37c>
    26dc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    26e5:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    26e9:	48 8d 05 20 1e 00 00 	lea    0x1e20(%rip),%rax        # 4510 <barriered_reset>
    26f0:	66 48 0f 6e e0       	movq   %rax,%xmm4
    26f5:	0f 16 25 44 85 00 00 	movhps 0x8544(%rip),%xmm4        # ac40 <__do_global_dtors_aux_fini_array_entry+0x8>
    26fc:	0f 29 a5 00 ff ff ff 	movaps %xmm4,-0x100(%rbp)
    2703:	e8 48 fc ff ff       	call   2350 <puts@plt>
    2708:	bf 0a 00 00 00       	mov    $0xa,%edi
    270d:	e8 1e fc ff ff       	call   2330 <putchar@plt>
    2712:	ba 01 00 00 00       	mov    $0x1,%edx
    2717:	48 8d 35 56 5b 00 00 	lea    0x5b56(%rip),%rsi        # 8274 <_IO_stdin_used+0x274>
    271e:	31 c0                	xor    %eax,%eax
    2720:	bf 01 00 00 00       	mov    $0x1,%edi
    2725:	e8 b6 fd ff ff       	call   24e0 <__printf_chk@plt>
    272a:	ba 06 00 00 00       	mov    $0x6,%edx
    272f:	48 8d 35 4e 5b 00 00 	lea    0x5b4e(%rip),%rsi        # 8284 <_IO_stdin_used+0x284>
    2736:	31 c0                	xor    %eax,%eax
    2738:	bf 01 00 00 00       	mov    $0x1,%edi
    273d:	e8 9e fd ff ff       	call   24e0 <__printf_chk@plt>
    2742:	ba 03 00 00 00       	mov    $0x3,%edx
    2747:	48 8d 35 4b 5b 00 00 	lea    0x5b4b(%rip),%rsi        # 8299 <_IO_stdin_used+0x299>
    274e:	31 c0                	xor    %eax,%eax
    2750:	bf 01 00 00 00       	mov    $0x1,%edi
    2755:	e8 86 fd ff ff       	call   24e0 <__printf_chk@plt>
    275a:	ba 02 00 00 00       	mov    $0x2,%edx
    275f:	48 8d 35 43 5b 00 00 	lea    0x5b43(%rip),%rsi        # 82a9 <_IO_stdin_used+0x2a9>
    2766:	31 c0                	xor    %eax,%eax
    2768:	bf 01 00 00 00       	mov    $0x1,%edi
    276d:	e8 6e fd ff ff       	call   24e0 <__printf_chk@plt>
    2772:	48 8d 3d 46 5b 00 00 	lea    0x5b46(%rip),%rdi        # 82bf <_IO_stdin_used+0x2bf>
    2779:	e8 d2 fb ff ff       	call   2350 <puts@plt>
    277e:	ba 02 00 00 00       	mov    $0x2,%edx
    2783:	48 8d 35 51 5b 00 00 	lea    0x5b51(%rip),%rsi        # 82db <_IO_stdin_used+0x2db>
    278a:	31 c0                	xor    %eax,%eax
    278c:	bf 01 00 00 00       	mov    $0x1,%edi
    2791:	e8 4a fd ff ff       	call   24e0 <__printf_chk@plt>
    2796:	ba 0a 00 00 00       	mov    $0xa,%edx
    279b:	48 8d 35 53 5b 00 00 	lea    0x5b53(%rip),%rsi        # 82f5 <_IO_stdin_used+0x2f5>
    27a2:	31 c0                	xor    %eax,%eax
    27a4:	bf 01 00 00 00       	mov    $0x1,%edi
    27a9:	e8 32 fd ff ff       	call   24e0 <__printf_chk@plt>
    27ae:	ba 01 00 00 00       	mov    $0x1,%edx
    27b3:	48 8d 35 4f 5b 00 00 	lea    0x5b4f(%rip),%rsi        # 8309 <_IO_stdin_used+0x309>
    27ba:	31 c0                	xor    %eax,%eax
    27bc:	bf 01 00 00 00       	mov    $0x1,%edi
    27c1:	e8 1a fd ff ff       	call   24e0 <__printf_chk@plt>
    27c6:	ba 01 00 00 00       	mov    $0x1,%edx
    27cb:	48 8d 35 48 5b 00 00 	lea    0x5b48(%rip),%rsi        # 831a <_IO_stdin_used+0x31a>
    27d2:	31 c0                	xor    %eax,%eax
    27d4:	bf 01 00 00 00       	mov    $0x1,%edi
    27d9:	e8 02 fd ff ff       	call   24e0 <__printf_chk@plt>
    27de:	ba 02 00 00 00       	mov    $0x2,%edx
    27e3:	48 8d 35 48 5b 00 00 	lea    0x5b48(%rip),%rsi        # 8332 <_IO_stdin_used+0x332>
    27ea:	31 c0                	xor    %eax,%eax
    27ec:	bf 01 00 00 00       	mov    $0x1,%edi
    27f1:	e8 ea fc ff ff       	call   24e0 <__printf_chk@plt>
    27f6:	ba 01 00 00 00       	mov    $0x1,%edx
    27fb:	48 8d 35 ce 5e 00 00 	lea    0x5ece(%rip),%rsi        # 86d0 <_IO_stdin_used+0x6d0>
    2802:	31 c0                	xor    %eax,%eax
    2804:	bf 01 00 00 00       	mov    $0x1,%edi
    2809:	e8 d2 fc ff ff       	call   24e0 <__printf_chk@plt>
    280e:	ba 01 00 00 00       	mov    $0x1,%edx
    2813:	48 8d 35 e6 5e 00 00 	lea    0x5ee6(%rip),%rsi        # 8700 <_IO_stdin_used+0x700>
    281a:	31 c0                	xor    %eax,%eax
    281c:	bf 01 00 00 00       	mov    $0x1,%edi
    2821:	e8 ba fc ff ff       	call   24e0 <__printf_chk@plt>
    2826:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    282b:	48 8d 35 1c 5b 00 00 	lea    0x5b1c(%rip),%rsi        # 834e <_IO_stdin_used+0x34e>
    2832:	31 c0                	xor    %eax,%eax
    2834:	bf 01 00 00 00       	mov    $0x1,%edi
    2839:	e8 a2 fc ff ff       	call   24e0 <__printf_chk@plt>
    283e:	ba 05 00 00 00       	mov    $0x5,%edx
    2843:	48 8d 35 1e 5b 00 00 	lea    0x5b1e(%rip),%rsi        # 8368 <_IO_stdin_used+0x368>
    284a:	31 c0                	xor    %eax,%eax
    284c:	bf 01 00 00 00       	mov    $0x1,%edi
    2851:	e8 8a fc ff ff       	call   24e0 <__printf_chk@plt>
    2856:	48 8d 3d 98 58 00 00 	lea    0x5898(%rip),%rdi        # 80f5 <_IO_stdin_used+0xf5>
    285d:	e8 ee fa ff ff       	call   2350 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2862:	be 18 00 00 00       	mov    $0x18,%esi
    2867:	bf 03 00 00 00       	mov    $0x3,%edi
    286c:	e8 af fb ff ff       	call   2420 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2871:	be d8 00 00 00       	mov    $0xd8,%esi
    2876:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    287b:	48 89 85 20 ff ff ff 	mov    %rax,-0xe0(%rbp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2882:	e8 99 fb ff ff       	call   2420 <calloc@plt>
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    2887:	be 28 00 00 00       	mov    $0x28,%esi
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
    288c:	45 31 ff             	xor    %r15d,%r15d
  int cc = 0; 
    288f:	45 31 f6             	xor    %r14d,%r14d
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    2892:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2897:	48 89 45 88          	mov    %rax,-0x78(%rbp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    289b:	e8 80 fb ff ff       	call   2420 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28a0:	be 28 00 00 00       	mov    $0x28,%esi
    28a5:	bf 64 00 00 00       	mov    $0x64,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28aa:	48 89 85 f0 fe ff ff 	mov    %rax,-0x110(%rbp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28b1:	e8 6a fb ff ff       	call   2420 <calloc@plt>
    28b6:	48 89 85 e8 fe ff ff 	mov    %rax,-0x118(%rbp)
    for (int y = 0 ; y < total_threads; y++) {
    28bd:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
int main() {
    28c1:	49 89 c5             	mov    %rax,%r13
    for (int y = 0 ; y < total_threads; y++) {
    28c4:	31 db                	xor    %ebx,%ebx
    28c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    28d0:	42 8d 14 33          	lea    (%rbx,%r14,1),%edx
    28d4:	41 89 d8             	mov    %ebx,%r8d
    28d7:	44 89 f9             	mov    %r15d,%ecx
    28da:	4c 89 e6             	mov    %r12,%rsi
    28dd:	bf 01 00 00 00       	mov    $0x1,%edi
    28e2:	31 c0                	xor    %eax,%eax
    28e4:	83 c3 01             	add    $0x1,%ebx
    28e7:	e8 f4 fb ff ff       	call   24e0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    28ec:	4c 89 ef             	mov    %r13,%rdi
    28ef:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    28f1:	49 83 c5 28          	add    $0x28,%r13
      pthread_mutex_init(&swapmutex[cc++], NULL);
    28f5:	e8 c6 fc ff ff       	call   25c0 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    28fa:	83 fb 0a             	cmp    $0xa,%ebx
    28fd:	75 d1                	jne    28d0 <main+0x220>
    28ff:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    2903:	41 83 c6 0a          	add    $0xa,%r14d
  for (int x = 0 ; x < total_threads; x++) {
    2907:	41 83 c7 01          	add    $0x1,%r15d
    290b:	48 05 90 01 00 00    	add    $0x190,%rax
    2911:	41 83 fe 64          	cmp    $0x64,%r14d
    2915:	75 a6                	jne    28bd <main+0x20d>
    2917:	ba 06 00 00 00       	mov    $0x6,%edx
    291c:	48 8d 35 69 5a 00 00 	lea    0x5a69(%rip),%rsi        # 838c <_IO_stdin_used+0x38c>
    2923:	bf 01 00 00 00       	mov    $0x1,%edi
    2928:	31 c0                	xor    %eax,%eax
    292a:	e8 b1 fb ff ff       	call   24e0 <__printf_chk@plt>
    292f:	ba 0c 00 00 00       	mov    $0xc,%edx
    2934:	48 8d 35 67 5a 00 00 	lea    0x5a67(%rip),%rsi        # 83a2 <_IO_stdin_used+0x3a2>
    293b:	31 c0                	xor    %eax,%eax
    293d:	bf 01 00 00 00       	mov    $0x1,%edi
    2942:	e8 99 fb ff ff       	call   24e0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2947:	be 10 00 00 00       	mov    $0x10,%esi
    294c:	bf 0c 00 00 00       	mov    $0xc,%edi
    2951:	e8 ca fa ff ff       	call   2420 <calloc@plt>
    2956:	48 89 85 10 ff ff ff 	mov    %rax,-0xf0(%rbp)
    295d:	49 89 c7             	mov    %rax,%r15
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2960:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2967:	49 89 c6             	mov    %rax,%r14
    buffers[x].count = buffer_size;
    296a:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2971:	be 00 01 00 00       	mov    $0x100,%esi
    2976:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    297b:	49 83 c6 10          	add    $0x10,%r14
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    297f:	e8 9c fa ff ff       	call   2420 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2984:	be 20 00 00 00       	mov    $0x20,%esi
    2989:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    298e:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    2992:	49 89 c4             	mov    %rax,%r12
      buffers[x].buffer[y].available = 0;
    2995:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    299f:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29a9:	e8 72 fa ff ff       	call   2420 <calloc@plt>
    29ae:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
  for (int x = 0 ; x < buffers_required; x++) {
    29b6:	4c 39 f3             	cmp    %r14,%rbx
    29b9:	75 af                	jne    296a <main+0x2ba>
    29bb:	48 8b b5 20 ff ff ff 	mov    -0xe0(%rbp),%rsi
    29c2:	4c 89 f8             	mov    %r15,%rax
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  int swap = 0;
  for (int k = 0 ; k < group_count ; k++) {
    29c5:	45 31 ed             	xor    %r13d,%r13d
  int dataid = 0;
    29c8:	45 31 e4             	xor    %r12d,%r12d
    29cb:	48 8b 5d 88          	mov    -0x78(%rbp),%rbx
  int swap = 0;
    29cf:	c7 45 90 00 00 00 00 	movl   $0x0,-0x70(%rbp)
    29d6:	48 89 b5 28 ff ff ff 	mov    %rsi,-0xd8(%rbp)
  int cur_buffer = 0;
    29dd:	c7 85 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rbp)
    29e7:	49 89 df             	mov    %rbx,%r15
  int curcpu = 0;
    29ea:	c7 85 44 ff ff ff 00 00 00 00 	movl   $0x0,-0xbc(%rbp)
    29f4:	48 89 9d 18 ff ff ff 	mov    %rbx,-0xe8(%rbp)
    29fb:	48 89 c3             	mov    %rax,%rbx
    for (int d = 0 ; d < threads_per_group ; d++) {
    29fe:	48 63 85 40 ff ff ff 	movslq -0xc0(%rbp),%rax
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2a05:	4d 89 f9             	mov    %r15,%r9
    2a08:	45 89 ee             	mov    %r13d,%r14d
    2a0b:	4c 89 bd e0 fe ff ff 	mov    %r15,-0x120(%rbp)
    2a12:	48 89 b5 f8 fe ff ff 	mov    %rsi,-0x108(%rbp)
    2a19:	48 c1 e0 04          	shl    $0x4,%rax
    2a1d:	48 89 9d d8 fe ff ff 	mov    %rbx,-0x128(%rbp)
    2a24:	48 01 d8             	add    %rbx,%rax
    2a27:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
    2a2e:	43 8d 44 2d 00       	lea    0x0(%r13,%r13,1),%eax
    2a33:	8d 78 01             	lea    0x1(%rax),%edi
    2a36:	83 c0 03             	add    $0x3,%eax
    2a39:	89 7d 98             	mov    %edi,-0x68(%rbp)
    2a3c:	89 85 38 ff ff ff    	mov    %eax,-0xc8(%rbp)
    2a42:	8b 7d 98             	mov    -0x68(%rbp),%edi
    2a45:	44 89 f2             	mov    %r14d,%edx
    2a48:	48 8d 35 d9 5c 00 00 	lea    0x5cd9(%rip),%rsi        # 8728 <_IO_stdin_used+0x728>
    2a4f:	31 c0                	xor    %eax,%eax
    2a51:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
      int x = (k * threads_per_group) + d;
    2a55:	44 8d 7f ff          	lea    -0x1(%rdi),%r15d
    2a59:	bf 01 00 00 00       	mov    $0x1,%edi
    2a5e:	44 89 f9             	mov    %r15d,%ecx
    2a61:	44 89 7d a0          	mov    %r15d,-0x60(%rbp)
    2a65:	e8 76 fa ff ff       	call   24e0 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a6a:	be 08 00 00 00       	mov    $0x8,%esi
    2a6f:	bf 02 00 00 00       	mov    $0x2,%edi
    2a74:	e8 a7 f9 ff ff       	call   2420 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a79:	be 80 00 00 00       	mov    $0x80,%esi
    2a7e:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a83:	48 89 c3             	mov    %rax,%rbx
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a86:	e8 95 f9 ff ff       	call   2420 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2a8b:	41 83 e7 01          	and    $0x1,%r15d
    2a8f:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
    2a93:	44 89 bd 60 ff ff ff 	mov    %r15d,-0xa0(%rbp)
    2a9a:	45 89 f8             	mov    %r15d,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a9d:	49 89 c5             	mov    %rax,%r13
        other = abs(x - 1) % total_threads;
    2aa0:	44 8b 7d 98          	mov    -0x68(%rbp),%r15d
      if (x % 2 == 1) {
    2aa4:	0f 84 dd 10 00 00    	je     3b87 <main+0x14d7>
        other = abs(x - 1) % total_threads;
    2aaa:	41 8d 47 fe          	lea    -0x2(%r15),%eax
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    2aae:	48 8b 75 88          	mov    -0x78(%rbp),%rsi
        my_thread_data[1] = &thread_data[x]; 
    2ab2:	4c 89 ca             	mov    %r9,%rdx
        other = abs(x - 1) % total_threads;
    2ab5:	48 89 c1             	mov    %rax,%rcx
        my_thread_data[0] = &thread_data[other]; 
    2ab8:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2abc:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    2ac0:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2ac4:	48 8d 73 08          	lea    0x8(%rbx),%rsi
    2ac8:	48 89 b5 70 ff ff ff 	mov    %rsi,-0x90(%rbp)
        thread_data[x].protected_state = &protected_state[k];
    2acf:	48 8b bd f8 fe ff ff 	mov    -0x108(%rbp),%rdi
        thread_data[x].thread_index = 1;
    2ad6:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2ada:	48 8d 35 77 5c 00 00 	lea    0x5c77(%rip),%rsi        # 8758 <_IO_stdin_used+0x758>
    2ae1:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    2ae5:	8b 55 a0             	mov    -0x60(%rbp),%edx
        thread_data[x].protected_state = &protected_state[k];
    2ae8:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2aec:	bf 01 00 00 00       	mov    $0x1,%edi
    2af1:	48 89 03             	mov    %rax,(%rbx)
    2af4:	31 c0                	xor    %eax,%eax
    2af6:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    2afa:	89 4d b8             	mov    %ecx,-0x48(%rbp)
    2afd:	e8 de f9 ff ff       	call   24e0 <__printf_chk@plt>
      thread_data[x].other = other;
    2b02:	8b 4d b8             	mov    -0x48(%rbp),%ecx
    2b05:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    2b09:	31 c0                	xor    %eax,%eax
    2b0b:	8b 55 a0             	mov    -0x60(%rbp),%edx
    2b0e:	48 8d 35 73 5c 00 00 	lea    0x5c73(%rip),%rsi        # 8788 <_IO_stdin_used+0x788>
    2b15:	bf 01 00 00 00       	mov    $0x1,%edi
    2b1a:	41 89 89 b8 00 00 00 	mov    %ecx,0xb8(%r9)
    2b21:	8b 8d 44 ff ff ff    	mov    -0xbc(%rbp),%ecx
    2b27:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
    2b2b:	e8 b0 f9 ff ff       	call   24e0 <__printf_chk@plt>
        if (x < thread_count) {
    2b30:	83 7d a0 01          	cmpl   $0x1,-0x60(%rbp)
    2b34:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
    2b38:	0f 87 6e 10 00 00    	ja     3bac <main+0x14fc>
          CPU_SET(curcpu, sendercpu);
    2b3e:	48 63 85 44 ff ff ff 	movslq -0xbc(%rbp),%rax
    2b45:	48 89 c7             	mov    %rax,%rdi
    2b48:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2b4e:	77 13                	ja     2b63 <main+0x4b3>
    2b50:	48 c1 e8 06          	shr    $0x6,%rax
    2b54:	ba 01 00 00 00       	mov    $0x1,%edx
    2b59:	89 f9                	mov    %edi,%ecx
    2b5b:	48 d3 e2             	shl    %cl,%rdx
    2b5e:	49 09 54 c5 00       	or     %rdx,0x0(%r13,%rax,8)
          curcpu += 2;
    2b63:	83 85 44 ff ff ff 02 	addl   $0x2,-0xbc(%rbp)
      thread_data[x].swapmutex = swapmutex;
    2b6a:	48 8b 85 e8 fe ff ff 	mov    -0x118(%rbp),%rax
      thread_data[x].threads = my_thread_data;
    2b71:	49 89 59 18          	mov    %rbx,0x18(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b75:	be 10 00 00 00       	mov    $0x10,%esi
    2b7a:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].kind = KERNEL_THREAD;
    2b7f:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
            data[0].messages_count = 0;
    2b86:	44 89 e3             	mov    %r12d,%ebx
      thread_data[x].swapmutex = swapmutex;
    2b89:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2b90:	48 8b 85 f0 fe ff ff 	mov    -0x110(%rbp),%rax
      thread_data[x].cpu_set = sendercpu;
    2b97:	4d 89 a9 b0 00 00 00 	mov    %r13,0xb0(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2b9e:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].real_thread_index = x;
    2ba5:	8b 45 a0             	mov    -0x60(%rbp),%eax
      thread_data[x].task_count = total_barrier_count;
    2ba8:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].real_thread_index = x;
    2bb0:	41 89 41 08          	mov    %eax,0x8(%r9)
      thread_data[x].all_threads = thread_data;
    2bb4:	48 8b 45 88          	mov    -0x78(%rbp),%rax
      thread_data[x].task_count = total_barrier_count;
    2bb8:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
      thread_data[x].all_threads = thread_data;
    2bbc:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2bc0:	48 8b 05 09 61 00 00 	mov    0x6109(%rip),%rax        # 8cd0 <_IO_stdin_used+0xcd0>
    2bc7:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2bce:	48 8b 05 03 61 00 00 	mov    0x6103(%rip),%rax        # 8cd8 <_IO_stdin_used+0xcd8>
    2bd5:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2bd9:	e8 42 f8 ff ff       	call   2420 <calloc@plt>
    2bde:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2be2:	be 10 00 00 00       	mov    $0x10,%esi
    2be7:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2bec:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2bf0:	e8 2b f8 ff ff       	call   2420 <calloc@plt>
    2bf5:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bf9:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2bfe:	66 0f 6f 25 9a 60 00 00 	movdqa 0x609a(%rip),%xmm4        # 8ca0 <_IO_stdin_used+0xca0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c06:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2c0b:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2c0f:	41 0f 11 a1 80 00 00 00 	movups %xmm4,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c17:	e8 04 f8 ff ff       	call   2420 <calloc@plt>
    2c1c:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c20:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2c25:	66 0f 6f 0d 73 60 00 00 	movdqa 0x6073(%rip),%xmm1        # 8ca0 <_IO_stdin_used+0xca0>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c2d:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c32:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2c39:	41 0f 11 89 98 00 00 00 	movups %xmm1,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c41:	e8 da f7 ff ff       	call   2420 <calloc@plt>
        thread_data[x].tasks = barriers;
    2c46:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c4a:	4c 89 ff             	mov    %r15,%rdi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2c4d:	45 31 ff             	xor    %r15d,%r15d
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c50:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2c53:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c57:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
    2c5c:	48 0f af f8          	imul   %rax,%rdi
            data[0].messages_count = 0;
    2c60:	4c 89 8d 68 ff ff ff 	mov    %r9,-0x98(%rbp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c67:	48 c1 ef 22          	shr    $0x22,%rdi
    2c6b:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2c6e:	8b 7d 98             	mov    -0x68(%rbp),%edi
    2c71:	01 c0                	add    %eax,%eax
    2c73:	29 c7                	sub    %eax,%edi
            data[0].messages_count = 0;
    2c75:	89 bd 3c ff ff ff    	mov    %edi,-0xc4(%rbp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c7b:	49 63 c7             	movslq %r15d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c7e:	bf 06 00 00 00       	mov    $0x6,%edi
    2c83:	be 40 00 00 00       	mov    $0x40,%esi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c88:	45 31 e4             	xor    %r12d,%r12d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c8b:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)
    2c92:	48 c1 e0 09          	shl    $0x9,%rax
    2c96:	4c 8d 2c 02          	lea    (%rdx,%rax,1),%r13
    2c9a:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    2c9e:	48 8d 05 1b 18 00 00 	lea    0x181b(%rip),%rax        # 44c0 <do_protected_write>
    2ca5:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2cac:	e8 6f f7 ff ff       	call   2420 <calloc@plt>
    2cb1:	8b bd 60 ff ff ff    	mov    -0xa0(%rbp),%edi
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2cb7:	49 89 85 70 01 00 00 	mov    %rax,0x170(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2cbe:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cc1:	85 ff                	test   %edi,%edi
    2cc3:	0f 84 59 06 00 00    	je     3322 <main+0xc72>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2cc9:	8b 45 98             	mov    -0x68(%rbp),%eax
    2ccc:	44 89 7d b8          	mov    %r15d,-0x48(%rbp)
    2cd0:	49 89 cd             	mov    %rcx,%r13
    2cd3:	48 89 8d 30 ff ff ff 	mov    %rcx,-0xd0(%rbp)
    2cda:	83 e8 02             	sub    $0x2,%eax
    2cdd:	89 85 48 ff ff ff    	mov    %eax,-0xb8(%rbp)
    2ce3:	eb 15                	jmp    2cfa <main+0x64a>
    2ce5:	0f 1f 00             	nopl   (%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ce8:	41 83 c4 01          	add    $0x1,%r12d
    2cec:	49 83 c5 40          	add    $0x40,%r13
    2cf0:	41 83 fc 06          	cmp    $0x6,%r12d
    2cf4:	0f 84 55 01 00 00    	je     2e4f <main+0x79f>
            int group_of = b / threads_per_group;
    2cfa:	45 89 e7             	mov    %r12d,%r15d
    2cfd:	31 c0                	xor    %eax,%eax
    2cff:	44 89 e2             	mov    %r12d,%edx
    2d02:	bf 01 00 00 00       	mov    $0x1,%edi
    2d07:	41 d1 ff             	sar    %r15d
    2d0a:	48 8d 35 ab 56 00 00 	lea    0x56ab(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2d11:	44 89 f9             	mov    %r15d,%ecx
    2d14:	e8 c7 f7 ff ff       	call   24e0 <__printf_chk@plt>
            if (k == group_of) {
    2d19:	45 39 fe             	cmp    %r15d,%r14d
    2d1c:	75 ca                	jne    2ce8 <main+0x638>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d1e:	be 08 00 00 00       	mov    $0x8,%esi
    2d23:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d28:	49 83 c5 40          	add    $0x40,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d2c:	e8 ef f6 ff ff       	call   2420 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d31:	be 08 00 00 00       	mov    $0x8,%esi
    2d36:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d3b:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d42:	e8 d9 f6 ff ff       	call   2420 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2d47:	be 80 03 00 00       	mov    $0x380,%esi
    2d4c:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d51:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2d55:	e8 c6 f6 ff ff       	call   2420 <calloc@plt>
              data[0].a = x;
    2d5a:	8b 7d a0             	mov    -0x60(%rbp),%edi
              data[0].b = y;
    2d5d:	8b 75 b8             	mov    -0x48(%rbp),%esi
              mailboxes[b].pending_lower = NULL;
    2d60:	66 0f ef ff          	pxor   %xmm7,%xmm7
              struct Data *data = calloc(3, sizeof(struct Data));
    2d64:	49 89 c1             	mov    %rax,%r9
              mailboxes[b].pending_lower = NULL;
    2d67:	41 0f 11 7d d0       	movups %xmm7,-0x30(%r13)
    2d6c:	44 89 e2             	mov    %r12d,%edx
              data[0].a = x;
    2d6f:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].b = y;
    2d75:	89 b0 20 03 00 00    	mov    %esi,0x320(%rax)
              data[0].c = b;
    2d7b:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
              data[0].kind = MAILBOX_LOWER;
    2d82:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].id = dataid++;
    2d8c:	8d 43 01             	lea    0x1(%rbx),%eax
              data[1].id = dataid++;
    2d8f:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2d96:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2d9d:	49 89 45 c8          	mov    %rax,-0x38(%r13)
    2da1:	8b 85 48 ff ff ff    	mov    -0xb8(%rbp),%eax
              data[0].id = dataid++;
    2da7:	41 89 99 28 03 00 00 	mov    %ebx,0x328(%r9)
              data[1].id = dataid++;
    2dae:	83 c3 02             	add    $0x2,%ebx
              data[1].a = x;
    2db1:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    2db8:	89 c1                	mov    %eax,%ecx
    2dba:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].b = y;
    2dbf:	41 89 b1 a0 06 00 00 	mov    %esi,0x6a0(%r9)
    2dc6:	48 8d 35 db 59 00 00 	lea    0x59db(%rip),%rsi        # 87a8 <_IO_stdin_used+0x7a8>
              data[1].c = b;
    2dcd:	45 89 a1 a4 06 00 00 	mov    %r12d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2dd4:	41 83 c4 01          	add    $0x1,%r12d
              mailboxes[b].lower = &data[0];
    2dd8:	4d 89 4d c0          	mov    %r9,-0x40(%r13)
    2ddc:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    2de0:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    2de2:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[0].finished_reading = 1;
    2ded:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    2df8:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2e03:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    2e0b:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    2e0f:	e8 cc f6 ff ff       	call   24e0 <__printf_chk@plt>
              data[0].messages = messages;
    2e14:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    2e18:	4c 8b 9d 58 ff ff ff 	mov    -0xa8(%rbp),%r11
              data[0].messages_count = 0;
    2e1f:	66 0f 6f 3d 89 5e 00 00 	movdqa 0x5e89(%rip),%xmm7        # 8cb0 <_IO_stdin_used+0xcb0>
              data[1].messages = messages2;
    2e27:	4c 8b 55 a8          	mov    -0x58(%rbp),%r10
              data[0].messages = messages;
    2e2b:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2e2e:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2e35:	41 0f 29 b9 80 00 00 00 	movaps %xmm7,0x80(%r9)
              data[1].messages_count = 0;
    2e3d:	41 0f 29 b9 00 04 00 00 	movaps %xmm7,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e45:	41 83 fc 06          	cmp    $0x6,%r12d
    2e49:	0f 85 ab fe ff ff    	jne    2cfa <main+0x64a>
    2e4f:	44 8b 7d b8          	mov    -0x48(%rbp),%r15d
    2e53:	48 8b 8d 30 ff ff ff 	mov    -0xd0(%rbp),%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e5a:	45 31 ed             	xor    %r13d,%r13d
            mailboxes[b].pending_lower = NULL;
    2e5d:	44 89 75 b8          	mov    %r14d,-0x48(%rbp)
    2e61:	41 89 de             	mov    %ebx,%r14d
    2e64:	44 89 eb             	mov    %r13d,%ebx
    2e67:	49 89 cd             	mov    %rcx,%r13
    2e6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
            int group_of = b / threads_per_group;
    2e70:	89 d8                	mov    %ebx,%eax
    2e72:	d1 f8                	sar    %eax
            if (k == group_of) {
    2e74:	39 45 b8             	cmp    %eax,-0x48(%rbp)
    2e77:	0f 84 69 01 00 00    	je     2fe6 <main+0x936>
    2e7d:	89 da                	mov    %ebx,%edx
    2e7f:	48 8d 35 46 55 00 00 	lea    0x5546(%rip),%rsi        # 83cc <_IO_stdin_used+0x3cc>
    2e86:	bf 01 00 00 00       	mov    $0x1,%edi
    2e8b:	31 c0                	xor    %eax,%eax
    2e8d:	e8 4e f6 ff ff       	call   24e0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e92:	be 08 00 00 00       	mov    $0x8,%esi
    2e97:	bf 01 00 00 00       	mov    $0x1,%edi
    2e9c:	e8 7f f5 ff ff       	call   2420 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ea1:	be 08 00 00 00       	mov    $0x8,%esi
    2ea6:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2eab:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2eaf:	e8 6c f5 ff ff       	call   2420 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2eb4:	be 80 03 00 00       	mov    $0x380,%esi
    2eb9:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ebe:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
            struct Data *data = calloc(3, sizeof(struct Data));
    2ec2:	e8 59 f5 ff ff       	call   2420 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2ec7:	be 80 03 00 00       	mov    $0x380,%esi
    2ecc:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2ed1:	49 89 c4             	mov    %rax,%r12
            struct Data **stack = calloc(3, sizeof(struct Data));
    2ed4:	e8 47 f5 ff ff       	call   2420 <calloc@plt>
            data[0].a = x;
    2ed9:	8b 7d a0             	mov    -0x60(%rbp),%edi
            data[0].id = dataid++;
    2edc:	41 8d 76 01          	lea    0x1(%r14),%esi
            data[0].messages = messages;
    2ee0:	4c 8b 4d a8          	mov    -0x58(%rbp),%r9
            data[1].messages = messages2;
    2ee4:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
            data[0].messages_count = 0;
    2ee8:	66 0f 6f 35 c0 5d 00 00 	movdqa 0x5dc0(%rip),%xmm6        # 8cb0 <_IO_stdin_used+0xcb0>
            mailboxes[b].pending_lower = NULL;
    2ef0:	66 0f ef ed          	pxor   %xmm5,%xmm5
            data[1].id = dataid++;
    2ef4:	41 89 b4 24 a8 06 00 00 	mov    %esi,0x6a8(%r12)
            mailboxes[b].higher = &data[1];
    2efc:	49 8d b4 24 80 03 00 00 	lea    0x380(%r12),%rsi
            data[0].id = dataid++;
    2f04:	45 89 b4 24 28 03 00 00 	mov    %r14d,0x328(%r12)
            data[1].id = dataid++;
    2f0c:	41 83 c6 02          	add    $0x2,%r14d
            data[0].kind = MAILBOX_LOWER;
    2f10:	41 c7 84 24 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r12)
            data[0].a = x;
    2f1c:	41 89 bc 24 1c 03 00 00 	mov    %edi,0x31c(%r12)
            data[0].b = y;
    2f24:	45 89 bc 24 20 03 00 00 	mov    %r15d,0x320(%r12)
            data[0].c = b;
    2f2c:	41 89 9c 24 24 03 00 00 	mov    %ebx,0x324(%r12)
            data[1].kind = MAILBOX_HIGHER;
    2f34:	41 c7 84 24 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r12)
            data[1].a = x;
    2f40:	41 89 bc 24 9c 06 00 00 	mov    %edi,0x69c(%r12)
            data[1].b = y;
    2f48:	45 89 bc 24 a0 06 00 00 	mov    %r15d,0x6a0(%r12)
            data[1].c = b;
    2f50:	41 89 9c 24 a4 06 00 00 	mov    %ebx,0x6a4(%r12)
            mailboxes[b].lower = &data[0];
    2f58:	4d 89 65 00          	mov    %r12,0x0(%r13)
            mailboxes[b].my_lower = &data[0];
    2f5c:	4d 89 65 28          	mov    %r12,0x28(%r13)
            mailboxes[b].higher = &data[1];
    2f60:	49 89 75 08          	mov    %rsi,0x8(%r13)
            data[0].finished_reading = 1;
    2f64:	41 c7 84 24 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r12)
            data[1].finished_reading = 1;
    2f70:	41 c7 84 24 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r12)
            mailboxes[b].my_higher = &data[1];
    2f7c:	49 89 75 30          	mov    %rsi,0x30(%r13)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2f80:	41 c7 45 38 02 00 00 00 	movl   $0x2,0x38(%r13)
            stack[0] = mailboxes[b].lower;
    2f88:	4c 89 20             	mov    %r12,(%rax)
            stack[1] = mailboxes[b].higher;
    2f8b:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2f8f:	49 89 45 20          	mov    %rax,0x20(%r13)
            data[0].available_sending = 0;
    2f93:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
            data[0].available_receiving = 0;
    2f9f:	41 c7 84 24 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r12)
            data[0].messages = messages;
    2fab:	4d 89 0c 24          	mov    %r9,(%r12)
            data[1].messages = messages2;
    2faf:	49 89 94 24 80 03 00 00 	mov    %rdx,0x380(%r12)
            data[1].available_sending = 1;
    2fb7:	41 c7 84 24 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r12)
            data[1].available_receiving = 0;
    2fc3:	41 c7 84 24 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r12)
            mailboxes[b].pending_lower = NULL;
    2fcf:	41 0f 11 6d 10       	movups %xmm5,0x10(%r13)
            data[0].messages_count = 0;
    2fd4:	41 0f 29 b4 24 80 00 00 00 	movaps %xmm6,0x80(%r12)
            data[1].messages_count = 0;
    2fdd:	41 0f 29 b4 24 00 04 00 00 	movaps %xmm6,0x400(%r12)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2fe6:	83 c3 01             	add    $0x1,%ebx
    2fe9:	49 83 c5 40          	add    $0x40,%r13
    2fed:	83 fb 06             	cmp    $0x6,%ebx
    2ff0:	0f 85 7a fe ff ff    	jne    2e70 <main+0x7c0>
          char *message = malloc(sizeof(char) * 256);
    2ff6:	be 01 00 00 00       	mov    $0x1,%esi
    2ffb:	bf 00 01 00 00       	mov    $0x100,%edi
    3000:	44 89 f3             	mov    %r14d,%ebx
    3003:	44 8b 75 b8          	mov    -0x48(%rbp),%r14d
    3007:	e8 14 f4 ff ff       	call   2420 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    300c:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    3011:	49 89 c5             	mov    %rax,%r13
          struct Message *messaged = malloc(sizeof(struct Message));
    3014:	e8 87 f4 ff ff       	call   24a0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3019:	48 83 ec 08          	sub    $0x8,%rsp
    301d:	44 8b 45 a0          	mov    -0x60(%rbp),%r8d
    3021:	4c 89 ef             	mov    %r13,%rdi
    3024:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    3028:	45 89 f9             	mov    %r15d,%r9d
    302b:	ba 00 01 00 00       	mov    $0x100,%edx
    3030:	31 c0                	xor    %eax,%eax
    3032:	41 56                	push   %r14
    3034:	48 8d 0d 95 57 00 00 	lea    0x5795(%rip),%rcx        # 87d0 <_IO_stdin_used+0x7d0>
    303b:	be 01 00 00 00       	mov    $0x1,%esi
    3040:	e8 9b f5 ff ff       	call   25e0 <__sprintf_chk@plt>
          messaged->message = message;
    3045:	4c 8b 5d b8          	mov    -0x48(%rbp),%r11
          thread_data[x].tasks[y].swap = swap;
    3049:	48 8b 4d 80          	mov    -0x80(%rbp),%rcx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    304d:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->task_index = y;
    3052:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3059:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->message = message;
    305e:	4d 89 2b             	mov    %r13,(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    3061:	4c 8b ad 68 ff ff ff 	mov    -0x98(%rbp),%r13
          messaged->task_index = y;
    3068:	49 89 43 10          	mov    %rax,0x10(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    306c:	49 63 45 08          	movslq 0x8(%r13),%rax
          thread_data[x].tasks[y].swap = swap;
    3070:	49 8b 55 38          	mov    0x38(%r13),%rdx
          messaged->group = k;
    3074:	45 89 73 18          	mov    %r14d,0x18(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    3078:	49 89 43 08          	mov    %rax,0x8(%r11)
          thread_data[x].tasks[y].swap = swap;
    307c:	8b 45 90             	mov    -0x70(%rbp),%eax
    307f:	48 01 d1             	add    %rdx,%rcx
          thread_data[x].tasks[y].group = k;
    3082:	44 89 b1 94 01 00 00 	mov    %r14d,0x194(%rcx)
          thread_data[x].tasks[y].swap = swap;
    3089:	89 81 98 01 00 00    	mov    %eax,0x198(%rcx)
          swap += 1;
    308f:	83 c0 01             	add    $0x1,%eax
    3092:	89 45 90             	mov    %eax,-0x70(%rbp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3095:	41 8d 47 01          	lea    0x1(%r15),%eax
    3099:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    309c:	c7 01 41 00 00 00    	movl   $0x41,(%rcx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    30a2:	89 81 90 01 00 00    	mov    %eax,0x190(%rcx)
          thread_data[x].tasks[y].message = messaged;
    30a8:	4c 89 99 88 01 00 00 	mov    %r11,0x188(%rcx)
          thread_data[x].tasks[y].sending = 1;
    30af:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
          thread_data[x].tasks[y].snapshot_count = 99;
    30b9:	48 c7 81 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rcx)
          thread_data[x].tasks[y].swap = swap;
    30c4:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
          thread_data[x].tasks[y].snapshot_count = 99;
    30c8:	48 89 4d b8          	mov    %rcx,-0x48(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    30cc:	e8 4f f3 ff ff       	call   2420 <calloc@plt>
    30d1:	48 8b 4d b8          	mov    -0x48(%rbp),%rcx
    30d5:	48 89 81 50 01 00 00 	mov    %rax,0x150(%rcx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    30dc:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    30e3:	48 c7 81 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rcx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    30ee:	48 8b 00             	mov    (%rax),%rax
    30f1:	8b 70 04             	mov    0x4(%rax),%esi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    30f4:	4c 39 e8             	cmp    %r13,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    30f7:	48 89 81 28 01 00 00 	mov    %rax,0x128(%rcx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    30fe:	89 b1 30 01 00 00    	mov    %esi,0x130(%rcx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    3104:	5a                   	pop    %rdx
    3105:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    3109:	5e                   	pop    %rsi
    310a:	0f 85 47 12 00 00    	jne    4357 <main+0x1ca7>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    3110:	66 0f 6f 05 a8 5b 00 00 	movdqa 0x5ba8(%rip),%xmm0        # 8cc0 <_IO_stdin_used+0xcc0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    3118:	44 89 79 04          	mov    %r15d,0x4(%rcx)
          thread_data[x].tasks[y].available = 1;
    311c:	4c 8b 2d bd 5b 00 00 	mov    0x5bbd(%rip),%r13        # 8ce0 <_IO_stdin_used+0xce0>
          thread_data[x].tasks[y].arrived = 0;
    3123:	c7 81 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rcx)
          thread_data[x].tasks[y].worker_count = thread_count;
    312d:	c7 81 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rcx)
          thread_data[x].tasks[y].available = 1;
    3137:	4c 89 a9 44 01 00 00 	mov    %r13,0x144(%rcx)
          thread_data[x].tasks[y].thread_count = 2;
    313e:	0f 11 81 34 01 00 00 	movups %xmm0,0x134(%rcx)
          if (y == barrier_count - 1) {
    3145:	41 83 ff 01          	cmp    $0x1,%r15d
    3149:	0f 84 79 03 00 00    	je     34c8 <main+0xe18>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    314f:	45 85 ff             	test   %r15d,%r15d
    3152:	0f 84 57 03 00 00    	je     34af <main+0xdff>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    3158:	4c 8b 8d 68 ff ff ff 	mov    -0x98(%rbp),%r9
    315f:	48 8d 05 6a 38 00 00 	lea    0x386a(%rip),%rax        # 69d0 <barriered_work>
    3166:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    316a:	41 89 dc             	mov    %ebx,%r12d
    316d:	48 89 81 18 01 00 00 	mov    %rax,0x118(%rcx)
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3174:	be 08 00 00 00       	mov    $0x8,%esi
    3179:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
    317e:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    3189:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    318d:	e8 8e f2 ff ff       	call   2420 <calloc@plt>
    3192:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3196:	48 8b 9d 50 ff ff ff 	mov    -0xb0(%rbp),%rbx
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    319d:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    31a1:	66 0f 6f bd 00 ff ff ff 	movdqa -0x100(%rbp),%xmm7
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    31a9:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    31ac:	48 83 c3 10          	add    $0x10,%rbx
    31b0:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    31b7:	49 89 81 78 ff ff ff 	mov    %rax,-0x88(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    31be:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    31c5:	83 45 98 01          	addl   $0x1,-0x68(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    31c9:	48 8b 00             	mov    (%rax),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    31cc:	83 85 40 ff ff ff 01 	addl   $0x1,-0xc0(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    31d3:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    31dd:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    31e4:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    31ee:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    31f8:	41 8b 81 2c ff ff ff 	mov    -0xd4(%r9),%eax
    for (int d = 0 ; d < threads_per_group ; d++) {
    31ff:	48 89 9d 50 ff ff ff 	mov    %rbx,-0xb0(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    3206:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    320c:	8b 45 98             	mov    -0x68(%rbp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    320f:	c7 82 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
    3219:	4c 89 aa 44 05 00 00 	mov    %r13,0x544(%rdx)
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3220:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3227:	39 85 38 ff ff ff    	cmp    %eax,-0xc8(%rbp)
    322d:	0f 85 0f f8 ff ff    	jne    2a42 <main+0x392>
    3233:	4c 8b bd e0 fe ff ff 	mov    -0x120(%rbp),%r15
    323a:	48 8b b5 f8 fe ff ff 	mov    -0x108(%rbp),%rsi
    3241:	45 89 f5             	mov    %r14d,%r13d
  for (int k = 0 ; k < group_count ; k++) {
    3244:	41 83 c5 01          	add    $0x1,%r13d
    3248:	48 8b 9d d8 fe ff ff 	mov    -0x128(%rbp),%rbx
    324f:	48 83 c6 18          	add    $0x18,%rsi
    3253:	49 81 c7 b0 01 00 00 	add    $0x1b0,%r15
    325a:	41 83 fd 03          	cmp    $0x3,%r13d
    325e:	0f 85 9a f7 ff ff    	jne    29fe <main+0x34e>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3264:	be 08 00 00 00       	mov    $0x8,%esi
    3269:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    326e:	31 db                	xor    %ebx,%ebx
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3270:	e8 ab f1 ff ff       	call   2420 <calloc@plt>
    3275:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    3279:	49 89 c7             	mov    %rax,%r15
    327c:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    327e:	49 89 d1             	mov    %rdx,%r9
    3281:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3284:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3288:	45 85 d2             	test   %r10d,%r10d
    328b:	7e 7a                	jle    3307 <main+0xc57>
    328d:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3291:	4d 63 c2             	movslq %r10d,%r8
    3294:	48 63 cb             	movslq %ebx,%rcx
    3297:	49 c1 e0 09          	shl    $0x9,%r8
    329b:	49 8d 0c cf          	lea    (%r15,%rcx,8),%rcx
    329f:	49 01 f8             	add    %rdi,%r8
    32a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32a8:	48 8b b7 70 01 00 00 	mov    0x170(%rdi),%rsi
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    32af:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    32b6:	48 83 c1 60          	add    $0x60,%rcx
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32ba:	f3 0f 6f 66 40       	movdqu 0x40(%rsi),%xmm4
    32bf:	f3 0f 6f 9e 80 00 00 00 	movdqu 0x80(%rsi),%xmm3
    32c7:	f3 0f 6f 96 c0 00 00 00 	movdqu 0xc0(%rsi),%xmm2
    32cf:	f3 0f 6f 8e 00 01 00 00 	movdqu 0x100(%rsi),%xmm1
    32d7:	f3 0f 6f 86 40 01 00 00 	movdqu 0x140(%rsi),%xmm0
    32df:	f3 0f 6f 2e          	movdqu (%rsi),%xmm5
    32e3:	0f 11 61 b0          	movups %xmm4,-0x50(%rcx)
    32e7:	0f 11 59 c0          	movups %xmm3,-0x40(%rcx)
    32eb:	0f 11 69 a0          	movups %xmm5,-0x60(%rcx)
    32ef:	0f 11 51 d0          	movups %xmm2,-0x30(%rcx)
    32f3:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    32f7:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    32fb:	49 39 f8             	cmp    %rdi,%r8
    32fe:	75 a8                	jne    32a8 <main+0xbf8>
    3300:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3304:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3307:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    330e:	45 85 db             	test   %r11d,%r11d
    3311:	0f 85 c0 01 00 00    	jne    34d7 <main+0xe27>
    3317:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    331d:	e9 62 ff ff ff       	jmp    3284 <main+0xbd4>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3322:	44 89 7d b8          	mov    %r15d,-0x48(%rbp)
    3326:	49 89 c5             	mov    %rax,%r13
    3329:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
    3330:	eb 18                	jmp    334a <main+0xc9a>
    3332:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3338:	41 83 c4 01          	add    $0x1,%r12d
    333c:	49 83 c5 40          	add    $0x40,%r13
    3340:	41 83 fc 06          	cmp    $0x6,%r12d
    3344:	0f 84 55 01 00 00    	je     349f <main+0xdef>
            int group_of = b / threads_per_group;
    334a:	45 89 e7             	mov    %r12d,%r15d
    334d:	31 c0                	xor    %eax,%eax
    334f:	44 89 e2             	mov    %r12d,%edx
    3352:	bf 01 00 00 00       	mov    $0x1,%edi
    3357:	41 d1 ff             	sar    %r15d
    335a:	48 8d 35 5b 50 00 00 	lea    0x505b(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    3361:	44 89 f9             	mov    %r15d,%ecx
    3364:	e8 77 f1 ff ff       	call   24e0 <__printf_chk@plt>
            if (k == group_of) {
    3369:	45 39 fe             	cmp    %r15d,%r14d
    336c:	75 ca                	jne    3338 <main+0xc88>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    336e:	be 08 00 00 00       	mov    $0x8,%esi
    3373:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3378:	49 83 c5 40          	add    $0x40,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    337c:	e8 9f f0 ff ff       	call   2420 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3381:	be 08 00 00 00       	mov    $0x8,%esi
    3386:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    338b:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3392:	e8 89 f0 ff ff       	call   2420 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    3397:	be 80 03 00 00       	mov    $0x380,%esi
    339c:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    33a1:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
              struct Data *data = calloc(3, sizeof(struct Data));
    33a5:	e8 76 f0 ff ff       	call   2420 <calloc@plt>
              data[0].a = x;
    33aa:	8b 7d a0             	mov    -0x60(%rbp),%edi
              data[0].b = y;
    33ad:	8b 75 b8             	mov    -0x48(%rbp),%esi
              mailboxes[b].pending_lower = NULL;
    33b0:	66 0f ef c9          	pxor   %xmm1,%xmm1
              struct Data *data = calloc(3, sizeof(struct Data));
    33b4:	49 89 c1             	mov    %rax,%r9
    33b7:	44 89 e2             	mov    %r12d,%edx
              data[0].c = b;
    33ba:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
              data[0].a = x;
    33c1:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].b = y;
    33c7:	89 b0 20 03 00 00    	mov    %esi,0x320(%rax)
              data[0].kind = MAILBOX_LOWER;
    33cd:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].id = dataid++;
    33d7:	8d 43 01             	lea    0x1(%rbx),%eax
              data[1].id = dataid++;
    33da:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    33e1:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    33e8:	49 89 45 c8          	mov    %rax,-0x38(%r13)
    33ec:	8b 85 3c ff ff ff    	mov    -0xc4(%rbp),%eax
              data[0].id = dataid++;
    33f2:	41 89 99 28 03 00 00 	mov    %ebx,0x328(%r9)
              data[1].id = dataid++;
    33f9:	83 c3 02             	add    $0x2,%ebx
              data[1].a = x;
    33fc:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    3403:	89 c1                	mov    %eax,%ecx
    3405:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].b = y;
    340a:	41 89 b1 a0 06 00 00 	mov    %esi,0x6a0(%r9)
    3411:	48 8d 35 90 53 00 00 	lea    0x5390(%rip),%rsi        # 87a8 <_IO_stdin_used+0x7a8>
              data[1].c = b;
    3418:	45 89 a1 a4 06 00 00 	mov    %r12d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    341f:	41 83 c4 01          	add    $0x1,%r12d
              mailboxes[b].lower = &data[0];
    3423:	4d 89 4d c0          	mov    %r9,-0x40(%r13)
    3427:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    342b:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    342d:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[0].finished_reading = 1;
    3438:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    3443:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    344e:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              mailboxes[b].pending_lower = NULL;
    3456:	41 0f 11 4d d0       	movups %xmm1,-0x30(%r13)
              data[1].finished_reading = 1;
    345b:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    345f:	e8 7c f0 ff ff       	call   24e0 <__printf_chk@plt>
              data[0].messages = messages;
    3464:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    3468:	4c 8b 9d 58 ff ff ff 	mov    -0xa8(%rbp),%r11
              data[0].messages_count = 0;
    346f:	66 0f 6f 15 39 58 00 00 	movdqa 0x5839(%rip),%xmm2        # 8cb0 <_IO_stdin_used+0xcb0>
              data[1].messages = messages2;
    3477:	4c 8b 55 a8          	mov    -0x58(%rbp),%r10
              data[0].messages = messages;
    347b:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    347e:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    3485:	41 0f 29 91 80 00 00 00 	movaps %xmm2,0x80(%r9)
              data[1].messages_count = 0;
    348d:	41 0f 29 91 00 04 00 00 	movaps %xmm2,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3495:	41 83 fc 06          	cmp    $0x6,%r12d
    3499:	0f 85 ab fe ff ff    	jne    334a <main+0xc9a>
    349f:	44 8b 7d b8          	mov    -0x48(%rbp),%r15d
    34a3:	48 8b 8d 48 ff ff ff 	mov    -0xb8(%rbp),%rcx
    34aa:	e9 ab f9 ff ff       	jmp    2e5a <main+0x7aa>
    34af:	48 8d 05 0a 3b 00 00 	lea    0x3b0a(%rip),%rax        # 6fc0 <barriered_work_ingest_andwork>
    34b6:	41 bf 01 00 00 00    	mov    $0x1,%r15d
            thread_data[x].tasks[y].run = barriered_work; 
    34bc:	48 89 81 18 01 00 00 	mov    %rax,0x118(%rcx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    34c3:	e9 b3 f7 ff ff       	jmp    2c7b <main+0x5cb>
    34c8:	48 8d 05 01 35 00 00 	lea    0x3501(%rip),%rax        # 69d0 <barriered_work>
    34cf:	41 bf 02 00 00 00    	mov    $0x2,%r15d
    34d5:	eb e5                	jmp    34bc <main+0xe0c>
  for (int k = 0 ; k < group_count ; k++) {
    34d7:	83 c0 02             	add    $0x2,%eax
    34da:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    34e1:	83 f8 06             	cmp    $0x6,%eax
    34e4:	0f 85 94 fd ff ff    	jne    327e <main+0xbce>
    34ea:	48 8d 3d f9 4e 00 00 	lea    0x4ef9(%rip),%rdi        # 83ea <_IO_stdin_used+0x3ea>
    34f1:	44 89 5d a8          	mov    %r11d,-0x58(%rbp)
    34f5:	e8 56 ee ff ff       	call   2350 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    34fa:	48 8d 35 fe 4e 00 00 	lea    0x4efe(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3501:	48 8d 3d f9 4e 00 00 	lea    0x4ef9(%rip),%rdi        # 8401 <_IO_stdin_used+0x401>
    3508:	e8 13 f0 ff ff       	call   2520 <fopen@plt>
    350d:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas_size; x++) {
    3510:	85 db                	test   %ebx,%ebx
    3512:	7e 74                	jle    3588 <main+0xed8>
    3514:	48 63 db             	movslq %ebx,%rbx
    3517:	4c 8d 2d c0 4e 00 00 	lea    0x4ec0(%rip),%r13        # 83de <_IO_stdin_used+0x3de>
    351e:	4c 8d 25 fd 4e 00 00 	lea    0x4efd(%rip),%r12        # 8422 <_IO_stdin_used+0x422>
    3525:	49 8d 04 df          	lea    (%r15,%rbx,8),%rax
    3529:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    char * c = calloc(250, sizeof(char));
    352d:	be 01 00 00 00       	mov    $0x1,%esi
    3532:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    3537:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    353b:	e8 e0 ee ff ff       	call   2420 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3540:	4c 89 e9             	mov    %r13,%rcx
    3543:	ba fa 00 00 00       	mov    $0xfa,%edx
    3548:	be 01 00 00 00       	mov    $0x1,%esi
    354d:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    3550:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3554:	48 89 df             	mov    %rbx,%rdi
    3557:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    355e:	31 c0                	xor    %eax,%eax
    3560:	e8 7b f0 ff ff       	call   25e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3565:	48 89 da             	mov    %rbx,%rdx
    3568:	4c 89 e6             	mov    %r12,%rsi
    356b:	bf 01 00 00 00       	mov    $0x1,%edi
    3570:	31 c0                	xor    %eax,%eax
    3572:	e8 69 ef ff ff       	call   24e0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3577:	4c 89 f6             	mov    %r14,%rsi
    357a:	48 89 df             	mov    %rbx,%rdi
    357d:	e8 5e ee ff ff       	call   23e0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    3582:	4c 39 7d b8          	cmp    %r15,-0x48(%rbp)
    3586:	75 a5                	jne    352d <main+0xe7d>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    3588:	4c 89 f7             	mov    %r14,%rdi

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    358b:	45 31 ff             	xor    %r15d,%r15d
    358e:	4c 8d 2d b7 4e 00 00 	lea    0x4eb7(%rip),%r13        # 844c <_IO_stdin_used+0x44c>
  fclose(m1);
    3595:	e8 e6 ed ff ff       	call   2380 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    359a:	48 8d 3d 69 4e 00 00 	lea    0x4e69(%rip),%rdi        # 840a <_IO_stdin_used+0x40a>
    35a1:	e8 aa ed ff ff       	call   2350 <puts@plt>
    35a6:	48 8b 45 88          	mov    -0x78(%rbp),%rax
    35aa:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    35ae:	44 89 fa             	mov    %r15d,%edx
    35b1:	48 8d 35 6d 4e 00 00 	lea    0x4e6d(%rip),%rsi        # 8425 <_IO_stdin_used+0x425>
    35b8:	31 c0                	xor    %eax,%eax
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    35ba:	45 31 e4             	xor    %r12d,%r12d
    35bd:	bf 01 00 00 00       	mov    $0x1,%edi
    35c2:	47 8d 34 3f          	lea    (%r15,%r15,1),%r14d
    35c6:	e8 15 ef ff ff       	call   24e0 <__printf_chk@plt>
    35cb:	48 8b 5d b0          	mov    -0x50(%rbp),%rbx
    35cf:	48 89 d8             	mov    %rbx,%rax
    35d2:	44 89 e3             	mov    %r12d,%ebx
    35d5:	49 89 c4             	mov    %rax,%r12
      int x = (k * threads_per_group) + d;
    35d8:	42 8d 0c 33          	lea    (%rbx,%r14,1),%ecx
    35dc:	89 da                	mov    %ebx,%edx
    35de:	48 8d 35 4a 4e 00 00 	lea    0x4e4a(%rip),%rsi        # 842f <_IO_stdin_used+0x42f>
    35e5:	31 c0                	xor    %eax,%eax
    35e7:	bf 01 00 00 00       	mov    $0x1,%edi
    35ec:	e8 ef ee ff ff       	call   24e0 <__printf_chk@plt>
    35f1:	89 5d a0             	mov    %ebx,-0x60(%rbp)
    35f4:	31 c9                	xor    %ecx,%ecx
    35f6:	44 89 7d 98          	mov    %r15d,-0x68(%rbp)
    35fa:	44 89 75 90          	mov    %r14d,-0x70(%rbp)
    35fe:	89 ca                	mov    %ecx,%edx
    3600:	48 8d 35 3a 4e 00 00 	lea    0x4e3a(%rip),%rsi        # 8441 <_IO_stdin_used+0x441>
    3607:	bf 01 00 00 00       	mov    $0x1,%edi
    360c:	31 c0                	xor    %eax,%eax
    360e:	48 89 4d b8          	mov    %rcx,-0x48(%rbp)
    3612:	45 31 f6             	xor    %r14d,%r14d
    3615:	e8 c6 ee ff ff       	call   24e0 <__printf_chk@plt>
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    361a:	48 8b 5d b8          	mov    -0x48(%rbp),%rbx
    361e:	48 c1 e3 09          	shl    $0x9,%rbx
    3622:	eb 2d                	jmp    3651 <main+0xfa1>
    3624:	0f 1f 40 00          	nopl   0x0(%rax)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    3628:	83 fe 01             	cmp    $0x1,%esi
    362b:	0f 84 9e 00 00 00    	je     36cf <main+0x101f>
    3631:	44 8b 40 3c          	mov    0x3c(%rax),%r8d
    3635:	44 89 fa             	mov    %r15d,%edx
    3638:	4c 89 ee             	mov    %r13,%rsi
    363b:	bf 01 00 00 00       	mov    $0x1,%edi
    3640:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3642:	49 83 c6 01          	add    $0x1,%r14
    3646:	e8 95 ee ff ff       	call   24e0 <__printf_chk@plt>
    364b:	49 83 fe 06          	cmp    $0x6,%r14
    364f:	74 4e                	je     369f <main+0xfef>
          char * mailbox_kind = calloc(100, sizeof(char));
    3651:	be 01 00 00 00       	mov    $0x1,%esi
    3656:	bf 64 00 00 00       	mov    $0x64,%edi
    365b:	45 89 f7             	mov    %r14d,%r15d
    365e:	e8 bd ed ff ff       	call   2420 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3663:	4d 8b 44 24 38       	mov    0x38(%r12),%r8
    3668:	4c 89 f7             	mov    %r14,%rdi
          char * mailbox_kind = calloc(100, sizeof(char));
    366b:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    366e:	48 c1 e7 06          	shl    $0x6,%rdi
    3672:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    367a:	48 01 f8             	add    %rdi,%rax
    367d:	8b 70 38             	mov    0x38(%rax),%esi
    3680:	83 fe 02             	cmp    $0x2,%esi
    3683:	75 a3                	jne    3628 <main+0xf78>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3685:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    368f:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3692:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    369a:	48 01 f8             	add    %rdi,%rax
    369d:	eb 92                	jmp    3631 <main+0xf81>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    369f:	48 8b 4d b8          	mov    -0x48(%rbp),%rcx
    36a3:	48 83 c1 01          	add    $0x1,%rcx
    36a7:	48 83 f9 03          	cmp    $0x3,%rcx
    36ab:	0f 85 4d ff ff ff    	jne    35fe <main+0xf4e>
    for (int d = 0 ; d < threads_per_group ; d++) {
    36b1:	8b 5d a0             	mov    -0x60(%rbp),%ebx
    36b4:	44 8b 7d 98          	mov    -0x68(%rbp),%r15d
    36b8:	49 81 c4 d8 00 00 00 	add    $0xd8,%r12
    36bf:	44 8b 75 90          	mov    -0x70(%rbp),%r14d
    36c3:	85 db                	test   %ebx,%ebx
    36c5:	75 25                	jne    36ec <main+0x103c>
    36c7:	8b 5d a8             	mov    -0x58(%rbp),%ebx
    36ca:	e9 09 ff ff ff       	jmp    35d8 <main+0xf28>
    36cf:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    36d5:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    36dc:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    36e4:	48 01 f8             	add    %rdi,%rax
    36e7:	e9 45 ff ff ff       	jmp    3631 <main+0xf81>
  for (int k = 0 ; k < group_count ; k++) {
    36ec:	41 83 c7 01          	add    $0x1,%r15d
    36f0:	48 81 45 b0 b0 01 00 00 	addq   $0x1b0,-0x50(%rbp)
    36f8:	41 83 ff 03          	cmp    $0x3,%r15d
    36fc:	0f 85 ac fe ff ff    	jne    35ae <main+0xefe>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3702:	ba 07 00 00 00       	mov    $0x7,%edx
    3707:	48 8d 35 59 4d 00 00 	lea    0x4d59(%rip),%rsi        # 8467 <_IO_stdin_used+0x467>
    370e:	bf 01 00 00 00       	mov    $0x1,%edi
    3713:	31 c0                	xor    %eax,%eax
    3715:	e8 c6 ed ff ff       	call   24e0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    371a:	be 08 00 00 00       	mov    $0x8,%esi
    371f:	bf 02 00 00 00       	mov    $0x2,%edi
    3724:	e8 f7 ec ff ff       	call   2420 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    3729:	4c 8b 6d 88          	mov    -0x78(%rbp),%r13
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    372d:	be 38 00 00 00       	mov    $0x38,%esi
    3732:	bf 0a 00 00 00       	mov    $0xa,%edi
    my_thread_data[0] = &thread_data[x]; 
    3737:	4d 8d bd e8 05 00 00 	lea    0x5e8(%r13),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    373e:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3742:	4d 8d b5 d8 00 00 00 	lea    0xd8(%r13),%r14
    thread_data[x].threads = my_thread_data;
    3749:	49 89 85 00 06 00 00 	mov    %rax,0x600(%r13)
    my_thread_data[0] = &thread_data[x]; 
    3750:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3753:	49 8b 45 38          	mov    0x38(%r13),%rax
    thread_data[x].thread_count = 2;
    3757:	41 c7 85 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r13)
    thread_data[x].thread_index = 0;
    3762:	41 c7 85 ec 05 00 00 00 00 00 00 	movl   $0x0,0x5ec(%r13)
    thread_data[x].task_count = total_barrier_count;
    376d:	41 c7 85 28 06 00 00 03 00 00 00 	movl   $0x3,0x628(%r13)
    thread_data[n].tasks[0].scheduled = 1;
    3778:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3782:	49 8b 85 10 01 00 00 	mov    0x110(%r13),%rax
    3789:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3793:	e8 88 ec ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3798:	be 38 00 00 00       	mov    $0x38,%esi
    379d:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37a2:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37a6:	e8 75 ec ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37ab:	be 38 00 00 00       	mov    $0x38,%esi
    37b0:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37b5:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37b8:	e8 63 ec ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37bd:	be 38 00 00 00       	mov    $0x38,%esi
    37c2:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37c7:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37cb:	e8 50 ec ff ff       	call   2420 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37d0:	be 08 00 00 00       	mov    $0x8,%esi
    37d5:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37da:	48 89 45 a0          	mov    %rax,-0x60(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37de:	e8 3d ec ff ff       	call   2420 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    37e3:	be 08 00 00 00       	mov    $0x8,%esi
    37e8:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
    37ed:	41 c7 85 1c 05 00 00 00 00 00 00 	movl   $0x0,0x51c(%r13)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37f8:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  thread_data[timer_threadi].task_count = total_barrier_count;
    37fc:	48 8b 05 e5 54 00 00 	mov    0x54e5(%rip),%rax        # 8ce8 <_IO_stdin_used+0xce8>
    3803:	49 89 85 50 05 00 00 	mov    %rax,0x550(%r13)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    380a:	e8 11 ec ff ff       	call   2420 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    380f:	49 8d 95 b0 01 00 00 	lea    0x1b0(%r13),%rdx
    3816:	4c 89 ef             	mov    %r13,%rdi
    3819:	49 8d 8d 10 05 00 00 	lea    0x510(%r13),%rcx
    3820:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3824:	49 8d 95 88 02 00 00 	lea    0x288(%r13),%rdx
    382b:	48 8d 35 44 4c 00 00 	lea    0x4c44(%rip),%rsi        # 8476 <_IO_stdin_used+0x476>
    3832:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3836:	49 8d 95 60 03 00 00 	lea    0x360(%r13),%rdx
    383d:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3841:	49 8d 95 38 04 00 00 	lea    0x438(%r13),%rdx
    3848:	4c 89 28             	mov    %r13,(%rax)
    384b:	4d 8d ad c0 06 00 00 	lea    0x6c0(%r13),%r13
    3852:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3856:	48 8d 97 98 07 00 00 	lea    0x798(%rdi),%rdx
    385d:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3861:	4c 89 78 38          	mov    %r15,0x38(%rax)
    3865:	4c 89 68 40          	mov    %r13,0x40(%rax)
    3869:	48 89 50 48          	mov    %rdx,0x48(%rax)
    386d:	ba 06 00 00 00       	mov    $0x6,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3872:	48 89 87 28 05 00 00 	mov    %rax,0x528(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    3879:	4c 89 70 08          	mov    %r14,0x8(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    387d:	48 8b 05 6c 54 00 00 	mov    0x546c(%rip),%rax        # 8cf0 <_IO_stdin_used+0xcf0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3884:	c7 87 40 05 00 00 06 00 00 00 	movl   $0x6,0x540(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    388e:	48 89 87 38 05 00 00 	mov    %rax,0x538(%rdi)
    3895:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3897:	c7 87 14 05 00 00 00 00 00 00 	movl   $0x0,0x514(%rdi)
    38a1:	48 89 7d 88          	mov    %rdi,-0x78(%rbp)
    38a5:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    38aa:	48 89 4d 98          	mov    %rcx,-0x68(%rbp)
    38ae:	e8 2d ec ff ff       	call   24e0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38b3:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
    38b7:	49 8d b4 24 50 01 00 00 	lea    0x150(%r12),%rsi
    38bf:	4c 8b 65 b8          	mov    -0x48(%rbp),%r12
    38c3:	48 8d 15 d6 0d 00 00 	lea    0xdd6(%rip),%rdx        # 46a0 <timer_thread>
    38ca:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    38cf:	e8 2c ec ff ff       	call   2500 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    38d4:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
    38d8:	89 5d 98             	mov    %ebx,-0x68(%rbp)
    38db:	45 31 c0             	xor    %r8d,%r8d
    38de:	4c 89 75 80          	mov    %r14,-0x80(%rbp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38e2:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    38e6:	4c 89 e1             	mov    %r12,%rcx
    38e9:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    38ef:	4c 89 7d 90          	mov    %r15,-0x70(%rbp)
    38f3:	49 89 c7             	mov    %rax,%r15
    38f6:	4c 89 ad 78 ff ff ff 	mov    %r13,-0x88(%rbp)
    38fd:	45 89 c5             	mov    %r8d,%r13d
    3900:	4c 89 7d b0          	mov    %r15,-0x50(%rbp)
    3904:	43 8d 5c 2d 00       	lea    0x0(%r13,%r13,1),%ebx
    3909:	49 89 ce             	mov    %rcx,%r14
    390c:	49 89 d4             	mov    %rdx,%r12
    390f:	48 89 95 68 ff ff ff 	mov    %rdx,-0x98(%rbp)
    3916:	48 89 8d 60 ff ff ff 	mov    %rcx,-0xa0(%rbp)
    391d:	4c 89 bd 70 ff ff ff 	mov    %r15,-0x90(%rbp)
    3924:	45 89 d7             	mov    %r10d,%r15d
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3927:	41 c7 44 24 0c 01 00 00 00 	movl   $0x1,0xc(%r12)
    3930:	89 da                	mov    %ebx,%edx
    3932:	44 89 e9             	mov    %r13d,%ecx
    3935:	31 c0                	xor    %eax,%eax
    3937:	48 8d 35 c2 4e 00 00 	lea    0x4ec2(%rip),%rsi        # 8800 <_IO_stdin_used+0x800>
    393e:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    3943:	83 c3 01             	add    $0x1,%ebx
      thread_data[x].running = 1;
    3946:	41 c7 44 24 44 01 00 00 00 	movl   $0x1,0x44(%r12)
    394f:	e8 8c eb ff ff       	call   24e0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3954:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
    3958:	4c 89 e1             	mov    %r12,%rcx
    395b:	4c 89 f7             	mov    %r14,%rdi
    395e:	48 8d 15 fb 29 00 00 	lea    0x29fb(%rip),%rdx        # 6360 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3965:	49 81 c4 d8 00 00 00 	add    $0xd8,%r12
    396c:	49 83 c6 08          	add    $0x8,%r14
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3970:	e8 8b eb ff ff       	call   2500 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3975:	49 8b 54 24 d8       	mov    -0x28(%r12),%rdx
    397a:	49 8b 7e f8          	mov    -0x8(%r14),%rdi
    397e:	be 08 00 00 00       	mov    $0x8,%esi
    3983:	e8 b8 e9 ff ff       	call   2340 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3988:	48 83 45 b0 38       	addq   $0x38,-0x50(%rbp)
    398d:	44 39 fb             	cmp    %r15d,%ebx
    3990:	75 95                	jne    3927 <main+0x1277>
  for (int k = 0 ; k < group_count ; k++) {
    3992:	4c 8b bd 70 ff ff ff 	mov    -0x90(%rbp),%r15
    3999:	48 8b 95 68 ff ff ff 	mov    -0x98(%rbp),%rdx
    39a0:	41 83 c5 01          	add    $0x1,%r13d
    39a4:	44 8d 53 02          	lea    0x2(%rbx),%r10d
    39a8:	48 8b 8d 60 ff ff ff 	mov    -0xa0(%rbp),%rcx
    39af:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    39b6:	49 83 c7 70          	add    $0x70,%r15
    39ba:	48 83 c1 10          	add    $0x10,%rcx
    39be:	41 83 fd 03          	cmp    $0x3,%r13d
    39c2:	0f 85 38 ff ff ff    	jne    3900 <main+0x1250>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    39c8:	4c 8b 65 88          	mov    -0x78(%rbp),%r12
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39cc:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    39d1:	48 8b 05 20 53 00 00 	mov    0x5320(%rip),%rax        # 8cf8 <_IO_stdin_used+0xcf8>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39d8:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    39dd:	4c 8b 7d 90          	mov    -0x70(%rbp),%r15
    39e1:	4c 8b 75 80          	mov    -0x80(%rbp),%r14
    39e5:	41 c7 84 24 f4 05 00 00 02 00 00 00 	movl   $0x2,0x5f4(%r12)
    39f1:	8b 5d 98             	mov    -0x68(%rbp),%ebx
    thread_data[x].task_count = 0;
    39f4:	49 89 84 24 28 06 00 00 	mov    %rax,0x628(%r12)
    thread_data[x].type = IO;
    39fc:	4c 8b ad 78 ff ff ff 	mov    -0x88(%rbp),%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a03:	e8 18 ea ff ff       	call   2420 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a08:	be 00 08 00 00       	mov    $0x800,%esi
    3a0d:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a0f:	49 89 84 24 40 06 00 00 	mov    %rax,0x640(%r12)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a17:	e8 44 eb ff ff       	call   2560 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a1c:	be 08 00 00 00       	mov    $0x8,%esi
    3a21:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a26:	41 89 84 24 48 06 00 00 	mov    %eax,0x648(%r12)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a2e:	e8 ed e9 ff ff       	call   2420 <calloc@plt>
    3a33:	ba 07 00 00 00       	mov    $0x7,%edx
    3a38:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3a3d:	41 c7 84 24 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r12)
      my_thread_data[n] = &thread_data[n]; 
    3a49:	4c 89 20             	mov    %r12,(%rax)
    3a4c:	48 8d 35 41 4a 00 00 	lea    0x4a41(%rip),%rsi        # 8494 <_IO_stdin_used+0x494>
    thread_data[x].threads = my_thread_data;
    3a53:	49 89 84 24 00 06 00 00 	mov    %rax,0x600(%r12)
      my_thread_data[n] = &thread_data[n]; 
    3a5b:	4c 89 70 08          	mov    %r14,0x8(%rax)
    3a5f:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3a61:	41 c7 84 24 ec 05 00 00 07 00 00 00 	movl   $0x7,0x5ec(%r12)
    3a6d:	e8 6e ea ff ff       	call   24e0 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3a72:	4c 8b 65 b8          	mov    -0x48(%rbp),%r12
    3a76:	48 8b 75 a8          	mov    -0x58(%rbp),%rsi
    3a7a:	4c 89 f9             	mov    %r15,%rcx
    3a7d:	48 8d 15 8c 20 00 00 	lea    0x208c(%rip),%rdx        # 5b10 <io_thread>
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a84:	41 bf 08 00 00 00    	mov    $0x8,%r15d
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3a8a:	49 8d 7c 24 38       	lea    0x38(%r12),%rdi
    3a8f:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3a96:	e8 65 ea ff ff       	call   2500 <pthread_create@plt>
    3a9b:	ba 08 00 00 00       	mov    $0x8,%edx
    3aa0:	48 8d 35 04 4a 00 00 	lea    0x4a04(%rip),%rsi        # 84ab <_IO_stdin_used+0x4ab>
    3aa7:	31 c0                	xor    %eax,%eax
    3aa9:	bf 01 00 00 00       	mov    $0x1,%edi
    3aae:	e8 2d ea ff ff       	call   24e0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3ab3:	49 8d 44 24 40       	lea    0x40(%r12),%rax
    3ab8:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    3abc:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    3ac0:	49 81 c4 c0 01 00 00 	add    $0x1c0,%r12
    3ac7:	44 89 fa             	mov    %r15d,%edx
    3aca:	48 8d 35 f0 49 00 00 	lea    0x49f0(%rip),%rsi        # 84c1 <_IO_stdin_used+0x4c1>
    3ad1:	bf 01 00 00 00       	mov    $0x1,%edi
    3ad6:	31 c0                	xor    %eax,%eax
    3ad8:	e8 03 ea ff ff       	call   24e0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3add:	be 08 00 00 00       	mov    $0x8,%esi
    3ae2:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3ae7:	48 8b 05 0a 52 00 00 	mov    0x520a(%rip),%rax        # 8cf8 <_IO_stdin_used+0xcf8>
    thread_data[x].type = EXTERNAL;
    3aee:	41 c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%r13)
    thread_data[x].task_count = 0;
    3af6:	49 89 45 40          	mov    %rax,0x40(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3afa:	e8 21 e9 ff ff       	call   2420 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3aff:	48 8b bd 10 ff ff ff 	mov    -0xf0(%rbp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3b06:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3b0b:	41 c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3b16:	49 89 45 50          	mov    %rax,0x50(%r13)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3b1a:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3b1d:	bf 02 00 00 00       	mov    $0x2,%edi
    3b22:	e8 f9 e8 ff ff       	call   2420 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3b27:	48 8b 75 88          	mov    -0x78(%rbp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    3b2b:	45 89 7d 04          	mov    %r15d,0x4(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b2f:	4c 89 e9             	mov    %r13,%rcx
    thread_data[x].threads = my_thread_data;
    3b32:	49 89 45 18          	mov    %rax,0x18(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b36:	48 8b 7d b0          	mov    -0x50(%rbp),%rdi
    3b3a:	48 8d 15 3f 0a 00 00 	lea    0xa3f(%rip),%rdx        # 4580 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b41:	49 81 c5 d8 00 00 00 	add    $0xd8,%r13
      my_thread_data[n] = &thread_data[n]; 
    3b48:	48 89 30             	mov    %rsi,(%rax)
    thread_data[x].thread_count = thread_count;
    3b4b:	48 8b 35 86 51 00 00 	mov    0x5186(%rip),%rsi        # 8cd8 <_IO_stdin_used+0xcd8>
      my_thread_data[n] = &thread_data[n]; 
    3b52:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3b56:	49 89 b5 50 ff ff ff 	mov    %rsi,-0xb0(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b5d:	4c 89 e6             	mov    %r12,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b60:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b64:	e8 97 e9 ff ff       	call   2500 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b69:	48 83 85 10 ff ff ff 10 	addq   $0x10,-0xf0(%rbp)
    3b71:	48 83 45 b0 08       	addq   $0x8,-0x50(%rbp)
    3b76:	41 83 ff 08          	cmp    $0x8,%r15d
    3b7a:	75 3d                	jne    3bb9 <main+0x1509>
    3b7c:	41 bf 09 00 00 00    	mov    $0x9,%r15d
    3b82:	e9 40 ff ff ff       	jmp    3ac7 <main+0x1417>
        my_thread_data[1] = &thread_data[other]; 
    3b87:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
    3b8b:	4b 8d 04 7f          	lea    (%r15,%r15,2),%rax
        other = (x + 1) % total_threads;
    3b8f:	44 89 f9             	mov    %r15d,%ecx
        my_thread_data[1] = &thread_data[other]; 
    3b92:	45 31 c0             	xor    %r8d,%r8d
    3b95:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3b99:	48 89 9d 70 ff ff ff 	mov    %rbx,-0x90(%rbp)
    3ba0:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        my_thread_data[0] = &thread_data[x]; 
    3ba4:	4c 89 c8             	mov    %r9,%rax
    3ba7:	e9 23 ef ff ff       	jmp    2acf <main+0x41f>
            CPU_SET(j, sendercpu);
    3bac:	49 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%r13)
          for (int j = 0 ; j < cores ; j++) {
    3bb4:	e9 b1 ef ff ff       	jmp    2b6a <main+0x4ba>
    3bb9:	48 8b 45 88          	mov    -0x78(%rbp),%rax
    3bbd:	4c 8d 2d 1a 49 00 00 	lea    0x491a(%rip),%r13        # 84de <_IO_stdin_used+0x4de>
    3bc4:	4c 8d 78 04          	lea    0x4(%rax),%r15
    3bc8:	4c 8d b0 74 08 00 00 	lea    0x874(%rax),%r14
    3bcf:	41 8b 4f 04          	mov    0x4(%r15),%ecx
    3bd3:	41 8b 17             	mov    (%r15),%edx
    3bd6:	4c 89 ee             	mov    %r13,%rsi
    3bd9:	bf 01 00 00 00       	mov    $0x1,%edi
    3bde:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3be0:	49 81 c7 d8 00 00 00 	add    $0xd8,%r15
    3be7:	e8 f4 e8 ff ff       	call   24e0 <__printf_chk@plt>
    3bec:	4d 39 fe             	cmp    %r15,%r14
    3bef:	75 de                	jne    3bcf <main+0x151f>
    3bf1:	48 8d 3d f9 48 00 00 	lea    0x48f9(%rip),%rdi        # 84f1 <_IO_stdin_used+0x4f1>
    3bf8:	45 31 ff             	xor    %r15d,%r15d
    3bfb:	4c 8d 75 c0          	lea    -0x40(%rbp),%r14
    3bff:	e8 4c e7 ff ff       	call   2350 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3c04:	4c 8b 65 b8          	mov    -0x48(%rbp),%r12
    3c08:	4c 8d 2d 00 49 00 00 	lea    0x4900(%rip),%r13        # 850f <_IO_stdin_used+0x50f>
    void * result; 
    pthread_join(thread[x], &result);
    3c0f:	4b 8b 3c fc          	mov    (%r12,%r15,8),%rdi
    3c13:	4c 89 f6             	mov    %r14,%rsi
    3c16:	e8 85 e9 ff ff       	call   25a0 <pthread_join@plt>
    3c1b:	44 89 fa             	mov    %r15d,%edx
    3c1e:	4c 89 ee             	mov    %r13,%rsi
    3c21:	bf 01 00 00 00       	mov    $0x1,%edi
    3c26:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3c28:	49 83 c7 01          	add    $0x1,%r15
    3c2c:	e8 af e8 ff ff       	call   24e0 <__printf_chk@plt>
    3c31:	49 83 ff 0a          	cmp    $0xa,%r15
    3c35:	75 d8                	jne    3c0f <main+0x155f>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c37:	be 08 00 00 00       	mov    $0x8,%esi
    3c3c:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3c41:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c44:	e8 d7 e7 ff ff       	call   2420 <calloc@plt>
    3c49:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    3c4d:	49 89 c6             	mov    %rax,%r14
    3c50:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c52:	49 89 d1             	mov    %rdx,%r9
    3c55:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c58:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3c5c:	45 85 d2             	test   %r10d,%r10d
    3c5f:	7e 7f                	jle    3ce0 <main+0x1630>
    3c61:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3c65:	4d 63 c2             	movslq %r10d,%r8
    3c68:	49 63 cc             	movslq %r12d,%rcx
    3c6b:	49 c1 e0 09          	shl    $0x9,%r8
    3c6f:	49 8d 0c ce          	lea    (%r14,%rcx,8),%rcx
    3c73:	49 01 f8             	add    %rdi,%r8
    3c76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c80:	48 8b b7 70 01 00 00 	mov    0x170(%rdi),%rsi
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c87:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3c8e:	48 83 c1 60          	add    $0x60,%rcx
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c92:	f3 0f 6f 66 40       	movdqu 0x40(%rsi),%xmm4
    3c97:	f3 0f 6f 9e 80 00 00 00 	movdqu 0x80(%rsi),%xmm3
    3c9f:	f3 0f 6f 96 c0 00 00 00 	movdqu 0xc0(%rsi),%xmm2
    3ca7:	f3 0f 6f 8e 00 01 00 00 	movdqu 0x100(%rsi),%xmm1
    3caf:	f3 0f 6f 86 40 01 00 00 	movdqu 0x140(%rsi),%xmm0
    3cb7:	f3 0f 6f 36          	movdqu (%rsi),%xmm6
    3cbb:	0f 11 61 b0          	movups %xmm4,-0x50(%rcx)
    3cbf:	0f 11 59 c0          	movups %xmm3,-0x40(%rcx)
    3cc3:	0f 11 71 a0          	movups %xmm6,-0x60(%rcx)
    3cc7:	0f 11 51 d0          	movups %xmm2,-0x30(%rcx)
    3ccb:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    3ccf:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3cd3:	4c 39 c7             	cmp    %r8,%rdi
    3cd6:	75 a8                	jne    3c80 <main+0x15d0>
    3cd8:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3cdc:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    3ce0:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    3ce7:	45 85 db             	test   %r11d,%r11d
    3cea:	75 08                	jne    3cf4 <main+0x1644>
    3cec:	41 89 db             	mov    %ebx,%r11d
    3cef:	e9 64 ff ff ff       	jmp    3c58 <main+0x15a8>
  for (int k = 0 ; k < group_count ; k++) {
    3cf4:	83 c0 02             	add    $0x2,%eax
    3cf7:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3cfe:	83 f8 06             	cmp    $0x6,%eax
    3d01:	0f 85 4b ff ff ff    	jne    3c52 <main+0x15a2>
    3d07:	48 8d 3d 15 48 00 00 	lea    0x4815(%rip),%rdi        # 8523 <_IO_stdin_used+0x523>
    3d0e:	e8 3d e6 ff ff       	call   2350 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3d13:	48 8d 35 e5 46 00 00 	lea    0x46e5(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3d1a:	48 8d 3d 1a 48 00 00 	lea    0x481a(%rip),%rdi        # 853b <_IO_stdin_used+0x53b>
    3d21:	e8 fa e7 ff ff       	call   2520 <fopen@plt>
    3d26:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas2_size; x++) {
    3d29:	45 85 e4             	test   %r12d,%r12d
    3d2c:	7e 77                	jle    3da5 <main+0x16f5>
    3d2e:	4d 63 e4             	movslq %r12d,%r12
    3d31:	4c 8d 2d a6 46 00 00 	lea    0x46a6(%rip),%r13        # 83de <_IO_stdin_used+0x3de>
    3d38:	4b 8d 04 e6          	lea    (%r14,%r12,8),%rax
    3d3c:	4c 8d 25 df 46 00 00 	lea    0x46df(%rip),%r12        # 8422 <_IO_stdin_used+0x422>
    3d43:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    char * c = calloc(250, sizeof(char));
    3d47:	be 01 00 00 00       	mov    $0x1,%esi
    3d4c:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3d51:	49 83 c6 08          	add    $0x8,%r14
    char * c = calloc(250, sizeof(char));
    3d55:	e8 c6 e6 ff ff       	call   2420 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3d5a:	4c 89 e9             	mov    %r13,%rcx
    3d5d:	ba fa 00 00 00       	mov    $0xfa,%edx
    3d62:	be 01 00 00 00       	mov    $0x1,%esi
    3d67:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3d6a:	49 8b 46 f8          	mov    -0x8(%r14),%rax
    3d6e:	48 89 df             	mov    %rbx,%rdi
    3d71:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3d78:	31 c0                	xor    %eax,%eax
    3d7a:	e8 61 e8 ff ff       	call   25e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3d7f:	48 89 da             	mov    %rbx,%rdx
    3d82:	4c 89 e6             	mov    %r12,%rsi
    3d85:	bf 01 00 00 00       	mov    $0x1,%edi
    3d8a:	31 c0                	xor    %eax,%eax
    3d8c:	e8 4f e7 ff ff       	call   24e0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3d91:	4c 89 fe             	mov    %r15,%rsi
    3d94:	48 89 df             	mov    %rbx,%rdi
    3d97:	e8 44 e6 ff ff       	call   23e0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3d9c:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    3da0:	49 39 c6             	cmp    %rax,%r14
    3da3:	75 a2                	jne    3d47 <main+0x1697>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    3da5:	4c 89 ff             	mov    %r15,%rdi
    3da8:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    3dae:	31 db                	xor    %ebx,%ebx
  fclose(m2);
    3db0:	e8 cb e5 ff ff       	call   2380 <fclose@plt>
  long sents = 0;
    3db5:	48 c7 45 98 00 00 00 00 	movq   $0x0,-0x68(%rbp)
  long sends = 0;
    3dbd:	48 c7 45 a0 00 00 00 00 	movq   $0x0,-0x60(%rbp)
  long ingests = 0;
    3dc5:	48 c7 45 a8 00 00 00 00 	movq   $0x0,-0x58(%rbp)
  long total = 0;
    3dcd:	48 c7 45 90 00 00 00 00 	movq   $0x0,-0x70(%rbp)
  int datas2_size = 0; 
    3dd5:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
    3ddc:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    3de1:	4c 8b b5 18 ff ff ff 	mov    -0xe8(%rbp),%r14
    3de8:	45 89 e5             	mov    %r12d,%r13d
    3deb:	44 89 85 78 ff ff ff 	mov    %r8d,-0x88(%rbp)
    3df2:	48 89 45 80          	mov    %rax,-0x80(%rbp)
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
    3df6:	44 89 e8             	mov    %r13d,%eax
    3df9:	41 83 c5 01          	add    $0x1,%r13d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3dfd:	bf 0a 00 00 00       	mov    $0xa,%edi
      long v = 0;
      
      int other = -1;
      int me = x;
      if (x % 2 == 1) {
        other = abs(x - 1) % total_threads;
    3e02:	41 f6 c5 01          	test   $0x1,%r13b
    3e06:	8d 50 02             	lea    0x2(%rax),%edx
    3e09:	0f 44 c2             	cmove  %edx,%eax
    3e0c:	4c 63 e0             	movslq %eax,%r12
    3e0f:	e8 1c e5 ff ff       	call   2330 <putchar@plt>
    3e14:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    3e18:	bf 01 00 00 00       	mov    $0x1,%edi
    3e1d:	48 8d 35 20 47 00 00 	lea    0x4720(%rip),%rsi        # 8544 <_IO_stdin_used+0x544>
    3e24:	48 8b 10             	mov    (%rax),%rdx
    3e27:	31 c0                	xor    %eax,%eax
    3e29:	e8 b2 e6 ff ff       	call   24e0 <__printf_chk@plt>
        other = (x + 1) % total_threads;
      }
      printf("\n");
      printf("Total Protected %ld\n", protected_state[me].protected);

      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e2e:	41 8b 56 40          	mov    0x40(%r14),%edx
    3e32:	85 d2                	test   %edx,%edx
    3e34:	0f 8e 16 05 00 00    	jle    4350 <main+0x1ca0>
    3e3a:	48 63 ca             	movslq %edx,%rcx
    3e3d:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    3e41:	31 d2                	xor    %edx,%edx
    3e43:	48 c1 e1 09          	shl    $0x9,%rcx
    3e47:	48 01 c1             	add    %rax,%rcx
    3e4a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3e50:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e57:	48 05 00 02 00 00    	add    $0x200,%rax
    3e5d:	48 39 c8             	cmp    %rcx,%rax
    3e60:	75 ee                	jne    3e50 <main+0x17a0>
      }
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3e62:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
    3e66:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
    3e6a:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3e6e:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3e72:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3e76:	85 c9                	test   %ecx,%ecx
    3e78:	7e 20                	jle    3e9a <main+0x17ea>
    3e7a:	48 8b 40 38          	mov    0x38(%rax),%rax
    3e7e:	48 c1 e1 09          	shl    $0x9,%rcx
    3e82:	48 01 c1             	add    %rax,%rcx
    3e85:	0f 1f 00             	nopl   (%rax)
        v += thread_data[other].tasks[n].v;
    3e88:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3e8f:	48 05 00 02 00 00    	add    $0x200,%rax
    3e95:	48 39 c8             	cmp    %rcx,%rax
    3e98:	75 ee                	jne    3e88 <main+0x17d8>
    3e9a:	48 8d 35 b8 46 00 00 	lea    0x46b8(%rip),%rsi        # 8559 <_IO_stdin_used+0x559>
    3ea1:	bf 01 00 00 00       	mov    $0x1,%edi
    3ea6:	31 c0                	xor    %eax,%eax
    3ea8:	e8 33 e6 ff ff       	call   24e0 <__printf_chk@plt>
      }
      printf("Total V %ld\n", v);
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3ead:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    3eb1:	bf 01 00 00 00       	mov    $0x1,%edi
    3eb6:	48 8d 35 73 49 00 00 	lea    0x4973(%rip),%rsi        # 8830 <_IO_stdin_used+0x830>
    3ebd:	48 8b 08             	mov    (%rax),%rcx
    3ec0:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3eca:	48 f7 e9             	imul   %rcx
    3ecd:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3ed1:	31 c0                	xor    %eax,%eax
    3ed3:	48 d1 fa             	sar    %rdx
    3ed6:	48 29 ca             	sub    %rcx,%rdx
    3ed9:	e8 02 e6 ff ff       	call   24e0 <__printf_chk@plt>
    3ede:	bf 0a 00 00 00       	mov    $0xa,%edi
    3ee3:	e8 48 e4 ff ff       	call   2330 <putchar@plt>
      printf("\n");
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3ee8:	45 8b 66 40          	mov    0x40(%r14),%r12d
    3eec:	45 85 e4             	test   %r12d,%r12d
    3eef:	0f 8e 29 01 00 00    	jle    401e <main+0x196e>
    3ef5:	4c 8b 55 90          	mov    -0x70(%rbp),%r10
    3ef9:	48 8b 75 a8          	mov    -0x58(%rbp),%rsi
    3efd:	44 89 6d b8          	mov    %r13d,-0x48(%rbp)
    3f01:	31 d2                	xor    %edx,%edx
    3f03:	48 8b 7d a0          	mov    -0x60(%rbp),%rdi
    3f07:	4c 8b 7d 98          	mov    -0x68(%rbp),%r15
    3f0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        total += thread_data[x].tasks[n].n;
    3f10:	49 8b 46 38          	mov    0x38(%r14),%rax
    3f14:	49 89 d1             	mov    %rdx,%r9
        ingests += thread_data[x].tasks[n].ingest_count;
        sends += thread_data[x].tasks[n].sends;
    3f17:	48 89 55 90          	mov    %rdx,-0x70(%rbp)
    3f1b:	41 89 d5             	mov    %edx,%r13d
        total += thread_data[x].tasks[n].n;
    3f1e:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    3f22:	45 31 e4             	xor    %r12d,%r12d
        total += thread_data[x].tasks[n].n;
    3f25:	4c 01 c8             	add    %r9,%rax
        sends += thread_data[x].tasks[n].sends;
    3f28:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
        total += thread_data[x].tasks[n].n;
    3f2c:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
        ingests += thread_data[x].tasks[n].ingest_count;
    3f33:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
        sends += thread_data[x].tasks[n].sends;
    3f3a:	48 03 b8 78 01 00 00 	add    0x178(%rax),%rdi
    3f41:	4c 89 55 a8          	mov    %r10,-0x58(%rbp)
    3f45:	48 89 75 a0          	mov    %rsi,-0x60(%rbp)
    3f49:	48 89 7d 98          	mov    %rdi,-0x68(%rbp)
    3f4d:	0f 1f 00             	nopl   (%rax)
    3f50:	8b 55 b8             	mov    -0x48(%rbp),%edx
    3f53:	45 89 e0             	mov    %r12d,%r8d
    3f56:	44 89 e9             	mov    %r13d,%ecx
    3f59:	48 8d 35 06 46 00 00 	lea    0x4606(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    3f60:	bf 01 00 00 00       	mov    $0x1,%edi
    3f65:	31 c0                	xor    %eax,%eax
    3f67:	e8 74 e5 ff ff       	call   24e0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          printf("combo %d %d %d\n", x, n, kk);
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f6c:	49 8b 56 38          	mov    0x38(%r14),%rdx
    3f70:	48 8b 7d b0          	mov    -0x50(%rbp),%rdi
    3f74:	4c 89 e0             	mov    %r12,%rax
    3f77:	48 c1 e0 06          	shl    $0x6,%rax
    3f7b:	48 83 ec 08          	sub    $0x8,%rsp
    3f7f:	45 89 e0             	mov    %r12d,%r8d
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3f82:	49 83 c4 01          	add    $0x1,%r12
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f86:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    3f8e:	48 8b 38             	mov    (%rax),%rdi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3f91:	48 8b 70 08          	mov    0x8(%rax),%rsi

          long tempsent = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3f95:	48 8b 87 10 03 00 00 	mov    0x310(%rdi),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3f9c:	48 8b 96 08 03 00 00 	mov    0x308(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3fa3:	48 8b b6 10 03 00 00 	mov    0x310(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3faa:	48 8b 8f 08 03 00 00 	mov    0x308(%rdi),%rcx
    3fb1:	bf 01 00 00 00       	mov    $0x1,%edi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3fb6:	48 01 c3             	add    %rax,%rbx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3fb9:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fbc:	49 01 cf             	add    %rcx,%r15
    3fbf:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3fc3:	48 01 f3             	add    %rsi,%rbx
    3fc6:	50                   	push   %rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3fc7:	49 01 d7             	add    %rdx,%r15
    3fca:	8b 55 b8             	mov    -0x48(%rbp),%edx
    3fcd:	44 89 e9             	mov    %r13d,%ecx
    3fd0:	48 8d 35 79 48 00 00 	lea    0x4879(%rip),%rsi        # 8850 <_IO_stdin_used+0x850>
    3fd7:	31 c0                	xor    %eax,%eax
    3fd9:	e8 02 e5 ff ff       	call   24e0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3fde:	41 5a                	pop    %r10
    3fe0:	41 5b                	pop    %r11
    3fe2:	49 83 fc 06          	cmp    $0x6,%r12
    3fe6:	0f 85 64 ff ff ff    	jne    3f50 <main+0x18a0>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3fec:	48 8b 55 90          	mov    -0x70(%rbp),%rdx
    3ff0:	4c 8b 55 a8          	mov    -0x58(%rbp),%r10
    3ff4:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
    3ff8:	48 8b 7d 98          	mov    -0x68(%rbp),%rdi
    3ffc:	48 83 c2 01          	add    $0x1,%rdx
    4000:	41 39 56 40          	cmp    %edx,0x40(%r14)
    4004:	0f 8f 06 ff ff ff    	jg     3f10 <main+0x1860>
    400a:	4c 89 55 90          	mov    %r10,-0x70(%rbp)
    400e:	44 8b 6d b8          	mov    -0x48(%rbp),%r13d
    4012:	48 89 75 a8          	mov    %rsi,-0x58(%rbp)
    4016:	48 89 7d a0          	mov    %rdi,-0x60(%rbp)
    401a:	4c 89 7d 98          	mov    %r15,-0x68(%rbp)
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        // printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
        // printf("%ld iterations\n", thread_data[x].iteration_count);
      }
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    401e:	45 31 ff             	xor    %r15d,%r15d
    4021:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    4029:	4c 8d 25 40 48 00 00 	lea    0x4840(%rip),%r12        # 8870 <_IO_stdin_used+0x870>
    4030:	7e 65                	jle    4097 <main+0x19e7>
    4032:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4038:	49 8b 86 90 00 00 00 	mov    0x90(%r14),%rax
    403f:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    4043:	48 83 ec 08          	sub    $0x8,%rsp
    4047:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    404c:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4050:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    4054:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    405e:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    4062:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    4066:	48 f7 e6             	mul    %rsi
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4069:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    406d:	4c 2b 01             	sub    (%rcx),%r8
    4070:	31 c0                	xor    %eax,%eax
    4072:	8b 49 20             	mov    0x20(%rcx),%ecx
    4075:	56                   	push   %rsi
    4076:	4c 89 e6             	mov    %r12,%rsi
    4079:	48 c1 ea 12          	shr    $0x12,%rdx
    407d:	49 89 d1             	mov    %rdx,%r9
    4080:	ba 02 00 00 00       	mov    $0x2,%edx
    4085:	e8 56 e4 ff ff       	call   24e0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    408a:	41 58                	pop    %r8
    408c:	41 59                	pop    %r9
    408e:	4d 39 be a0 00 00 00 	cmp    %r15,0xa0(%r14)
    4095:	7f a1                	jg     4038 <main+0x1988>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4097:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    409e:	85 d2                	test   %edx,%edx
    40a0:	0f 8e 14 01 00 00    	jle    41ba <main+0x1b0a>
    40a6:	48 89 9d 70 ff ff ff 	mov    %rbx,-0x90(%rbp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    40ad:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    40b1:	45 31 ff             	xor    %r15d,%r15d
    40b4:	44 89 ad 68 ff ff ff 	mov    %r13d,-0x98(%rbp)
    40bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    40c0:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    40c4:	44 89 fb             	mov    %r15d,%ebx
    40c7:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    40cf:	8b 30                	mov    (%rax),%esi
    40d1:	85 f6                	test   %esi,%esi
    40d3:	0f 8e c6 00 00 00    	jle    419f <main+0x1aef>
    40d9:	4c 89 7d b0          	mov    %r15,-0x50(%rbp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    40dd:	31 d2                	xor    %edx,%edx
    40df:	48 8b 48 08          	mov    0x8(%rax),%rcx
    40e3:	49 89 f8             	mov    %rdi,%r8
    40e6:	48 89 d7             	mov    %rdx,%rdi
    40e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    40f0:	49 89 fc             	mov    %rdi,%r12
    40f3:	45 31 ff             	xor    %r15d,%r15d
    40f6:	49 c1 e4 08          	shl    $0x8,%r12
    40fa:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    40fe:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4104:	85 d2                	test   %edx,%edx
    4106:	7e 7d                	jle    4185 <main+0x1ad5>
    4108:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)
    410c:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4110:	4c 89 f9             	mov    %r15,%rcx
    4113:	48 83 ec 08          	sub    $0x8,%rsp
    4117:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    411c:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4120:	48 c1 e1 05          	shl    $0x5,%rcx
    4124:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    412b:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    4135:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    4139:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    413d:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4140:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    4144:	4c 2b 01             	sub    (%rcx),%r8
    4147:	56                   	push   %rsi
    4148:	89 d9                	mov    %ebx,%ecx
    414a:	48 8d 35 6f 47 00 00 	lea    0x476f(%rip),%rsi        # 88c0 <_IO_stdin_used+0x8c0>
    4151:	31 c0                	xor    %eax,%eax
    4153:	48 c1 ea 12          	shr    $0x12,%rdx
    4157:	49 89 d1             	mov    %rdx,%r9
    415a:	ba 02 00 00 00       	mov    $0x2,%edx
    415f:	e8 7c e3 ff ff       	call   24e0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    4164:	4d 8b 46 50          	mov    0x50(%r14),%r8
    4168:	5e                   	pop    %rsi
    4169:	5f                   	pop    %rdi
    416a:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    416e:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    4172:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    4176:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    417d:	7f 91                	jg     4110 <main+0x1a60>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    417f:	48 8b 7d b8          	mov    -0x48(%rbp),%rdi
    4183:	8b 32                	mov    (%rdx),%esi
    4185:	48 83 c7 01          	add    $0x1,%rdi
    4189:	39 fe                	cmp    %edi,%esi
    418b:	0f 8f 5f ff ff ff    	jg     40f0 <main+0x1a40>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4191:	4c 8b 7d b0          	mov    -0x50(%rbp),%r15
    4195:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    419c:	4c 89 c7             	mov    %r8,%rdi
    419f:	49 83 c7 01          	add    $0x1,%r15
    41a3:	44 39 fa             	cmp    %r15d,%edx
    41a6:	0f 8f 14 ff ff ff    	jg     40c0 <main+0x1a10>
    41ac:	48 8b 9d 70 ff ff ff 	mov    -0x90(%rbp),%rbx
    41b3:	44 8b ad 68 ff ff ff 	mov    -0x98(%rbp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    41ba:	48 83 45 80 18       	addq   $0x18,-0x80(%rbp)
    41bf:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    41c6:	44 39 ad 78 ff ff ff 	cmp    %r13d,-0x88(%rbp)
    41cd:	0f 85 23 fc ff ff    	jne    3df6 <main+0x1746>
  for (int k = 0 ; k < group_count ; k++) {
    41d3:	44 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%r8d
    41da:	48 83 85 28 ff ff ff 30 	addq   $0x30,-0xd8(%rbp)
    41e2:	48 81 85 18 ff ff ff b0 01 00 00 	addq   $0x1b0,-0xe8(%rbp)
    41ed:	41 83 f8 05          	cmp    $0x5,%r8d
    41f1:	74 08                	je     41fb <main+0x1b4b>
    41f3:	45 89 c4             	mov    %r8d,%r12d
    41f6:	e9 da fb ff ff       	jmp    3dd5 <main+0x1725>
    41fb:	4c 8b 75 90          	mov    -0x70(%rbp),%r14
    41ff:	48 8d 35 70 43 00 00 	lea    0x4370(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    4206:	31 c0                	xor    %eax,%eax
    4208:	49 89 df             	mov    %rbx,%r15
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    420b:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4215:	bf 01 00 00 00       	mov    $0x1,%edi
    421a:	4c 89 f2             	mov    %r14,%rdx
    421d:	e8 be e2 ff ff       	call   24e0 <__printf_chk@plt>
    4222:	bf 0a 00 00 00       	mov    $0xa,%edi
    4227:	e8 04 e1 ff ff       	call   2330 <putchar@plt>
    422c:	48 8b bd 20 ff ff ff 	mov    -0xe0(%rbp),%rdi
    4233:	48 8d 35 de 46 00 00 	lea    0x46de(%rip),%rsi        # 8918 <_IO_stdin_used+0x918>
    423a:	31 c0                	xor    %eax,%eax
    423c:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    4240:	bf 01 00 00 00       	mov    $0x1,%edi
    4245:	e8 96 e2 ff ff       	call   24e0 <__printf_chk@plt>
    424a:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
    424e:	48 8b 7d a8          	mov    -0x58(%rbp),%rdi
    4252:	48 8d 35 e7 46 00 00 	lea    0x46e7(%rip),%rsi        # 8940 <_IO_stdin_used+0x940>
    4259:	48 f7 eb             	imul   %rbx
    425c:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4260:	31 c0                	xor    %eax,%eax
    4262:	48 d1 fa             	sar    %rdx
    4265:	48 29 fa             	sub    %rdi,%rdx
    4268:	bf 01 00 00 00       	mov    $0x1,%edi
    426d:	e8 6e e2 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    4272:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
    4276:	48 8b 7d a0          	mov    -0x60(%rbp),%rdi
    427a:	48 8d 35 ef 46 00 00 	lea    0x46ef(%rip),%rsi        # 8970 <_IO_stdin_used+0x970>
    4281:	48 f7 eb             	imul   %rbx
    4284:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4288:	31 c0                	xor    %eax,%eax
    428a:	48 d1 fa             	sar    %rdx
    428d:	48 29 fa             	sub    %rdi,%rdx
    4290:	bf 01 00 00 00       	mov    $0x1,%edi
    4295:	e8 46 e2 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    429a:	4c 89 f0             	mov    %r14,%rax
    429d:	bf 01 00 00 00       	mov    $0x1,%edi
    42a2:	48 8d 35 f7 46 00 00 	lea    0x46f7(%rip),%rsi        # 89a0 <_IO_stdin_used+0x9a0>
    42a9:	48 f7 eb             	imul   %rbx
    42ac:	4c 89 f0             	mov    %r14,%rax
    42af:	48 c1 f8 3f          	sar    $0x3f,%rax
    42b3:	48 d1 fa             	sar    %rdx
    42b6:	48 29 c2             	sub    %rax,%rdx
    42b9:	31 c0                	xor    %eax,%eax
    42bb:	e8 20 e2 ff ff       	call   24e0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    42c0:	48 8b 45 98          	mov    -0x68(%rbp),%rax
    42c4:	bf 01 00 00 00       	mov    $0x1,%edi
    42c9:	48 8d 35 ba 42 00 00 	lea    0x42ba(%rip),%rsi        # 858a <_IO_stdin_used+0x58a>
    42d0:	48 f7 eb             	imul   %rbx
    42d3:	48 8b 45 98          	mov    -0x68(%rbp),%rax
    42d7:	48 c1 f8 3f          	sar    $0x3f,%rax
    42db:	48 d1 fa             	sar    %rdx
    42de:	48 29 c2             	sub    %rax,%rdx
    42e1:	31 c0                	xor    %eax,%eax
    42e3:	49 89 d4             	mov    %rdx,%r12
    42e6:	e8 f5 e1 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total sents %ld\n", sentdur);
  long recdur = received / DURATION;
    42eb:	4c 89 f8             	mov    %r15,%rax
    42ee:	bf 01 00 00 00       	mov    $0x1,%edi
    42f3:	48 8d 35 a1 42 00 00 	lea    0x42a1(%rip),%rsi        # 859b <_IO_stdin_used+0x59b>
    42fa:	48 f7 eb             	imul   %rbx
    42fd:	4c 89 f8             	mov    %r15,%rax
    4300:	48 c1 f8 3f          	sar    $0x3f,%rax
    4304:	48 89 d3             	mov    %rdx,%rbx
    4307:	48 d1 fb             	sar    %rbx
    430a:	48 29 c3             	sub    %rax,%rbx
    430d:	31 c0                	xor    %eax,%eax
    430f:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    4312:	4c 29 e3             	sub    %r12,%rbx
    4315:	e8 c6 e1 ff ff       	call   24e0 <__printf_chk@plt>
    431a:	31 c0                	xor    %eax,%eax
    431c:	48 89 da             	mov    %rbx,%rdx
    431f:	bf 01 00 00 00       	mov    $0x1,%edi
    4324:	48 8d 35 84 42 00 00 	lea    0x4284(%rip),%rsi        # 85af <_IO_stdin_used+0x5af>
    432b:	e8 b0 e1 ff ff       	call   24e0 <__printf_chk@plt>
  return 0;

}
    4330:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4334:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    433d:	75 22                	jne    4361 <main+0x1cb1>
    433f:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    4343:	31 c0                	xor    %eax,%eax
    4345:	5b                   	pop    %rbx
    4346:	41 5c                	pop    %r12
    4348:	41 5d                	pop    %r13
    434a:	41 5e                	pop    %r14
    434c:	41 5f                	pop    %r15
    434e:	5d                   	pop    %rbp
    434f:	c3                   	ret
      long v = 0;
    4350:	31 d2                	xor    %edx,%edx
    4352:	e9 0b fb ff ff       	jmp    3e62 <main+0x17b2>
            exit(1);
    4357:	bf 01 00 00 00       	mov    $0x1,%edi
    435c:	e8 ef e1 ff ff       	call   2550 <exit@plt>
}
    4361:	e8 3a e0 ff ff       	call   23a0 <__stack_chk_fail@plt>
    4366:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004370 <_start>:
    4370:	f3 0f 1e fa          	endbr64
    4374:	31 ed                	xor    %ebp,%ebp
    4376:	49 89 d1             	mov    %rdx,%r9
    4379:	5e                   	pop    %rsi
    437a:	48 89 e2             	mov    %rsp,%rdx
    437d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4381:	50                   	push   %rax
    4382:	54                   	push   %rsp
    4383:	45 31 c0             	xor    %r8d,%r8d
    4386:	31 c9                	xor    %ecx,%ecx
    4388:	48 8d 3d 21 e3 ff ff 	lea    -0x1cdf(%rip),%rdi        # 26b0 <main>
    438f:	ff 15 3b 6c 00 00    	call   *0x6c3b(%rip)        # afd0 <__libc_start_main@GLIBC_2.34>
    4395:	f4                   	hlt
    4396:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000043a0 <__gmon_start__>:
    43a0:	f3 0f 1e fa          	endbr64
    43a4:	8b 05 7e 6c 00 00    	mov    0x6c7e(%rip),%eax        # b028 <called.0>
    43aa:	85 c0                	test   %eax,%eax
    43ac:	74 02                	je     43b0 <__gmon_start__+0x10>
    43ae:	c3                   	ret
    43af:	90                   	nop
    43b0:	48 83 ec 08          	sub    $0x8,%rsp
    43b4:	48 8d 35 b2 31 00 00 	lea    0x31b2(%rip),%rsi        # 756d <etext>
    43bb:	48 8d 3d 3e bc ff ff 	lea    -0x43c2(%rip),%rdi        # 0 <__executable_start>
    43c2:	c7 05 5c 6c 00 00 01 00 00 00 	movl   $0x1,0x6c5c(%rip)        # b028 <called.0>
    43cc:	e8 6f e0 ff ff       	call   2440 <__monstartup@plt>
    43d1:	48 8b 3d 08 6c 00 00 	mov    0x6c08(%rip),%rdi        # afe0 <_mcleanup@GLIBC_2.2.5>
    43d8:	48 83 c4 08          	add    $0x8,%rsp
    43dc:	e9 4f 31 00 00       	jmp    7530 <atexit>
    43e1:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    43eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000043f0 <_dl_relocate_static_pie>:
    43f0:	f3 0f 1e fa          	endbr64
    43f4:	c3                   	ret
    43f5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    43ff:	90                   	nop

0000000000004400 <deregister_tm_clones>:
    4400:	48 8d 3d 19 6c 00 00 	lea    0x6c19(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4407:	48 8d 05 12 6c 00 00 	lea    0x6c12(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    440e:	48 39 f8             	cmp    %rdi,%rax
    4411:	74 15                	je     4428 <deregister_tm_clones+0x28>
    4413:	48 8b 05 be 6b 00 00 	mov    0x6bbe(%rip),%rax        # afd8 <_ITM_deregisterTMCloneTable@Base>
    441a:	48 85 c0             	test   %rax,%rax
    441d:	74 09                	je     4428 <deregister_tm_clones+0x28>
    441f:	ff e0                	jmp    *%rax
    4421:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4428:	c3                   	ret
    4429:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004430 <register_tm_clones>:
    4430:	48 8d 3d e9 6b 00 00 	lea    0x6be9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4437:	48 8d 35 e2 6b 00 00 	lea    0x6be2(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    443e:	48 29 fe             	sub    %rdi,%rsi
    4441:	48 89 f0             	mov    %rsi,%rax
    4444:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4448:	48 c1 f8 03          	sar    $0x3,%rax
    444c:	48 01 c6             	add    %rax,%rsi
    444f:	48 d1 fe             	sar    %rsi
    4452:	74 14                	je     4468 <register_tm_clones+0x38>
    4454:	48 8b 05 95 6b 00 00 	mov    0x6b95(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    445b:	48 85 c0             	test   %rax,%rax
    445e:	74 08                	je     4468 <register_tm_clones+0x38>
    4460:	ff e0                	jmp    *%rax
    4462:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4468:	c3                   	ret
    4469:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004470 <__do_global_dtors_aux>:
    4470:	f3 0f 1e fa          	endbr64
    4474:	80 3d b1 6b 00 00 00 	cmpb   $0x0,0x6bb1(%rip)        # b02c <completed.0>
    447b:	75 2b                	jne    44a8 <__do_global_dtors_aux+0x38>
    447d:	55                   	push   %rbp
    447e:	48 83 3d 72 6b 00 00 00 	cmpq   $0x0,0x6b72(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    4486:	48 89 e5             	mov    %rsp,%rbp
    4489:	74 0c                	je     4497 <__do_global_dtors_aux+0x27>
    448b:	48 8b 3d 76 6b 00 00 	mov    0x6b76(%rip),%rdi        # b008 <__dso_handle>
    4492:	e8 79 de ff ff       	call   2310 <__cxa_finalize@plt>
    4497:	e8 64 ff ff ff       	call   4400 <deregister_tm_clones>
    449c:	c6 05 89 6b 00 00 01 	movb   $0x1,0x6b89(%rip)        # b02c <completed.0>
    44a3:	5d                   	pop    %rbp
    44a4:	c3                   	ret
    44a5:	0f 1f 00             	nopl   (%rax)
    44a8:	c3                   	ret
    44a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044b0 <frame_dummy>:
    44b0:	f3 0f 1e fa          	endbr64
    44b4:	e9 77 ff ff ff       	jmp    4430 <register_tm_clones>
    44b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044c0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    44c0:	f3 0f 1e fa          	endbr64
    44c4:	55                   	push   %rbp
    44c5:	48 89 e5             	mov    %rsp,%rbp
    44c8:	ff 15 1a 6b 00 00    	call   *0x6b1a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  struct ProtectedState *protected = data->thread->protected_state;
    44ce:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    44d5:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    44d9:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    44e1:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    44e5:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    44e9:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    44f0:	48 85 c9             	test   %rcx,%rcx
    44f3:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    44fa:	48 0f 4f d6          	cmovg  %rsi,%rdx
    44fe:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4502:	31 c0                	xor    %eax,%eax
    4504:	5d                   	pop    %rbp
    4505:	c3                   	ret
    4506:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004510 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4510:	f3 0f 1e fa          	endbr64
    4514:	55                   	push   %rbp
    4515:	48 89 e5             	mov    %rsp,%rbp
    4518:	ff 15 ca 6a 00 00    	call   *0x6aca(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    for (int x = 0 ; x < data->task_count ; x++) {
    451e:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    4525:	85 c9                	test   %ecx,%ecx
    4527:	7e 4d                	jle    4576 <barriered_reset+0x66>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4529:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4530:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    4537:	48 c1 e1 09          	shl    $0x9,%rcx
    453b:	48 8b 50 18          	mov    0x18(%rax),%rdx
    453f:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    4543:	48 8b 70 38          	mov    0x38(%rax),%rsi
    4547:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4549:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    454d:	0f 1f 00             	nopl   (%rax)
    4550:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4558:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4560:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    456b:	48 05 00 02 00 00    	add    $0x200,%rax
    4571:	48 39 c1             	cmp    %rax,%rcx
    4574:	75 da                	jne    4550 <barriered_reset+0x40>
  asm volatile ("sfence" ::: "memory");
    4576:	0f ae f8             	sfence
}
    4579:	31 c0                	xor    %eax,%eax
    457b:	5d                   	pop    %rbp
    457c:	c3                   	ret
    457d:	0f 1f 00             	nopl   (%rax)

0000000000004580 <external_thread>:
void * external_thread(void *arg) {
    4580:	f3 0f 1e fa          	endbr64
    4584:	55                   	push   %rbp
    4585:	48 89 e5             	mov    %rsp,%rbp
    4588:	41 57                	push   %r15
    458a:	41 56                	push   %r14
    458c:	41 55                	push   %r13
    458e:	41 54                	push   %r12
    4590:	53                   	push   %rbx
    4591:	48 83 ec 08          	sub    $0x8,%rsp
    4595:	ff 15 4d 6a 00 00    	call   *0x6a4d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  while (data->running == 1) {
    459b:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
void * external_thread(void *arg) {
    459f:	49 89 fe             	mov    %rdi,%r14
  while (data->running == 1) {
    45a2:	75 6b                	jne    460f <external_thread+0x8f>
    for (int b = 0; b < data->buffers_count; b++) {
    45a4:	8b b7 bc 00 00 00    	mov    0xbc(%rdi),%esi
    45aa:	4c 8b 47 50          	mov    0x50(%rdi),%r8
    45ae:	66 90                	xchg   %ax,%ax
    45b0:	85 f6                	test   %esi,%esi
    45b2:	7e 6c                	jle    4620 <external_thread+0xa0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    45b4:	45 31 ed             	xor    %r13d,%r13d
    45b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    45c0:	4e 8d 3c ed 00 00 00 00 	lea    0x0(,%r13,8),%r15
    45c8:	31 db                	xor    %ebx,%ebx
    45ca:	4b 8d 3c 38          	lea    (%r8,%r15,1),%rdi
    45ce:	48 8b 07             	mov    (%rdi),%rax
    45d1:	8b 10                	mov    (%rax),%edx
    45d3:	85 d2                	test   %edx,%edx
    45d5:	7e 28                	jle    45ff <external_thread+0x7f>
    45d7:	48 8b 70 08          	mov    0x8(%rax),%rsi
				if (data->buffers[b]->buffer[x].available == 0) {
    45db:	49 89 dc             	mov    %rbx,%r12
    45de:	49 c1 e4 08          	shl    $0x8,%r12
    45e2:	4a 8d 04 26          	lea    (%rsi,%r12,1),%rax
    45e6:	8b 88 80 00 00 00    	mov    0x80(%rax),%ecx
    45ec:	85 c9                	test   %ecx,%ecx
    45ee:	74 38                	je     4628 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    45f0:	48 83 c3 01          	add    $0x1,%rbx
    45f4:	39 da                	cmp    %ebx,%edx
    45f6:	7f e3                	jg     45db <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    45f8:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    45ff:	49 83 c5 01          	add    $0x1,%r13
    4603:	44 39 ee             	cmp    %r13d,%esi
    4606:	7f b8                	jg     45c0 <external_thread+0x40>
  while (data->running == 1) {
    4608:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    460d:	74 a1                	je     45b0 <external_thread+0x30>
}
    460f:	48 83 c4 08          	add    $0x8,%rsp
    4613:	31 c0                	xor    %eax,%eax
    4615:	5b                   	pop    %rbx
    4616:	41 5c                	pop    %r12
    4618:	41 5d                	pop    %r13
    461a:	41 5e                	pop    %r14
    461c:	41 5f                	pop    %r15
    461e:	5d                   	pop    %rbp
    461f:	c3                   	ret
  while (data->running == 1) {
    4620:	eb fe                	jmp    4620 <external_thread+0xa0>
    4622:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    4628:	48 8d 0d d5 39 00 00 	lea    0x39d5(%rip),%rcx        # 8004 <_IO_stdin_used+0x4>
    462f:	48 89 08             	mov    %rcx,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    4632:	48 8b 07             	mov    (%rdi),%rax
    4635:	bf 04 00 00 00       	mov    $0x4,%edi
    463a:	48 8b 48 08          	mov    0x8(%rax),%rcx
    463e:	4c 01 e1             	add    %r12,%rcx
    4641:	48 63 b1 94 00 00 00 	movslq 0x94(%rcx),%rsi
    4648:	48 c1 e6 05          	shl    $0x5,%rsi
    464c:	48 03 b1 88 00 00 00 	add    0x88(%rcx),%rsi
    4653:	e8 18 dd ff ff       	call   2370 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4658:	49 8b 46 50          	mov    0x50(%r14),%rax
    465c:	4a 8b 04 38          	mov    (%rax,%r15,1),%rax
    4660:	48 8b 40 08          	mov    0x8(%rax),%rax
    4664:	42 c7 84 20 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%r12,1)
          asm volatile ("sfence" ::: "memory");
    4670:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4673:	4d 8b 46 50          	mov    0x50(%r14),%r8
    4677:	48 83 c3 01          	add    $0x1,%rbx
    467b:	4b 8d 3c 38          	lea    (%r8,%r15,1),%rdi
    467f:	48 8b 07             	mov    (%rdi),%rax
    4682:	8b 10                	mov    (%rax),%edx
    4684:	39 da                	cmp    %ebx,%edx
    4686:	0f 8f 4b ff ff ff    	jg     45d7 <external_thread+0x57>
    468c:	e9 67 ff ff ff       	jmp    45f8 <external_thread+0x78>
    4691:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    469c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000046a0 <timer_thread>:
void* timer_thread(void *arg) {
    46a0:	f3 0f 1e fa          	endbr64
    46a4:	55                   	push   %rbp
    46a5:	48 89 e5             	mov    %rsp,%rbp
    46a8:	41 57                	push   %r15
    46aa:	41 56                	push   %r14
    46ac:	41 55                	push   %r13
    46ae:	41 54                	push   %r12
    46b0:	53                   	push   %rbx
    46b1:	48 83 ec 68          	sub    $0x68,%rsp
    46b5:	ff 15 2d 69 00 00    	call   *0x692d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    46bb:	48 8d 35 4e 39 00 00 	lea    0x394e(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    46c2:	8b 57 04             	mov    0x4(%rdi),%edx
    46c5:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    46ce:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    46d2:	31 c0                	xor    %eax,%eax
    46d4:	49 89 ff             	mov    %rdi,%r15
    46d7:	bf 01 00 00 00       	mov    $0x1,%edi
    46dc:	e8 ff dd ff ff       	call   24e0 <__printf_chk@plt>
  struct timespec preempt = {
    46e1:	66 0f 6f 05 d7 44 00 00 	movdqa 0x44d7(%rip),%xmm0        # 8bc0 <_IO_stdin_used+0xbc0>
    46e9:	ba 88 13 00 00       	mov    $0x1388,%edx
    46ee:	31 c0                	xor    %eax,%eax
    46f0:	48 8d 35 2b 39 00 00 	lea    0x392b(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    46f7:	bf 01 00 00 00       	mov    $0x1,%edi
    46fc:	0f 29 45 90          	movaps %xmm0,-0x70(%rbp)
    4700:	e8 db dd ff ff       	call   24e0 <__printf_chk@plt>
  while (data->running && n < times) {
    4705:	41 8b 5f 44          	mov    0x44(%r15),%ebx
    4709:	85 db                	test   %ebx,%ebx
    470b:	0f 84 9a 00 00 00    	je     47ab <timer_thread+0x10b>
  int n = 0;
    4711:	45 31 e4             	xor    %r12d,%r12d
    4714:	4c 8d 75 80          	lea    -0x80(%rbp),%r14
    4718:	4c 8d 6d 90          	lea    -0x70(%rbp),%r13
  int y = 0;
    471c:	31 db                	xor    %ebx,%ebx
    nanosleep(&preempt , &rem2);
    471e:	4c 89 ef             	mov    %r13,%rdi
    4721:	4c 89 f6             	mov    %r14,%rsi
    n++;
    4724:	41 83 c4 01          	add    $0x1,%r12d
    nanosleep(&preempt , &rem2);
    4728:	e8 93 dc ff ff       	call   23c0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    472d:	49 63 47 30          	movslq 0x30(%r15),%rax
    y++;
    4731:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4734:	85 c0                	test   %eax,%eax
    4736:	7e 4c                	jle    4784 <timer_thread+0xe4>
    4738:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    473c:	4c 63 c3             	movslq %ebx,%r8
    473f:	49 c1 e0 09          	shl    $0x9,%r8
    4743:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4747:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    4750:	48 8b 19             	mov    (%rcx),%rbx
    4753:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4755:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4759:	99                   	cltd
    475a:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    475d:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4761:	48 63 d2             	movslq %edx,%rdx
    4764:	48 c1 e2 09          	shl    $0x9,%rdx
    4768:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4773:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    477f:	49 39 c9             	cmp    %rcx,%r9
    4782:	75 cc                	jne    4750 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    4784:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4787:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
    478b:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    y++;
    478f:	31 db                	xor    %ebx,%ebx
    if (y >= data->threads[0]->task_count) {
    4791:	48 8b 00             	mov    (%rax),%rax
    y++;
    4794:	39 78 40             	cmp    %edi,0x40(%rax)
    4797:	0f 4f df             	cmovg  %edi,%ebx
  while (data->running && n < times) {
    479a:	85 c9                	test   %ecx,%ecx
    479c:	74 0d                	je     47ab <timer_thread+0x10b>
    479e:	41 81 fc 88 13 00 00 	cmp    $0x1388,%r12d
    47a5:	0f 85 73 ff ff ff    	jne    471e <timer_thread+0x7e>
    47ab:	48 8d 3d 86 38 00 00 	lea    0x3886(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    47b2:	e8 99 db ff ff       	call   2350 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    47b7:	49 63 57 30          	movslq 0x30(%r15),%rdx
    47bb:	85 d2                	test   %edx,%edx
    47bd:	7e 6e                	jle    482d <timer_thread+0x18d>
    for (int y = 0 ; y < data->task_count ; y++) {
    47bf:	49 63 47 40          	movslq 0x40(%r15),%rax
    47c3:	85 c0                	test   %eax,%eax
    47c5:	7e 66                	jle    482d <timer_thread+0x18d>
    47c7:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    47cb:	4d 8b 47 18          	mov    0x18(%r15),%r8
    47cf:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    47d7:	31 c9                	xor    %ecx,%ecx
    47d9:	48 89 c6             	mov    %rax,%rsi
    47dc:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    47e0:	48 8b 40 38          	mov    0x38(%rax),%rax
    47e4:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    47e8:	f7 c6 00 02 00 00    	test   $0x200,%esi
    47ee:	74 18                	je     4808 <timer_thread+0x168>
    47f0:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    47fa:	48 05 00 02 00 00    	add    $0x200,%rax
    4800:	48 39 c2             	cmp    %rax,%rdx
    4803:	74 1f                	je     4824 <timer_thread+0x184>
    4805:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->tasks[y].sending = 0;
    4808:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4812:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4818:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    481f:	48 39 c2             	cmp    %rax,%rdx
    4822:	75 e4                	jne    4808 <timer_thread+0x168>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    4824:	48 83 c1 08          	add    $0x8,%rcx
    4828:	48 39 cf             	cmp    %rcx,%rdi
    482b:	75 af                	jne    47dc <timer_thread+0x13c>
  asm volatile ("mfence" ::: "memory");
    482d:	0f ae f0             	mfence
  struct timespec drain = {
    4830:	66 0f 6f 05 98 43 00 00 	movdqa 0x4398(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4838:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    483c:	49 63 47 28          	movslq 0x28(%r15),%rax
    y++;
    4840:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    4843:	85 c0                	test   %eax,%eax
    4845:	7e 4d                	jle    4894 <timer_thread+0x1f4>
    4847:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    484b:	4c 63 c3             	movslq %ebx,%r8
    484e:	49 c1 e0 09          	shl    $0x9,%r8
    4852:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4856:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    4860:	48 8b 19             	mov    (%rcx),%rbx
    4863:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    4865:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4869:	99                   	cltd
    486a:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    486d:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4871:	48 63 d2             	movslq %edx,%rdx
    4874:	48 c1 e2 09          	shl    $0x9,%rdx
    4878:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4883:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    488f:	49 39 c9             	cmp    %rcx,%r9
    4892:	75 cc                	jne    4860 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    4894:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4897:	49 8b 77 18          	mov    0x18(%r15),%rsi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    489b:	45 8b 57 30          	mov    0x30(%r15),%r10d
    y++;
    489f:	31 db                	xor    %ebx,%ebx
    if (y >= data->threads[0]->task_count) {
    48a1:	48 8b 06             	mov    (%rsi),%rax
    y++;
    48a4:	39 78 40             	cmp    %edi,0x40(%rax)
    48a7:	0f 4f df             	cmovg  %edi,%ebx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48aa:	45 85 d2             	test   %r10d,%r10d
    48ad:	0f 8e d3 01 00 00    	jle    4a86 <timer_thread+0x3e6>
    int all_empty = 1;
    48b3:	89 9d 7c ff ff ff    	mov    %ebx,-0x84(%rbp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48b9:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    48bc:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    48c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    48c8:	44 89 f3             	mov    %r14d,%ebx
      for (int y = 0 ; y < 2 ; y++) {
    48cb:	4e 8d 24 f5 00 00 00 00 	lea    0x0(,%r14,8),%r12
    48d3:	45 31 ed             	xor    %r13d,%r13d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    48d6:	45 85 d2             	test   %r10d,%r10d
    48d9:	7e 7d                	jle    4958 <timer_thread+0x2b8>
    48db:	4c 89 ee             	mov    %r13,%rsi
    48de:	49 63 ca             	movslq %r10d,%rcx
    48e1:	45 31 c0             	xor    %r8d,%r8d
    48e4:	48 c1 e6 09          	shl    $0x9,%rsi
    48e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          if (x == k) { continue; }
    48f0:	45 39 f0             	cmp    %r14d,%r8d
    48f3:	74 42                	je     4937 <timer_thread+0x297>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    48f5:	49 8b 47 18          	mov    0x18(%r15),%rax
    48f9:	4a 8b 04 20          	mov    (%rax,%r12,1),%rax
    48fd:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4901:	4c 89 c0             	mov    %r8,%rax
    4904:	48 c1 e0 06          	shl    $0x6,%rax
    4908:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4910:	48 8b 10             	mov    (%rax),%rdx
    4913:	48 8b 40 08          	mov    0x8(%rax),%rax
    4917:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    491e:	48 8b b8 80 00 00 00 	mov    0x80(%rax),%rdi
    4925:	4d 85 c9             	test   %r9,%r9
    4928:	0f 8f aa 00 00 00    	jg     49d8 <timer_thread+0x338>
    492e:	48 85 ff             	test   %rdi,%rdi
    4931:	0f 8f a1 00 00 00    	jg     49d8 <timer_thread+0x338>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4937:	49 83 c0 01          	add    $0x1,%r8
    493b:	4c 39 c1             	cmp    %r8,%rcx
    493e:	75 b0                	jne    48f0 <timer_thread+0x250>
      for (int y = 0 ; y < 2 ; y++) {
    4940:	49 83 fd 01          	cmp    $0x1,%r13
    4944:	74 12                	je     4958 <timer_thread+0x2b8>
    4946:	41 bd 01 00 00 00    	mov    $0x1,%r13d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    494c:	45 85 d2             	test   %r10d,%r10d
    494f:	7f 8a                	jg     48db <timer_thread+0x23b>
    4951:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4958:	49 83 c6 01          	add    $0x1,%r14
    495c:	45 39 f2             	cmp    %r14d,%r10d
    495f:	0f 8f 63 ff ff ff    	jg     48c8 <timer_thread+0x228>
    4965:	8b 9d 7c ff ff ff    	mov    -0x84(%rbp),%ebx
    for (int k = 0 ; k < data->my_thread_count; k++) {
    496b:	45 85 d2             	test   %r10d,%r10d
    496e:	7e 48                	jle    49b8 <timer_thread+0x318>
    4970:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4974:	41 8b 57 40          	mov    0x40(%r15),%edx
    4978:	45 31 e4             	xor    %r12d,%r12d
    int all_waited = 1;
    497b:	bf 01 00 00 00       	mov    $0x1,%edi
    4980:	45 89 dd             	mov    %r11d,%r13d
    4983:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4988:	4a 8b 04 e6          	mov    (%rsi,%r12,8),%rax
    498c:	48 8b 40 38          	mov    0x38(%rax),%rax
    4990:	8b 88 9c 01 00 00    	mov    0x19c(%rax),%ecx
    4996:	39 d1                	cmp    %edx,%ecx
    4998:	0f 8c b2 00 00 00    	jl     4a50 <timer_thread+0x3b0>
    499e:	8b 80 9c 03 00 00    	mov    0x39c(%rax),%eax
    49a4:	39 d0                	cmp    %edx,%eax
    49a6:	7c 70                	jl     4a18 <timer_thread+0x378>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    49a8:	49 83 c4 01          	add    $0x1,%r12
    49ac:	45 39 67 30          	cmp    %r12d,0x30(%r15)
    49b0:	7f d6                	jg     4988 <timer_thread+0x2e8>
    49b2:	45 89 eb             	mov    %r13d,%r11d
    49b5:	41 21 fb             	and    %edi,%r11d
    if (all_empty == 1 && all_waited == 1) {
    49b8:	45 85 db             	test   %r11d,%r11d
    49bb:	0f 85 c5 00 00 00    	jne    4a86 <timer_thread+0x3e6>
      nanosleep(&drain , &drainrem);
    49c1:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    49c5:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    49c9:	e8 f2 d9 ff ff       	call   23c0 <nanosleep@plt>
    49ce:	e9 69 fe ff ff       	jmp    483c <timer_thread+0x19c>
    49d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    49d8:	8b 80 28 03 00 00    	mov    0x328(%rax),%eax
    49de:	48 83 ec 08          	sub    $0x8,%rsp
    49e2:	44 89 e9             	mov    %r13d,%ecx
    49e5:	48 8d 35 71 36 00 00 	lea    0x3671(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    49ec:	50                   	push   %rax
    49ed:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    49f3:	89 da                	mov    %ebx,%edx
    49f5:	50                   	push   %rax
    49f6:	31 c0                	xor    %eax,%eax
    49f8:	57                   	push   %rdi
    49f9:	bf 01 00 00 00       	mov    $0x1,%edi
    49fe:	e8 dd da ff ff       	call   24e0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4a03:	45 8b 57 30          	mov    0x30(%r15),%r10d
    4a07:	48 83 c4 20          	add    $0x20,%rsp
            all_empty = 0;
    4a0b:	45 31 db             	xor    %r11d,%r11d
    4a0e:	e9 2d ff ff ff       	jmp    4940 <timer_thread+0x2a0>
    4a13:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4a18:	89 c2                	mov    %eax,%edx
    4a1a:	bf 01 00 00 00       	mov    $0x1,%edi
    4a1f:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4a21:	49 83 c4 01          	add    $0x1,%r12
    4a25:	48 8d 35 d9 38 00 00 	lea    0x38d9(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4a2c:	e8 af da ff ff       	call   24e0 <__printf_chk@plt>
    4a31:	45 39 67 30          	cmp    %r12d,0x30(%r15)
    4a35:	7e 45                	jle    4a7c <timer_thread+0x3dc>
    4a37:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4a3b:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    4a3f:	31 ff                	xor    %edi,%edi
    4a41:	e9 42 ff ff ff       	jmp    4988 <timer_thread+0x2e8>
    4a46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4a50:	89 ca                	mov    %ecx,%edx
    4a52:	48 8d 35 ac 38 00 00 	lea    0x38ac(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4a59:	bf 01 00 00 00       	mov    $0x1,%edi
    4a5e:	31 c0                	xor    %eax,%eax
    4a60:	e8 7b da ff ff       	call   24e0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4a65:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4a69:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    4a6d:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4a6f:	4a 8b 04 e6          	mov    (%rsi,%r12,8),%rax
    4a73:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a77:	e9 22 ff ff ff       	jmp    499e <timer_thread+0x2fe>
          all_waited = 0; 
    4a7c:	45 89 eb             	mov    %r13d,%r11d
    4a7f:	31 ff                	xor    %edi,%edi
    4a81:	e9 2f ff ff ff       	jmp    49b5 <timer_thread+0x315>
    4a86:	48 8d 3d c7 35 00 00 	lea    0x35c7(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4a8d:	e8 be d8 ff ff       	call   2350 <puts@plt>
  while (data->running) {
    4a92:	41 8b 57 44          	mov    0x44(%r15),%edx
    4a96:	85 d2                	test   %edx,%edx
    4a98:	0f 84 f1 00 00 00    	je     4b8f <timer_thread+0x4ef>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4a9e:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4aa2:	31 db                	xor    %ebx,%ebx
    4aa4:	4c 8d 25 cf 35 00 00 	lea    0x35cf(%rip),%r12        # 807a <_IO_stdin_used+0x7a>
    4aab:	4c 8d 2d e3 35 00 00 	lea    0x35e3(%rip),%r13        # 8095 <_IO_stdin_used+0x95>
    4ab2:	85 c0                	test   %eax,%eax
    4ab4:	7e 3e                	jle    4af4 <timer_thread+0x454>
    4ab6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4ac0:	31 c0                	xor    %eax,%eax
    4ac2:	89 da                	mov    %ebx,%edx
    4ac4:	4c 89 e6             	mov    %r12,%rsi
    4ac7:	bf 01 00 00 00       	mov    $0x1,%edi
    4acc:	e8 0f da ff ff       	call   24e0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4ad1:	49 8b 47 18          	mov    0x18(%r15),%rax
    4ad5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4ad9:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4add:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4ae4:	0f 84 d1 00 00 00    	je     4bbb <timer_thread+0x51b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4aea:	48 83 c3 01          	add    $0x1,%rbx
    4aee:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4af2:	7f cc                	jg     4ac0 <timer_thread+0x420>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4af4:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4af8:	85 d2                	test   %edx,%edx
    4afa:	7e 7c                	jle    4b78 <timer_thread+0x4d8>
      for (int y = 0 ; y < data->task_count ; y++) {
    4afc:	41 8b 47 40          	mov    0x40(%r15),%eax
    4b00:	85 c0                	test   %eax,%eax
    4b02:	7e 74                	jle    4b78 <timer_thread+0x4d8>
    4b04:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4b07:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4b0b:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4b13:	31 c9                	xor    %ecx,%ecx
    4b15:	48 c1 e6 09          	shl    $0x9,%rsi
    4b19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4b20:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4b24:	48 8b 40 38          	mov    0x38(%rax),%rax
    4b28:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4b2c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4b32:	74 1c                	je     4b50 <timer_thread+0x4b0>
    4b34:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4b3e:	48 05 00 02 00 00    	add    $0x200,%rax
    4b44:	48 39 d0             	cmp    %rdx,%rax
    4b47:	74 26                	je     4b6f <timer_thread+0x4cf>
    4b49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4b50:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4b5a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4b60:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4b6a:	48 39 d0             	cmp    %rdx,%rax
    4b6d:	75 e1                	jne    4b50 <timer_thread+0x4b0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4b6f:	48 83 c1 08          	add    $0x8,%rcx
    4b73:	48 39 cf             	cmp    %rcx,%rdi
    4b76:	75 a8                	jne    4b20 <timer_thread+0x480>
    asm volatile ("mfence" ::: "memory");
    4b78:	0f ae f0             	mfence
    4b7b:	48 8d 3d 25 35 00 00 	lea    0x3525(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4b82:	e8 c9 d7 ff ff       	call   2350 <puts@plt>
    data->running = 0;
    4b87:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4b8f:	48 8d 3d 18 35 00 00 	lea    0x3518(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4b96:	e8 b5 d7 ff ff       	call   2350 <puts@plt>
}
    4b9b:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4b9f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ba8:	75 41                	jne    4beb <timer_thread+0x54b>
    4baa:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    4bae:	31 c0                	xor    %eax,%eax
    4bb0:	5b                   	pop    %rbx
    4bb1:	41 5c                	pop    %r12
    4bb3:	41 5d                	pop    %r13
    4bb5:	41 5e                	pop    %r14
    4bb7:	41 5f                	pop    %r15
    4bb9:	5d                   	pop    %rbp
    4bba:	c3                   	ret
    4bbb:	4c 89 ef             	mov    %r13,%rdi
    4bbe:	e8 8d d7 ff ff       	call   2350 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4bc3:	49 8b 47 18          	mov    0x18(%r15),%rax
    4bc7:	be 01 00 00 00       	mov    $0x1,%esi
    4bcc:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4bd0:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4bd4:	8b 78 60             	mov    0x60(%rax),%edi
    4bd7:	e8 b4 d8 ff ff       	call   2490 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4bdc:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4be0:	0f 8f da fe ff ff    	jg     4ac0 <timer_thread+0x420>
    4be6:	e9 09 ff ff ff       	jmp    4af4 <timer_thread+0x454>
}
    4beb:	e8 b0 d7 ff ff       	call   23a0 <__stack_chk_fail@plt>

0000000000004bf0 <minf>:
int minf(int a, int b) {
    4bf0:	f3 0f 1e fa          	endbr64
    4bf4:	55                   	push   %rbp
    4bf5:	48 89 e5             	mov    %rsp,%rbp
    4bf8:	ff 15 ea 63 00 00    	call   *0x63ea(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    4bfe:	5d                   	pop    %rbp
  if (b < a) { return b; }
    4bff:	39 f7                	cmp    %esi,%edi
    4c01:	89 f0                	mov    %esi,%eax
    4c03:	0f 4e c7             	cmovle %edi,%eax
}
    4c06:	c3                   	ret
    4c07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004c10 <maxf>:
int maxf(int a, int b) {
    4c10:	f3 0f 1e fa          	endbr64
    4c14:	55                   	push   %rbp
    4c15:	48 89 e5             	mov    %rsp,%rbp
    4c18:	ff 15 ca 63 00 00    	call   *0x63ca(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    4c1e:	5d                   	pop    %rbp
  if (b > a) { return b; }
    4c1f:	39 f7                	cmp    %esi,%edi
    4c21:	89 f0                	mov    %esi,%eax
    4c23:	0f 4d c7             	cmovge %edi,%eax
}
    4c26:	c3                   	ret
    4c27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004c30 <strtolower>:
void strtolower(char *str) {
    4c30:	f3 0f 1e fa          	endbr64
    4c34:	55                   	push   %rbp
    4c35:	48 89 e5             	mov    %rsp,%rbp
    4c38:	41 54                	push   %r12
    4c3a:	53                   	push   %rbx
    4c3b:	ff 15 a7 63 00 00    	call   *0x63a7(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    for (; *str; ++str)
    4c41:	48 0f be 1f          	movsbq (%rdi),%rbx
void strtolower(char *str) {
    4c45:	49 89 fc             	mov    %rdi,%r12
    for (; *str; ++str)
    4c48:	84 db                	test   %bl,%bl
    4c4a:	74 24                	je     4c70 <strtolower+0x40>
        *str = (char)tolower(*str);
    4c4c:	e8 7f d9 ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    4c51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c58:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4c5b:	49 83 c4 01          	add    $0x1,%r12
        *str = (char)tolower(*str);
    4c5f:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4c62:	41 88 54 24 ff       	mov    %dl,-0x1(%r12)
    for (; *str; ++str)
    4c67:	49 0f be 1c 24       	movsbq (%r12),%rbx
    4c6c:	84 db                	test   %bl,%bl
    4c6e:	75 e8                	jne    4c58 <strtolower+0x28>
}
    4c70:	5b                   	pop    %rbx
    4c71:	41 5c                	pop    %r12
    4c73:	5d                   	pop    %rbp
    4c74:	c3                   	ret
    4c75:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004c80 <zh_malloc>:
void *zh_malloc(size_t size) {
    4c80:	f3 0f 1e fa          	endbr64
    4c84:	55                   	push   %rbp
    4c85:	48 89 e5             	mov    %rsp,%rbp
    4c88:	ff 15 5a 63 00 00    	call   *0x635a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    void *buf = malloc(size);
    4c8e:	e8 0d d8 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4c93:	48 85 c0             	test   %rax,%rax
    4c96:	74 02                	je     4c9a <zh_malloc+0x1a>
}
    4c98:	5d                   	pop    %rbp
    4c99:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4c9a:	48 8b 0d 7f 63 00 00 	mov    0x637f(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4ca1:	ba 28 00 00 00       	mov    $0x28,%edx
    4ca6:	be 01 00 00 00       	mov    $0x1,%esi
    4cab:	48 8d 3d 0e 39 00 00 	lea    0x390e(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    4cb2:	e8 b9 d8 ff ff       	call   2570 <fwrite@plt>
        exit(1);
    4cb7:	bf 01 00 00 00       	mov    $0x1,%edi
    4cbc:	e8 8f d8 ff ff       	call   2550 <exit@plt>
    4cc1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4ccc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004cd0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4cd0:	f3 0f 1e fa          	endbr64
    4cd4:	55                   	push   %rbp
    4cd5:	48 89 e5             	mov    %rsp,%rbp
    4cd8:	53                   	push   %rbx
    4cd9:	48 83 ec 08          	sub    $0x8,%rsp
    4cdd:	ff 15 05 63 00 00    	call   *0x6305(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    const char *dot = strrchr(filename, '.');
    4ce3:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4ce8:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4ceb:	e8 e0 d6 ff ff       	call   23d0 <strrchr@plt>
    if (!dot || dot == filename)
    4cf0:	48 85 c0             	test   %rax,%rax
    4cf3:	74 13                	je     4d08 <get_filename_ext+0x38>
    4cf5:	48 39 c3             	cmp    %rax,%rbx
    4cf8:	74 0e                	je     4d08 <get_filename_ext+0x38>
}
    4cfa:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    return dot + 1;
    4cfe:	48 83 c0 01          	add    $0x1,%rax
}
    4d02:	c9                   	leave
    4d03:	c3                   	ret
    4d04:	0f 1f 40 00          	nopl   0x0(%rax)
    4d08:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
        return "";
    4d0c:	48 8d 05 e3 33 00 00 	lea    0x33e3(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4d13:	c9                   	leave
    4d14:	c3                   	ret
    4d15:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004d20 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4d20:	f3 0f 1e fa          	endbr64
    4d24:	55                   	push   %rbp
    4d25:	48 89 e5             	mov    %rsp,%rbp
    4d28:	41 56                	push   %r14
    4d2a:	41 55                	push   %r13
    4d2c:	41 54                	push   %r12
    4d2e:	53                   	push   %rbx
    4d2f:	48 81 ec 10 08 00 00 	sub    $0x810,%rsp
    4d36:	ff 15 ac 62 00 00    	call   *0x62ac(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    4d3c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4d45:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    4d49:	31 c0                	xor    %eax,%eax
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d4b:	4c 8d ad d0 f7 ff ff 	lea    -0x830(%rbp),%r13
    4d52:	49 89 f6             	mov    %rsi,%r14
    4d55:	49 89 d4             	mov    %rdx,%r12
    4d58:	48 89 fe             	mov    %rdi,%rsi
    4d5b:	ba 00 04 00 00       	mov    $0x400,%edx
    4d60:	4c 89 ef             	mov    %r13,%rdi
    4d63:	e8 58 d7 ff ff       	call   24c0 <__strcpy_chk@plt>
    for (; *str; ++str)
    4d68:	48 0f be 9d d0 f7 ff ff 	movsbq -0x830(%rbp),%rbx
    4d70:	84 db                	test   %bl,%bl
    4d72:	74 1e                	je     4d92 <send_headers+0x72>
        *str = (char)tolower(*str);
    4d74:	e8 57 d8 ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    4d79:	48 8b 08             	mov    (%rax),%rcx
    4d7c:	4c 89 e8             	mov    %r13,%rax
    4d7f:	90                   	nop
    4d80:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4d83:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4d87:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4d8a:	48 0f be 18          	movsbq (%rax),%rbx
    4d8e:	84 db                	test   %bl,%bl
    4d90:	75 ee                	jne    4d80 <send_headers+0x60>
    void *buf = malloc(size);
    4d92:	bf 11 00 00 00       	mov    $0x11,%edi
    4d97:	e8 04 d7 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4d9c:	48 85 c0             	test   %rax,%rax
    4d9f:	0f 84 72 04 00 00    	je     5217 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4da5:	66 0f 6f 05 33 3e 00 00 	movdqa 0x3e33(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    iov[0].iov_base = zh_malloc(slen);
    4dad:	49 89 04 24          	mov    %rax,(%r12)
    void *buf = malloc(size);
    4db1:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4db6:	49 c7 44 24 08 11 00 00 00 	movq   $0x11,0x8(%r12)
    4dbf:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4dc3:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4dc6:	e8 d5 d6 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4dcb:	48 85 c0             	test   %rax,%rax
    4dce:	0f 84 43 04 00 00    	je     5217 <send_headers+0x4f7>
    4dd4:	66 0f 6f 05 14 3e 00 00 	movdqa 0x3e14(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    iov[1].iov_base = zh_malloc(slen);
    4ddc:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    const char *dot = strrchr(filename, '.');
    4de1:	4c 89 ef             	mov    %r13,%rdi
    4de4:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4dee:	49 c7 44 24 18 17 00 00 00 	movq   $0x17,0x18(%r12)
    4df7:	0f 11 00             	movups %xmm0,(%rax)
    4dfa:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4dfe:	be 2e 00 00 00       	mov    $0x2e,%esi
    4e03:	e8 c8 d5 ff ff       	call   23d0 <strrchr@plt>
    if (!dot || dot == filename)
    4e08:	48 85 c0             	test   %rax,%rax
    4e0b:	0f 84 df 02 00 00    	je     50f0 <send_headers+0x3d0>
    4e11:	4c 39 e8             	cmp    %r13,%rax
    4e14:	0f 84 d6 02 00 00    	je     50f0 <send_headers+0x3d0>
    return dot + 1;
    4e1a:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4e1e:	48 8d 3d 9f 32 00 00 	lea    0x329f(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4e25:	48 89 de             	mov    %rbx,%rsi
    4e28:	e8 03 d6 ff ff       	call   2430 <strcmp@plt>
    4e2d:	85 c0                	test   %eax,%eax
    4e2f:	75 1e                	jne    4e4f <send_headers+0x12f>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4e31:	66 0f 6f 05 c7 3d 00 00 	movdqa 0x3dc7(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4e39:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4e40:	66 0f 6f 05 c8 3d 00 00 	movdqa 0x3dc8(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e48:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("jpeg", file_ext) == 0)
    4e4f:	48 89 de             	mov    %rbx,%rsi
    4e52:	48 8d 3d 6f 32 00 00 	lea    0x326f(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4e59:	e8 d2 d5 ff ff       	call   2430 <strcmp@plt>
    4e5e:	85 c0                	test   %eax,%eax
    4e60:	75 1e                	jne    4e80 <send_headers+0x160>
    4e62:	66 0f 6f 05 96 3d 00 00 	movdqa 0x3d96(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4e6a:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4e71:	66 0f 6f 05 97 3d 00 00 	movdqa 0x3d97(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e79:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("png", file_ext) == 0)
    4e80:	48 89 de             	mov    %rbx,%rsi
    4e83:	48 8d 3d 43 32 00 00 	lea    0x3243(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4e8a:	e8 a1 d5 ff ff       	call   2430 <strcmp@plt>
    4e8f:	85 c0                	test   %eax,%eax
    4e91:	0f 84 09 02 00 00    	je     50a0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4e97:	48 89 de             	mov    %rbx,%rsi
    4e9a:	48 8d 3d 30 32 00 00 	lea    0x3230(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4ea1:	e8 8a d5 ff ff       	call   2430 <strcmp@plt>
    4ea6:	85 c0                	test   %eax,%eax
    4ea8:	0f 84 a2 02 00 00    	je     5150 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4eae:	48 89 de             	mov    %rbx,%rsi
    4eb1:	48 8d 3d 1d 32 00 00 	lea    0x321d(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4eb8:	e8 73 d5 ff ff       	call   2430 <strcmp@plt>
    4ebd:	85 c0                	test   %eax,%eax
    4ebf:	0f 84 63 02 00 00    	je     5128 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4ec5:	48 89 de             	mov    %rbx,%rsi
    4ec8:	48 8d 3d 49 32 00 00 	lea    0x3249(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4ecf:	e8 5c d5 ff ff       	call   2430 <strcmp@plt>
    4ed4:	85 c0                	test   %eax,%eax
    4ed6:	0f 84 24 02 00 00    	je     5100 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4edc:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4edf:	0f 84 53 01 00 00    	je     5038 <send_headers+0x318>
    if (strcmp("css", file_ext) == 0)
    4ee5:	48 89 de             	mov    %rbx,%rsi
    4ee8:	48 8d 3d ea 31 00 00 	lea    0x31ea(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4eef:	e8 3c d5 ff ff       	call   2430 <strcmp@plt>
    4ef4:	85 c0                	test   %eax,%eax
    4ef6:	0f 84 a4 02 00 00    	je     51a0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4efc:	48 89 de             	mov    %rbx,%rsi
    4eff:	48 8d 3d d7 31 00 00 	lea    0x31d7(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4f06:	e8 25 d5 ff ff       	call   2430 <strcmp@plt>
    4f0b:	85 c0                	test   %eax,%eax
    4f0d:	0f 84 65 02 00 00    	je     5178 <send_headers+0x458>
    slen = strlen(send_buffer);
    4f13:	4c 8d ad d0 fb ff ff 	lea    -0x430(%rbp),%r13
    4f1a:	4c 89 ef             	mov    %r13,%rdi
    4f1d:	e8 6e d4 ff ff       	call   2390 <strlen@plt>
    void *buf = malloc(size);
    4f22:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4f25:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4f28:	e8 73 d5 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4f2d:	48 85 c0             	test   %rax,%rax
    4f30:	0f 84 e1 02 00 00    	je     5217 <send_headers+0x4f7>
    iov[2].iov_base = zh_malloc(slen);
    4f36:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    iov[2].iov_len = slen;
    4f3b:	49 89 5c 24 28       	mov    %rbx,0x28(%r12)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f40:	83 fb 08             	cmp    $0x8,%ebx
    4f43:	0f 83 37 01 00 00    	jae    5080 <send_headers+0x360>
    4f49:	f6 c3 04             	test   $0x4,%bl
    4f4c:	0f 85 71 02 00 00    	jne    51c3 <send_headers+0x4a3>
    4f52:	85 db                	test   %ebx,%ebx
    4f54:	74 12                	je     4f68 <send_headers+0x248>
    4f56:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    4f5d:	88 10                	mov    %dl,(%rax)
    4f5f:	f6 c3 02             	test   $0x2,%bl
    4f62:	0f 85 8b 02 00 00    	jne    51f3 <send_headers+0x4d3>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4f68:	4d 89 f0             	mov    %r14,%r8
    4f6b:	48 8d 0d 6f 31 00 00 	lea    0x316f(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4f72:	4c 89 ef             	mov    %r13,%rdi
    4f75:	31 c0                	xor    %eax,%eax
    4f77:	ba 00 04 00 00       	mov    $0x400,%edx
    4f7c:	be 01 00 00 00       	mov    $0x1,%esi
    4f81:	e8 5a d6 ff ff       	call   25e0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4f86:	4c 89 ef             	mov    %r13,%rdi
    4f89:	e8 02 d4 ff ff       	call   2390 <strlen@plt>
    void *buf = malloc(size);
    4f8e:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4f91:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4f94:	e8 07 d5 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4f99:	48 85 c0             	test   %rax,%rax
    4f9c:	0f 84 75 02 00 00    	je     5217 <send_headers+0x4f7>
    iov[3].iov_base = zh_malloc(slen);
    4fa2:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    iov[3].iov_len = slen;
    4fa7:	49 89 5c 24 38       	mov    %rbx,0x38(%r12)
    4fac:	83 fb 08             	cmp    $0x8,%ebx
    4faf:	0f 83 13 01 00 00    	jae    50c8 <send_headers+0x3a8>
    4fb5:	f6 c3 04             	test   $0x4,%bl
    4fb8:	0f 85 1d 02 00 00    	jne    51db <send_headers+0x4bb>
    4fbe:	85 db                	test   %ebx,%ebx
    4fc0:	74 12                	je     4fd4 <send_headers+0x2b4>
    4fc2:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    4fc9:	88 10                	mov    %dl,(%rax)
    4fcb:	f6 c3 02             	test   $0x2,%bl
    4fce:	0f 85 31 02 00 00    	jne    5205 <send_headers+0x4e5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4fd4:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4fd9:	bf 02 00 00 00       	mov    $0x2,%edi
    4fde:	c6 85 d2 fb ff ff 00 	movb   $0x0,-0x42e(%rbp)
    4fe5:	66 89 85 d0 fb ff ff 	mov    %ax,-0x430(%rbp)
    4fec:	e8 af d4 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4ff1:	48 85 c0             	test   %rax,%rax
    4ff4:	0f 84 1d 02 00 00    	je     5217 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ffa:	0f b7 95 d0 fb ff ff 	movzwl -0x430(%rbp),%edx
    iov[4].iov_base = zh_malloc(slen);
    5001:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    iov[4].iov_len = slen;
    5006:	49 c7 44 24 48 02 00 00 00 	movq   $0x2,0x48(%r12)
    500f:	66 89 10             	mov    %dx,(%rax)
}
    5012:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    5016:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    501f:	0f 85 19 02 00 00    	jne    523e <send_headers+0x51e>
    5025:	48 81 c4 10 08 00 00 	add    $0x810,%rsp
    502c:	5b                   	pop    %rbx
    502d:	41 5c                	pop    %r12
    502f:	41 5d                	pop    %r13
    5031:	41 5e                	pop    %r14
    5033:	5d                   	pop    %rbp
    5034:	c3                   	ret
    5035:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
    5038:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    503c:	0f 85 a3 fe ff ff    	jne    4ee5 <send_headers+0x1c5>
    5042:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    5046:	0f 85 99 fe ff ff    	jne    4ee5 <send_headers+0x1c5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    504c:	66 0f 6f 05 0c 3c 00 00 	movdqa 0x3c0c(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5054:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    505e:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    5065:	66 0f 6f 05 03 3c 00 00 	movdqa 0x3c03(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    506d:	0f 29 85 e0 fb ff ff 	movaps %xmm0,-0x420(%rbp)
    5074:	48 89 85 ef fb ff ff 	mov    %rax,-0x411(%rbp)
    507b:	e9 65 fe ff ff       	jmp    4ee5 <send_headers+0x1c5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5080:	89 da                	mov    %ebx,%edx
    5082:	48 89 c7             	mov    %rax,%rdi
    5085:	4c 89 ee             	mov    %r13,%rsi
    5088:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    508d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5092:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5095:	c1 e9 03             	shr    $0x3,%ecx
    5098:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    509b:	e9 c8 fe ff ff       	jmp    4f68 <send_headers+0x248>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    50a0:	66 0f 6f 05 58 3b 00 00 	movdqa 0x3b58(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    50a8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    50af:	66 0f 6f 05 69 3b 00 00 	movdqa 0x3b69(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    50b7:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    50be:	e9 d4 fd ff ff       	jmp    4e97 <send_headers+0x177>
    50c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    50c8:	89 da                	mov    %ebx,%edx
    50ca:	48 89 c7             	mov    %rax,%rdi
    50cd:	4c 89 ee             	mov    %r13,%rsi
    50d0:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    50d5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    50da:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    50dd:	c1 e9 03             	shr    $0x3,%ecx
    50e0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    50e3:	e9 ec fe ff ff       	jmp    4fd4 <send_headers+0x2b4>
    50e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    50f0:	48 8d 1d ff 2f 00 00 	lea    0x2fff(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    50f7:	e9 9b fd ff ff       	jmp    4e97 <send_headers+0x177>
    50fc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5100:	66 0f 6f 05 38 3b 00 00 	movdqa 0x3b38(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    5108:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    510f:	66 0f 6f 05 39 3b 00 00 	movdqa 0x3b39(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5117:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    511e:	e9 b9 fd ff ff       	jmp    4edc <send_headers+0x1bc>
    5123:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5128:	66 0f 6f 05 10 3b 00 00 	movdqa 0x3b10(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    5130:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    5137:	66 0f 6f 05 11 3b 00 00 	movdqa 0x3b11(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    513f:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    5146:	e9 7a fd ff ff       	jmp    4ec5 <send_headers+0x1a5>
    514b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5150:	66 0f 6f 05 a8 3a 00 00 	movdqa 0x3aa8(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    5158:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    515f:	66 0f 6f 05 c9 3a 00 00 	movdqa 0x3ac9(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    5167:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    516e:	e9 3b fd ff ff       	jmp    4eae <send_headers+0x18e>
    5173:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5178:	66 0f 6f 05 c0 3a 00 00 	movdqa 0x3ac0(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    5180:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    5187:	66 0f 6f 05 01 3b 00 00 	movdqa 0x3b01(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    518f:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    5196:	e9 78 fd ff ff       	jmp    4f13 <send_headers+0x1f3>
    519b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    51a0:	66 0f 6f 05 98 3a 00 00 	movdqa 0x3a98(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    51a8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    51af:	66 0f 6f 05 c9 3a 00 00 	movdqa 0x3ac9(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    51b7:	0f 11 85 d9 fb ff ff 	movups %xmm0,-0x427(%rbp)
    51be:	e9 39 fd ff ff       	jmp    4efc <send_headers+0x1dc>
  return __builtin___memcpy_chk (__dest, __src, __len,
    51c3:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    51c9:	89 db                	mov    %ebx,%ebx
    51cb:	89 10                	mov    %edx,(%rax)
    51cd:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    51d2:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    51d6:	e9 8d fd ff ff       	jmp    4f68 <send_headers+0x248>
    51db:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    51e1:	89 db                	mov    %ebx,%ebx
    51e3:	89 10                	mov    %edx,(%rax)
    51e5:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    51ea:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    51ee:	e9 e1 fd ff ff       	jmp    4fd4 <send_headers+0x2b4>
    51f3:	89 db                	mov    %ebx,%ebx
    51f5:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    51fb:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5200:	e9 63 fd ff ff       	jmp    4f68 <send_headers+0x248>
    5205:	89 db                	mov    %ebx,%ebx
    5207:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    520d:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5212:	e9 bd fd ff ff       	jmp    4fd4 <send_headers+0x2b4>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5217:	48 8b 0d 02 5e 00 00 	mov    0x5e02(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    521e:	ba 28 00 00 00       	mov    $0x28,%edx
    5223:	be 01 00 00 00       	mov    $0x1,%esi
    5228:	48 8d 3d 91 33 00 00 	lea    0x3391(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    522f:	e8 3c d3 ff ff       	call   2570 <fwrite@plt>
        exit(1);
    5234:	bf 01 00 00 00       	mov    $0x1,%edi
    5239:	e8 12 d3 ff ff       	call   2550 <exit@plt>
}
    523e:	e8 5d d1 ff ff       	call   23a0 <__stack_chk_fail@plt>
    5243:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    524e:	66 90                	xchg   %ax,%ax

0000000000005250 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5250:	f3 0f 1e fa          	endbr64
    5254:	55                   	push   %rbp
    5255:	48 89 e5             	mov    %rsp,%rbp
    5258:	41 56                	push   %r14
    525a:	41 55                	push   %r13
    525c:	41 54                	push   %r12
    525e:	53                   	push   %rbx
    525f:	ff 15 83 5d 00 00    	call   *0x5d83(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    5265:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    5268:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    526b:	48 89 f3             	mov    %rsi,%rbx
    526e:	49 89 d6             	mov    %rdx,%r14
    void *buf = malloc(size);
    5271:	e8 2a d2 ff ff       	call   24a0 <malloc@plt>
    5276:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    5279:	48 85 c0             	test   %rax,%rax
    527c:	74 69                	je     52e7 <copy_file_contents+0x97>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    527e:	4c 89 ef             	mov    %r13,%rdi
    5281:	31 f6                	xor    %esi,%esi
    5283:	31 c0                	xor    %eax,%eax
    5285:	e8 86 d2 ff ff       	call   2510 <open@plt>
    528a:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    528d:	85 c0                	test   %eax,%eax
    528f:	0f 88 88 d3 ff ff    	js     261d <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    5295:	48 89 da             	mov    %rbx,%rdx
    5298:	4c 89 e6             	mov    %r12,%rsi
    529b:	89 c7                	mov    %eax,%edi
    529d:	e8 6e d1 ff ff       	call   2410 <read@plt>
    if (ret < file_size) {
    52a2:	48 98                	cltq
    52a4:	48 39 d8             	cmp    %rbx,%rax
    52a7:	7c 1f                	jl     52c8 <copy_file_contents+0x78>
    close(fd);
    52a9:	44 89 ef             	mov    %r13d,%edi
    52ac:	e8 3f d1 ff ff       	call   23f0 <close@plt>
    iov->iov_base = buf;
    52b1:	4d 89 26             	mov    %r12,(%r14)
    iov->iov_len = file_size;
    52b4:	49 89 5e 08          	mov    %rbx,0x8(%r14)
}
    52b8:	5b                   	pop    %rbx
    52b9:	41 5c                	pop    %r12
    52bb:	41 5d                	pop    %r13
    52bd:	41 5e                	pop    %r14
    52bf:	5d                   	pop    %rbp
    52c0:	c3                   	ret
    52c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    52c8:	48 8b 0d 51 5d 00 00 	mov    0x5d51(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    52cf:	ba 1a 00 00 00       	mov    $0x1a,%edx
    52d4:	be 01 00 00 00       	mov    $0x1,%esi
    52d9:	48 8d 3d 17 2e 00 00 	lea    0x2e17(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    52e0:	e8 8b d2 ff ff       	call   2570 <fwrite@plt>
    52e5:	eb c2                	jmp    52a9 <copy_file_contents+0x59>
    52e7:	48 8b 0d 32 5d 00 00 	mov    0x5d32(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    52ee:	ba 28 00 00 00       	mov    $0x28,%edx
    52f3:	be 01 00 00 00       	mov    $0x1,%esi
    52f8:	48 8d 3d c1 32 00 00 	lea    0x32c1(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    52ff:	e8 6c d2 ff ff       	call   2570 <fwrite@plt>
        exit(1);
    5304:	bf 01 00 00 00       	mov    $0x1,%edi
    5309:	e8 42 d2 ff ff       	call   2550 <exit@plt>
    530e:	66 90                	xchg   %ax,%ax

0000000000005310 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    5310:	f3 0f 1e fa          	endbr64
    5314:	55                   	push   %rbp
    5315:	48 89 e5             	mov    %rsp,%rbp
    5318:	ff 15 ca 5c 00 00    	call   *0x5cca(%rip)        # afe8 <mcount@GLIBC_2.2.5>
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    531e:	8b 46 44             	mov    0x44(%rsi),%eax
    5321:	48 89 fa             	mov    %rdi,%rdx
    5324:	48 89 f7             	mov    %rsi,%rdi
    5327:	8d 70 01             	lea    0x1(%rax),%esi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    532a:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5330:	48 8b 07             	mov    (%rdi),%rax
    5333:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5336:	f6 c1 02             	test   $0x2,%cl
    5339:	74 00                	je     533b <add_write_request+0x2b>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    533b:	89 f0                	mov    %esi,%eax
    533d:	44 29 c0             	sub    %r8d,%eax
    5340:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5343:	0f 82 e0 d2 ff ff    	jb     2629 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5349:	c1 e9 0a             	shr    $0xa,%ecx
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    534c:	8b 47 44             	mov    0x44(%rdi),%eax
    534f:	23 47 58             	and    0x58(%rdi),%eax
		sq->sqe_tail = next;
    5352:	89 77 44             	mov    %esi,0x44(%rdi)
	if (ring->flags & IORING_SETUP_SQE128)
    5355:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5358:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    535b:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    535f:	d3 e0                	shl    %cl,%eax
    5361:	8b 4a 04             	mov    0x4(%rdx),%ecx
    5364:	48 c1 e0 06          	shl    $0x6,%rax
    5368:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    536c:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    5372:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5375:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    5379:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    537f:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5387:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    538b:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    538e:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    5395:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    539d:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    53a1:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    53a5:	e8 06 d0 ff ff       	call   23b0 <io_uring_submit@plt>
}
    53aa:	31 c0                	xor    %eax,%eax
    53ac:	5d                   	pop    %rbp
    53ad:	c3                   	ret
    53ae:	66 90                	xchg   %ax,%ax

00000000000053b0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    53b0:	f3 0f 1e fa          	endbr64
    53b4:	55                   	push   %rbp
    53b5:	48 89 e5             	mov    %rsp,%rbp
    53b8:	41 56                	push   %r14
    53ba:	41 55                	push   %r13
    53bc:	41 54                	push   %r12
    53be:	53                   	push   %rbx
    53bf:	ff 15 23 5c 00 00    	call   *0x5c23(%rip)        # afe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    53c5:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    53c8:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    53ce:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    53d1:	83 c0 01             	add    $0x1,%eax
    53d4:	48 89 f3             	mov    %rsi,%rbx
    53d7:	41 89 fe             	mov    %edi,%r14d
		head = IO_URING_READ_ONCE(*sq->khead);
    53da:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    53dc:	f6 c1 02             	test   $0x2,%cl
    53df:	74 00                	je     53e1 <add_read_request+0x31>
	if (next - head <= sq->ring_entries) {
    53e1:	89 c2                	mov    %eax,%edx
    53e3:	29 f2                	sub    %esi,%edx
    53e5:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    53e8:	0f 82 4b d2 ff ff    	jb     2639 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53ee:	44 8b 63 44          	mov    0x44(%rbx),%r12d
	if (ring->flags & IORING_SETUP_SQE128)
    53f2:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    53f5:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    53f8:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    53fd:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5400:	44 23 63 58          	and    0x58(%rbx),%r12d
    5404:	41 d3 e4             	shl    %cl,%r12d
    5407:	49 c1 e4 06          	shl    $0x6,%r12
    540b:	4c 03 63 38          	add    0x38(%rbx),%r12
    540f:	e8 8c d0 ff ff       	call   24a0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    5414:	be 01 00 00 00       	mov    $0x1,%esi
    5419:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    541e:	49 89 c5             	mov    %rax,%r13
    req->iov[0].iov_base = malloc(READ_SZ);
    5421:	e8 fa cf ff ff       	call   2420 <calloc@plt>
    req->client_socket = client_socket;
    5426:	45 89 75 08          	mov    %r14d,0x8(%r13)
	sqe->addr3 = 0;
    542a:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    542e:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5431:	49 89 45 10          	mov    %rax,0x10(%r13)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    5435:	49 8d 45 10          	lea    0x10(%r13),%rax
    req->iov[0].iov_len = READ_SZ;
    5439:	49 c7 45 18 00 20 00 00 	movq   $0x2000,0x18(%r13)
    req->event_type = EVENT_TYPE_READ;
    5441:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
	sqe->fd = fd;
    5449:	45 89 74 24 04       	mov    %r14d,0x4(%r12)
	sqe->user_data = (unsigned long) data;
    544e:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
	sqe->opcode = (__u8) op;
    5453:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->off = offset;
    545b:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    5464:	49 89 44 24 10       	mov    %rax,0x10(%r12)
	sqe->len = len;
    5469:	49 c7 44 24 18 01 00 00 00 	movq   $0x1,0x18(%r12)
	sqe->buf_index = 0;
    5472:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->addr3 = 0;
    547b:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    io_uring_submit(ring);
    5481:	e8 2a cf ff ff       	call   23b0 <io_uring_submit@plt>
}
    5486:	5b                   	pop    %rbx
    5487:	31 c0                	xor    %eax,%eax
    5489:	41 5c                	pop    %r12
    548b:	41 5d                	pop    %r13
    548d:	41 5e                	pop    %r14
    548f:	5d                   	pop    %rbp
    5490:	c3                   	ret
    5491:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    549c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000054a0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    54a0:	f3 0f 1e fa          	endbr64
    54a4:	55                   	push   %rbp
    54a5:	48 89 e5             	mov    %rsp,%rbp
    54a8:	41 57                	push   %r15
    54aa:	41 56                	push   %r14
    54ac:	41 55                	push   %r13
    54ae:	41 54                	push   %r12
    54b0:	53                   	push   %rbx
    54b1:	48 83 ec 08          	sub    $0x8,%rsp
    54b5:	ff 15 2d 5b 00 00    	call   *0x5b2d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    54bb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    54be:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    54c3:	41 89 f7             	mov    %esi,%r15d
    54c6:	49 89 d4             	mov    %rdx,%r12
    void *buf = malloc(size);
    54c9:	e8 d2 cf ff ff       	call   24a0 <malloc@plt>
    54ce:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    54d1:	48 85 c0             	test   %rax,%rax
    54d4:	0f 84 eb 00 00 00    	je     55c5 <_send_static_string_content+0x125>
    unsigned long slen = strlen(str);
    54da:	4c 89 ef             	mov    %r13,%rdi
    54dd:	e8 ae ce ff ff       	call   2390 <strlen@plt>
    req->iovec_count = 1;
    54e2:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    54e9:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
    void *buf = malloc(size);
    54ed:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    54f0:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    54f3:	e8 a8 cf ff ff       	call   24a0 <malloc@plt>
    54f8:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    54fb:	48 85 c0             	test   %rax,%rax
    54fe:	0f 84 c1 00 00 00    	je     55c5 <_send_static_string_content+0x125>
    req->iov[0].iov_base = zh_malloc(slen);
    5504:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5508:	4c 89 f2             	mov    %r14,%rdx
    550b:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    550e:	4c 89 73 18          	mov    %r14,0x18(%rbx)
    5512:	e8 59 cf ff ff       	call   2470 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5517:	41 8b 44 24 44       	mov    0x44(%r12),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    551c:	41 8b 8c 24 c0 00 00 00 	mov    0xc0(%r12),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5524:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5527:	49 8b 04 24          	mov    (%r12),%rax
    552b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    552d:	f6 c1 02             	test   $0x2,%cl
    5530:	0f 85 8a 00 00 00    	jne    55c0 <_send_static_string_content+0x120>
	if (next - head <= sq->ring_entries) {
    5536:	89 d0                	mov    %edx,%eax
    5538:	29 f0                	sub    %esi,%eax
    553a:	41 39 44 24 5c       	cmp    %eax,0x5c(%r12)
    553f:	0f 82 fe d0 ff ff    	jb     2643 <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5545:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5548:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    554d:	41 23 44 24 58       	and    0x58(%r12),%eax
    io_uring_submit(ring);
    5552:	4c 89 e7             	mov    %r12,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    5555:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5558:	41 89 54 24 44       	mov    %edx,0x44(%r12)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    555d:	8b 53 04             	mov    0x4(%rbx),%edx
	sqe->addr3 = 0;
    5560:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5564:	d3 e0                	shl    %cl,%eax
    5566:	8b 4b 08             	mov    0x8(%rbx),%ecx
    req->event_type = EVENT_TYPE_WRITE;
    5569:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    556f:	48 c1 e0 06          	shl    $0x6,%rax
    5573:	49 03 44 24 38       	add    0x38(%r12),%rax
	sqe->fd = fd;
    5578:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    557b:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    557f:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5585:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    558d:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5591:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5594:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    559b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    55a3:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    55a7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    55ab:	48 83 c4 08          	add    $0x8,%rsp
    55af:	5b                   	pop    %rbx
    55b0:	41 5c                	pop    %r12
    55b2:	41 5d                	pop    %r13
    55b4:	41 5e                	pop    %r14
    55b6:	41 5f                	pop    %r15
    55b8:	5d                   	pop    %rbp
    io_uring_submit(ring);
    55b9:	e9 f2 cd ff ff       	jmp    23b0 <io_uring_submit@plt>
    55be:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    55c0:	e9 71 ff ff ff       	jmp    5536 <_send_static_string_content+0x96>
    55c5:	48 8b 0d 54 5a 00 00 	mov    0x5a54(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    55cc:	ba 28 00 00 00       	mov    $0x28,%edx
    55d1:	be 01 00 00 00       	mov    $0x1,%esi
    55d6:	48 8d 3d e3 2f 00 00 	lea    0x2fe3(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    55dd:	e8 8e cf ff ff       	call   2570 <fwrite@plt>
        exit(1);
    55e2:	bf 01 00 00 00       	mov    $0x1,%edi
    55e7:	e8 64 cf ff ff       	call   2550 <exit@plt>
    55ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000055f0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    55f0:	f3 0f 1e fa          	endbr64
    55f4:	55                   	push   %rbp
    55f5:	48 89 e5             	mov    %rsp,%rbp
    55f8:	ff 15 ea 59 00 00    	call   *0x59ea(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    55fe:	5d                   	pop    %rbp
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    55ff:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5602:	89 fe                	mov    %edi,%esi
    5604:	48 8b 3d 0d 5a 00 00 	mov    0x5a0d(%rip),%rdi        # b018 <unimplemented_content>
    560b:	e9 90 fe ff ff       	jmp    54a0 <_send_static_string_content>

0000000000005610 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5610:	f3 0f 1e fa          	endbr64
    5614:	55                   	push   %rbp
    5615:	48 89 e5             	mov    %rsp,%rbp
    5618:	ff 15 ca 59 00 00    	call   *0x59ca(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    561e:	5d                   	pop    %rbp
void handle_http_404(int client_socket, struct io_uring *ring) {
    561f:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5622:	89 fe                	mov    %edi,%esi
    5624:	48 8b 3d e5 59 00 00 	mov    0x59e5(%rip),%rdi        # b010 <http_404_content>
    562b:	e9 70 fe ff ff       	jmp    54a0 <_send_static_string_content>

0000000000005630 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    5630:	f3 0f 1e fa          	endbr64
    5634:	55                   	push   %rbp
    5635:	48 89 e5             	mov    %rsp,%rbp
    5638:	41 57                	push   %r15
    563a:	41 56                	push   %r14
    563c:	41 55                	push   %r13
    563e:	41 54                	push   %r12
    5640:	53                   	push   %rbx
    5641:	48 81 ec a8 04 00 00 	sub    $0x4a8,%rsp
    5648:	ff 15 9a 59 00 00    	call   *0x599a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    564e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5657:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    565b:	31 c0                	xor    %eax,%eax
    565d:	49 89 fc             	mov    %rdi,%r12
    5660:	41 89 f5             	mov    %esi,%r13d
    5663:	49 89 d6             	mov    %rdx,%r14
    if (path[strlen(path) - 1] == '/') {
    5666:	e8 25 cd ff ff       	call   2390 <strlen@plt>
    566b:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
    5671:	48 89 c3             	mov    %rax,%rbx
    5674:	0f 84 b6 00 00 00    	je     5730 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    567a:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    567f:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    5683:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5688:	4c 89 e6             	mov    %r12,%rsi
    568b:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5692:	66 89 85 c4 fb ff ff 	mov    %ax,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5699:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    56a0:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    56aa:	e8 a1 cd ff ff       	call   2450 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    56af:	48 8d b5 30 fb ff ff 	lea    -0x4d0(%rbp),%rsi
    56b6:	4c 89 ff             	mov    %r15,%rdi
    56b9:	e8 a2 cd ff ff       	call   2460 <stat@plt>
    56be:	83 f8 ff             	cmp    $0xffffffff,%eax
    56c1:	0f 84 41 01 00 00    	je     5808 <handle_get_method+0x1d8>
        if (S_ISREG(path_stat.st_mode)) {
    56c7:	8b 85 48 fb ff ff    	mov    -0x4b8(%rbp),%eax
    56cd:	25 00 f0 00 00       	and    $0xf000,%eax
    56d2:	3d 00 80 00 00       	cmp    $0x8000,%eax
    56d7:	0f 84 b3 00 00 00    	je     5790 <handle_get_method+0x160>
    _send_static_string_content(http_404_content, client_socket, ring);
    56dd:	48 8b 3d 2c 59 00 00 	mov    0x592c(%rip),%rdi        # b010 <http_404_content>
    56e4:	4c 89 f2             	mov    %r14,%rdx
    56e7:	44 89 ee             	mov    %r13d,%esi
    56ea:	e8 b1 fd ff ff       	call   54a0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    56ef:	4c 89 fa             	mov    %r15,%rdx
    56f2:	bf 01 00 00 00       	mov    $0x1,%edi
    56f7:	31 c0                	xor    %eax,%eax
    56f9:	48 8d 35 47 2a 00 00 	lea    0x2a47(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5700:	e8 db cd ff ff       	call   24e0 <__printf_chk@plt>
}
    5705:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5709:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5712:	0f 85 20 01 00 00    	jne    5838 <handle_get_method+0x208>
    5718:	48 81 c4 a8 04 00 00 	add    $0x4a8,%rsp
    571f:	5b                   	pop    %rbx
    5720:	41 5c                	pop    %r12
    5722:	41 5d                	pop    %r13
    5724:	41 5e                	pop    %r14
    5726:	41 5f                	pop    %r15
    5728:	5d                   	pop    %rbp
    5729:	c3                   	ret
    572a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5730:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5735:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
    573c:	4c 89 e6             	mov    %r12,%rsi
    573f:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5744:	66 89 95 c4 fb ff ff 	mov    %dx,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    574b:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    574e:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
    5755:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    575f:	e8 ec cc ff ff       	call   2450 <__memcpy_chk@plt>
    5764:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5769:	49 8d 7c 1f 06       	lea    0x6(%r15,%rbx,1),%rdi
    576e:	ba 0b 00 00 00       	mov    $0xb,%edx
    5773:	48 29 d9             	sub    %rbx,%rcx
    5776:	48 8d 35 95 29 00 00 	lea    0x2995(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    577d:	e8 ce cc ff ff       	call   2450 <__memcpy_chk@plt>
    5782:	e9 28 ff ff ff       	jmp    56af <handle_get_method+0x7f>
    5787:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5790:	bf 70 00 00 00       	mov    $0x70,%edi
    5795:	e8 06 cd ff ff       	call   24a0 <malloc@plt>
    579a:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    579d:	48 85 c0             	test   %rax,%rax
    57a0:	0f 84 97 00 00 00    	je     583d <handle_get_method+0x20d>
            req->client_socket = client_socket;
    57a6:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    57aa:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    57b1:	48 8d 50 10          	lea    0x10(%rax),%rdx
    57b5:	4c 89 ff             	mov    %r15,%rdi
            req->iovec_count = 6;
    57b8:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    57bf:	e8 5c f5 ff ff       	call   4d20 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    57c4:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    57cb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    57cf:	4c 89 ff             	mov    %r15,%rdi
    57d2:	e8 79 fa ff ff       	call   5250 <copy_file_contents>
    57d7:	4c 89 fa             	mov    %r15,%rdx
    57da:	bf 01 00 00 00       	mov    $0x1,%edi
    57df:	31 c0                	xor    %eax,%eax
    57e1:	48 8b 8d 60 fb ff ff 	mov    -0x4a0(%rbp),%rcx
    57e8:	48 8d 35 46 29 00 00 	lea    0x2946(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    57ef:	e8 ec cc ff ff       	call   24e0 <__printf_chk@plt>
            add_write_request(req, ring);
    57f4:	4c 89 f6             	mov    %r14,%rsi
    57f7:	48 89 df             	mov    %rbx,%rdi
    57fa:	e8 11 fb ff ff       	call   5310 <add_write_request>
    57ff:	e9 01 ff ff ff       	jmp    5705 <handle_get_method+0xd5>
    5804:	0f 1f 40 00          	nopl   0x0(%rax)
    5808:	4c 89 fa             	mov    %r15,%rdx
    580b:	4c 89 e1             	mov    %r12,%rcx
    580e:	48 8d 35 08 29 00 00 	lea    0x2908(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    5815:	31 c0                	xor    %eax,%eax
    5817:	bf 01 00 00 00       	mov    $0x1,%edi
    581c:	e8 bf cc ff ff       	call   24e0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    5821:	48 8b 3d e8 57 00 00 	mov    0x57e8(%rip),%rdi        # b010 <http_404_content>
    5828:	4c 89 f2             	mov    %r14,%rdx
    582b:	44 89 ee             	mov    %r13d,%esi
    582e:	e8 6d fc ff ff       	call   54a0 <_send_static_string_content>
}
    5833:	e9 cd fe ff ff       	jmp    5705 <handle_get_method+0xd5>
}
    5838:	e8 63 cb ff ff       	call   23a0 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    583d:	48 8b 0d dc 57 00 00 	mov    0x57dc(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5844:	ba 28 00 00 00       	mov    $0x28,%edx
    5849:	be 01 00 00 00       	mov    $0x1,%esi
    584e:	48 8d 3d 6b 2d 00 00 	lea    0x2d6b(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    5855:	e8 16 cd ff ff       	call   2570 <fwrite@plt>
        exit(1);
    585a:	bf 01 00 00 00       	mov    $0x1,%edi
    585f:	e8 ec cc ff ff       	call   2550 <exit@plt>
    5864:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    586f:	90                   	nop

0000000000005870 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5870:	f3 0f 1e fa          	endbr64
    5874:	55                   	push   %rbp
    5875:	48 89 e5             	mov    %rsp,%rbp
    5878:	41 57                	push   %r15
    587a:	41 56                	push   %r14
    587c:	41 55                	push   %r13
    587e:	41 54                	push   %r12
    5880:	53                   	push   %rbx
    5881:	48 83 ec 28          	sub    $0x28,%rsp
    5885:	ff 15 5d 57 00 00    	call   *0x575d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    method = strtok_r(method_buffer, " ", &saveptr);
    588b:	4c 8d 35 1a 28 00 00 	lea    0x281a(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5892:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    589b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    589f:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    58a1:	4c 8d 7d c0          	lea    -0x40(%rbp),%r15
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    58a5:	41 89 f4             	mov    %esi,%r12d
    58a8:	49 89 d5             	mov    %rdx,%r13
    method = strtok_r(method_buffer, " ", &saveptr);
    58ab:	4c 89 f6             	mov    %r14,%rsi
    58ae:	4c 89 fa             	mov    %r15,%rdx
    58b1:	e8 4a cb ff ff       	call   2400 <strtok_r@plt>
    for (; *str; ++str)
    58b6:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    58b9:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    58bc:	84 d2                	test   %dl,%dl
    58be:	88 55 bf             	mov    %dl,-0x41(%rbp)
    58c1:	74 22                	je     58e5 <handle_http_method+0x75>
        *str = (char)tolower(*str);
    58c3:	e8 08 cd ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    58c8:	48 0f be 55 bf       	movsbq -0x41(%rbp),%rdx
    58cd:	48 89 d9             	mov    %rbx,%rcx
    58d0:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    58d3:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    58d7:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    58da:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    58dd:	48 0f be 11          	movsbq (%rcx),%rdx
    58e1:	84 d2                	test   %dl,%dl
    58e3:	75 eb                	jne    58d0 <handle_http_method+0x60>
    path = strtok_r(NULL, " ", &saveptr);
    58e5:	4c 89 fa             	mov    %r15,%rdx
    58e8:	4c 89 f6             	mov    %r14,%rsi
    58eb:	31 ff                	xor    %edi,%edi
    58ed:	e8 0e cb ff ff       	call   2400 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    58f2:	48 8d 35 61 28 00 00 	lea    0x2861(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    58f9:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    58fc:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    58ff:	e8 2c cb ff ff       	call   2430 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5904:	4c 89 ea             	mov    %r13,%rdx
    5907:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    590a:	85 c0                	test   %eax,%eax
    590c:	75 2a                	jne    5938 <handle_http_method+0xc8>
        handle_get_method(path, client_socket, ring);
    590e:	4c 89 f7             	mov    %r14,%rdi
    5911:	e8 1a fd ff ff       	call   5630 <handle_get_method>
}
    5916:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    591a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5923:	75 21                	jne    5946 <handle_http_method+0xd6>
    5925:	48 83 c4 28          	add    $0x28,%rsp
    5929:	5b                   	pop    %rbx
    592a:	41 5c                	pop    %r12
    592c:	41 5d                	pop    %r13
    592e:	41 5e                	pop    %r14
    5930:	41 5f                	pop    %r15
    5932:	5d                   	pop    %rbp
    5933:	c3                   	ret
    5934:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5938:	48 8b 3d d9 56 00 00 	mov    0x56d9(%rip),%rdi        # b018 <unimplemented_content>
    593f:	e8 5c fb ff ff       	call   54a0 <_send_static_string_content>
}
    5944:	eb d0                	jmp    5916 <handle_http_method+0xa6>
    5946:	e8 55 ca ff ff       	call   23a0 <__stack_chk_fail@plt>
    594b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005950 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5950:	f3 0f 1e fa          	endbr64
    5954:	55                   	push   %rbp
    5955:	48 89 e5             	mov    %rsp,%rbp
    5958:	ff 15 8a 56 00 00    	call   *0x568a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    for (int i = 0; i < dest_sz; i++) {
    595e:	85 d2                	test   %edx,%edx
    5960:	7e 36                	jle    5998 <get_line+0x48>
    5962:	48 63 d2             	movslq %edx,%rdx
    5965:	48 83 c7 01          	add    $0x1,%rdi
    5969:	48 01 f2             	add    %rsi,%rdx
    596c:	eb 0f                	jmp    597d <get_line+0x2d>
    596e:	66 90                	xchg   %ax,%ax
    5970:	48 83 c6 01          	add    $0x1,%rsi
    5974:	48 83 c7 01          	add    $0x1,%rdi
    5978:	48 39 d6             	cmp    %rdx,%rsi
    597b:	74 1b                	je     5998 <get_line+0x48>
        dest[i] = src[i];
    597d:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5981:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5983:	3c 0d                	cmp    $0xd,%al
    5985:	75 e9                	jne    5970 <get_line+0x20>
    5987:	80 3f 0a             	cmpb   $0xa,(%rdi)
    598a:	75 e4                	jne    5970 <get_line+0x20>
            return 0;
    598c:	31 c0                	xor    %eax,%eax
            dest[i] = '\0';
    598e:	c6 06 00             	movb   $0x0,(%rsi)
}
    5991:	5d                   	pop    %rbp
    5992:	c3                   	ret
    5993:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return 1;
    5998:	b8 01 00 00 00       	mov    $0x1,%eax
}
    599d:	5d                   	pop    %rbp
    599e:	c3                   	ret
    599f:	90                   	nop

00000000000059a0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    59a0:	f3 0f 1e fa          	endbr64
    59a4:	55                   	push   %rbp
    59a5:	48 89 e5             	mov    %rsp,%rbp
    59a8:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    59af:	ff 15 33 56 00 00    	call   *0x5633(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    59b5:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    59b9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    59c2:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
    59c6:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    59c8:	4c 8d 95 f0 fb ff ff 	lea    -0x410(%rbp),%r10
    59cf:	4c 8d 4d f0          	lea    -0x10(%rbp),%r9
    59d3:	4c 89 d0             	mov    %r10,%rax
    59d6:	eb 15                	jmp    59ed <handle_client_request+0x4d>
    59d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    59e0:	48 83 c0 01          	add    $0x1,%rax
    59e4:	48 83 c1 01          	add    $0x1,%rcx
    59e8:	4c 39 c8             	cmp    %r9,%rax
    59eb:	74 43                	je     5a30 <handle_client_request+0x90>
        dest[i] = src[i];
    59ed:	44 0f b6 01          	movzbl (%rcx),%r8d
    59f1:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    59f4:	41 80 f8 0d          	cmp    $0xd,%r8b
    59f8:	75 e6                	jne    59e0 <handle_client_request+0x40>
    59fa:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    59fe:	75 e0                	jne    59e0 <handle_client_request+0x40>
            dest[i] = '\0';
    5a00:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5a03:	8b 47 08             	mov    0x8(%rdi),%eax
    5a06:	48 89 f2             	mov    %rsi,%rdx
    5a09:	4c 89 d7             	mov    %r10,%rdi
    5a0c:	89 c6                	mov    %eax,%esi
    5a0e:	e8 5d fe ff ff       	call   5870 <handle_http_method>
}
    5a13:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    5a17:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5a20:	75 35                	jne    5a57 <handle_client_request+0xb7>
    5a22:	c9                   	leave
    5a23:	31 c0                	xor    %eax,%eax
    5a25:	c3                   	ret
    5a26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5a30:	48 8b 0d e9 55 00 00 	mov    0x55e9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5a37:	ba 12 00 00 00       	mov    $0x12,%edx
    5a3c:	be 01 00 00 00       	mov    $0x1,%esi
    5a41:	48 8d 3d 16 27 00 00 	lea    0x2716(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5a48:	e8 23 cb ff ff       	call   2570 <fwrite@plt>
        exit(1);
    5a4d:	bf 01 00 00 00       	mov    $0x1,%edi
    5a52:	e8 f9 ca ff ff       	call   2550 <exit@plt>
}
    5a57:	e8 44 c9 ff ff       	call   23a0 <__stack_chk_fail@plt>
    5a5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005a60 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5a60:	f3 0f 1e fa          	endbr64
    5a64:	55                   	push   %rbp
    5a65:	48 89 e5             	mov    %rsp,%rbp
    5a68:	41 54                	push   %r12
    5a6a:	53                   	push   %rbx
    5a6b:	ff 15 77 55 00 00    	call   *0x5577(%rip)        # afe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    5a71:	8b 41 44             	mov    0x44(%rcx),%eax
    5a74:	83 c0 01             	add    $0x1,%eax
    5a77:	48 89 cb             	mov    %rcx,%rbx
	if (ring->flags & IORING_SETUP_SQE128)
    5a7a:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    5a80:	4c 8b 03             	mov    (%rbx),%r8
    5a83:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5a86:	f6 c1 02             	test   $0x2,%cl
    5a89:	74 00                	je     5a8b <add_accept_request+0x2b>
	if (next - head <= sq->ring_entries) {
    5a8b:	41 89 c0             	mov    %eax,%r8d
    5a8e:	45 29 c8             	sub    %r9d,%r8d
    5a91:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    5a95:	0f 82 b8 cb ff ff    	jb     2653 <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5a9b:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a9e:	44 8b 63 44          	mov    0x44(%rbx),%r12d
    5aa2:	44 23 63 58          	and    0x58(%rbx),%r12d
		sq->sqe_tail = next;
    5aa6:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5aa9:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5aac:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5ab0:	41 d3 e4             	shl    %cl,%r12d
    5ab3:	49 c1 e4 06          	shl    $0x6,%r12
    5ab7:	4c 03 63 38          	add    0x38(%rbx),%r12
	sqe->fd = fd;
    5abb:	41 89 7c 24 04       	mov    %edi,0x4(%r12)
  struct Request *req = malloc(sizeof(*req));
    5ac0:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5ac5:	41 c7 04 24 0d 00 00 00 	movl   $0xd,(%r12)
	sqe->off = offset;
    5acd:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
	sqe->addr = (unsigned long) addr;
    5ad2:	49 89 74 24 10       	mov    %rsi,0x10(%r12)
	sqe->buf_index = 0;
    5ad7:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->len = len;
    5ae0:	49 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%r12)
	sqe->addr3 = 0;
    5ae9:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    5aef:	e8 ac c9 ff ff       	call   24a0 <malloc@plt>
  io_uring_submit(ring);
    5af4:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5af7:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    5afd:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
    5b02:	5b                   	pop    %rbx
    5b03:	41 5c                	pop    %r12
    5b05:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5b06:	e9 a5 c8 ff ff       	jmp    23b0 <io_uring_submit@plt>
    5b0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005b10 <io_thread>:
void* io_thread(void *arg) {
    5b10:	f3 0f 1e fa          	endbr64
    5b14:	55                   	push   %rbp
    5b15:	48 89 e5             	mov    %rsp,%rbp
    5b18:	41 57                	push   %r15
    5b1a:	41 56                	push   %r14
    5b1c:	41 55                	push   %r13
    5b1e:	41 54                	push   %r12
    5b20:	53                   	push   %rbx
    5b21:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    5b28:	ff 15 ba 54 00 00    	call   *0x54ba(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5b2e:	31 d2                	xor    %edx,%edx
  struct io_uring ring = *data->ring;
    5b30:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5b39:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    5b3d:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5b41:	48 8d 9d e0 fa ff ff 	lea    -0x520(%rbp),%rbx
void* io_thread(void *arg) {
    5b48:	49 89 fc             	mov    %rdi,%r12
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5b4b:	bf 00 01 00 00       	mov    $0x100,%edi
    5b50:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    5b53:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5b57:	0f 29 8d e0 fa ff ff 	movaps %xmm1,-0x520(%rbp)
    5b5e:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5b63:	0f 29 95 f0 fa ff ff 	movaps %xmm2,-0x510(%rbp)
    5b6a:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5b6f:	0f 29 9d 00 fb ff ff 	movaps %xmm3,-0x500(%rbp)
    5b76:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5b7b:	0f 29 a5 10 fb ff ff 	movaps %xmm4,-0x4f0(%rbp)
    5b82:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5b87:	0f 29 ad 20 fb ff ff 	movaps %xmm5,-0x4e0(%rbp)
    5b8e:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5b93:	0f 29 b5 30 fb ff ff 	movaps %xmm6,-0x4d0(%rbp)
    5b9a:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5b9f:	0f 29 bd 40 fb ff ff 	movaps %xmm7,-0x4c0(%rbp)
    5ba6:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5bab:	0f 29 8d 50 fb ff ff 	movaps %xmm1,-0x4b0(%rbp)
    5bb2:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5bba:	0f 29 95 60 fb ff ff 	movaps %xmm2,-0x4a0(%rbp)
    5bc1:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5bc9:	0f 29 9d 70 fb ff ff 	movaps %xmm3,-0x490(%rbp)
    5bd0:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5bd8:	0f 29 a5 80 fb ff ff 	movaps %xmm4,-0x480(%rbp)
    5bdf:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5be7:	0f 29 ad 90 fb ff ff 	movaps %xmm5,-0x470(%rbp)
    5bee:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5bf6:	0f 29 b5 a0 fb ff ff 	movaps %xmm6,-0x460(%rbp)
    5bfd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5c04:	48 89 85 b0 fb ff ff 	mov    %rax,-0x450(%rbp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5c0b:	e8 70 c8 ff ff       	call   2480 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5c10:	49 8b 7c 24 58       	mov    0x58(%r12),%rdi
    5c15:	31 f6                	xor    %esi,%esi
    5c17:	e8 74 c9 ff ff       	call   2590 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5c1c:	31 d2                	xor    %edx,%edx
    5c1e:	be 01 00 00 00       	mov    $0x1,%esi
    5c23:	bf 02 00 00 00       	mov    $0x2,%edi
    5c28:	e8 c3 c9 ff ff       	call   25f0 <socket@plt>
    5c2d:	89 85 ac fa ff ff    	mov    %eax,-0x554(%rbp)
  if (sock == -1)
    5c33:	83 f8 ff             	cmp    $0xffffffff,%eax
    5c36:	0f 84 59 ca ff ff    	je     2695 <io_thread.cold+0x38>
    5c3c:	89 c7                	mov    %eax,%edi
  if (setsockopt(sock,
    5c3e:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5c44:	ba 02 00 00 00       	mov    $0x2,%edx
    5c49:	be 01 00 00 00       	mov    $0x1,%esi
    5c4e:	48 8d 8d b0 fa ff ff 	lea    -0x550(%rbp),%rcx
  int enable = 1;
    5c55:	c7 85 b0 fa ff ff 01 00 00 00 	movl   $0x1,-0x550(%rbp)
  if (setsockopt(sock,
    5c5f:	e8 fc c6 ff ff       	call   2360 <setsockopt@plt>
    5c64:	85 c0                	test   %eax,%eax
    5c66:	0f 88 fd c9 ff ff    	js     2669 <io_thread.cold+0xc>
  if (bind(sock,
    5c6c:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5c72:	ba 10 00 00 00       	mov    $0x10,%edx
  return __builtin___memset_chk (__dest, __ch, __len,
    5c77:	48 8d b5 c0 fa ff ff 	lea    -0x540(%rbp),%rsi
    5c7e:	48 c7 85 c4 fa ff ff 00 00 00 00 	movq   $0x0,-0x53c(%rbp)
    5c89:	c7 85 cc fa ff ff 00 00 00 00 	movl   $0x0,-0x534(%rbp)
  srv_addr.sin_family = AF_INET;
    5c93:	c7 85 c0 fa ff ff 02 00 18 db 	movl   $0xdb180002,-0x540(%rbp)
  if (bind(sock,
    5c9d:	e8 4e c8 ff ff       	call   24f0 <bind@plt>
    5ca2:	85 c0                	test   %eax,%eax
    5ca4:	0f 88 f7 c9 ff ff    	js     26a1 <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5caa:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5cb0:	be 0a 00 00 00       	mov    $0xa,%esi
    5cb5:	e8 f6 c7 ff ff       	call   24b0 <listen@plt>
    5cba:	85 c0                	test   %eax,%eax
    5cbc:	0f 88 b3 c9 ff ff    	js     2675 <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5cc2:	ba db 18 00 00       	mov    $0x18db,%edx
    5cc7:	48 8d 35 d5 24 00 00 	lea    0x24d5(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5cce:	bf 01 00 00 00       	mov    $0x1,%edi
    5cd3:	31 c0                	xor    %eax,%eax
    5cd5:	e8 06 c8 ff ff       	call   24e0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5cda:	48 8d 85 d0 fa ff ff 	lea    -0x530(%rbp),%rax
    5ce1:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5ce7:	48 89 d9             	mov    %rbx,%rcx
    5cea:	48 8d 95 b4 fa ff ff 	lea    -0x54c(%rbp),%rdx
    5cf1:	48 89 c6             	mov    %rax,%rsi
  socklen_t client_addr_len = sizeof(client_addr);
    5cf4:	c7 85 b4 fa ff ff 10 00 00 00 	movl   $0x10,-0x54c(%rbp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5cfe:	48 89 95 88 fa ff ff 	mov    %rdx,-0x578(%rbp)
    5d05:	48 89 85 90 fa ff ff 	mov    %rax,-0x570(%rbp)
    5d0c:	e8 4f fd ff ff       	call   5a60 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5d11:	bf 01 00 00 00       	mov    $0x1,%edi
    5d16:	be 10 00 00 00       	mov    $0x10,%esi
    5d1b:	e8 00 c7 ff ff       	call   2420 <calloc@plt>
    void *buf = malloc(size);
    5d20:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5d25:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    5d28:	e8 73 c7 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    5d2d:	48 85 c0             	test   %rax,%rax
    5d30:	0f 84 cf 04 00 00    	je     6205 <io_thread+0x6f5>
  iov->iov_base = zh_malloc(10);
    5d36:	49 89 06             	mov    %rax,(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    5d39:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5d3f:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
  iov->iov_len = 10;
    5d45:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    5d4d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5d50:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    5d57:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5d59:	f6 c1 02             	test   $0x2,%cl
    5d5c:	0f 85 2e 04 00 00    	jne    6190 <io_thread+0x680>
	if (next - head <= sq->ring_entries) {
    5d62:	89 d0                	mov    %edx,%eax
    5d64:	29 f0                	sub    %esi,%eax
    5d66:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    5d6c:	0f 82 19 c9 ff ff    	jb     268b <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5d72:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d75:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    5d7b:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5d7f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d82:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5d88:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5d8b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5d91:	49 8d 74 24 60       	lea    0x60(%r12),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5d96:	41 8b 54 24 60       	mov    0x60(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d9b:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5d9d:	48 89 b5 98 fa ff ff 	mov    %rsi,-0x568(%rbp)
    5da4:	48 c1 e0 06          	shl    $0x6,%rax
    5da8:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    5daf:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5db5:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5db8:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5dc0:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    5dc4:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5dcc:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5dd4:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5dd8:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5ddc:	e8 cf c5 ff ff       	call   23b0 <io_uring_submit@plt>
  while (data->running == 1) {
    5de1:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5de7:	4c 8d 8d b8 fa ff ff 	lea    -0x548(%rbp),%r9
    5dee:	4c 8d 95 c0 fb ff ff 	lea    -0x440(%rbp),%r10
    5df5:	0f 85 ed 01 00 00    	jne    5fe8 <io_thread+0x4d8>
    5dfb:	4c 89 8d a0 fa ff ff 	mov    %r9,-0x560(%rbp)
    5e02:	4c 89 95 80 fa ff ff 	mov    %r10,-0x580(%rbp)
    5e09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e10:	48 8d 3d a2 23 00 00 	lea    0x23a2(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5e17:	e8 34 c5 ff ff       	call   2350 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5e1c:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5e22:	8b bd 90 fb ff ff    	mov    -0x470(%rbp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5e28:	c1 e9 0b             	shr    $0xb,%ecx
    5e2b:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5e2e:	48 8b 85 50 fb ff ff 	mov    -0x4b0(%rbp),%rax
    5e35:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5e37:	48 8b b5 48 fb ff ff 	mov    -0x4b8(%rbp),%rsi
    5e3e:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5e40:	39 d0                	cmp    %edx,%eax
    5e42:	74 34                	je     5e78 <io_thread+0x368>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5e44:	89 f8                	mov    %edi,%eax
    5e46:	21 d0                	and    %edx,%eax
    5e48:	d3 e0                	shl    %cl,%eax
    5e4a:	48 c1 e0 04          	shl    $0x4,%rax
    5e4e:	48 03 85 78 fb ff ff 	add    -0x488(%rbp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5e55:	f6 85 a9 fb ff ff 01 	testb  $0x1,-0x457(%rbp)
    5e5c:	0f 85 be 01 00 00    	jne    6020 <io_thread+0x510>
    5e62:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5e66:	0f 85 2c 03 00 00    	jne    6198 <io_thread+0x688>
			if (cqe->res < 0)
    5e6c:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5e6f:	83 c2 01             	add    $0x1,%edx
    5e72:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5e74:	85 c0                	test   %eax,%eax
    5e76:	79 b6                	jns    5e2e <io_thread+0x31e>
	*cqe_ptr = cqe;
    5e78:	48 c7 85 b8 fa ff ff 00 00 00 00 	movq   $0x0,-0x548(%rbp)
	return err;
    5e83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5e88:	48 8b b5 a0 fa ff ff 	mov    -0x560(%rbp),%rsi
    5e8f:	45 31 c0             	xor    %r8d,%r8d
    5e92:	31 d2                	xor    %edx,%edx
    5e94:	48 89 df             	mov    %rbx,%rdi
    5e97:	b9 01 00 00 00       	mov    $0x1,%ecx
    5e9c:	e8 2f c6 ff ff       	call   24d0 <__io_uring_get_cqe@plt>
    5ea1:	41 89 c5             	mov    %eax,%r13d
      if (cqe->user_data == 1) {
    5ea4:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    5eab:	48 83 38 01          	cmpq   $0x1,(%rax)
    5eaf:	0f 84 f3 02 00 00    	je     61a8 <io_thread+0x698>
    5eb5:	48 8d 3d 23 23 00 00 	lea    0x2323(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5ebc:	e8 8f c4 ff ff       	call   2350 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5ec1:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    5ec8:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    5ecb:	45 85 ed             	test   %r13d,%r13d
    5ece:	0f 88 89 c7 ff ff    	js     265d <io_thread.cold>
      if (cqe->res < 0) {
    5ed4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5ed7:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
    5eda:	85 c0                	test   %eax,%eax
    5edc:	0f 88 e5 02 00 00    	js     61c7 <io_thread+0x6b7>
      switch (req->event_type) {
    5ee2:	41 83 f8 01          	cmp    $0x1,%r8d
    5ee6:	0f 84 84 01 00 00    	je     6070 <io_thread+0x560>
    5eec:	41 83 f8 02          	cmp    $0x2,%r8d
    5ef0:	0f 84 aa 01 00 00    	je     60a0 <io_thread+0x590>
    5ef6:	45 85 c0             	test   %r8d,%r8d
    5ef9:	0f 85 59 01 00 00    	jne    6058 <io_thread+0x548>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5eff:	48 8b 95 88 fa ff ff 	mov    -0x578(%rbp),%rdx
    5f06:	48 8b b5 90 fa ff ff 	mov    -0x570(%rbp),%rsi
    5f0d:	48 89 d9             	mov    %rbx,%rcx
    5f10:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5f16:	e8 45 fb ff ff       	call   5a60 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5f1b:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    5f22:	48 89 de             	mov    %rbx,%rsi
    5f25:	8b 78 08             	mov    0x8(%rax),%edi
    5f28:	e8 83 f4 ff ff       	call   53b0 <add_read_request>
              free(req);
    5f2d:	4c 89 ff             	mov    %r15,%rdi
    5f30:	e8 eb c3 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5f35:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
	if (cqe)
    5f3c:	48 85 c0             	test   %rax,%rax
    5f3f:	0f 85 13 01 00 00    	jne    6058 <io_thread+0x548>
	unsigned int head, next = sq->sqe_tail + 1;
    5f45:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5f4b:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5f51:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5f54:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    5f5b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5f5d:	f6 c1 02             	test   $0x2,%cl
    5f60:	74 00                	je     5f62 <io_thread+0x452>
	if (next - head <= sq->ring_entries) {
    5f62:	89 d0                	mov    %edx,%eax
    5f64:	29 f0                	sub    %esi,%eax
    5f66:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    5f6c:	0f 82 0f c7 ff ff    	jb     2681 <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5f72:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f75:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    5f7b:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5f7f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f82:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5f88:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5f8b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f91:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5f93:	41 8b 54 24 60       	mov    0x60(%r12),%edx
	sqe->user_data = (unsigned long) data;
    5f98:	48 8b b5 98 fa ff ff 	mov    -0x568(%rbp),%rsi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f9f:	48 c1 e0 06          	shl    $0x6,%rax
    5fa3:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    5faa:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5fb0:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5fb3:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5fbb:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    5fbf:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5fc7:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5fcf:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5fd3:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5fd7:	e8 d4 c3 ff ff       	call   23b0 <io_uring_submit@plt>
  while (data->running == 1) {
    5fdc:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5fe2:	0f 84 28 fe ff ff    	je     5e10 <io_thread+0x300>
    5fe8:	48 8d 3d 29 22 00 00 	lea    0x2229(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5fef:	e8 5c c3 ff ff       	call   2350 <puts@plt>
}
    5ff4:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5ff8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    6001:	0f 85 25 02 00 00    	jne    622c <io_thread+0x71c>
    6007:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    600e:	31 c0                	xor    %eax,%eax
    6010:	5b                   	pop    %rbx
    6011:	41 5c                	pop    %r12
    6013:	41 5d                	pop    %r13
    6015:	41 5e                	pop    %r14
    6017:	41 5f                	pop    %r15
    6019:	5d                   	pop    %rbp
    601a:	c3                   	ret
    601b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    6020:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    6027:	48 85 c0             	test   %rax,%rax
    602a:	0f 84 58 fe ff ff    	je     5e88 <io_thread+0x378>
      if (cqe->user_data == 1) {
    6030:	48 83 38 01          	cmpq   $0x1,(%rax)
    6034:	0f 84 6e 01 00 00    	je     61a8 <io_thread+0x698>
    603a:	48 8d 3d 9e 21 00 00 	lea    0x219e(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    6041:	e8 0a c3 ff ff       	call   2350 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    6046:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    604d:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    6050:	e9 7f fe ff ff       	jmp    5ed4 <io_thread+0x3c4>
    6055:	0f 1f 00             	nopl   (%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6058:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
    605f:	8b 02                	mov    (%rdx),%eax
    6061:	83 c0 01             	add    $0x1,%eax
    6064:	89 02                	mov    %eax,(%rdx)
}
    6066:	e9 da fe ff ff       	jmp    5f45 <io_thread+0x435>
    606b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
    6070:	85 c0                	test   %eax,%eax
    6072:	75 7c                	jne    60f0 <io_thread+0x5e0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6074:	48 8b 0d a5 4f 00 00 	mov    0x4fa5(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    607b:	ba 0f 00 00 00       	mov    $0xf,%edx
    6080:	be 01 00 00 00       	mov    $0x1,%esi
    6085:	48 8d 3d 7c 21 00 00 	lea    0x217c(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    608c:	e8 df c4 ff ff       	call   2570 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    6091:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    6098:	e9 9f fe ff ff       	jmp    5f3c <io_thread+0x42c>
    609d:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    60a0:	41 8b 47 04          	mov    0x4(%r15),%eax
    60a4:	45 31 ed             	xor    %r13d,%r13d
    60a7:	85 c0                	test   %eax,%eax
    60a9:	7e 20                	jle    60cb <io_thread+0x5bb>
    60ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
    60b0:	4c 89 e8             	mov    %r13,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    60b3:	49 83 c5 01          	add    $0x1,%r13
                  free(req->iov[i].iov_base);
    60b7:	48 c1 e0 04          	shl    $0x4,%rax
    60bb:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    60c0:	e8 5b c2 ff ff       	call   2320 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    60c5:	45 39 6f 04          	cmp    %r13d,0x4(%r15)
    60c9:	7f e5                	jg     60b0 <io_thread+0x5a0>
              close(req->client_socket);
    60cb:	41 8b 7f 08          	mov    0x8(%r15),%edi
    60cf:	e8 1c c3 ff ff       	call   23f0 <close@plt>
              free(req);
    60d4:	4c 89 ff             	mov    %r15,%rdi
    60d7:	e8 44 c2 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    60dc:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    60e3:	e9 54 fe ff ff       	jmp    5f3c <io_thread+0x42c>
    60e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    60f0:	49 8b 57 10          	mov    0x10(%r15),%rdx
    60f4:	48 8b 85 80 fa ff ff 	mov    -0x580(%rbp),%rax
    60fb:	48 8d 75 c0          	lea    -0x40(%rbp),%rsi
    60ff:	eb 14                	jmp    6115 <io_thread+0x605>
    6101:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6108:	48 83 c0 01          	add    $0x1,%rax
    610c:	48 83 c2 01          	add    $0x1,%rdx
    6110:	48 39 c6             	cmp    %rax,%rsi
    6113:	74 4b                	je     6160 <io_thread+0x650>
        dest[i] = src[i];
    6115:	0f b6 0a             	movzbl (%rdx),%ecx
    6118:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    611a:	80 f9 0d             	cmp    $0xd,%cl
    611d:	75 e9                	jne    6108 <io_thread+0x5f8>
    611f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    6123:	75 e3                	jne    6108 <io_thread+0x5f8>
            dest[i] = '\0';
    6125:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    6128:	48 8b bd 80 fa ff ff 	mov    -0x580(%rbp),%rdi
    612f:	48 89 da             	mov    %rbx,%rdx
    6132:	41 8b 77 08          	mov    0x8(%r15),%esi
    6136:	e8 35 f7 ff ff       	call   5870 <handle_http_method>
              free(req->iov[0].iov_base);
    613b:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    613f:	e8 dc c1 ff ff       	call   2320 <free@plt>
              free(req);
    6144:	4c 89 ff             	mov    %r15,%rdi
    6147:	e8 d4 c1 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    614c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    6153:	e9 e4 fd ff ff       	jmp    5f3c <io_thread+0x42c>
    6158:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6160:	48 8b 0d b9 4e 00 00 	mov    0x4eb9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6167:	ba 12 00 00 00       	mov    $0x12,%edx
    616c:	be 01 00 00 00       	mov    $0x1,%esi
    6171:	48 8d 3d e6 1f 00 00 	lea    0x1fe6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6178:	e8 f3 c3 ff ff       	call   2570 <fwrite@plt>
        exit(1);
    617d:	bf 01 00 00 00       	mov    $0x1,%edi
    6182:	e8 c9 c3 ff ff       	call   2550 <exit@plt>
    6187:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    6190:	e9 cd fb ff ff       	jmp    5d62 <io_thread+0x252>
    6195:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    6198:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	return err;
    619f:	e9 8c fe ff ff       	jmp    6030 <io_thread+0x520>
    61a4:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    61a8:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    61af:	48 8d 3d 15 20 00 00 	lea    0x2015(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    61b6:	8b 02                	mov    (%rdx),%eax
    61b8:	83 c0 01             	add    $0x1,%eax
    61bb:	89 02                	mov    %eax,(%rdx)
    61bd:	e8 8e c1 ff ff       	call   2350 <puts@plt>
    61c2:	e9 21 fe ff ff       	jmp    5fe8 <io_thread+0x4d8>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    61c7:	f7 d8                	neg    %eax
    61c9:	44 89 85 ac fa ff ff 	mov    %r8d,-0x554(%rbp)
    61d0:	89 c7                	mov    %eax,%edi
    61d2:	e8 d9 c3 ff ff       	call   25b0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    61d7:	48 8b 3d 42 4e 00 00 	mov    0x4e42(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    61de:	be 01 00 00 00       	mov    $0x1,%esi
    61e3:	44 8b 85 ac fa ff ff 	mov    -0x554(%rbp),%r8d
    61ea:	48 89 c1             	mov    %rax,%rcx
    61ed:	48 8d 15 fc 23 00 00 	lea    0x23fc(%rip),%rdx        # 85f0 <_IO_stdin_used+0x5f0>
    61f4:	31 c0                	xor    %eax,%eax
    61f6:	e8 85 c3 ff ff       	call   2580 <__fprintf_chk@plt>
          exit(1);
    61fb:	bf 01 00 00 00       	mov    $0x1,%edi
    6200:	e8 4b c3 ff ff       	call   2550 <exit@plt>
    6205:	48 8b 0d 14 4e 00 00 	mov    0x4e14(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    620c:	ba 28 00 00 00       	mov    $0x28,%edx
    6211:	be 01 00 00 00       	mov    $0x1,%esi
    6216:	48 8d 3d a3 23 00 00 	lea    0x23a3(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    621d:	e8 4e c3 ff ff       	call   2570 <fwrite@plt>
        exit(1);
    6222:	bf 01 00 00 00       	mov    $0x1,%edi
    6227:	e8 24 c3 ff ff       	call   2550 <exit@plt>
}
    622c:	e8 6f c1 ff ff       	call   23a0 <__stack_chk_fail@plt>
    6231:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    623c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006240 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    6240:	f3 0f 1e fa          	endbr64
    6244:	55                   	push   %rbp
    6245:	48 89 e5             	mov    %rsp,%rbp
    6248:	41 57                	push   %r15
    624a:	41 56                	push   %r14
    624c:	41 55                	push   %r13
    624e:	41 54                	push   %r12
    6250:	53                   	push   %rbx
    6251:	48 83 ec 08          	sub    $0x8,%rsp
    6255:	ff 15 8d 4d 00 00    	call   *0x4d8d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    625b:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    6262:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
int barriered_work_ingest(struct BarrierTask *data) {
    6268:	49 89 fd             	mov    %rdi,%r13
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    626b:	85 c9                	test   %ecx,%ecx
    626d:	7e 54                	jle    62c3 <barriered_work_ingest+0x83>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    626f:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6273:	45 31 f6             	xor    %r14d,%r14d
    6276:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6280:	4a 8b 04 f7          	mov    (%rdi,%r14,8),%rax
    6284:	4e 8d 3c f5 00 00 00 00 	lea    0x0(,%r14,8),%r15
    628c:	31 db                	xor    %ebx,%ebx
    628e:	8b 10                	mov    (%rax),%edx
    6290:	85 d2                	test   %edx,%edx
    6292:	7e 26                	jle    62ba <barriered_work_ingest+0x7a>
    6294:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    6298:	49 89 dc             	mov    %rbx,%r12
    629b:	49 c1 e4 08          	shl    $0x8,%r12
    629f:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    62a3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    62aa:	74 2c                	je     62d8 <barriered_work_ingest+0x98>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    62ac:	48 83 c3 01          	add    $0x1,%rbx
    62b0:	39 da                	cmp    %ebx,%edx
    62b2:	7f e4                	jg     6298 <barriered_work_ingest+0x58>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    62b4:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    62ba:	49 83 c6 01          	add    $0x1,%r14
    62be:	44 39 f1             	cmp    %r14d,%ecx
    62c1:	7f bd                	jg     6280 <barriered_work_ingest+0x40>
}
    62c3:	48 83 c4 08          	add    $0x8,%rsp
    62c7:	31 c0                	xor    %eax,%eax
    62c9:	5b                   	pop    %rbx
    62ca:	41 5c                	pop    %r12
    62cc:	41 5d                	pop    %r13
    62ce:	41 5e                	pop    %r14
    62d0:	41 5f                	pop    %r15
    62d2:	5d                   	pop    %rbp
    62d3:	c3                   	ret
    62d4:	0f 1f 40 00          	nopl   0x0(%rax)
        data->ingest_count++;
    62d8:	49 83 85 68 01 00 00 01 	addq   $0x1,0x168(%r13)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    62e0:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    62e7:	bf 04 00 00 00       	mov    $0x4,%edi
    62ec:	48 c1 e6 05          	shl    $0x5,%rsi
    62f0:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    62f7:	48 83 c6 10          	add    $0x10,%rsi
    62fb:	e8 70 c0 ff ff       	call   2370 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6300:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
    6307:	48 8b 40 50          	mov    0x50(%rax),%rax
    630b:	4a 8b 04 38          	mov    (%rax,%r15,1),%rax
    630f:	4c 03 60 08          	add    0x8(%rax),%r12
    6313:	41 8b 84 24 94 00 00 00 	mov    0x94(%r12),%eax
        data->thread->buffers[b]->buffer[x].available = 0;
    631b:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6327:	83 c0 01             	add    $0x1,%eax
    632a:	99                   	cltd
    632b:	41 f7 bc 24 90 00 00 00 	idivl  0x90(%r12)
    6333:	41 89 94 24 94 00 00 00 	mov    %edx,0x94(%r12)
        asm volatile ("sfence" ::: "memory");
    633b:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    633e:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
    6345:	48 83 c3 01          	add    $0x1,%rbx
    6349:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    634d:	4a 8b 04 3f          	mov    (%rdi,%r15,1),%rax
    6351:	8b 10                	mov    (%rax),%edx
    6353:	39 da                	cmp    %ebx,%edx
    6355:	0f 8f 39 ff ff ff    	jg     6294 <barriered_work_ingest+0x54>
    635b:	e9 54 ff ff ff       	jmp    62b4 <barriered_work_ingest+0x74>

0000000000006360 <barriered_thread>:
void* barriered_thread(void *arg) {
    6360:	f3 0f 1e fa          	endbr64
    6364:	55                   	push   %rbp
    6365:	48 89 e5             	mov    %rsp,%rbp
    6368:	41 57                	push   %r15
    636a:	41 56                	push   %r14
    636c:	41 55                	push   %r13
    636e:	41 54                	push   %r12
    6370:	53                   	push   %rbx
    6371:	48 83 ec 08          	sub    $0x8,%rsp
    6375:	ff 15 6d 4c 00 00    	call   *0x4c6d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  int waiting = 0;
    637b:	45 31 e4             	xor    %r12d,%r12d
  int t = 0;
    637e:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
    6381:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    6384:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6388:	0f 85 1c 02 00 00    	jne    65aa <barriered_thread+0x24a>
    if (t >= data->task_count) {
    638e:	8b 43 40             	mov    0x40(%rbx),%eax
    6391:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6398:	41 39 c5             	cmp    %eax,%r13d
    639b:	0f 8d 6f 01 00 00    	jge    6510 <barriered_thread+0x1b0>
    63a1:	49 63 fd             	movslq %r13d,%rdi
    63a4:	48 c1 e7 09          	shl    $0x9,%rdi
    63a8:	49 89 fe             	mov    %rdi,%r14
    63ab:	eb 32                	jmp    63df <barriered_thread+0x7f>
    63ad:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    63b0:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    63b4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    63b8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    63bc:	48 8b 78 38          	mov    0x38(%rax),%rdi
    63c0:	4c 01 f7             	add    %r14,%rdi
    63c3:	e8 78 fe ff ff       	call   6240 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    63c8:	8b 43 40             	mov    0x40(%rbx),%eax
    63cb:	41 83 c5 01          	add    $0x1,%r13d
    63cf:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    63d6:	44 39 e8             	cmp    %r13d,%eax
    63d9:	0f 8e c1 01 00 00    	jle    65a0 <barriered_thread+0x240>
      if (data->tasks[t].available == 1) {
    63df:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    63e3:	4a 8d 34 32          	lea    (%rdx,%r14,1),%rsi
    63e7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    63ee:	75 c0                	jne    63b0 <barriered_thread+0x50>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    63f0:	8b 7b 28             	mov    0x28(%rbx),%edi
          previous = t - 1;
    63f3:	83 e8 01             	sub    $0x1,%eax
    63f6:	41 8d 4d ff          	lea    -0x1(%r13),%ecx
    63fa:	45 85 ed             	test   %r13d,%r13d
    63fd:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6400:	85 ff                	test   %edi,%edi
    6402:	0f 8e d8 01 00 00    	jle    65e0 <barriered_thread+0x280>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6408:	48 63 c8             	movslq %eax,%rcx
    640b:	48 8b 43 18          	mov    0x18(%rbx),%rax
    640f:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    6412:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6415:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    641c:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6423:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    6427:	45 31 ff             	xor    %r15d,%r15d
    642a:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    642e:	66 90                	xchg   %ax,%ax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6430:	48 8b 10             	mov    (%rax),%rdx
    6433:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6437:	49 01 cb             	add    %rcx,%r11
    643a:	4c 89 da             	mov    %r11,%rdx
    643d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6444:	75 04                	jne    644a <barriered_thread+0xea>
            arrived++;
    6446:	41 83 c7 01          	add    $0x1,%r15d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    644a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    6451:	75 04                	jne    6457 <barriered_thread+0xf7>
            prearrive++;
    6453:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6457:	48 83 c0 08          	add    $0x8,%rax
    645b:	48 39 c6             	cmp    %rax,%rsi
    645e:	75 d0                	jne    6430 <barriered_thread+0xd0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    6460:	45 85 d2             	test   %r10d,%r10d
    6463:	0f 84 bf 00 00 00    	je     6528 <barriered_thread+0x1c8>
    6469:	44 39 d7             	cmp    %r10d,%edi
    646c:	0f 84 b6 00 00 00    	je     6528 <barriered_thread+0x1c8>
        if (arrived == 0 || arrived == data->thread_count) {
    6472:	45 85 ff             	test   %r15d,%r15d
    6475:	74 0a                	je     6481 <barriered_thread+0x121>
    6477:	44 39 7b 28          	cmp    %r15d,0x28(%rbx)
    647b:	0f 85 b0 01 00 00    	jne    6631 <barriered_thread+0x2d1>
    6481:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    6485:	4c 01 f2             	add    %r14,%rdx
    6488:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    648f:	45 85 ed             	test   %r13d,%r13d
    6492:	75 14                	jne    64a8 <barriered_thread+0x148>
    6494:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    649b:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    64a2:	0f 8c 18 01 00 00    	jl     65c0 <barriered_thread+0x260>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    64a8:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    64ac:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    64b0:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    64ba:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    64be:	48 8b 78 38          	mov    0x38(%rax),%rdi
    64c2:	4c 01 f7             	add    %r14,%rdi
    64c5:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    64cb:	48 8b 43 38          	mov    0x38(%rbx),%rax
    64cf:	4c 01 f0             	add    %r14,%rax
    64d2:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    64d9:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    64dc:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    64e1:	83 e8 01             	sub    $0x1,%eax
    64e4:	44 39 e8             	cmp    %r13d,%eax
    64e7:	74 57                	je     6540 <barriered_thread+0x1e0>
          asm volatile ("sfence" ::: "memory");
    64e9:	0f ae f8             	sfence
          if (waiting == 0) {
    64ec:	45 85 e4             	test   %r12d,%r12d
    64ef:	74 7f                	je     6570 <barriered_thread+0x210>
        int arrived = 0; 
    64f1:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    64f7:	e9 cc fe ff ff       	jmp    63c8 <barriered_thread+0x68>
  while (data->running == 1) {
    64fc:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6500:	0f 85 a4 00 00 00    	jne    65aa <barriered_thread+0x24a>
    6506:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->cycles++;
    6510:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    6518:	85 c0                	test   %eax,%eax
    651a:	7e e0                	jle    64fc <barriered_thread+0x19c>
    651c:	45 31 ed             	xor    %r13d,%r13d
    651f:	e9 7d fe ff ff       	jmp    63a1 <barriered_thread+0x41>
    6524:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6528:	41 83 fc 01          	cmp    $0x1,%r12d
    652c:	0f 84 be 00 00 00    	je     65f0 <barriered_thread+0x290>
        int arrived = 0; 
    6532:	45 31 e4             	xor    %r12d,%r12d
    6535:	e9 38 ff ff ff       	jmp    6472 <barriered_thread+0x112>
    653a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6540:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6547:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    654e:	7d 99                	jge    64e9 <barriered_thread+0x189>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    6550:	48 c1 e6 04          	shl    $0x4,%rsi
    6554:	bf 04 00 00 00       	mov    $0x4,%edi
    6559:	48 03 73 70          	add    0x70(%rbx),%rsi
    655d:	e8 0e be ff ff       	call   2370 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6562:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    656a:	e9 7a ff ff ff       	jmp    64e9 <barriered_thread+0x189>
    656f:	90                   	nop
            data->task_snapshot[data->task_timestamp_count].task = t;
    6570:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6577:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    657c:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6580:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6587:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    658b:	44 89 6e 20          	mov    %r13d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    658f:	e8 dc bd ff ff       	call   2370 <clock_gettime@plt>
            waiting = 1;
    6594:	e9 58 ff ff ff       	jmp    64f1 <barriered_thread+0x191>
    6599:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    65a0:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    65a4:	0f 84 ee fd ff ff    	je     6398 <barriered_thread+0x38>
}
    65aa:	48 83 c4 08          	add    $0x8,%rsp
    65ae:	31 c0                	xor    %eax,%eax
    65b0:	5b                   	pop    %rbx
    65b1:	41 5c                	pop    %r12
    65b3:	41 5d                	pop    %r13
    65b5:	41 5e                	pop    %r14
    65b7:	41 5f                	pop    %r15
    65b9:	5d                   	pop    %rbp
    65ba:	c3                   	ret
    65bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    65c0:	48 c1 e6 04          	shl    $0x4,%rsi
    65c4:	bf 04 00 00 00       	mov    $0x4,%edi
    65c9:	48 03 73 68          	add    0x68(%rbx),%rsi
    65cd:	e8 9e bd ff ff       	call   2370 <clock_gettime@plt>
          data->tasks[t].available = 0;
    65d2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    65d6:	4c 01 f2             	add    %r14,%rdx
    65d9:	e9 ca fe ff ff       	jmp    64a8 <barriered_thread+0x148>
    65de:	66 90                	xchg   %ax,%ax
          if (waiting == 1) {
    65e0:	41 83 fc 01          	cmp    $0x1,%r12d
    65e4:	0f 85 9b fe ff ff    	jne    6485 <barriered_thread+0x125>
        int arrived = 0; 
    65ea:	45 31 ff             	xor    %r15d,%r15d
    65ed:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    65f0:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    65f7:	bf 04 00 00 00       	mov    $0x4,%edi
    65fc:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6600:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6607:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    660c:	e8 5f bd ff ff       	call   2370 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    6611:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6618:	48 83 c0 01          	add    $0x1,%rax
    661c:	48 99                	cqto
    661e:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    6625:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    662c:	e9 01 ff ff ff       	jmp    6532 <barriered_thread+0x1d2>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    6631:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6635:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6639:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    663d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6641:	4c 01 f7             	add    %r14,%rdi
    6644:	e8 f7 fb ff ff       	call   6240 <barriered_work_ingest>
          break;
    6649:	e9 36 fd ff ff       	jmp    6384 <barriered_thread+0x24>
    664e:	66 90                	xchg   %ax,%ax

0000000000006650 <receive>:
int receive(struct BarrierTask *data) {
    6650:	f3 0f 1e fa          	endbr64
    6654:	55                   	push   %rbp
    6655:	48 89 e5             	mov    %rsp,%rbp
    6658:	41 57                	push   %r15
    665a:	41 56                	push   %r14
    665c:	41 55                	push   %r13
    665e:	41 54                	push   %r12
    6660:	53                   	push   %rbx
    6661:	48 83 ec 08          	sub    $0x8,%rsp
    6665:	ff 15 7d 49 00 00    	call   *0x497d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    666b:	4c 63 af 40 01 00 00 	movslq 0x140(%rdi),%r13
int receive(struct BarrierTask *data) {
    6672:	48 89 fe             	mov    %rdi,%rsi
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6675:	45 85 ed             	test   %r13d,%r13d
    6678:	0f 8e 25 01 00 00    	jle    67a3 <receive+0x153>
    if (n == data->thread->real_thread_index) { continue; }
    667e:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    6685:	31 db                	xor    %ebx,%ebx
    6687:	4d 63 67 08          	movslq 0x8(%r15),%r12
    668b:	4d 89 e6             	mov    %r12,%r14
    668e:	66 90                	xchg   %ax,%ax
    6690:	41 39 de             	cmp    %ebx,%r14d
    6693:	0f 84 fd 00 00 00    	je     6796 <receive+0x146>
    struct Data *me = data->mailboxes[n].lower;
    6699:	48 89 d8             	mov    %rbx,%rax
    669c:	48 c1 e0 06          	shl    $0x6,%rax
    66a0:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    66a7:	48 8b 10             	mov    (%rax),%rdx
    if (me->available_reading == 1) {
    66aa:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    66b0:	83 f8 01             	cmp    $0x1,%eax
    66b3:	74 11                	je     66c6 <receive+0x76>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    66b5:	83 ba 18 03 00 00 02 	cmpl   $0x2,0x318(%rdx)
    66bc:	75 08                	jne    66c6 <receive+0x76>
    66be:	85 c0                	test   %eax,%eax
    66c0:	0f 84 d0 00 00 00    	je     6796 <receive+0x146>
    for (; me->messages_count > 0 ; ) {
    66c6:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    66cd:	48 85 ff             	test   %rdi,%rdi
    66d0:	0f 8e a2 00 00 00    	jle    6778 <receive+0x128>
    66d6:	4c 8b 8e 78 01 00 00 	mov    0x178(%rsi),%r9
    66dd:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    66e4:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
    66e8:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    66eb:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    66ef:	49 01 f9             	add    %rdi,%r9
    66f2:	49 01 f8             	add    %rdi,%r8
    66f5:	48 03 ba 10 03 00 00 	add    0x310(%rdx),%rdi
    66fc:	eb 08                	jmp    6706 <receive+0xb6>
    66fe:	66 90                	xchg   %ax,%ax
    for (; me->messages_count > 0 ; ) {
    6700:	48 83 e8 01          	sub    $0x1,%rax
    6704:	72 72                	jb     6778 <receive+0x128>
      data->sends++;
    6706:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
    6709:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
    6710:	48 29 c1             	sub    %rax,%rcx
    6713:	48 89 8e 78 01 00 00 	mov    %rcx,0x178(%rsi)
      data->n++;
    671a:	4c 89 c1             	mov    %r8,%rcx
    671d:	48 29 c1             	sub    %rax,%rcx
    6720:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
    6727:	48 89 f9             	mov    %rdi,%rcx
    672a:	48 29 c1             	sub    %rax,%rcx
    672d:	48 89 8a 10 03 00 00 	mov    %rcx,0x310(%rdx)
      if (me->messages[x]->group == data->group) {
    6734:	48 63 c8             	movslq %eax,%rcx
    6737:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    673b:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    673f:	75 bf                	jne    6700 <receive+0xb0>
    6741:	4c 39 61 08          	cmp    %r12,0x8(%rcx)
    6745:	75 b9                	jne    6700 <receive+0xb0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    6747:	49 63 47 04          	movslq 0x4(%r15),%rax
    674b:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    674d:	bf 01 00 00 00       	mov    $0x1,%edi
    6752:	ba 01 00 00 00       	mov    $0x1,%edx
    6757:	48 8d 35 ba 1e 00 00 	lea    0x1eba(%rip),%rsi        # 8618 <_IO_stdin_used+0x618>
    675e:	4c 39 e0             	cmp    %r12,%rax
    6761:	0f 94 c1             	sete   %cl
    6764:	31 c0                	xor    %eax,%eax
    6766:	e8 75 bd ff ff       	call   24e0 <__printf_chk@plt>
        exit(1);
    676b:	bf 01 00 00 00       	mov    $0x1,%edi
    6770:	e8 db bd ff ff       	call   2550 <exit@plt>
    6775:	0f 1f 00             	nopl   (%rax)
      me->available_reading = 0;
    6778:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    6782:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
    678c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6796:	48 83 c3 01          	add    $0x1,%rbx
    679a:	49 39 dd             	cmp    %rbx,%r13
    679d:	0f 85 ed fe ff ff    	jne    6690 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    67a3:	0f ae f8             	sfence
}
    67a6:	48 83 c4 08          	add    $0x8,%rsp
    67aa:	31 c0                	xor    %eax,%eax
    67ac:	5b                   	pop    %rbx
    67ad:	41 5c                	pop    %r12
    67af:	41 5d                	pop    %r13
    67b1:	41 5e                	pop    %r14
    67b3:	41 5f                	pop    %r15
    67b5:	5d                   	pop    %rbp
    67b6:	c3                   	ret
    67b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000067c0 <sendm>:
int sendm(struct BarrierTask *data) {
    67c0:	f3 0f 1e fa          	endbr64
    67c4:	55                   	push   %rbp
    67c5:	48 89 e5             	mov    %rsp,%rbp
    67c8:	41 57                	push   %r15
    67ca:	41 56                	push   %r14
    67cc:	41 55                	push   %r13
    67ce:	41 54                	push   %r12
    67d0:	53                   	push   %rbx
    67d1:	48 83 ec 18          	sub    $0x18,%rsp
    67d5:	ff 15 0d 48 00 00    	call   *0x480d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    67db:	48 89 f9             	mov    %rdi,%rcx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    67de:	48 63 bf 40 01 00 00 	movslq 0x140(%rdi),%rdi
    67e5:	85 ff                	test   %edi,%edi
    67e7:	7e 67                	jle    6850 <sendm+0x90>
        if (n == data->thread->real_thread_index) { continue; }
    67e9:	48 8b 81 28 01 00 00 	mov    0x128(%rcx),%rax
    67f0:	44 8b 48 08          	mov    0x8(%rax),%r9d
    67f4:	31 c0                	xor    %eax,%eax
    67f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6800:	41 39 c1             	cmp    %eax,%r9d
    6803:	74 42                	je     6847 <sendm+0x87>
        struct Data *them = data->mailboxes[n].higher;
    6805:	48 89 c2             	mov    %rax,%rdx
    6808:	48 c1 e2 06          	shl    $0x6,%rdx
    680c:	48 03 91 70 01 00 00 	add    0x170(%rcx),%rdx
    6813:	48 8b 52 08          	mov    0x8(%rdx),%rdx
        if (them->messages_count > 0) {
    6817:	48 8b b2 80 00 00 00 	mov    0x80(%rdx),%rsi
    681e:	48 85 f6             	test   %rsi,%rsi
    6821:	7f 24                	jg     6847 <sendm+0x87>
        if (them->available_sending == 1) {
    6823:	44 8b 82 00 01 00 00 	mov    0x100(%rdx),%r8d
    682a:	41 83 f8 01          	cmp    $0x1,%r8d
    682e:	74 0e                	je     683e <sendm+0x7e>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    6830:	83 ba 18 03 00 00 02 	cmpl   $0x2,0x318(%rdx)
    6837:	75 05                	jne    683e <sendm+0x7e>
    6839:	45 85 c0             	test   %r8d,%r8d
    683c:	74 09                	je     6847 <sendm+0x87>
        if (data->sending == 1) {
    683e:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
    6845:	74 21                	je     6868 <sendm+0xa8>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6847:	48 83 c0 01          	add    $0x1,%rax
    684b:	48 39 c7             	cmp    %rax,%rdi
    684e:	75 b0                	jne    6800 <sendm+0x40>
      asm volatile ("sfence" ::: "memory");
    6850:	0f ae f8             	sfence
}
    6853:	48 83 c4 18          	add    $0x18,%rsp
    6857:	31 c0                	xor    %eax,%eax
    6859:	5b                   	pop    %rbx
    685a:	41 5c                	pop    %r12
    685c:	41 5d                	pop    %r13
    685e:	41 5e                	pop    %r14
    6860:	41 5f                	pop    %r15
    6862:	5d                   	pop    %rbp
    6863:	c3                   	ret
    6864:	0f 1f 40 00          	nopl   0x0(%rax)
          for (; them->messages_count < min;) {
    6868:	4c 63 a2 88 00 00 00 	movslq 0x88(%rdx),%r12
    686f:	4c 39 e6             	cmp    %r12,%rsi
    6872:	0f 8d a8 00 00 00    	jge    6920 <sendm+0x160>
    6878:	48 8b 99 08 01 00 00 	mov    0x108(%rcx),%rbx
            them->messages[them->messages_count++] = data->message; 
    687f:	4c 8b 1a             	mov    (%rdx),%r11
    6882:	48 89 5d c8          	mov    %rbx,-0x38(%rbp)
    6886:	48 8b 9a 08 03 00 00 	mov    0x308(%rdx),%rbx
    688d:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    6891:	4c 89 e3             	mov    %r12,%rbx
    6894:	48 29 f3             	sub    %rsi,%rbx
    6897:	4c 8d 43 ff          	lea    -0x1(%rbx),%r8
    689b:	49 83 f8 02          	cmp    $0x2,%r8
    689f:	0f 86 13 01 00 00    	jbe    69b8 <sendm+0x1f8>
    68a5:	4e 8d 14 e5 00 00 00 00 	lea    0x0(,%r12,8),%r10
    68ad:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    68b5:	4f 8d 34 13          	lea    (%r11,%r10,1),%r14
    68b9:	4c 8d b9 88 01 00 00 	lea    0x188(%rcx),%r15
    68c0:	4f 8d 2c 03          	lea    (%r11,%r8,1),%r13
    68c4:	4d 39 f7             	cmp    %r14,%r15
    68c7:	73 7f                	jae    6948 <sendm+0x188>
    68c9:	4c 8d b1 90 01 00 00 	lea    0x190(%rcx),%r14
    68d0:	4d 39 f5             	cmp    %r14,%r13
    68d3:	73 73                	jae    6948 <sendm+0x188>
    68d5:	4d 01 d8             	add    %r11,%r8
    68d8:	4b 8d 34 13          	lea    (%r11,%r10,1),%rsi
    68dc:	0f 1f 40 00          	nopl   0x0(%rax)
    68e0:	4c 8b 91 88 01 00 00 	mov    0x188(%rcx),%r10
          for (; them->messages_count < min;) {
    68e7:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    68eb:	4d 89 50 f8          	mov    %r10,-0x8(%r8)
          for (; them->messages_count < min;) {
    68ef:	4c 39 c6             	cmp    %r8,%rsi
    68f2:	75 ec                	jne    68e0 <sendm+0x120>
    68f4:	0f 1f 40 00          	nopl   0x0(%rax)
    68f8:	48 8b 75 c8          	mov    -0x38(%rbp),%rsi
    68fc:	48 01 de             	add    %rbx,%rsi
    68ff:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
    6906:	48 8b 75 c0          	mov    -0x40(%rbp),%rsi
    690a:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
    6911:	48 01 de             	add    %rbx,%rsi
    6914:	48 89 b2 08 03 00 00 	mov    %rsi,0x308(%rdx)
    691b:	4f 89 54 e3 f8       	mov    %r10,-0x8(%r11,%r12,8)
          them->available_sending = 0;
    6920:	c7 82 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdx)
          them->available_reading = 1;
    692a:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
          them->available_receiving = 1;
    6934:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
    693e:	e9 04 ff ff ff       	jmp    6847 <sendm+0x87>
    6943:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6948:	49 89 de             	mov    %rbx,%r14
    694b:	4c 8b 91 88 01 00 00 	mov    0x188(%rcx),%r10
    6952:	4d 89 e8             	mov    %r13,%r8
    6955:	49 d1 ee             	shr    %r14
    6958:	49 c1 e6 04          	shl    $0x4,%r14
    695c:	66 49 0f 6e c2       	movq   %r10,%xmm0
    6961:	4f 8d 7c 35 00       	lea    0x0(%r13,%r14,1),%r15
    6966:	41 83 e6 10          	and    $0x10,%r14d
    696a:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    696e:	74 10                	je     6980 <sendm+0x1c0>
            them->messages[them->messages_count++] = data->message; 
    6970:	49 83 c0 10          	add    $0x10,%r8
    6974:	41 0f 11 45 00       	movups %xmm0,0x0(%r13)
          for (; them->messages_count < min;) {
    6979:	4d 39 f8             	cmp    %r15,%r8
    697c:	74 14                	je     6992 <sendm+0x1d2>
    697e:	66 90                	xchg   %ax,%ax
            them->messages[them->messages_count++] = data->message; 
    6980:	41 0f 11 00          	movups %xmm0,(%r8)
    6984:	49 83 c0 20          	add    $0x20,%r8
    6988:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    698d:	4d 39 f8             	cmp    %r15,%r8
    6990:	75 ee                	jne    6980 <sendm+0x1c0>
    6992:	49 89 d8             	mov    %rbx,%r8
    6995:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6999:	4c 01 c6             	add    %r8,%rsi
    699c:	f6 c3 01             	test   $0x1,%bl
    699f:	0f 84 53 ff ff ff    	je     68f8 <sendm+0x138>
            them->messages[them->messages_count++] = data->message; 
    69a5:	4c 8b 91 88 01 00 00 	mov    0x188(%rcx),%r10
    69ac:	4d 89 14 f3          	mov    %r10,(%r11,%rsi,8)
          for (; them->messages_count < min;) {
    69b0:	e9 43 ff ff ff       	jmp    68f8 <sendm+0x138>
    69b5:	0f 1f 00             	nopl   (%rax)
    69b8:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    69c0:	4e 8d 14 e5 00 00 00 00 	lea    0x0(,%r12,8),%r10
    69c8:	e9 08 ff ff ff       	jmp    68d5 <sendm+0x115>
    69cd:	0f 1f 00             	nopl   (%rax)

00000000000069d0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    69d0:	f3 0f 1e fa          	endbr64
    69d4:	55                   	push   %rbp
    69d5:	48 89 e5             	mov    %rsp,%rbp
    69d8:	41 57                	push   %r15
    69da:	41 56                	push   %r14
    69dc:	41 55                	push   %r13
    69de:	41 54                	push   %r12
    69e0:	53                   	push   %rbx
    69e1:	48 83 ec 68          	sub    $0x68,%rsp
    69e5:	ff 15 fd 45 00 00    	call   *0x45fd(%rip)        # afe8 <mcount@GLIBC_2.2.5>
        int t = data->task_index;
    69eb:	8b 47 04             	mov    0x4(%rdi),%eax
int barriered_work(struct BarrierTask *data) {
    69ee:	49 89 fc             	mov    %rdi,%r12
        int t = data->task_index;
    69f1:	89 45 ac             	mov    %eax,-0x54(%rbp)
  if (data->thread_index == data->task_index) {
    69f4:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    69fa:	74 69                	je     6a65 <barriered_work+0x95>
    receive(data);
    69fc:	e8 4f fc ff ff       	call   6650 <receive>
    while (data->scheduled == 1) {
    6a01:	41 83 bc 24 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r12)
    6a0a:	75 1b                	jne    6a27 <barriered_work+0x57>
    6a0c:	0f 1f 40 00          	nopl   0x0(%rax)
      data->n++;
    6a10:	49 83 84 24 08 01 00 00 01 	addq   $0x1,0x108(%r12)
      asm volatile ("sfence" ::: "memory");
    6a19:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6a1c:	41 83 bc 24 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r12)
    6a25:	74 e9                	je     6a10 <barriered_work+0x40>
    sendm(data);
    6a27:	4c 89 e7             	mov    %r12,%rdi
    6a2a:	e8 91 fd ff ff       	call   67c0 <sendm>
  if (t == data->thread_count - 1) {
    6a2f:	41 8b 84 24 34 01 00 00 	mov    0x134(%r12),%eax
    6a37:	8b 7d ac             	mov    -0x54(%rbp),%edi
    6a3a:	83 e8 01             	sub    $0x1,%eax
    6a3d:	39 f8                	cmp    %edi,%eax
    6a3f:	0f 84 e6 04 00 00    	je     6f2b <barriered_work+0x55b>
  data->swap = 0;
    6a45:	41 c7 84 24 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%r12)
  asm volatile ("sfence" ::: "memory");
    6a51:	0f ae f8             	sfence
}
    6a54:	48 83 c4 68          	add    $0x68,%rsp
    6a58:	31 c0                	xor    %eax,%eax
    6a5a:	5b                   	pop    %rbx
    6a5b:	41 5c                	pop    %r12
    6a5d:	41 5d                	pop    %r13
    6a5f:	41 5e                	pop    %r14
    6a61:	41 5f                	pop    %r15
    6a63:	5d                   	pop    %rbp
    6a64:	c3                   	ret
    receive(data);
    6a65:	e8 e6 fb ff ff       	call   6650 <receive>
        if (data->thread->real_thread_index == 0) {
    6a6a:	4d 8b bc 24 28 01 00 00 	mov    0x128(%r12),%r15
    6a72:	45 8b 5f 08          	mov    0x8(%r15),%r11d
    6a76:	45 85 db             	test   %r11d,%r11d
    6a79:	0f 85 5e 02 00 00    	jne    6cdd <barriered_work+0x30d>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6a7f:	41 8b b4 24 40 01 00 00 	mov    0x140(%r12),%esi
    6a87:	85 f6                	test   %esi,%esi
    6a89:	0f 8e 4e 02 00 00    	jle    6cdd <barriered_work+0x30d>
              int next_task = abs((t + 1) % (data->thread_count));
    6a8f:	49 63 84 24 34 01 00 00 	movslq 0x134(%r12),%rax
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6a97:	45 31 ed             	xor    %r13d,%r13d
    6a9a:	4d 89 e0             	mov    %r12,%r8
    6a9d:	31 db                	xor    %ebx,%ebx
    6a9f:	4c 63 55 ac          	movslq -0x54(%rbp),%r10
    6aa3:	4c 89 6d c0          	mov    %r13,-0x40(%rbp)
    6aa7:	4c 63 f6             	movslq %esi,%r14
              int next_task = abs((t + 1) % (data->thread_count));
    6aaa:	89 45 84             	mov    %eax,-0x7c(%rbp)
    6aad:	48 c1 e0 09          	shl    $0x9,%rax
    6ab1:	48 8d b8 98 01 00 00 	lea    0x198(%rax),%rdi
    6ab8:	48 05 70 01 00 00    	add    $0x170,%rax
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6abe:	49 c1 e2 09          	shl    $0x9,%r10
    6ac2:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)
    6ac9:	49 89 fc             	mov    %rdi,%r12
    6acc:	0f 1f 40 00          	nopl   0x0(%rax)
    6ad0:	31 c9                	xor    %ecx,%ecx
    6ad2:	4d 89 e5             	mov    %r12,%r13
    6ad5:	89 75 b8             	mov    %esi,-0x48(%rbp)
    6ad8:	31 ff                	xor    %edi,%edi
    6ada:	48 89 4d c8          	mov    %rcx,-0x38(%rbp)
    6ade:	4d 89 c4             	mov    %r8,%r12
    6ae1:	eb 1e                	jmp    6b01 <barriered_work+0x131>
    6ae3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6ae8:	48 83 45 c8 01       	addq   $0x1,-0x38(%rbp)
    6aed:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    6af1:	48 81 c7 d8 00 00 00 	add    $0xd8,%rdi
    6af8:	49 39 c6             	cmp    %rax,%r14
    6afb:	0f 84 b7 01 00 00    	je     6cb8 <barriered_work+0x2e8>
              if (y == b) { continue; }
    6b01:	8b 45 c8             	mov    -0x38(%rbp),%eax
    6b04:	41 39 c3             	cmp    %eax,%r11d
    6b07:	74 df                	je     6ae8 <barriered_work+0x118>
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6b09:	49 8b 57 20          	mov    0x20(%r15),%rdx
    6b0d:	48 8b 74 1a 38       	mov    0x38(%rdx,%rbx,1),%rsi
    6b12:	4a 8d 04 16          	lea    (%rsi,%r10,1),%rax
    6b16:	44 8b 80 98 01 00 00 	mov    0x198(%rax),%r8d
    6b1d:	45 85 c0             	test   %r8d,%r8d
    6b20:	75 c6                	jne    6ae8 <barriered_work+0x118>
    6b22:	4c 8b 44 3a 38       	mov    0x38(%rdx,%rdi,1),%r8
    6b27:	4b 8d 14 10          	lea    (%r8,%r10,1),%rdx
    6b2b:	44 8b 8a 98 01 00 00 	mov    0x198(%rdx),%r9d
    6b32:	45 85 c9             	test   %r9d,%r9d
    6b35:	75 b1                	jne    6ae8 <barriered_work+0x118>
    6b37:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    6b3e:	48 8b 4d c0          	mov    -0x40(%rbp),%rcx
    6b42:	83 7c 0a 38 02       	cmpl   $0x2,0x38(%rdx,%rcx,1)
    6b47:	75 9f                	jne    6ae8 <barriered_work+0x118>
    6b49:	48 8b 4d c8          	mov    -0x38(%rbp),%rcx
    6b4d:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6b54:	48 c1 e1 06          	shl    $0x6,%rcx
    6b58:	83 7c 08 38 02       	cmpl   $0x2,0x38(%rax,%rcx,1)
    6b5d:	48 89 4d b0          	mov    %rcx,-0x50(%rbp)
    6b61:	75 85                	jne    6ae8 <barriered_work+0x118>
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6b63:	8b 45 84             	mov    -0x7c(%rbp),%eax
    6b66:	85 c0                	test   %eax,%eax
    6b68:	0f 8e 7a ff ff ff    	jle    6ae8 <barriered_work+0x118>
    6b6e:	4c 89 7d a0          	mov    %r15,-0x60(%rbp)
    6b72:	b9 70 01 00 00       	mov    $0x170,%ecx
    6b77:	4c 89 55 98          	mov    %r10,-0x68(%rbp)
    6b7b:	44 89 5d a8          	mov    %r11d,-0x58(%rbp)
    6b7f:	4c 8b 5d b0          	mov    -0x50(%rbp),%r11
    6b83:	48 89 5d 90          	mov    %rbx,-0x70(%rbp)
    6b87:	48 8b 5d c0          	mov    -0x40(%rbp),%rbx
    6b8b:	48 89 7d 88          	mov    %rdi,-0x78(%rbp)
    6b8f:	89 c7                	mov    %eax,%edi
    6b91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                      int next_task = abs((nn + 1) % data->thread_count);
    6b98:	41 83 c1 01          	add    $0x1,%r9d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6b9c:	4d 8b 14 08          	mov    (%r8,%rcx,1),%r10
                      int next_task = abs((nn + 1) % data->thread_count);
    6ba0:	44 89 c8             	mov    %r9d,%eax
    6ba3:	99                   	cltd
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6ba4:	49 01 da             	add    %rbx,%r10
                      int next_task = abs((nn + 1) % data->thread_count);
    6ba7:	f7 ff                	idiv   %edi
    return mailbox->lower;
    6ba9:	f3 41 0f 6f 0a       	movdqu (%r10),%xmm1
    6bae:	66 0f c6 c9 01       	shufpd $0x1,%xmm1,%xmm1
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6bb3:	48 63 d2             	movslq %edx,%rdx
    6bb6:	48 c1 e2 09          	shl    $0x9,%rdx
    6bba:	48 8b 84 16 70 01 00 00 	mov    0x170(%rsi,%rdx,1),%rax
    6bc2:	4c 01 d8             	add    %r11,%rax
    return mailbox->higher;
    6bc5:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    6bc9:	0f 11 08             	movups %xmm1,(%rax)
    6bcc:	0f 12 d8             	movhlps %xmm0,%xmm3
    6bcf:	66 49 0f 7e c7       	movq   %xmm0,%r15
    return mailbox->lower;
    6bd4:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
    mailbox->lower = data;
    6bd9:	41 0f 11 02          	movups %xmm0,(%r10)
    6bdd:	66 48 0f 7e da       	movq   %xmm3,%rdx
    6be2:	41 ba 98 01 00 00    	mov    $0x198,%r10d
    6be8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
    6bf0:	43 c7 04 10 01 00 00 00 	movl   $0x1,(%r8,%r10,1)
                        data->thread->all_threads[t2].tasks[jj].swap = 1;
    6bf8:	42 c7 04 16 01 00 00 00 	movl   $0x1,(%rsi,%r10,1)
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
    6c00:	49 81 c2 00 02 00 00 	add    $0x200,%r10
    6c07:	4d 39 d5             	cmp    %r10,%r13
    6c0a:	75 e4                	jne    6bf0 <barriered_work+0x220>
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6c0c:	4c 8b 14 0e          	mov    (%rsi,%rcx,1),%r10
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6c10:	48 8b 00             	mov    (%rax),%rax
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    6c13:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6c1e:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6c25:	4f 8b 54 1a 08       	mov    0x8(%r10,%r11,1),%r10
    6c2a:	41 c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r10)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6c35:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6c3f:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6c49:	44 39 cf             	cmp    %r9d,%edi
    6c4c:	0f 85 46 ff ff ff    	jne    6b98 <barriered_work+0x1c8>
    6c52:	4c 8b 55 98          	mov    -0x68(%rbp),%r10
    6c56:	44 8b 5d a8          	mov    -0x58(%rbp),%r11d
    6c5a:	b8 70 01 00 00       	mov    $0x170,%eax
    6c5f:	48 8b 5d 90          	mov    -0x70(%rbp),%rbx
    6c63:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
    6c67:	44 89 5d 98          	mov    %r11d,-0x68(%rbp)
    6c6b:	4d 89 d1             	mov    %r10,%r9
    6c6e:	4c 8b 5d b0          	mov    -0x50(%rbp),%r11
    6c72:	4c 8b 55 c0          	mov    -0x40(%rbp),%r10
    6c76:	4c 8b bd 78 ff ff ff 	mov    -0x88(%rbp),%r15
    6c7d:	0f 1f 00             	nopl   (%rax)
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6c80:	48 8b 0c 06          	mov    (%rsi,%rax,1),%rcx
    6c84:	49 8b 14 00          	mov    (%r8,%rax,1),%rdx
    6c88:	4a 8b 0c 19          	mov    (%rcx,%r11,1),%rcx
    6c8c:	4a 39 0c 12          	cmp    %rcx,(%rdx,%r10,1)
    6c90:	0f 84 08 03 00 00    	je     6f9e <barriered_work+0x5ce>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6c96:	48 05 00 02 00 00    	add    $0x200,%rax
    6c9c:	4c 39 f8             	cmp    %r15,%rax
    6c9f:	75 df                	jne    6c80 <barriered_work+0x2b0>
    6ca1:	4c 8b 7d a0          	mov    -0x60(%rbp),%r15
    6ca5:	44 8b 5d 98          	mov    -0x68(%rbp),%r11d
    6ca9:	4d 89 ca             	mov    %r9,%r10
    6cac:	e9 37 fe ff ff       	jmp    6ae8 <barriered_work+0x118>
    6cb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6cb8:	8b 75 b8             	mov    -0x48(%rbp),%esi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6cbb:	41 83 c3 01          	add    $0x1,%r11d
    6cbf:	4d 89 e0             	mov    %r12,%r8
    6cc2:	48 83 45 c0 40       	addq   $0x40,-0x40(%rbp)
    6cc7:	4d 89 ec             	mov    %r13,%r12
    6cca:	48 81 c3 d8 00 00 00 	add    $0xd8,%rbx
    6cd1:	41 39 f3             	cmp    %esi,%r11d
    6cd4:	0f 85 f6 fd ff ff    	jne    6ad0 <barriered_work+0x100>
    6cda:	4d 89 c4             	mov    %r8,%r12
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6cdd:	41 8b 8f c4 00 00 00 	mov    0xc4(%r15),%ecx
          int k = data->group;
    6ce4:	41 8b 94 24 94 01 00 00 	mov    0x194(%r12),%edx
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6cec:	85 c9                	test   %ecx,%ecx
    6cee:	0f 8e 4c 01 00 00    	jle    6e40 <barriered_work+0x470>
            int y = (k * data->thread->threads_per_group) + d;
    6cf4:	0f af d1             	imul   %ecx,%edx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6cf7:	48 63 45 ac          	movslq -0x54(%rbp),%rax
    6cfb:	4c 63 d1             	movslq %ecx,%r10
    6cfe:	4c 89 65 b0          	mov    %r12,-0x50(%rbp)
              int next_task = abs((t + 1) % (data->thread_count));
    6d02:	45 8b 8c 24 34 01 00 00 	mov    0x134(%r12),%r9d
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6d0a:	48 c1 e0 09          	shl    $0x9,%rax
    6d0e:	48 63 d2             	movslq %edx,%rdx
    6d11:	49 89 c0             	mov    %rax,%r8
    6d14:	48 8d 04 52          	lea    (%rdx,%rdx,2),%rax
    6d18:	49 01 d2             	add    %rdx,%r10
    6d1b:	4c 89 45 b8          	mov    %r8,-0x48(%rbp)
    6d1f:	48 8d 34 c0          	lea    (%rax,%rax,8),%rsi
    6d23:	49 8b 47 20          	mov    0x20(%r15),%rax
    6d27:	49 c1 e2 06          	shl    $0x6,%r10
    6d2b:	4c 8d 3c f0          	lea    (%rax,%rsi,8),%r15
    6d2f:	48 89 d0             	mov    %rdx,%rax
    6d32:	48 c1 e0 06          	shl    $0x6,%rax
    6d36:	4d 89 fe             	mov    %r15,%r14
    6d39:	49 89 c3             	mov    %rax,%r11
    6d3c:	49 89 c0             	mov    %rax,%r8
    6d3f:	90                   	nop
    6d40:	4d 8b 66 38          	mov    0x38(%r14),%r12
    6d44:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    6d48:	4c 89 ff             	mov    %r15,%rdi
    6d4b:	4c 89 c6             	mov    %r8,%rsi
    6d4e:	49 8b 9c 04 70 01 00 00 	mov    0x170(%r12,%rax,1),%rbx
    6d56:	eb 1c                	jmp    6d74 <barriered_work+0x3a4>
    6d58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6d60:	48 83 c6 40          	add    $0x40,%rsi
    6d64:	48 81 c7 d8 00 00 00 	add    $0xd8,%rdi
    6d6b:	49 39 f2             	cmp    %rsi,%r10
    6d6e:	0f 84 b4 00 00 00    	je     6e28 <barriered_work+0x458>
              if (kind == MAILBOX_FRIEND) {
    6d74:	83 7c 33 38 01       	cmpl   $0x1,0x38(%rbx,%rsi,1)
    6d79:	75 e5                	jne    6d60 <barriered_work+0x390>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6d7b:	4c 8b 6f 38          	mov    0x38(%rdi),%r13
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6d7f:	45 85 c9             	test   %r9d,%r9d
    6d82:	7e dc                	jle    6d60 <barriered_work+0x390>
    6d84:	48 89 5d c8          	mov    %rbx,-0x38(%rbp)
    6d88:	49 81 c5 70 01 00 00 	add    $0x170,%r13
    6d8f:	31 c9                	xor    %ecx,%ecx
    6d91:	4c 89 55 c0          	mov    %r10,-0x40(%rbp)
    6d95:	eb 51                	jmp    6de8 <barriered_work+0x418>
    6d97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6da0:	48 63 d2             	movslq %edx,%rdx
    6da3:	48 c1 e2 09          	shl    $0x9,%rdx
    6da7:	49 8b 84 14 70 01 00 00 	mov    0x170(%r12,%rdx,1),%rax
    6daf:	48 01 f0             	add    %rsi,%rax
    return mailbox->lower;
    6db2:	48 8b 10             	mov    (%rax),%rdx
                      if (dest->messages_count != 0) { 
    6db5:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    6dbd:	75 1d                	jne    6ddc <barriered_work+0x40c>
    return mailbox->higher;
    6dbf:	f3 0f 7e 40 08       	movq   0x8(%rax),%xmm0
    6dc4:	66 48 0f 6e d2       	movq   %rdx,%xmm2
    mailbox->lower = data;
    6dc9:	49 8b 52 08          	mov    0x8(%r10),%rdx
    6dcd:	66 0f 6c c2          	punpcklqdq %xmm2,%xmm0
    6dd1:	48 89 10             	mov    %rdx,(%rax)
    6dd4:	41 0f 11 02          	movups %xmm0,(%r10)
    mailbox->higher = data;
    6dd8:	48 89 58 08          	mov    %rbx,0x8(%rax)
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6ddc:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    6de3:	41 39 c9             	cmp    %ecx,%r9d
    6de6:	74 1d                	je     6e05 <barriered_work+0x435>
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6de8:	4d 8b 55 00          	mov    0x0(%r13),%r10
                    int next_task = abs((nn + 1) % (data->thread_count));
    6dec:	83 c1 01             	add    $0x1,%ecx
    6def:	89 c8                	mov    %ecx,%eax
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6df1:	4d 01 da             	add    %r11,%r10
                    int next_task = abs((nn + 1) % (data->thread_count));
    6df4:	99                   	cltd
    6df5:	41 f7 f9             	idiv   %r9d
    return mailbox->lower;
    6df8:	49 8b 1a             	mov    (%r10),%rbx
                      if (source2->messages_count != 0) { 
    6dfb:	48 83 bb 80 00 00 00 00 	cmpq   $0x0,0x80(%rbx)
    6e03:	74 9b                	je     6da0 <barriered_work+0x3d0>
    6e05:	4c 8b 55 c0          	mov    -0x40(%rbp),%r10
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6e09:	48 83 c6 40          	add    $0x40,%rsi
    6e0d:	48 8b 5d c8          	mov    -0x38(%rbp),%rbx
    6e11:	48 81 c7 d8 00 00 00 	add    $0xd8,%rdi
    6e18:	49 39 f2             	cmp    %rsi,%r10
    6e1b:	0f 85 53 ff ff ff    	jne    6d74 <barriered_work+0x3a4>
    6e21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6e28:	49 83 c3 40          	add    $0x40,%r11
    6e2c:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    6e33:	4d 39 da             	cmp    %r11,%r10
    6e36:	0f 85 04 ff ff ff    	jne    6d40 <barriered_work+0x370>
    6e3c:	4c 8b 65 b0          	mov    -0x50(%rbp),%r12
      receive(data);
    6e40:	4c 89 e7             	mov    %r12,%rdi
    6e43:	e8 08 f8 ff ff       	call   6650 <receive>
      asm volatile ("sfence" ::: "memory");
    6e48:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6e4b:	49 8b b4 24 60 01 00 00 	mov    0x160(%r12),%rsi
    6e53:	31 ff                	xor    %edi,%edi
    6e55:	48 c1 e6 05          	shl    $0x5,%rsi
    6e59:	49 03 b4 24 50 01 00 00 	add    0x150(%r12),%rsi
    6e61:	e8 0a b5 ff ff       	call   2370 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6e66:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    while (data->scheduled == 1) {
    6e6e:	41 83 bc 24 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r12)
    int modcount = ++data->thread->protected_state->modcount;
    6e77:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6e7b:	8b 7a 10             	mov    0x10(%rdx),%edi
    6e7e:	8d 5f 01             	lea    0x1(%rdi),%ebx
    6e81:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6e84:	75 63                	jne    6ee9 <barriered_work+0x519>
    6e86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6e90:	49 63 94 24 30 01 00 00 	movslq 0x130(%r12),%rdx
    6e98:	48 8b 40 18          	mov    0x18(%rax),%rax
      data->n++;
    6e9c:	49 83 84 24 08 01 00 00 01 	addq   $0x1,0x108(%r12)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6ea5:	49 63 7c 24 04       	movslq 0x4(%r12),%rdi
    6eaa:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6eae:	48 c1 e7 09          	shl    $0x9,%rdi
    6eb2:	48 03 78 38          	add    0x38(%rax),%rdi
    6eb6:	41 ff 94 24 20 01 00 00 	call   *0x120(%r12)
      asm volatile ("sfence" ::: "memory");
    6ebe:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6ec1:	41 83 bc 24 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r12)
    if (modcount != data->thread->protected_state->modcount) {
    6eca:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    while (data->scheduled == 1) {
    6ed2:	74 bc                	je     6e90 <barriered_work+0x4c0>
    if (modcount != data->thread->protected_state->modcount) {
    6ed4:	48 8b 40 48          	mov    0x48(%rax),%rax
    6ed8:	3b 58 10             	cmp    0x10(%rax),%ebx
    6edb:	74 0c                	je     6ee9 <barriered_work+0x519>
    6edd:	48 8d 3d 62 13 00 00 	lea    0x1362(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6ee4:	e8 67 b4 ff ff       	call   2350 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6ee9:	49 8b b4 24 60 01 00 00 	mov    0x160(%r12),%rsi
    6ef1:	31 ff                	xor    %edi,%edi
    6ef3:	48 c1 e6 05          	shl    $0x5,%rsi
    6ef7:	49 03 b4 24 50 01 00 00 	add    0x150(%r12),%rsi
    6eff:	48 83 c6 10          	add    $0x10,%rsi
    6f03:	e8 68 b4 ff ff       	call   2370 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6f08:	49 8b 84 24 60 01 00 00 	mov    0x160(%r12),%rax
    6f10:	48 83 c0 01          	add    $0x1,%rax
    6f14:	48 99                	cqto
    6f16:	49 f7 bc 24 58 01 00 00 	idivq  0x158(%r12)
    6f1e:	49 89 94 24 60 01 00 00 	mov    %rdx,0x160(%r12)
    6f26:	e9 04 fb ff ff       	jmp    6a2f <barriered_work+0x5f>
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6f2b:	49 63 94 24 48 01 00 00 	movslq 0x148(%r12),%rdx
    6f33:	85 d2                	test   %edx,%edx
    6f35:	0f 8e 0a fb ff ff    	jle    6a45 <barriered_work+0x75>
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6f3b:	49 8b 8c 24 28 01 00 00 	mov    0x128(%r12),%rcx
    6f43:	48 c1 e2 09          	shl    $0x9,%rdx
    6f47:	48 63 41 08          	movslq 0x8(%rcx),%rax
    6f4b:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    6f4f:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    6f53:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    6f57:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    6f5b:	48 8b 40 38          	mov    0x38(%rax),%rax
    6f5f:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    6f63:	80 e6 02             	and    $0x2,%dh
    6f66:	74 18                	je     6f80 <barriered_work+0x5b0>
    6f68:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6f6f:	48 05 00 02 00 00    	add    $0x200,%rax
    6f75:	48 39 c8             	cmp    %rcx,%rax
    6f78:	0f 84 c7 fa ff ff    	je     6a45 <barriered_work+0x75>
    6f7e:	66 90                	xchg   %ax,%ax
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6f80:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
    6f87:	83 80 9c 03 00 00 01 	addl   $0x1,0x39c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6f8e:	48 05 00 04 00 00    	add    $0x400,%rax
    6f94:	48 39 c8             	cmp    %rcx,%rax
    6f97:	75 e7                	jne    6f80 <barriered_work+0x5b0>
    6f99:	e9 a7 fa ff ff       	jmp    6a45 <barriered_work+0x75>
    6f9e:	bf 01 00 00 00       	mov    $0x1,%edi
    6fa3:	48 8d 35 81 12 00 00 	lea    0x1281(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6faa:	31 c0                	xor    %eax,%eax
    6fac:	e8 2f b5 ff ff       	call   24e0 <__printf_chk@plt>
                          exit(1);
    6fb1:	bf 01 00 00 00       	mov    $0x1,%edi
    6fb6:	e8 95 b5 ff ff       	call   2550 <exit@plt>
    6fbb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006fc0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6fc0:	f3 0f 1e fa          	endbr64
    6fc4:	55                   	push   %rbp
    6fc5:	48 89 e5             	mov    %rsp,%rbp
    6fc8:	53                   	push   %rbx
    6fc9:	48 83 ec 08          	sub    $0x8,%rsp
    6fcd:	ff 15 15 40 00 00    	call   *0x4015(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    6fd3:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6fd6:	e8 65 f2 ff ff       	call   6240 <barriered_work_ingest>
  barriered_work(data);
    6fdb:	48 89 df             	mov    %rbx,%rdi
}
    6fde:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    6fe2:	c9                   	leave
  barriered_work(data);
    6fe3:	e9 e8 f9 ff ff       	jmp    69d0 <barriered_work>
    6fe8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000006ff0 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6ff0:	f3 0f 1e fa          	endbr64
    6ff4:	55                   	push   %rbp
    6ff5:	48 89 e5             	mov    %rsp,%rbp
    6ff8:	ff 15 ea 3f 00 00    	call   *0x3fea(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  if (kind == 0) {
    6ffe:	85 f6                	test   %esi,%esi
    7000:	74 1e                	je     7020 <mailboxkind+0x30>
  return NULL;
    7002:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    7004:	83 fe 01             	cmp    $0x1,%esi
    7007:	74 07                	je     7010 <mailboxkind+0x20>
}
    7009:	5d                   	pop    %rbp
    700a:	c3                   	ret
    700b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return mailbox->higher;
    7010:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    7014:	5d                   	pop    %rbp
    7015:	c3                   	ret
    7016:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    return mailbox->lower;
    7020:	48 8b 07             	mov    (%rdi),%rax
}
    7023:	5d                   	pop    %rbp
    7024:	c3                   	ret
    7025:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000007030 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    7030:	f3 0f 1e fa          	endbr64
    7034:	55                   	push   %rbp
    7035:	48 89 e5             	mov    %rsp,%rbp
    7038:	ff 15 aa 3f 00 00    	call   *0x3faa(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  if (kind == 0) {
    703e:	85 d2                	test   %edx,%edx
    7040:	75 0e                	jne    7050 <setmailboxkind+0x20>
    mailbox->lower = data;
    7042:	48 89 37             	mov    %rsi,(%rdi)
}
    7045:	31 c0                	xor    %eax,%eax
    7047:	5d                   	pop    %rbp
    7048:	c3                   	ret
    7049:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (kind == 1) {
    7050:	83 fa 01             	cmp    $0x1,%edx
    7053:	74 13                	je     7068 <setmailboxkind+0x38>
  if (kind == 2) {
    7055:	83 fa 02             	cmp    $0x2,%edx
    7058:	75 16                	jne    7070 <setmailboxkind+0x40>
}
    705a:	31 c0                	xor    %eax,%eax
    mailbox->pending_lower = data;
    705c:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
    7060:	5d                   	pop    %rbp
    7061:	c3                   	ret
    7062:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    7068:	31 c0                	xor    %eax,%eax
    mailbox->higher = data;
    706a:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    706e:	5d                   	pop    %rbp
    706f:	c3                   	ret
  if (kind == 3) {
    7070:	83 fa 03             	cmp    $0x3,%edx
    7073:	75 d0                	jne    7045 <setmailboxkind+0x15>
}
    7075:	31 c0                	xor    %eax,%eax
    mailbox->pending_higher = data;
    7077:	48 89 77 18          	mov    %rsi,0x18(%rdi)
}
    707b:	5d                   	pop    %rbp
    707c:	c3                   	ret
    707d:	0f 1f 00             	nopl   (%rax)

0000000000007080 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    7080:	f3 0f 1e fa          	endbr64
    7084:	55                   	push   %rbp
    7085:	48 89 e5             	mov    %rsp,%rbp
    7088:	ff 15 5a 3f 00 00    	call   *0x3f5a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    708e:	31 c0                	xor    %eax,%eax
    7090:	5d                   	pop    %rbp
    7091:	c3                   	ret
    7092:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    709d:	0f 1f 00             	nopl   (%rax)

00000000000070a0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    70a0:	f3 0f 1e fa          	endbr64
    70a4:	55                   	push   %rbp
    70a5:	48 89 e5             	mov    %rsp,%rbp
    70a8:	ff 15 3a 3f 00 00    	call   *0x3f3a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    70ae:	31 c0                	xor    %eax,%eax
    70b0:	5d                   	pop    %rbp
    70b1:	c3                   	ret
    70b2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    70bd:	0f 1f 00             	nopl   (%rax)

00000000000070c0 <after>:
int after(struct timespec left, struct timespec right) {
    70c0:	f3 0f 1e fa          	endbr64
    70c4:	55                   	push   %rbp
    70c5:	48 89 e5             	mov    %rsp,%rbp
    70c8:	ff 15 1a 3f 00 00    	call   *0x3f1a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  return left.tv_sec > right.tv_sec &&
    70ce:	31 c0                	xor    %eax,%eax
    70d0:	48 39 d7             	cmp    %rdx,%rdi
    70d3:	7e 08                	jle    70dd <after+0x1d>
    70d5:	31 c0                	xor    %eax,%eax
    70d7:	48 39 ce             	cmp    %rcx,%rsi
    70da:	0f 9f c0             	setg   %al
}
    70dd:	5d                   	pop    %rbp
    70de:	c3                   	ret
    70df:	90                   	nop

00000000000070e0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    70e0:	f3 0f 1e fa          	endbr64
    70e4:	55                   	push   %rbp
    70e5:	48 89 e5             	mov    %rsp,%rbp
    70e8:	ff 15 fa 3e 00 00    	call   *0x3efa(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  return 0;
    70ee:	31 c0                	xor    %eax,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    70f0:	4c 8b 5d 10          	mov    0x10(%rbp),%r11
    70f4:	4c 8b 55 18          	mov    0x18(%rbp),%r10
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    70f8:	48 39 d7             	cmp    %rdx,%rdi
    70fb:	7f 18                	jg     7115 <within+0x35>
    70fd:	4d 39 d8             	cmp    %r11,%r8
    7100:	0f 9e c2             	setle  %dl
    7103:	48 39 ce             	cmp    %rcx,%rsi
    7106:	0f 9e c0             	setle  %al
    7109:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    710b:	31 c0                	xor    %eax,%eax
    710d:	4d 39 d1             	cmp    %r10,%r9
    7110:	0f 9e c0             	setle  %al
    7113:	21 d0                	and    %edx,%eax
}
    7115:	5d                   	pop    %rbp
    7116:	c3                   	ret
    7117:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007120 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    7120:	f3 0f 1e fa          	endbr64
    7124:	55                   	push   %rbp
    7125:	48 89 e5             	mov    %rsp,%rbp
    7128:	ff 15 ba 3e 00 00    	call   *0x3eba(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    712e:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    7132:	48 8b 75 30          	mov    0x30(%rbp),%rsi
    7136:	4c 8b 4d 20          	mov    0x20(%rbp),%r9
    713a:	4c 8b 55 28          	mov    0x28(%rbp),%r10
    713e:	4c 8b 45 40          	mov    0x40(%rbp),%r8
    7142:	4c 8b 5d 48          	mov    0x48(%rbp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    7146:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
    714a:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  return left.tv_sec > right.tv_sec &&
    714e:	48 39 fe             	cmp    %rdi,%rsi
    7151:	7d 2d                	jge    7180 <overlap+0x60>
    7153:	48 39 ca             	cmp    %rcx,%rdx
    7156:	7d 60                	jge    71b8 <overlap+0x98>
    7158:	4d 39 da             	cmp    %r11,%r10
    715b:	7d 0a                	jge    7167 <overlap+0x47>
    return 1;
    715d:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    7162:	4d 39 c1             	cmp    %r8,%r9
    7165:	7c 0f                	jl     7176 <overlap+0x56>
  return 0;
    7167:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7169:	4d 39 c1             	cmp    %r8,%r9
    716c:	7f 08                	jg     7176 <overlap+0x56>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    716e:	31 c0                	xor    %eax,%eax
    7170:	4d 39 da             	cmp    %r11,%r10
    7173:	0f 9e c0             	setle  %al
}
    7176:	5d                   	pop    %rbp
    7177:	c3                   	ret
    7178:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7180:	7e 56                	jle    71d8 <overlap+0xb8>
    7182:	48 39 ca             	cmp    %rcx,%rdx
    7185:	7f 39                	jg     71c0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7187:	75 31                	jne    71ba <overlap+0x9a>
    7189:	4d 39 c1             	cmp    %r8,%r9
    718c:	7c 2c                	jl     71ba <overlap+0x9a>
    return 1;
    718e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7193:	4d 39 da             	cmp    %r11,%r10
    7196:	7d de                	jge    7176 <overlap+0x56>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7198:	48 39 ca             	cmp    %rcx,%rdx
}
    719b:	5d                   	pop    %rbp
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    719c:	0f 94 c2             	sete   %dl
    719f:	48 39 fe             	cmp    %rdi,%rsi
    71a2:	0f 94 c0             	sete   %al
    71a5:	21 c2                	and    %eax,%edx
    71a7:	31 c0                	xor    %eax,%eax
    71a9:	4d 39 c1             	cmp    %r8,%r9
    71ac:	0f 94 c0             	sete   %al
    71af:	21 d0                	and    %edx,%eax
}
    71b1:	c3                   	ret
    71b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71b8:	74 ad                	je     7167 <overlap+0x47>
  return 0;
    71ba:	31 c0                	xor    %eax,%eax
}
    71bc:	5d                   	pop    %rbp
    71bd:	c3                   	ret
    71be:	66 90                	xchg   %ax,%ax
  return left.tv_sec > right.tv_sec &&
    71c0:	4d 39 da             	cmp    %r11,%r10
    71c3:	7e c4                	jle    7189 <overlap+0x69>
    return 1;
    71c5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    71ca:	4d 39 c1             	cmp    %r8,%r9
    71cd:	7e ba                	jle    7189 <overlap+0x69>
    71cf:	eb a5                	jmp    7176 <overlap+0x56>
    71d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71d8:	48 39 ca             	cmp    %rcx,%rdx
    71db:	7c 8a                	jl     7167 <overlap+0x47>
    71dd:	4d 39 c1             	cmp    %r8,%r9
    71e0:	7d ac                	jge    718e <overlap+0x6e>
    71e2:	48 39 ca             	cmp    %rcx,%rdx
    71e5:	74 87                	je     716e <overlap+0x4e>
  return 0;
    71e7:	31 c0                	xor    %eax,%eax
    71e9:	eb d1                	jmp    71bc <overlap+0x9c>
    71eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000071f0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    71f0:	f3 0f 1e fa          	endbr64
    71f4:	55                   	push   %rbp
    71f5:	48 89 e5             	mov    %rsp,%rbp
    71f8:	41 57                	push   %r15
    71fa:	41 56                	push   %r14
    71fc:	41 55                	push   %r13
    71fe:	41 54                	push   %r12
    7200:	53                   	push   %rbx
    7201:	48 83 ec 58          	sub    $0x58,%rsp
    7205:	ff 15 dd 3d 00 00    	call   *0x3ddd(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    720b:	41 89 f4             	mov    %esi,%r12d
  for (int x = 0 ; x < thread_count; x++) {
    720e:	85 f6                	test   %esi,%esi
    7210:	0f 8e df 02 00 00    	jle    74f5 <verify+0x305>
    7216:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    721a:	45 31 ff             	xor    %r15d,%r15d
    721d:	48 89 5d b8          	mov    %rbx,-0x48(%rbp)
    for (int z = 0 ; z < thread_count; z++) {
    7221:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    7225:	45 31 ed             	xor    %r13d,%r13d
    7228:	45 89 e6             	mov    %r12d,%r14d
      if (z != x)  {
    722b:	45 39 ef             	cmp    %r13d,%r15d
    722e:	0f 84 27 02 00 00    	je     745b <verify+0x26b>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    7234:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    7238:	8b 50 08             	mov    0x8(%rax),%edx
    723b:	85 d2                	test   %edx,%edx
    723d:	0f 8e 18 02 00 00    	jle    745b <verify+0x26b>
    7243:	48 89 5d 98          	mov    %rbx,-0x68(%rbp)
    7247:	45 31 e4             	xor    %r12d,%r12d
    724a:	44 89 6d 94          	mov    %r13d,-0x6c(%rbp)
    724e:	44 89 75 90          	mov    %r14d,-0x70(%rbp)
    7252:	4d 89 e6             	mov    %r12,%r14
    7255:	44 89 fa             	mov    %r15d,%edx
    7258:	48 8d 35 f7 0f 00 00 	lea    0xff7(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    725f:	bf 01 00 00 00       	mov    $0x1,%edi
    7264:	31 c0                	xor    %eax,%eax
    7266:	e8 75 b2 ff ff       	call   24e0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    726b:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    726f:	8b 40 08             	mov    0x8(%rax),%eax
    7272:	85 c0                	test   %eax,%eax
    7274:	0f 8e c3 01 00 00    	jle    743d <verify+0x24d>
    727a:	4c 89 f0             	mov    %r14,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    727d:	4c 89 75 88          	mov    %r14,-0x78(%rbp)
    7281:	31 db                	xor    %ebx,%ebx
    7283:	48 c1 e0 09          	shl    $0x9,%rax
    7287:	44 89 7d 84          	mov    %r15d,-0x7c(%rbp)
    728b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    728f:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    7293:	4c 8b 08             	mov    (%rax),%r9
    7296:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    72a0:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    72a4:	4c 8b 7d c8          	mov    -0x38(%rbp),%r15
    72a8:	49 89 de             	mov    %rbx,%r14
    72ab:	bf 01 00 00 00       	mov    $0x1,%edi
    72b0:	49 c1 e6 09          	shl    $0x9,%r14
    72b4:	48 8d 35 b0 0f 00 00 	lea    0xfb0(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    72bb:	49 8b 04 24          	mov    (%r12),%rax
    72bf:	4b 8b 8c 39 60 01 00 00 	mov    0x160(%r9,%r15,1),%rcx
    72c7:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    72cb:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    72d3:	31 c0                	xor    %eax,%eax
    72d5:	e8 06 b2 ff ff       	call   24e0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    72da:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    72de:	4c 8b 08             	mov    (%rax),%r9
    72e1:	4b 83 bc 39 60 01 00 00 00 	cmpq   $0x0,0x160(%r9,%r15,1)
    72ea:	0f 8e 34 01 00 00    	jle    7424 <verify+0x234>
    72f0:	4d 03 34 24          	add    (%r12),%r14
    72f4:	48 89 5d a0          	mov    %rbx,-0x60(%rbp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    72f8:	ba 01 00 00 00       	mov    $0x1,%edx
    72fd:	4d 89 f5             	mov    %r14,%r13
    7300:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7307:	4d 85 f6             	test   %r14,%r14
    730a:	0f 8e 10 01 00 00    	jle    7420 <verify+0x230>
    7310:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    7314:	49 89 d4             	mov    %rdx,%r12
    7317:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    731b:	31 db                	xor    %ebx,%ebx
    731d:	49 c1 e4 05          	shl    $0x5,%r12
    7321:	49 83 ec 20          	sub    $0x20,%r12
    7325:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
    7329:	eb 32                	jmp    735d <verify+0x16d>
    732b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7330:	4c 39 c1             	cmp    %r8,%rcx
    7333:	0f 8d 47 01 00 00    	jge    7480 <verify+0x290>
    7339:	4c 39 d7             	cmp    %r10,%rdi
    733c:	7e 05                	jle    7343 <verify+0x153>
    733e:	49 39 c3             	cmp    %rax,%r11
    7341:	7c 75                	jl     73b8 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7343:	4c 39 d7             	cmp    %r10,%rdi
    7346:	0f 8d 9b 01 00 00    	jge    74e7 <verify+0x2f7>
    734c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7350:	48 83 c3 01          	add    $0x1,%rbx
    7354:	49 39 de             	cmp    %rbx,%r14
    7357:	0f 8e a2 00 00 00    	jle    73ff <verify+0x20f>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    735d:	49 8b 8f 50 01 00 00 	mov    0x150(%r15),%rcx
    7364:	48 89 d8             	mov    %rbx,%rax
    7367:	48 c1 e0 05          	shl    $0x5,%rax
    736b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    7372:	4c 01 e1             	add    %r12,%rcx
    7375:	48 8b 30             	mov    (%rax),%rsi
    7378:	48 8b 78 10          	mov    0x10(%rax),%rdi
    737c:	48 8b 11             	mov    (%rcx),%rdx
    737f:	4c 8b 41 08          	mov    0x8(%rcx),%r8
    7383:	4c 8b 51 10          	mov    0x10(%rcx),%r10
    7387:	4c 8b 59 18          	mov    0x18(%rcx),%r11
    738b:	48 8b 48 08          	mov    0x8(%rax),%rcx
    738f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    7393:	48 39 d6             	cmp    %rdx,%rsi
    7396:	7c 98                	jl     7330 <verify+0x140>
    7398:	0f 8e 32 01 00 00    	jle    74d0 <verify+0x2e0>
    739e:	4c 39 c1             	cmp    %r8,%rcx
    73a1:	0f 8f e9 00 00 00    	jg     7490 <verify+0x2a0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    73a7:	75 a7                	jne    7350 <verify+0x160>
    73a9:	4c 39 d7             	cmp    %r10,%rdi
    73ac:	7f a2                	jg     7350 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    73ae:	49 39 c3             	cmp    %rax,%r11
    73b1:	7c 9d                	jl     7350 <verify+0x160>
    73b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    73b8:	49 89 c1             	mov    %rax,%r9
    73bb:	48 89 f9             	mov    %rdi,%rcx
    73be:	48 8d 35 7b 12 00 00 	lea    0x127b(%rip),%rsi        # 8640 <_IO_stdin_used+0x640>
    73c5:	31 c0                	xor    %eax,%eax
    73c7:	bf 01 00 00 00       	mov    $0x1,%edi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    73cc:	48 83 c3 01          	add    $0x1,%rbx
    73d0:	e8 0b b1 ff ff       	call   24e0 <__printf_chk@plt>
    73d5:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    73d9:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    73dd:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    73e0:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    73e4:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    73eb:	4c 8b 08             	mov    (%rax),%r9
    73ee:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    73f2:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    73f6:	49 39 de             	cmp    %rbx,%r14
    73f9:	0f 8f 5e ff ff ff    	jg     735d <verify+0x16d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    73ff:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    7403:	49 3b 97 60 01 00 00 	cmp    0x160(%r15),%rdx
    740a:	7d 14                	jge    7420 <verify+0x230>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    740c:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7413:	48 83 c2 01          	add    $0x1,%rdx
    7417:	4d 85 f6             	test   %r14,%r14
    741a:	0f 8f f0 fe ff ff    	jg     7310 <verify+0x120>
    7420:	48 8b 5d a0          	mov    -0x60(%rbp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    7424:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    7428:	48 83 c3 01          	add    $0x1,%rbx
    742c:	39 58 08             	cmp    %ebx,0x8(%rax)
    742f:	0f 8f 6b fe ff ff    	jg     72a0 <verify+0xb0>
    7435:	4c 8b 75 88          	mov    -0x78(%rbp),%r14
    7439:	44 8b 7d 84          	mov    -0x7c(%rbp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    743d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    7441:	49 83 c6 01          	add    $0x1,%r14
    7445:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    7449:	0f 8f 06 fe ff ff    	jg     7255 <verify+0x65>
    744f:	48 8b 5d 98          	mov    -0x68(%rbp),%rbx
    7453:	44 8b 6d 94          	mov    -0x6c(%rbp),%r13d
    7457:	44 8b 75 90          	mov    -0x70(%rbp),%r14d
    for (int z = 0 ; z < thread_count; z++) {
    745b:	41 8d 45 01          	lea    0x1(%r13),%eax
    745f:	48 81 45 c0 d8 00 00 00 	addq   $0xd8,-0x40(%rbp)
    7467:	41 39 c6             	cmp    %eax,%r14d
    746a:	0f 84 96 00 00 00    	je     7506 <verify+0x316>
    7470:	41 89 c5             	mov    %eax,%r13d
    7473:	e9 b3 fd ff ff       	jmp    722b <verify+0x3b>
    7478:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7480:	0f 85 ca fe ff ff    	jne    7350 <verify+0x160>
    7486:	e9 b8 fe ff ff       	jmp    7343 <verify+0x153>
    748b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7490:	49 39 c3             	cmp    %rax,%r11
    7493:	7e 09                	jle    749e <verify+0x2ae>
    7495:	4c 39 d7             	cmp    %r10,%rdi
    7498:	0f 8c 1a ff ff ff    	jl     73b8 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    749e:	4c 39 d7             	cmp    %r10,%rdi
    74a1:	0f 8f a9 fe ff ff    	jg     7350 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    74a7:	49 39 c3             	cmp    %rax,%r11
    74aa:	0f 8d 08 ff ff ff    	jge    73b8 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    74b0:	48 39 d6             	cmp    %rdx,%rsi
    74b3:	0f 85 97 fe ff ff    	jne    7350 <verify+0x160>
    74b9:	4c 39 c1             	cmp    %r8,%rcx
    74bc:	0f 85 8e fe ff ff    	jne    7350 <verify+0x160>
    74c2:	4c 39 d7             	cmp    %r10,%rdi
    74c5:	0f 84 ed fe ff ff    	je     73b8 <verify+0x1c8>
    74cb:	e9 80 fe ff ff       	jmp    7350 <verify+0x160>
    74d0:	4c 39 c1             	cmp    %r8,%rcx
    74d3:	0f 8c 6a fe ff ff    	jl     7343 <verify+0x153>
    74d9:	4c 39 d7             	cmp    %r10,%rdi
    74dc:	7e c9                	jle    74a7 <verify+0x2b7>
    74de:	4c 39 c1             	cmp    %r8,%rcx
    74e1:	0f 85 69 fe ff ff    	jne    7350 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    74e7:	49 39 c3             	cmp    %rax,%r11
    74ea:	0f 8f 60 fe ff ff    	jg     7350 <verify+0x160>
    74f0:	e9 c3 fe ff ff       	jmp    73b8 <verify+0x1c8>
}
    74f5:	48 83 c4 58          	add    $0x58,%rsp
    74f9:	31 c0                	xor    %eax,%eax
    74fb:	5b                   	pop    %rbx
    74fc:	41 5c                	pop    %r12
    74fe:	41 5d                	pop    %r13
    7500:	41 5e                	pop    %r14
    7502:	41 5f                	pop    %r15
    7504:	5d                   	pop    %rbp
    7505:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
    7506:	48 81 45 b8 d8 00 00 00 	addq   $0xd8,-0x48(%rbp)
    750e:	45 89 f4             	mov    %r14d,%r12d
    7511:	41 8d 57 01          	lea    0x1(%r15),%edx
    7515:	45 39 ef             	cmp    %r13d,%r15d
    7518:	74 db                	je     74f5 <verify+0x305>
    751a:	41 89 d7             	mov    %edx,%r15d
    751d:	e9 ff fc ff ff       	jmp    7221 <verify+0x31>
    7522:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    752c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000007530 <atexit>:
    7530:	f3 0f 1e fa          	endbr64
    7534:	48 8b 15 cd 3a 00 00 	mov    0x3acd(%rip),%rdx        # b008 <__dso_handle>
    753b:	31 f6                	xor    %esi,%esi
    753d:	e9 fe af ff ff       	jmp    2540 <__cxa_atexit@plt>
    7542:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    754c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000007550 <__stack_chk_fail_local>:
    7550:	f3 0f 1e fa          	endbr64
    7554:	50                   	push   %rax
    7555:	58                   	pop    %rax
    7556:	48 83 ec 08          	sub    $0x8,%rsp
    755a:	e8 41 ae ff ff       	call   23a0 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000007560 <_fini>:
    7560:	f3 0f 1e fa          	endbr64
    7564:	48 83 ec 08          	sub    $0x8,%rsp
    7568:	48 83 c4 08          	add    $0x8,%rsp
    756c:	c3                   	ret
