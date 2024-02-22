
multibarrier-evented4:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8d 05 41 24 00 00 	lea    0x2441(%rip),%rax        # 4450 <__gmon_start__>
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
    26ce:	48 8d 3d 8b 5f 00 00 	lea    0x5f8b(%rip),%rdi        # 8660 <_IO_stdin_used+0x660>
    26d5:	4c 8d 25 a0 5c 00 00 	lea    0x5ca0(%rip),%r12        # 837c <_IO_stdin_used+0x37c>
    26dc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    26e5:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    26e9:	48 8d 05 d0 1e 00 00 	lea    0x1ed0(%rip),%rax        # 45c0 <barriered_reset>
    26f0:	66 48 0f 6e f0       	movq   %rax,%xmm6
    26f5:	0f 16 35 44 85 00 00 	movhps 0x8544(%rip),%xmm6        # ac40 <__do_global_dtors_aux_fini_array_entry+0x8>
    26fc:	0f 29 b5 00 ff ff ff 	movaps %xmm6,-0x100(%rbp)
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
    27fb:	48 8d 35 c6 5e 00 00 	lea    0x5ec6(%rip),%rsi        # 86c8 <_IO_stdin_used+0x6c8>
    2802:	31 c0                	xor    %eax,%eax
    2804:	bf 01 00 00 00       	mov    $0x1,%edi
    2809:	e8 d2 fc ff ff       	call   24e0 <__printf_chk@plt>
    280e:	ba 01 00 00 00       	mov    $0x1,%edx
    2813:	48 8d 35 de 5e 00 00 	lea    0x5ede(%rip),%rsi        # 86f8 <_IO_stdin_used+0x6f8>
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
    2871:	be e0 00 00 00       	mov    $0xe0,%esi
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
    28d0:	41 8d 14 1e          	lea    (%r14,%rbx,1),%edx
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
    2a48:	48 8d 35 d1 5c 00 00 	lea    0x5cd1(%rip),%rsi        # 8720 <_IO_stdin_used+0x720>
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
    2aa4:	0f 84 54 11 00 00    	je     3bfe <main+0x154e>
        other = abs(x - 1) % total_threads;
    2aaa:	41 8d 57 fe          	lea    -0x2(%r15),%edx
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    2aae:	48 8b 75 88          	mov    -0x78(%rbp),%rsi
    2ab2:	48 8d 04 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rax
        other = abs(x - 1) % total_threads;
    2aba:	48 89 d1             	mov    %rdx,%rcx
        my_thread_data[0] = &thread_data[other]; 
    2abd:	48 29 d0             	sub    %rdx,%rax
        my_thread_data[1] = &thread_data[x]; 
    2ac0:	4c 89 ca             	mov    %r9,%rdx
        my_thread_data[0] = &thread_data[other]; 
    2ac3:	48 c1 e0 05          	shl    $0x5,%rax
    2ac7:	48 01 f0             	add    %rsi,%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2aca:	48 8d 73 08          	lea    0x8(%rbx),%rsi
    2ace:	48 89 b5 70 ff ff ff 	mov    %rsi,-0x90(%rbp)
        thread_data[x].protected_state = &protected_state[k];
    2ad5:	48 8b bd f8 fe ff ff 	mov    -0x108(%rbp),%rdi
        thread_data[x].thread_index = 1;
    2adc:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2ae0:	48 8d 35 69 5c 00 00 	lea    0x5c69(%rip),%rsi        # 8750 <_IO_stdin_used+0x750>
    2ae7:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    2aeb:	8b 55 a0             	mov    -0x60(%rbp),%edx
        thread_data[x].protected_state = &protected_state[k];
    2aee:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2af2:	bf 01 00 00 00       	mov    $0x1,%edi
    2af7:	48 89 03             	mov    %rax,(%rbx)
    2afa:	31 c0                	xor    %eax,%eax
    2afc:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    2b00:	89 4d b8             	mov    %ecx,-0x48(%rbp)
    2b03:	e8 d8 f9 ff ff       	call   24e0 <__printf_chk@plt>
      thread_data[x].other = other;
    2b08:	8b 4d b8             	mov    -0x48(%rbp),%ecx
    2b0b:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    2b0f:	31 c0                	xor    %eax,%eax
    2b11:	8b 55 a0             	mov    -0x60(%rbp),%edx
    2b14:	48 8d 35 65 5c 00 00 	lea    0x5c65(%rip),%rsi        # 8780 <_IO_stdin_used+0x780>
    2b1b:	bf 01 00 00 00       	mov    $0x1,%edi
    2b20:	41 89 89 b8 00 00 00 	mov    %ecx,0xb8(%r9)
    2b27:	8b 8d 44 ff ff ff    	mov    -0xbc(%rbp),%ecx
    2b2d:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
    2b31:	e8 aa f9 ff ff       	call   24e0 <__printf_chk@plt>
        if (x < thread_count) {
    2b36:	83 7d a0 01          	cmpl   $0x1,-0x60(%rbp)
    2b3a:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
    2b3e:	0f 87 e5 10 00 00    	ja     3c29 <main+0x1579>
          CPU_SET(curcpu, sendercpu);
    2b44:	48 63 85 44 ff ff ff 	movslq -0xbc(%rbp),%rax
    2b4b:	48 89 c7             	mov    %rax,%rdi
    2b4e:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2b54:	77 13                	ja     2b69 <main+0x4b9>
    2b56:	48 c1 e8 06          	shr    $0x6,%rax
    2b5a:	ba 01 00 00 00       	mov    $0x1,%edx
    2b5f:	89 f9                	mov    %edi,%ecx
    2b61:	48 d3 e2             	shl    %cl,%rdx
    2b64:	49 09 54 c5 00       	or     %rdx,0x0(%r13,%rax,8)
          curcpu += 2;
    2b69:	83 85 44 ff ff ff 02 	addl   $0x2,-0xbc(%rbp)
      thread_data[x].swapmutex = swapmutex;
    2b70:	48 8b 85 e8 fe ff ff 	mov    -0x118(%rbp),%rax
      thread_data[x].threads = my_thread_data;
    2b77:	49 89 59 18          	mov    %rbx,0x18(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b7b:	be 10 00 00 00       	mov    $0x10,%esi
    2b80:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].kind = KERNEL_THREAD;
    2b85:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
            data[0].messages_count = 0;
    2b8c:	44 89 e3             	mov    %r12d,%ebx
      thread_data[x].swapmutex = swapmutex;
    2b8f:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2b96:	48 8b 85 f0 fe ff ff 	mov    -0x110(%rbp),%rax
      thread_data[x].cpu_set = sendercpu;
    2b9d:	4d 89 a9 b0 00 00 00 	mov    %r13,0xb0(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2ba4:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].real_thread_index = x;
    2bab:	8b 45 a0             	mov    -0x60(%rbp),%eax
      thread_data[x].task_count = total_barrier_count;
    2bae:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].real_thread_index = x;
    2bb6:	41 89 41 08          	mov    %eax,0x8(%r9)
      thread_data[x].all_threads = thread_data;
    2bba:	48 8b 45 88          	mov    -0x78(%rbp),%rax
      thread_data[x].task_count = total_barrier_count;
    2bbe:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
      thread_data[x].all_threads = thread_data;
    2bc2:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2bc6:	48 8b 05 13 61 00 00 	mov    0x6113(%rip),%rax        # 8ce0 <_IO_stdin_used+0xce0>
    2bcd:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2bd4:	48 8b 05 0d 61 00 00 	mov    0x610d(%rip),%rax        # 8ce8 <_IO_stdin_used+0xce8>
    2bdb:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2bdf:	e8 3c f8 ff ff       	call   2420 <calloc@plt>
    2be4:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2be8:	be 10 00 00 00       	mov    $0x10,%esi
    2bed:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2bf2:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2bf6:	e8 25 f8 ff ff       	call   2420 <calloc@plt>
    2bfb:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bff:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2c04:	66 0f 6f 3d a4 60 00 00 	movdqa 0x60a4(%rip),%xmm7        # 8cb0 <_IO_stdin_used+0xcb0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c0c:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2c11:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2c15:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c1d:	e8 fe f7 ff ff       	call   2420 <calloc@plt>
    2c22:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c26:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2c2b:	66 0f 6f 35 7d 60 00 00 	movdqa 0x607d(%rip),%xmm6        # 8cb0 <_IO_stdin_used+0xcb0>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c33:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c38:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2c3f:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c47:	e8 d4 f7 ff ff       	call   2420 <calloc@plt>
        thread_data[x].tasks = barriers;
    2c4c:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c50:	4c 89 ff             	mov    %r15,%rdi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2c53:	45 31 ff             	xor    %r15d,%r15d
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c56:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2c59:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c5d:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
    2c62:	48 0f af f8          	imul   %rax,%rdi
            data[0].messages_count = 0;
    2c66:	4c 89 8d 68 ff ff ff 	mov    %r9,-0x98(%rbp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c6d:	48 c1 ef 22          	shr    $0x22,%rdi
    2c71:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2c74:	8b 7d 98             	mov    -0x68(%rbp),%edi
    2c77:	01 c0                	add    %eax,%eax
    2c79:	29 c7                	sub    %eax,%edi
            data[0].messages_count = 0;
    2c7b:	89 bd 3c ff ff ff    	mov    %edi,-0xc4(%rbp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c81:	49 63 c7             	movslq %r15d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c84:	bf 06 00 00 00       	mov    $0x6,%edi
    2c89:	be 80 01 00 00       	mov    $0x180,%esi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c8e:	45 31 e4             	xor    %r12d,%r12d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c91:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)
    2c98:	48 c1 e0 09          	shl    $0x9,%rax
    2c9c:	4c 8d 2c 02          	lea    (%rdx,%rax,1),%r13
    2ca0:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    2ca4:	48 8d 05 c5 18 00 00 	lea    0x18c5(%rip),%rax        # 4570 <do_protected_write>
    2cab:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2cb2:	e8 69 f7 ff ff       	call   2420 <calloc@plt>
    2cb7:	8b bd 60 ff ff ff    	mov    -0xa0(%rbp),%edi
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2cbd:	49 89 85 70 01 00 00 	mov    %rax,0x170(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2cc4:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cc7:	85 ff                	test   %edi,%edi
    2cc9:	0f 84 94 01 00 00    	je     2e63 <main+0x7b3>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2ccf:	8b 45 98             	mov    -0x68(%rbp),%eax
    2cd2:	44 89 7d b8          	mov    %r15d,-0x48(%rbp)
    2cd6:	49 89 cd             	mov    %rcx,%r13
    2cd9:	48 89 8d 30 ff ff ff 	mov    %rcx,-0xd0(%rbp)
    2ce0:	83 e8 02             	sub    $0x2,%eax
    2ce3:	89 85 48 ff ff ff    	mov    %eax,-0xb8(%rbp)
    2ce9:	eb 1a                	jmp    2d05 <main+0x655>
    2ceb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cf0:	41 83 c4 01          	add    $0x1,%r12d
    2cf4:	49 81 c5 80 01 00 00 	add    $0x180,%r13
    2cfb:	41 83 fc 06          	cmp    $0x6,%r12d
    2cff:	0f 84 e6 02 00 00    	je     2feb <main+0x93b>
            int group_of = b / threads_per_group;
    2d05:	45 89 e7             	mov    %r12d,%r15d
    2d08:	31 c0                	xor    %eax,%eax
    2d0a:	44 89 e2             	mov    %r12d,%edx
    2d0d:	bf 01 00 00 00       	mov    $0x1,%edi
    2d12:	41 d1 ff             	sar    %r15d
    2d15:	48 8d 35 a0 56 00 00 	lea    0x56a0(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2d1c:	44 89 f9             	mov    %r15d,%ecx
    2d1f:	e8 bc f7 ff ff       	call   24e0 <__printf_chk@plt>
            if (k == group_of) {
    2d24:	45 39 fe             	cmp    %r15d,%r14d
    2d27:	75 c7                	jne    2cf0 <main+0x640>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d29:	be 08 00 00 00       	mov    $0x8,%esi
    2d2e:	bf 01 00 00 00       	mov    $0x1,%edi
    2d33:	e8 e8 f6 ff ff       	call   2420 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d38:	be 08 00 00 00       	mov    $0x8,%esi
    2d3d:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d42:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d49:	e8 d2 f6 ff ff       	call   2420 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2d4e:	be 80 03 00 00       	mov    $0x380,%esi
    2d53:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d58:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2d5c:	e8 bf f6 ff ff       	call   2420 <calloc@plt>
              data[0].a = x;
    2d61:	8b 7d a0             	mov    -0x60(%rbp),%edi
              data[0].b = y;
    2d64:	8b 75 b8             	mov    -0x48(%rbp),%esi
    2d67:	44 89 e2             	mov    %r12d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    2d6a:	49 89 c1             	mov    %rax,%r9
              data[0].kind = MAILBOX_LOWER;
    2d6d:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].a = x;
    2d77:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].b = y;
    2d7d:	89 b0 20 03 00 00    	mov    %esi,0x320(%rax)
              data[0].c = b;
    2d83:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
              data[0].id = dataid++;
    2d8a:	8d 43 01             	lea    0x1(%rbx),%eax
              data[1].id = dataid++;
    2d8d:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2d94:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2d9b:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    2da2:	8b 85 48 ff ff ff    	mov    -0xb8(%rbp),%eax
              data[0].id = dataid++;
    2da8:	41 89 99 28 03 00 00 	mov    %ebx,0x328(%r9)
              data[1].id = dataid++;
    2daf:	83 c3 02             	add    $0x2,%ebx
              data[1].a = x;
    2db2:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    2db9:	89 c1                	mov    %eax,%ecx
    2dbb:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].b = y;
    2dc0:	41 89 b1 a0 06 00 00 	mov    %esi,0x6a0(%r9)
    2dc7:	48 8d 35 d2 59 00 00 	lea    0x59d2(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
              data[1].kind = MAILBOX_HIGHER;
    2dce:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].c = b;
    2dd9:	45 89 a1 a4 06 00 00 	mov    %r12d,0x6a4(%r9)
              mailboxes[b].lower = &data[0];
    2de0:	4d 89 4d 00          	mov    %r9,0x0(%r13)
              data[0].finished_reading = 1;
    2de4:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    2def:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
    2dfa:	41 89 85 b4 00 00 00 	mov    %eax,0xb4(%r13)
    2e01:	31 c0                	xor    %eax,%eax
              mailboxes[b].pending_lower = NULL;
    2e03:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
              mailboxes[b].pending_higher = NULL;
    2e0e:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2e19:	41 c7 85 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%r13)
              data[1].finished_reading = 1;
    2e24:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    2e28:	e8 b3 f6 ff ff       	call   24e0 <__printf_chk@plt>
              data[0].messages = messages;
    2e2d:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    2e31:	4c 8b 9d 58 ff ff ff 	mov    -0xa8(%rbp),%r11
              data[0].messages_count = 0;
    2e38:	66 0f 6f 35 80 5e 00 00 	movdqa 0x5e80(%rip),%xmm6        # 8cc0 <_IO_stdin_used+0xcc0>
              data[1].messages = messages2;
    2e40:	4c 8b 55 a8          	mov    -0x58(%rbp),%r10
              data[0].messages = messages;
    2e44:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2e47:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2e4e:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2e56:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
    2e5e:	e9 8d fe ff ff       	jmp    2cf0 <main+0x640>
    2e63:	44 89 7d b8          	mov    %r15d,-0x48(%rbp)
    2e67:	49 89 c5             	mov    %rax,%r13
    2e6a:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
    2e71:	eb 1a                	jmp    2e8d <main+0x7dd>
    2e73:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e78:	41 83 c4 01          	add    $0x1,%r12d
    2e7c:	49 81 c5 80 01 00 00 	add    $0x180,%r13
    2e83:	41 83 fc 06          	cmp    $0x6,%r12d
    2e87:	0f 84 82 06 00 00    	je     350f <main+0xe5f>
            int group_of = b / threads_per_group;
    2e8d:	45 89 e7             	mov    %r12d,%r15d
    2e90:	31 c0                	xor    %eax,%eax
    2e92:	44 89 e2             	mov    %r12d,%edx
    2e95:	bf 01 00 00 00       	mov    $0x1,%edi
    2e9a:	41 d1 ff             	sar    %r15d
    2e9d:	48 8d 35 18 55 00 00 	lea    0x5518(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2ea4:	44 89 f9             	mov    %r15d,%ecx
    2ea7:	e8 34 f6 ff ff       	call   24e0 <__printf_chk@plt>
            if (k == group_of) {
    2eac:	45 39 fe             	cmp    %r15d,%r14d
    2eaf:	75 c7                	jne    2e78 <main+0x7c8>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2eb1:	be 08 00 00 00       	mov    $0x8,%esi
    2eb6:	bf 01 00 00 00       	mov    $0x1,%edi
    2ebb:	e8 60 f5 ff ff       	call   2420 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ec0:	be 08 00 00 00       	mov    $0x8,%esi
    2ec5:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2eca:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ed1:	e8 4a f5 ff ff       	call   2420 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2ed6:	be 80 03 00 00       	mov    $0x380,%esi
    2edb:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ee0:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2ee4:	e8 37 f5 ff ff       	call   2420 <calloc@plt>
              data[0].a = x;
    2ee9:	8b 7d a0             	mov    -0x60(%rbp),%edi
              data[0].b = y;
    2eec:	8b 75 b8             	mov    -0x48(%rbp),%esi
    2eef:	44 89 e2             	mov    %r12d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    2ef2:	49 89 c1             	mov    %rax,%r9
              data[0].kind = MAILBOX_LOWER;
    2ef5:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].a = x;
    2eff:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].b = y;
    2f05:	89 b0 20 03 00 00    	mov    %esi,0x320(%rax)
              data[0].c = b;
    2f0b:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
              data[0].id = dataid++;
    2f12:	8d 43 01             	lea    0x1(%rbx),%eax
              data[1].id = dataid++;
    2f15:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2f1c:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2f23:	49 89 85 80 00 00 00 	mov    %rax,0x80(%r13)
    2f2a:	8b 85 3c ff ff ff    	mov    -0xc4(%rbp),%eax
              data[0].id = dataid++;
    2f30:	41 89 99 28 03 00 00 	mov    %ebx,0x328(%r9)
              data[1].id = dataid++;
    2f37:	83 c3 02             	add    $0x2,%ebx
              data[1].a = x;
    2f3a:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    2f41:	89 c1                	mov    %eax,%ecx
    2f43:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].b = y;
    2f48:	41 89 b1 a0 06 00 00 	mov    %esi,0x6a0(%r9)
    2f4f:	48 8d 35 4a 58 00 00 	lea    0x584a(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
              data[1].kind = MAILBOX_HIGHER;
    2f56:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].c = b;
    2f61:	45 89 a1 a4 06 00 00 	mov    %r12d,0x6a4(%r9)
              mailboxes[b].lower = &data[0];
    2f68:	4d 89 4d 00          	mov    %r9,0x0(%r13)
              data[0].finished_reading = 1;
    2f6c:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    2f77:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
    2f82:	41 89 85 b4 00 00 00 	mov    %eax,0xb4(%r13)
    2f89:	31 c0                	xor    %eax,%eax
              mailboxes[b].pending_lower = NULL;
    2f8b:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
              mailboxes[b].pending_higher = NULL;
    2f96:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2fa1:	41 c7 85 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%r13)
              data[1].finished_reading = 1;
    2fac:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    2fb0:	e8 2b f5 ff ff       	call   24e0 <__printf_chk@plt>
              data[0].messages = messages;
    2fb5:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    2fb9:	4c 8b 9d 58 ff ff ff 	mov    -0xa8(%rbp),%r11
              data[0].messages_count = 0;
    2fc0:	66 0f 6f 35 f8 5c 00 00 	movdqa 0x5cf8(%rip),%xmm6        # 8cc0 <_IO_stdin_used+0xcc0>
              data[1].messages = messages2;
    2fc8:	4c 8b 55 a8          	mov    -0x58(%rbp),%r10
              data[0].messages = messages;
    2fcc:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2fcf:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2fd6:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2fde:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
    2fe6:	e9 8d fe ff ff       	jmp    2e78 <main+0x7c8>
    2feb:	44 8b 7d b8          	mov    -0x48(%rbp),%r15d
    2fef:	48 8b 8d 30 ff ff ff 	mov    -0xd0(%rbp),%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ff6:	45 31 ed             	xor    %r13d,%r13d
    2ff9:	44 89 75 b8          	mov    %r14d,-0x48(%rbp)
    2ffd:	41 89 de             	mov    %ebx,%r14d
    3000:	44 89 eb             	mov    %r13d,%ebx
    3003:	49 89 cd             	mov    %rcx,%r13
    3006:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            int group_of = b / threads_per_group;
    3010:	89 d8                	mov    %ebx,%eax
    3012:	d1 f8                	sar    %eax
            if (k == group_of) {
    3014:	39 45 b8             	cmp    %eax,-0x48(%rbp)
    3017:	0f 84 85 01 00 00    	je     31a2 <main+0xaf2>
    301d:	89 da                	mov    %ebx,%edx
    301f:	48 8d 35 a6 53 00 00 	lea    0x53a6(%rip),%rsi        # 83cc <_IO_stdin_used+0x3cc>
    3026:	bf 01 00 00 00       	mov    $0x1,%edi
    302b:	31 c0                	xor    %eax,%eax
    302d:	e8 ae f4 ff ff       	call   24e0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3032:	be 08 00 00 00       	mov    $0x8,%esi
    3037:	bf 01 00 00 00       	mov    $0x1,%edi
    303c:	e8 df f3 ff ff       	call   2420 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3041:	be 08 00 00 00       	mov    $0x8,%esi
    3046:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    304b:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    304f:	e8 cc f3 ff ff       	call   2420 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    3054:	be 80 03 00 00       	mov    $0x380,%esi
    3059:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    305e:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
            struct Data *data = calloc(3, sizeof(struct Data));
    3062:	e8 b9 f3 ff ff       	call   2420 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    3067:	be 80 03 00 00       	mov    $0x380,%esi
    306c:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    3071:	49 89 c4             	mov    %rax,%r12
            struct Data **stack = calloc(3, sizeof(struct Data));
    3074:	e8 a7 f3 ff ff       	call   2420 <calloc@plt>
            data[0].a = x;
    3079:	8b 7d a0             	mov    -0x60(%rbp),%edi
            data[0].id = dataid++;
    307c:	41 8d 76 01          	lea    0x1(%r14),%esi
            data[0].messages = messages;
    3080:	4c 8b 4d a8          	mov    -0x58(%rbp),%r9
            data[1].messages = messages2;
    3084:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
            data[0].messages_count = 0;
    3088:	66 0f 6f 35 30 5c 00 00 	movdqa 0x5c30(%rip),%xmm6        # 8cc0 <_IO_stdin_used+0xcc0>
            data[1].id = dataid++;
    3090:	41 89 b4 24 a8 06 00 00 	mov    %esi,0x6a8(%r12)
            mailboxes[b].higher = &data[1];
    3098:	49 8d b4 24 80 03 00 00 	lea    0x380(%r12),%rsi
            data[0].id = dataid++;
    30a0:	45 89 b4 24 28 03 00 00 	mov    %r14d,0x328(%r12)
            data[1].id = dataid++;
    30a8:	41 83 c6 02          	add    $0x2,%r14d
            data[0].kind = MAILBOX_LOWER;
    30ac:	41 c7 84 24 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r12)
            data[0].a = x;
    30b8:	41 89 bc 24 1c 03 00 00 	mov    %edi,0x31c(%r12)
            data[0].b = y;
    30c0:	45 89 bc 24 20 03 00 00 	mov    %r15d,0x320(%r12)
            data[0].c = b;
    30c8:	41 89 9c 24 24 03 00 00 	mov    %ebx,0x324(%r12)
            data[1].kind = MAILBOX_HIGHER;
    30d0:	41 c7 84 24 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r12)
            data[1].a = x;
    30dc:	41 89 bc 24 9c 06 00 00 	mov    %edi,0x69c(%r12)
            data[1].b = y;
    30e4:	45 89 bc 24 a0 06 00 00 	mov    %r15d,0x6a0(%r12)
            data[1].c = b;
    30ec:	41 89 9c 24 a4 06 00 00 	mov    %ebx,0x6a4(%r12)
            mailboxes[b].lower = &data[0];
    30f4:	4d 89 65 00          	mov    %r12,0x0(%r13)
            mailboxes[b].my_lower = &data[0];
    30f8:	4d 89 a5 a0 00 00 00 	mov    %r12,0xa0(%r13)
            mailboxes[b].higher = &data[1];
    30ff:	49 89 b5 80 00 00 00 	mov    %rsi,0x80(%r13)
            mailboxes[b].pending_lower = NULL;
    3106:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
            mailboxes[b].pending_higher = NULL;
    3111:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
            data[0].finished_reading = 1;
    311c:	41 c7 84 24 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r12)
            data[1].finished_reading = 1;
    3128:	41 c7 84 24 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r12)
            mailboxes[b].my_higher = &data[1];
    3134:	49 89 b5 a8 00 00 00 	mov    %rsi,0xa8(%r13)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    313b:	41 c7 85 b0 00 00 00 02 00 00 00 	movl   $0x2,0xb0(%r13)
            stack[0] = mailboxes[b].lower;
    3146:	4c 89 20             	mov    %r12,(%rax)
            stack[1] = mailboxes[b].higher;
    3149:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    314d:	49 89 85 98 00 00 00 	mov    %rax,0x98(%r13)
            data[0].available_sending = 0;
    3154:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
            data[0].available_receiving = 0;
    3160:	41 c7 84 24 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r12)
            data[0].messages = messages;
    316c:	4d 89 0c 24          	mov    %r9,(%r12)
            data[1].messages = messages2;
    3170:	49 89 94 24 80 03 00 00 	mov    %rdx,0x380(%r12)
            data[1].available_sending = 1;
    3178:	41 c7 84 24 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r12)
            data[1].available_receiving = 0;
    3184:	41 c7 84 24 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r12)
            data[0].messages_count = 0;
    3190:	41 0f 29 b4 24 80 00 00 00 	movaps %xmm6,0x80(%r12)
            data[1].messages_count = 0;
    3199:	41 0f 29 b4 24 00 04 00 00 	movaps %xmm6,0x400(%r12)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    31a2:	83 c3 01             	add    $0x1,%ebx
    31a5:	49 81 c5 80 01 00 00 	add    $0x180,%r13
    31ac:	83 fb 06             	cmp    $0x6,%ebx
    31af:	0f 85 5b fe ff ff    	jne    3010 <main+0x960>
          char *message = malloc(sizeof(char) * 256);
    31b5:	be 01 00 00 00       	mov    $0x1,%esi
    31ba:	bf 00 01 00 00       	mov    $0x100,%edi
    31bf:	44 89 f3             	mov    %r14d,%ebx
    31c2:	44 8b 75 b8          	mov    -0x48(%rbp),%r14d
    31c6:	e8 55 f2 ff ff       	call   2420 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    31cb:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    31d0:	49 89 c5             	mov    %rax,%r13
          struct Message *messaged = malloc(sizeof(struct Message));
    31d3:	e8 c8 f2 ff ff       	call   24a0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    31d8:	48 83 ec 08          	sub    $0x8,%rsp
    31dc:	44 8b 45 a0          	mov    -0x60(%rbp),%r8d
    31e0:	4c 89 ef             	mov    %r13,%rdi
    31e3:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    31e7:	45 89 f9             	mov    %r15d,%r9d
    31ea:	ba 00 01 00 00       	mov    $0x100,%edx
    31ef:	31 c0                	xor    %eax,%eax
    31f1:	41 56                	push   %r14
    31f3:	48 8d 0d ce 55 00 00 	lea    0x55ce(%rip),%rcx        # 87c8 <_IO_stdin_used+0x7c8>
    31fa:	be 01 00 00 00       	mov    $0x1,%esi
    31ff:	e8 dc f3 ff ff       	call   25e0 <__sprintf_chk@plt>
          messaged->message = message;
    3204:	4c 8b 5d b8          	mov    -0x48(%rbp),%r11
          thread_data[x].tasks[y].swap = swap;
    3208:	48 8b 4d 80          	mov    -0x80(%rbp),%rcx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    320c:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->task_index = y;
    3211:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3218:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->message = message;
    321d:	4d 89 2b             	mov    %r13,(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    3220:	4c 8b ad 68 ff ff ff 	mov    -0x98(%rbp),%r13
          messaged->task_index = y;
    3227:	49 89 43 10          	mov    %rax,0x10(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    322b:	49 63 45 08          	movslq 0x8(%r13),%rax
          thread_data[x].tasks[y].swap = swap;
    322f:	49 8b 55 38          	mov    0x38(%r13),%rdx
          messaged->group = k;
    3233:	45 89 73 18          	mov    %r14d,0x18(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    3237:	49 89 43 08          	mov    %rax,0x8(%r11)
          thread_data[x].tasks[y].swap = swap;
    323b:	8b 45 90             	mov    -0x70(%rbp),%eax
    323e:	48 01 d1             	add    %rdx,%rcx
          thread_data[x].tasks[y].group = k;
    3241:	44 89 b1 94 01 00 00 	mov    %r14d,0x194(%rcx)
          thread_data[x].tasks[y].swap = swap;
    3248:	89 81 98 01 00 00    	mov    %eax,0x198(%rcx)
          swap += 1;
    324e:	83 c0 01             	add    $0x1,%eax
    3251:	89 45 90             	mov    %eax,-0x70(%rbp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3254:	41 8d 47 01          	lea    0x1(%r15),%eax
    3258:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    325b:	c7 01 41 00 00 00    	movl   $0x41,(%rcx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3261:	89 81 90 01 00 00    	mov    %eax,0x190(%rcx)
          thread_data[x].tasks[y].message = messaged;
    3267:	4c 89 99 88 01 00 00 	mov    %r11,0x188(%rcx)
          thread_data[x].tasks[y].sending = 1;
    326e:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
          thread_data[x].tasks[y].snapshot_count = 99;
    3278:	48 c7 81 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rcx)
          thread_data[x].tasks[y].swap = swap;
    3283:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
          thread_data[x].tasks[y].snapshot_count = 99;
    3287:	48 89 4d b8          	mov    %rcx,-0x48(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    328b:	e8 90 f1 ff ff       	call   2420 <calloc@plt>
    3290:	48 8b 4d b8          	mov    -0x48(%rbp),%rcx
    3294:	48 89 81 50 01 00 00 	mov    %rax,0x150(%rcx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    329b:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    32a2:	48 c7 81 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rcx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    32ad:	48 8b 00             	mov    (%rax),%rax
    32b0:	8b 70 04             	mov    0x4(%rax),%esi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    32b3:	4c 39 e8             	cmp    %r13,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    32b6:	48 89 81 28 01 00 00 	mov    %rax,0x128(%rcx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    32bd:	89 b1 30 01 00 00    	mov    %esi,0x130(%rcx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    32c3:	5a                   	pop    %rdx
    32c4:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    32c8:	5e                   	pop    %rsi
    32c9:	0f 85 40 11 00 00    	jne    440f <main+0x1d5f>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    32cf:	66 0f 6f 05 f9 59 00 00 	movdqa 0x59f9(%rip),%xmm0        # 8cd0 <_IO_stdin_used+0xcd0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    32d7:	44 89 79 04          	mov    %r15d,0x4(%rcx)
          thread_data[x].tasks[y].available = 1;
    32db:	4c 8b 2d 0e 5a 00 00 	mov    0x5a0e(%rip),%r13        # 8cf0 <_IO_stdin_used+0xcf0>
          thread_data[x].tasks[y].arrived = 0;
    32e2:	c7 81 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rcx)
          thread_data[x].tasks[y].worker_count = thread_count;
    32ec:	c7 81 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rcx)
          thread_data[x].tasks[y].available = 1;
    32f6:	4c 89 a9 44 01 00 00 	mov    %r13,0x144(%rcx)
          thread_data[x].tasks[y].thread_count = 2;
    32fd:	0f 11 81 34 01 00 00 	movups %xmm0,0x134(%rcx)
          if (y == barrier_count - 1) {
    3304:	41 83 ff 01          	cmp    $0x1,%r15d
    3308:	0f 84 2a 02 00 00    	je     3538 <main+0xe88>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    330e:	45 85 ff             	test   %r15d,%r15d
    3311:	0f 84 08 02 00 00    	je     351f <main+0xe6f>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    3317:	4c 8b 8d 68 ff ff ff 	mov    -0x98(%rbp),%r9
    331e:	48 8d 05 4b 38 00 00 	lea    0x384b(%rip),%rax        # 6b70 <barriered_work>
    3325:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    3329:	41 89 dc             	mov    %ebx,%r12d
    332c:	48 89 81 18 01 00 00 	mov    %rax,0x118(%rcx)
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3333:	be 08 00 00 00       	mov    $0x8,%esi
    3338:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
    333d:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    3348:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    334c:	e8 cf f0 ff ff       	call   2420 <calloc@plt>
    3351:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3355:	48 8b 9d 50 ff ff ff 	mov    -0xb0(%rbp),%rbx
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    335c:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    3360:	66 0f 6f bd 00 ff ff ff 	movdqa -0x100(%rbp),%xmm7
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3368:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    336b:	48 83 c3 10          	add    $0x10,%rbx
    336f:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3376:	49 89 81 70 ff ff ff 	mov    %rax,-0x90(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    337d:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    3384:	83 45 98 01          	addl   $0x1,-0x68(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3388:	48 8b 00             	mov    (%rax),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    338b:	83 85 40 ff ff ff 01 	addl   $0x1,-0xc0(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    3392:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    339c:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    33a3:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    33ad:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    33b7:	41 8b 81 24 ff ff ff 	mov    -0xdc(%r9),%eax
    for (int d = 0 ; d < threads_per_group ; d++) {
    33be:	48 89 9d 50 ff ff ff 	mov    %rbx,-0xb0(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    33c5:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    33cb:	8b 45 98             	mov    -0x68(%rbp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    33ce:	c7 82 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
    33d8:	4c 89 aa 44 05 00 00 	mov    %r13,0x544(%rdx)
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    33df:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    33e6:	39 85 38 ff ff ff    	cmp    %eax,-0xc8(%rbp)
    33ec:	0f 85 50 f6 ff ff    	jne    2a42 <main+0x392>
    33f2:	4c 8b bd e0 fe ff ff 	mov    -0x120(%rbp),%r15
    33f9:	48 8b b5 f8 fe ff ff 	mov    -0x108(%rbp),%rsi
    3400:	45 89 f5             	mov    %r14d,%r13d
  for (int k = 0 ; k < group_count ; k++) {
    3403:	41 83 c5 01          	add    $0x1,%r13d
    3407:	48 8b 9d d8 fe ff ff 	mov    -0x128(%rbp),%rbx
    340e:	48 83 c6 18          	add    $0x18,%rsi
    3412:	49 81 c7 c0 01 00 00 	add    $0x1c0,%r15
    3419:	41 83 fd 03          	cmp    $0x3,%r13d
    341d:	0f 85 db f5 ff ff    	jne    29fe <main+0x34e>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3423:	be 08 00 00 00       	mov    $0x8,%esi
    3428:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    342d:	31 db                	xor    %ebx,%ebx
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    342f:	e8 ec ef ff ff       	call   2420 <calloc@plt>
    3434:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    3438:	49 89 c7             	mov    %rax,%r15
    343b:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    343d:	49 89 d1             	mov    %rdx,%r9
    3440:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3443:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3447:	45 85 d2             	test   %r10d,%r10d
    344a:	0f 8e a8 00 00 00    	jle    34f8 <main+0xe48>
    3450:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3454:	4d 63 c2             	movslq %r10d,%r8
    3457:	48 63 cb             	movslq %ebx,%rcx
    345a:	49 c1 e0 09          	shl    $0x9,%r8
    345e:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    3462:	49 01 f8             	add    %rdi,%r8
    3465:	0f 1f 00             	nopl   (%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3468:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    346f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3476:	48 83 c6 60          	add    $0x60,%rsi
    347a:	f3 0f 7e a1 80 01 00 00 	movq   0x180(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3482:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3486:	f3 0f 7e 99 00 03 00 00 	movq   0x300(%rcx),%xmm3
    348e:	f3 0f 7e 91 80 04 00 00 	movq   0x480(%rcx),%xmm2
    3496:	f3 0f 7e 89 00 06 00 00 	movq   0x600(%rcx),%xmm1
    349e:	0f 16 a1 00 02 00 00 	movhps 0x200(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    34a5:	f3 0f 7e 81 80 07 00 00 	movq   0x780(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    34ad:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    34b4:	0f 16 99 80 03 00 00 	movhps 0x380(%rcx),%xmm3
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    34bb:	0f 16 91 00 05 00 00 	movhps 0x500(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    34c2:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    34c6:	0f 16 89 80 06 00 00 	movhps 0x680(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    34cd:	0f 16 81 00 08 00 00 	movhps 0x800(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    34d4:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    34d8:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    34dc:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    34e0:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    34e4:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    34e8:	49 39 f8             	cmp    %rdi,%r8
    34eb:	0f 85 77 ff ff ff    	jne    3468 <main+0xdb8>
    34f1:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    34f5:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    34f8:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    34ff:	45 85 db             	test   %r11d,%r11d
    3502:	75 43                	jne    3547 <main+0xe97>
    3504:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    350a:	e9 34 ff ff ff       	jmp    3443 <main+0xd93>
    350f:	44 8b 7d b8          	mov    -0x48(%rbp),%r15d
    3513:	48 8b 8d 48 ff ff ff 	mov    -0xb8(%rbp),%rcx
    351a:	e9 d7 fa ff ff       	jmp    2ff6 <main+0x946>
    351f:	48 8d 05 1a 3c 00 00 	lea    0x3c1a(%rip),%rax        # 7140 <barriered_work_ingest_andwork>
    3526:	41 bf 01 00 00 00    	mov    $0x1,%r15d
            thread_data[x].tasks[y].run = barriered_work; 
    352c:	48 89 81 18 01 00 00 	mov    %rax,0x118(%rcx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    3533:	e9 49 f7 ff ff       	jmp    2c81 <main+0x5d1>
    3538:	48 8d 05 31 36 00 00 	lea    0x3631(%rip),%rax        # 6b70 <barriered_work>
    353f:	41 bf 02 00 00 00    	mov    $0x2,%r15d
    3545:	eb e5                	jmp    352c <main+0xe7c>
  for (int k = 0 ; k < group_count ; k++) {
    3547:	83 c0 02             	add    $0x2,%eax
    354a:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    3551:	83 f8 06             	cmp    $0x6,%eax
    3554:	0f 85 e3 fe ff ff    	jne    343d <main+0xd8d>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    355a:	48 8d 3d 89 4e 00 00 	lea    0x4e89(%rip),%rdi        # 83ea <_IO_stdin_used+0x3ea>
    3561:	44 89 5d b0          	mov    %r11d,-0x50(%rbp)
    3565:	e8 e6 ed ff ff       	call   2350 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    356a:	48 8d 35 8e 4e 00 00 	lea    0x4e8e(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3571:	48 8d 3d 89 4e 00 00 	lea    0x4e89(%rip),%rdi        # 8401 <_IO_stdin_used+0x401>
    3578:	e8 a3 ef ff ff       	call   2520 <fopen@plt>
    357d:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas_size; x++) {
    3580:	85 db                	test   %ebx,%ebx
    3582:	7e 74                	jle    35f8 <main+0xf48>
    3584:	48 63 db             	movslq %ebx,%rbx
    3587:	4c 8d 2d 50 4e 00 00 	lea    0x4e50(%rip),%r13        # 83de <_IO_stdin_used+0x3de>
    358e:	4c 8d 25 8d 4e 00 00 	lea    0x4e8d(%rip),%r12        # 8422 <_IO_stdin_used+0x422>
    3595:	49 8d 04 df          	lea    (%r15,%rbx,8),%rax
    3599:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    char * c = calloc(250, sizeof(char));
    359d:	be 01 00 00 00       	mov    $0x1,%esi
    35a2:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    35a7:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    35ab:	e8 70 ee ff ff       	call   2420 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    35b0:	4c 89 e9             	mov    %r13,%rcx
    35b3:	ba fa 00 00 00       	mov    $0xfa,%edx
    35b8:	be 01 00 00 00       	mov    $0x1,%esi
    35bd:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    35c0:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    35c4:	48 89 df             	mov    %rbx,%rdi
    35c7:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    35ce:	31 c0                	xor    %eax,%eax
    35d0:	e8 0b f0 ff ff       	call   25e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    35d5:	48 89 da             	mov    %rbx,%rdx
    35d8:	4c 89 e6             	mov    %r12,%rsi
    35db:	bf 01 00 00 00       	mov    $0x1,%edi
    35e0:	31 c0                	xor    %eax,%eax
    35e2:	e8 f9 ee ff ff       	call   24e0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    35e7:	4c 89 f6             	mov    %r14,%rsi
    35ea:	48 89 df             	mov    %rbx,%rdi
    35ed:	e8 ee ed ff ff       	call   23e0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    35f2:	4c 39 7d b8          	cmp    %r15,-0x48(%rbp)
    35f6:	75 a5                	jne    359d <main+0xeed>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    35f8:	4c 89 f7             	mov    %r14,%rdi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    35fb:	45 31 ff             	xor    %r15d,%r15d
    35fe:	4c 8d 2d 47 4e 00 00 	lea    0x4e47(%rip),%r13        # 844c <_IO_stdin_used+0x44c>
    3605:	e8 76 ed ff ff       	call   2380 <fclose@plt>
    360a:	48 8d 3d f9 4d 00 00 	lea    0x4df9(%rip),%rdi        # 840a <_IO_stdin_used+0x40a>
    3611:	4d 89 fc             	mov    %r15,%r12
    3614:	e8 37 ed ff ff       	call   2350 <puts@plt>
    3619:	44 89 e2             	mov    %r12d,%edx
    361c:	48 8d 35 02 4e 00 00 	lea    0x4e02(%rip),%rsi        # 8425 <_IO_stdin_used+0x425>
    3623:	31 c0                	xor    %eax,%eax
    3625:	45 31 ff             	xor    %r15d,%r15d
    3628:	bf 01 00 00 00       	mov    $0x1,%edi
    362d:	4a 8d 1c e5 00 00 00 00 	lea    0x0(,%r12,8),%rbx
    3635:	47 8d 34 24          	lea    (%r12,%r12,1),%r14d
    3639:	e8 a2 ee ff ff       	call   24e0 <__printf_chk@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    363e:	4c 29 e3             	sub    %r12,%rbx
    3641:	48 8b 45 88          	mov    -0x78(%rbp),%rax
    3645:	48 c1 e3 06          	shl    $0x6,%rbx
    3649:	48 01 c3             	add    %rax,%rbx
      int x = (k * threads_per_group) + d;
    364c:	43 8d 0c 37          	lea    (%r15,%r14,1),%ecx
    3650:	44 89 fa             	mov    %r15d,%edx
    3653:	48 8d 35 d5 4d 00 00 	lea    0x4dd5(%rip),%rsi        # 842f <_IO_stdin_used+0x42f>
    365a:	31 c0                	xor    %eax,%eax
    365c:	bf 01 00 00 00       	mov    $0x1,%edi
    3661:	e8 7a ee ff ff       	call   24e0 <__printf_chk@plt>
    3666:	44 89 7d a8          	mov    %r15d,-0x58(%rbp)
    366a:	31 c9                	xor    %ecx,%ecx
    366c:	44 89 75 a0          	mov    %r14d,-0x60(%rbp)
    3670:	4c 89 65 98          	mov    %r12,-0x68(%rbp)
    3674:	89 ca                	mov    %ecx,%edx
    3676:	48 8d 35 c4 4d 00 00 	lea    0x4dc4(%rip),%rsi        # 8441 <_IO_stdin_used+0x441>
    367d:	bf 01 00 00 00       	mov    $0x1,%edi
    3682:	31 c0                	xor    %eax,%eax
    3684:	48 89 4d b8          	mov    %rcx,-0x48(%rbp)
    3688:	45 31 e4             	xor    %r12d,%r12d
    368b:	e8 50 ee ff ff       	call   24e0 <__printf_chk@plt>
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3690:	4c 8b 7d b8          	mov    -0x48(%rbp),%r15
    3694:	49 c1 e7 09          	shl    $0x9,%r15
    3698:	eb 32                	jmp    36cc <main+0x101c>
    369a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    36a0:	83 ff 01             	cmp    $0x1,%edi
    36a3:	0f 84 a7 00 00 00    	je     3750 <main+0x10a0>
    36a9:	44 8b 86 b4 00 00 00 	mov    0xb4(%rsi),%r8d
    36b0:	44 89 f2             	mov    %r14d,%edx
    36b3:	4c 89 ee             	mov    %r13,%rsi
    36b6:	31 c0                	xor    %eax,%eax
    36b8:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    36bd:	49 83 c4 01          	add    $0x1,%r12
    36c1:	e8 1a ee ff ff       	call   24e0 <__printf_chk@plt>
    36c6:	49 83 fc 06          	cmp    $0x6,%r12
    36ca:	74 51                	je     371d <main+0x106d>
          char * mailbox_kind = calloc(100, sizeof(char));
    36cc:	be 01 00 00 00       	mov    $0x1,%esi
    36d1:	bf 64 00 00 00       	mov    $0x64,%edi
    36d6:	45 89 e6             	mov    %r12d,%r14d
    36d9:	e8 42 ed ff ff       	call   2420 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    36de:	4c 8b 43 38          	mov    0x38(%rbx),%r8
          char * mailbox_kind = calloc(100, sizeof(char));
    36e2:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    36e5:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
    36e9:	4b 8b b4 38 70 01 00 00 	mov    0x170(%r8,%r15,1),%rsi
    36f1:	48 c1 e0 07          	shl    $0x7,%rax
    36f5:	48 01 c6             	add    %rax,%rsi
    36f8:	8b be b0 00 00 00    	mov    0xb0(%rsi),%edi
    36fe:	83 ff 02             	cmp    $0x2,%edi
    3701:	75 9d                	jne    36a0 <main+0xff0>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3703:	48 bf 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rdi
    370d:	48 89 39             	mov    %rdi,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3710:	4b 03 84 38 70 01 00 00 	add    0x170(%r8,%r15,1),%rax
    3718:	48 89 c6             	mov    %rax,%rsi
    371b:	eb 8c                	jmp    36a9 <main+0xff9>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    371d:	48 8b 4d b8          	mov    -0x48(%rbp),%rcx
    3721:	48 83 c1 01          	add    $0x1,%rcx
    3725:	48 83 f9 03          	cmp    $0x3,%rcx
    3729:	0f 85 45 ff ff ff    	jne    3674 <main+0xfc4>
    for (int d = 0 ; d < threads_per_group ; d++) {
    372f:	44 8b 7d a8          	mov    -0x58(%rbp),%r15d
    3733:	44 8b 75 a0          	mov    -0x60(%rbp),%r14d
    3737:	48 81 c3 e0 00 00 00 	add    $0xe0,%rbx
    373e:	4c 8b 65 98          	mov    -0x68(%rbp),%r12
    3742:	45 85 ff             	test   %r15d,%r15d
    3745:	75 26                	jne    376d <main+0x10bd>
    3747:	44 8b 7d b0          	mov    -0x50(%rbp),%r15d
    374b:	e9 fc fe ff ff       	jmp    364c <main+0xf9c>
    3750:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3756:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    375d:	4b 03 84 38 70 01 00 00 	add    0x170(%r8,%r15,1),%rax
    3765:	48 89 c6             	mov    %rax,%rsi
    3768:	e9 3c ff ff ff       	jmp    36a9 <main+0xff9>
  for (int k = 0 ; k < group_count ; k++) {
    376d:	49 83 c4 01          	add    $0x1,%r12
    3771:	49 83 fc 03          	cmp    $0x3,%r12
    3775:	0f 85 9e fe ff ff    	jne    3619 <main+0xf69>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    377b:	ba 07 00 00 00       	mov    $0x7,%edx
    3780:	bf 01 00 00 00       	mov    $0x1,%edi
    3785:	31 c0                	xor    %eax,%eax
    3787:	44 89 fb             	mov    %r15d,%ebx
    378a:	48 8d 35 d6 4c 00 00 	lea    0x4cd6(%rip),%rsi        # 8467 <_IO_stdin_used+0x467>
    3791:	e8 4a ed ff ff       	call   24e0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    3796:	be 08 00 00 00       	mov    $0x8,%esi
    379b:	bf 02 00 00 00       	mov    $0x2,%edi
    37a0:	e8 7b ec ff ff       	call   2420 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    37a5:	4c 8b 6d 88          	mov    -0x78(%rbp),%r13
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37a9:	be 38 00 00 00       	mov    $0x38,%esi
    37ae:	bf 0a 00 00 00       	mov    $0xa,%edi
    my_thread_data[0] = &thread_data[x]; 
    37b3:	4d 8d bd 20 06 00 00 	lea    0x620(%r13),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    37ba:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    37be:	4d 8d b5 e0 00 00 00 	lea    0xe0(%r13),%r14
    thread_data[x].threads = my_thread_data;
    37c5:	49 89 85 38 06 00 00 	mov    %rax,0x638(%r13)
    my_thread_data[0] = &thread_data[x]; 
    37cc:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    37cf:	49 8b 45 38          	mov    0x38(%r13),%rax
    thread_data[x].thread_count = 2;
    37d3:	41 c7 85 48 06 00 00 02 00 00 00 	movl   $0x2,0x648(%r13)
    thread_data[x].thread_index = 0;
    37de:	41 c7 85 24 06 00 00 00 00 00 00 	movl   $0x0,0x624(%r13)
    thread_data[x].task_count = total_barrier_count;
    37e9:	41 c7 85 60 06 00 00 03 00 00 00 	movl   $0x3,0x660(%r13)
    thread_data[n].tasks[0].scheduled = 1;
    37f4:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    37fe:	49 8b 85 18 01 00 00 	mov    0x118(%r13),%rax
    3805:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    380f:	e8 0c ec ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3814:	be 38 00 00 00       	mov    $0x38,%esi
    3819:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    381e:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3822:	e8 f9 eb ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3827:	be 38 00 00 00       	mov    $0x38,%esi
    382c:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3831:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3834:	e8 e7 eb ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3839:	be 38 00 00 00       	mov    $0x38,%esi
    383e:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3843:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3847:	e8 d4 eb ff ff       	call   2420 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    384c:	be 08 00 00 00       	mov    $0x8,%esi
    3851:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3856:	48 89 45 a0          	mov    %rax,-0x60(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    385a:	e8 c1 eb ff ff       	call   2420 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    385f:	be 08 00 00 00       	mov    $0x8,%esi
    3864:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
    3869:	41 c7 85 4c 05 00 00 00 00 00 00 	movl   $0x0,0x54c(%r13)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3874:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  thread_data[timer_threadi].task_count = total_barrier_count;
    3878:	48 8b 05 79 54 00 00 	mov    0x5479(%rip),%rax        # 8cf8 <_IO_stdin_used+0xcf8>
    387f:	49 89 85 80 05 00 00 	mov    %rax,0x580(%r13)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3886:	e8 95 eb ff ff       	call   2420 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    388b:	49 8d 95 c0 01 00 00 	lea    0x1c0(%r13),%rdx
    3892:	4c 89 ef             	mov    %r13,%rdi
    3895:	49 8d 8d 40 05 00 00 	lea    0x540(%r13),%rcx
    389c:	48 89 50 10          	mov    %rdx,0x10(%rax)
    38a0:	49 8d 95 a0 02 00 00 	lea    0x2a0(%r13),%rdx
    38a7:	48 8d 35 c8 4b 00 00 	lea    0x4bc8(%rip),%rsi        # 8476 <_IO_stdin_used+0x476>
    38ae:	48 89 50 18          	mov    %rdx,0x18(%rax)
    38b2:	49 8d 95 80 03 00 00 	lea    0x380(%r13),%rdx
    38b9:	48 89 50 20          	mov    %rdx,0x20(%rax)
    38bd:	49 8d 95 60 04 00 00 	lea    0x460(%r13),%rdx
    38c4:	4c 89 28             	mov    %r13,(%rax)
    38c7:	4d 8d ad 00 07 00 00 	lea    0x700(%r13),%r13
    38ce:	48 89 50 28          	mov    %rdx,0x28(%rax)
    38d2:	48 8d 97 e0 07 00 00 	lea    0x7e0(%rdi),%rdx
    38d9:	48 89 48 30          	mov    %rcx,0x30(%rax)
    38dd:	4c 89 78 38          	mov    %r15,0x38(%rax)
    38e1:	48 89 50 48          	mov    %rdx,0x48(%rax)
    38e5:	ba 06 00 00 00       	mov    $0x6,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    38ea:	48 89 87 58 05 00 00 	mov    %rax,0x558(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    38f1:	4c 89 70 08          	mov    %r14,0x8(%rax)
    38f5:	4c 89 68 40          	mov    %r13,0x40(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    38f9:	48 8b 05 00 54 00 00 	mov    0x5400(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3900:	c7 87 70 05 00 00 06 00 00 00 	movl   $0x6,0x570(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    390a:	48 89 87 68 05 00 00 	mov    %rax,0x568(%rdi)
    3911:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3913:	c7 87 44 05 00 00 00 00 00 00 	movl   $0x0,0x544(%rdi)
    391d:	48 89 7d 88          	mov    %rdi,-0x78(%rbp)
    3921:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    3926:	48 89 4d 98          	mov    %rcx,-0x68(%rbp)
    392a:	e8 b1 eb ff ff       	call   24e0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    392f:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
    3933:	49 8d b4 24 50 01 00 00 	lea    0x150(%r12),%rsi
    393b:	4c 8b 65 b8          	mov    -0x48(%rbp),%r12
    393f:	48 8d 15 0a 0e 00 00 	lea    0xe0a(%rip),%rdx        # 4750 <timer_thread>
    3946:	49 8d 7c 24 30       	lea    0x30(%r12),%rdi
    394b:	e8 b0 eb ff ff       	call   2500 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    3950:	4c 89 75 80          	mov    %r14,-0x80(%rbp)
    3954:	45 31 c0             	xor    %r8d,%r8d
    3957:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    395b:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3961:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    3965:	89 5d 98             	mov    %ebx,-0x68(%rbp)
    3968:	4c 89 e1             	mov    %r12,%rcx
    396b:	4c 89 ad 78 ff ff ff 	mov    %r13,-0x88(%rbp)
    3972:	44 89 c3             	mov    %r8d,%ebx
    3975:	4c 89 7d 90          	mov    %r15,-0x70(%rbp)
    3979:	45 89 d7             	mov    %r10d,%r15d
    397c:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    3980:	44 8d 34 1b          	lea    (%rbx,%rbx,1),%r14d
    3984:	49 89 cd             	mov    %rcx,%r13
    3987:	49 89 d4             	mov    %rdx,%r12
    398a:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
    3991:	48 89 8d 68 ff ff ff 	mov    %rcx,-0x98(%rbp)
    3998:	48 89 95 60 ff ff ff 	mov    %rdx,-0xa0(%rbp)
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    399f:	41 c7 44 24 0c 01 00 00 00 	movl   $0x1,0xc(%r12)
    39a8:	44 89 f2             	mov    %r14d,%edx
    39ab:	89 d9                	mov    %ebx,%ecx
    39ad:	31 c0                	xor    %eax,%eax
    39af:	48 8d 35 42 4e 00 00 	lea    0x4e42(%rip),%rsi        # 87f8 <_IO_stdin_used+0x7f8>
    39b6:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    39bb:	41 83 c6 01          	add    $0x1,%r14d
      thread_data[x].running = 1;
    39bf:	41 c7 44 24 44 01 00 00 00 	movl   $0x1,0x44(%r12)
    39c8:	e8 13 eb ff ff       	call   24e0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    39cd:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
    39d1:	4c 89 e1             	mov    %r12,%rcx
    39d4:	4c 89 ef             	mov    %r13,%rdi
    39d7:	48 8d 15 82 2a 00 00 	lea    0x2a82(%rip),%rdx        # 6460 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    39de:	49 81 c4 e0 00 00 00 	add    $0xe0,%r12
    39e5:	49 83 c5 08          	add    $0x8,%r13
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    39e9:	e8 12 eb ff ff       	call   2500 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    39ee:	49 8b 54 24 d0       	mov    -0x30(%r12),%rdx
    39f3:	49 8b 7d f8          	mov    -0x8(%r13),%rdi
    39f7:	be 08 00 00 00       	mov    $0x8,%esi
    39fc:	e8 3f e9 ff ff       	call   2340 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3a01:	48 83 45 b0 38       	addq   $0x38,-0x50(%rbp)
    3a06:	45 39 f7             	cmp    %r14d,%r15d
    3a09:	75 94                	jne    399f <main+0x12ef>
  for (int k = 0 ; k < group_count ; k++) {
    3a0b:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
    3a12:	48 8b 8d 68 ff ff ff 	mov    -0x98(%rbp),%rcx
    3a19:	83 c3 01             	add    $0x1,%ebx
    3a1c:	41 83 c7 02          	add    $0x2,%r15d
    3a20:	48 8b 95 60 ff ff ff 	mov    -0xa0(%rbp),%rdx
    3a27:	48 83 c1 10          	add    $0x10,%rcx
    3a2b:	48 83 c0 70          	add    $0x70,%rax
    3a2f:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    3a36:	83 fb 03             	cmp    $0x3,%ebx
    3a39:	0f 85 3d ff ff ff    	jne    397c <main+0x12cc>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    3a3f:	4c 8b 65 88          	mov    -0x78(%rbp),%r12
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a43:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    3a48:	48 8b 05 b9 52 00 00 	mov    0x52b9(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a4f:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    3a54:	4c 8b 7d 90          	mov    -0x70(%rbp),%r15
    3a58:	4c 8b 75 80          	mov    -0x80(%rbp),%r14
    3a5c:	41 c7 84 24 2c 06 00 00 02 00 00 00 	movl   $0x2,0x62c(%r12)
    3a68:	8b 5d 98             	mov    -0x68(%rbp),%ebx
    thread_data[x].task_count = 0;
    3a6b:	49 89 84 24 60 06 00 00 	mov    %rax,0x660(%r12)
    thread_data[x].type = IO;
    3a73:	4c 8b ad 78 ff ff ff 	mov    -0x88(%rbp),%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a7a:	e8 a1 e9 ff ff       	call   2420 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a7f:	be 00 08 00 00       	mov    $0x800,%esi
    3a84:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a86:	49 89 84 24 78 06 00 00 	mov    %rax,0x678(%r12)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a8e:	e8 cd ea ff ff       	call   2560 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a93:	be 08 00 00 00       	mov    $0x8,%esi
    3a98:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a9d:	41 89 84 24 80 06 00 00 	mov    %eax,0x680(%r12)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3aa5:	e8 76 e9 ff ff       	call   2420 <calloc@plt>
    3aaa:	ba 07 00 00 00       	mov    $0x7,%edx
    3aaf:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3ab4:	41 c7 84 24 48 06 00 00 02 00 00 00 	movl   $0x2,0x648(%r12)
      my_thread_data[n] = &thread_data[n]; 
    3ac0:	4c 89 20             	mov    %r12,(%rax)
    3ac3:	48 8d 35 ca 49 00 00 	lea    0x49ca(%rip),%rsi        # 8494 <_IO_stdin_used+0x494>
    thread_data[x].threads = my_thread_data;
    3aca:	49 89 84 24 38 06 00 00 	mov    %rax,0x638(%r12)
      my_thread_data[n] = &thread_data[n]; 
    3ad2:	4c 89 70 08          	mov    %r14,0x8(%rax)
    3ad6:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3ad8:	41 c7 84 24 24 06 00 00 07 00 00 00 	movl   $0x7,0x624(%r12)
    3ae4:	e8 f7 e9 ff ff       	call   24e0 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3ae9:	4c 8b 65 b8          	mov    -0x48(%rbp),%r12
    3aed:	48 8b 75 a8          	mov    -0x58(%rbp),%rsi
    3af1:	4c 89 f9             	mov    %r15,%rcx
    3af4:	48 8d 15 15 21 00 00 	lea    0x2115(%rip),%rdx        # 5c10 <io_thread>
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3afb:	41 bf 08 00 00 00    	mov    $0x8,%r15d
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3b01:	49 8d 7c 24 38       	lea    0x38(%r12),%rdi
    3b06:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3b0d:	e8 ee e9 ff ff       	call   2500 <pthread_create@plt>
    3b12:	ba 08 00 00 00       	mov    $0x8,%edx
    3b17:	48 8d 35 8d 49 00 00 	lea    0x498d(%rip),%rsi        # 84ab <_IO_stdin_used+0x4ab>
    3b1e:	31 c0                	xor    %eax,%eax
    3b20:	bf 01 00 00 00       	mov    $0x1,%edi
    3b25:	e8 b6 e9 ff ff       	call   24e0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b2a:	49 8d 44 24 40       	lea    0x40(%r12),%rax
    3b2f:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    3b33:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    3b37:	49 81 c4 c0 01 00 00 	add    $0x1c0,%r12
    3b3e:	44 89 fa             	mov    %r15d,%edx
    3b41:	48 8d 35 79 49 00 00 	lea    0x4979(%rip),%rsi        # 84c1 <_IO_stdin_used+0x4c1>
    3b48:	bf 01 00 00 00       	mov    $0x1,%edi
    3b4d:	31 c0                	xor    %eax,%eax
    3b4f:	e8 8c e9 ff ff       	call   24e0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3b54:	be 08 00 00 00       	mov    $0x8,%esi
    3b59:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3b5e:	48 8b 05 a3 51 00 00 	mov    0x51a3(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    thread_data[x].type = EXTERNAL;
    3b65:	41 c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%r13)
    thread_data[x].task_count = 0;
    3b6d:	49 89 45 40          	mov    %rax,0x40(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3b71:	e8 aa e8 ff ff       	call   2420 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3b76:	48 8b bd 10 ff ff ff 	mov    -0xf0(%rbp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3b7d:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3b82:	41 c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3b8d:	49 89 45 50          	mov    %rax,0x50(%r13)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3b91:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3b94:	bf 02 00 00 00       	mov    $0x2,%edi
    3b99:	e8 82 e8 ff ff       	call   2420 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3b9e:	48 8b 75 88          	mov    -0x78(%rbp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    3ba2:	45 89 7d 04          	mov    %r15d,0x4(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3ba6:	4c 89 e9             	mov    %r13,%rcx
    thread_data[x].threads = my_thread_data;
    3ba9:	49 89 45 18          	mov    %rax,0x18(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3bad:	48 8b 7d b0          	mov    -0x50(%rbp),%rdi
    3bb1:	48 8d 15 78 0a 00 00 	lea    0xa78(%rip),%rdx        # 4630 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3bb8:	49 81 c5 e0 00 00 00 	add    $0xe0,%r13
      my_thread_data[n] = &thread_data[n]; 
    3bbf:	48 89 30             	mov    %rsi,(%rax)
    thread_data[x].thread_count = thread_count;
    3bc2:	48 8b 35 1f 51 00 00 	mov    0x511f(%rip),%rsi        # 8ce8 <_IO_stdin_used+0xce8>
      my_thread_data[n] = &thread_data[n]; 
    3bc9:	4c 89 70 08          	mov    %r14,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3bcd:	49 89 b5 48 ff ff ff 	mov    %rsi,-0xb8(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3bd4:	4c 89 e6             	mov    %r12,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3bd7:	49 83 c4 38          	add    $0x38,%r12
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3bdb:	e8 20 e9 ff ff       	call   2500 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3be0:	48 83 85 10 ff ff ff 10 	addq   $0x10,-0xf0(%rbp)
    3be8:	48 83 45 b0 08       	addq   $0x8,-0x50(%rbp)
    3bed:	41 83 ff 08          	cmp    $0x8,%r15d
    3bf1:	75 43                	jne    3c36 <main+0x1586>
    3bf3:	41 bf 09 00 00 00    	mov    $0x9,%r15d
    3bf9:	e9 40 ff ff ff       	jmp    3b3e <main+0x148e>
        my_thread_data[1] = &thread_data[other]; 
    3bfe:	4a 8d 14 fd 00 00 00 00 	lea    0x0(,%r15,8),%rdx
    3c06:	48 8b 45 88          	mov    -0x78(%rbp),%rax
        other = (x + 1) % total_threads;
    3c0a:	44 89 f9             	mov    %r15d,%ecx
        my_thread_data[1] = &thread_data[other]; 
    3c0d:	45 31 c0             	xor    %r8d,%r8d
    3c10:	4c 29 fa             	sub    %r15,%rdx
    3c13:	48 89 9d 70 ff ff ff 	mov    %rbx,-0x90(%rbp)
    3c1a:	48 c1 e2 05          	shl    $0x5,%rdx
    3c1e:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    3c21:	4c 89 c8             	mov    %r9,%rax
    3c24:	e9 ac ee ff ff       	jmp    2ad5 <main+0x425>
            CPU_SET(j, sendercpu);
    3c29:	49 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%r13)
          for (int j = 0 ; j < cores ; j++) {
    3c31:	e9 3a ef ff ff       	jmp    2b70 <main+0x4c0>
    3c36:	48 8b 45 88          	mov    -0x78(%rbp),%rax
    3c3a:	4c 8d 2d 9d 48 00 00 	lea    0x489d(%rip),%r13        # 84de <_IO_stdin_used+0x4de>
    3c41:	4c 8d 78 04          	lea    0x4(%rax),%r15
    3c45:	4c 8d b0 c4 08 00 00 	lea    0x8c4(%rax),%r14
    3c4c:	41 8b 4f 04          	mov    0x4(%r15),%ecx
    3c50:	41 8b 17             	mov    (%r15),%edx
    3c53:	4c 89 ee             	mov    %r13,%rsi
    3c56:	bf 01 00 00 00       	mov    $0x1,%edi
    3c5b:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3c5d:	49 81 c7 e0 00 00 00 	add    $0xe0,%r15
    3c64:	e8 77 e8 ff ff       	call   24e0 <__printf_chk@plt>
    3c69:	4d 39 fe             	cmp    %r15,%r14
    3c6c:	75 de                	jne    3c4c <main+0x159c>
    3c6e:	48 8d 3d 7c 48 00 00 	lea    0x487c(%rip),%rdi        # 84f1 <_IO_stdin_used+0x4f1>
    3c75:	45 31 ff             	xor    %r15d,%r15d
    3c78:	4c 8d 75 c0          	lea    -0x40(%rbp),%r14
    3c7c:	e8 cf e6 ff ff       	call   2350 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3c81:	4c 8b 65 b8          	mov    -0x48(%rbp),%r12
    3c85:	4c 8d 2d 83 48 00 00 	lea    0x4883(%rip),%r13        # 850f <_IO_stdin_used+0x50f>
    void * result; 
    pthread_join(thread[x], &result);
    3c8c:	4b 8b 3c fc          	mov    (%r12,%r15,8),%rdi
    3c90:	4c 89 f6             	mov    %r14,%rsi
    3c93:	e8 08 e9 ff ff       	call   25a0 <pthread_join@plt>
    3c98:	44 89 fa             	mov    %r15d,%edx
    3c9b:	4c 89 ee             	mov    %r13,%rsi
    3c9e:	bf 01 00 00 00       	mov    $0x1,%edi
    3ca3:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3ca5:	49 83 c7 01          	add    $0x1,%r15
    3ca9:	e8 32 e8 ff ff       	call   24e0 <__printf_chk@plt>
    3cae:	49 83 ff 0a          	cmp    $0xa,%r15
    3cb2:	75 d8                	jne    3c8c <main+0x15dc>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3cb4:	be 08 00 00 00       	mov    $0x8,%esi
    3cb9:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3cbe:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3cc1:	e8 5a e7 ff ff       	call   2420 <calloc@plt>
    3cc6:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    3cca:	49 89 c6             	mov    %rax,%r14
    3ccd:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3ccf:	49 89 d1             	mov    %rdx,%r9
    3cd2:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3cd5:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3cd9:	45 85 d2             	test   %r10d,%r10d
    3cdc:	0f 8e af 00 00 00    	jle    3d91 <main+0x16e1>
    3ce2:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3ce6:	4d 63 c2             	movslq %r10d,%r8
    3ce9:	49 63 cc             	movslq %r12d,%rcx
    3cec:	49 c1 e0 09          	shl    $0x9,%r8
    3cf0:	49 8d 34 ce          	lea    (%r14,%rcx,8),%rsi
    3cf4:	49 01 f8             	add    %rdi,%r8
    3cf7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3d00:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3d07:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3d0e:	48 83 c6 60          	add    $0x60,%rsi
    3d12:	f3 0f 7e a1 80 01 00 00 	movq   0x180(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3d1a:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3d1e:	f3 0f 7e 99 00 03 00 00 	movq   0x300(%rcx),%xmm3
    3d26:	f3 0f 7e 91 80 04 00 00 	movq   0x480(%rcx),%xmm2
    3d2e:	f3 0f 7e 89 00 06 00 00 	movq   0x600(%rcx),%xmm1
    3d36:	0f 16 a1 00 02 00 00 	movhps 0x200(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3d3d:	f3 0f 7e 81 80 07 00 00 	movq   0x780(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3d45:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    3d4c:	0f 16 99 80 03 00 00 	movhps 0x380(%rcx),%xmm3
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3d53:	0f 16 91 00 05 00 00 	movhps 0x500(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3d5a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3d5e:	0f 16 89 80 06 00 00 	movhps 0x680(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3d65:	0f 16 81 00 08 00 00 	movhps 0x800(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3d6c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3d70:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3d74:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3d78:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3d7c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3d80:	4c 39 c7             	cmp    %r8,%rdi
    3d83:	0f 85 77 ff ff ff    	jne    3d00 <main+0x1650>
    3d89:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3d8d:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    3d91:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    3d98:	45 85 db             	test   %r11d,%r11d
    3d9b:	75 08                	jne    3da5 <main+0x16f5>
    3d9d:	41 89 db             	mov    %ebx,%r11d
    3da0:	e9 30 ff ff ff       	jmp    3cd5 <main+0x1625>
  for (int k = 0 ; k < group_count ; k++) {
    3da5:	83 c0 02             	add    $0x2,%eax
    3da8:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    3daf:	83 f8 06             	cmp    $0x6,%eax
    3db2:	0f 85 17 ff ff ff    	jne    3ccf <main+0x161f>
    3db8:	48 8d 3d 64 47 00 00 	lea    0x4764(%rip),%rdi        # 8523 <_IO_stdin_used+0x523>
    3dbf:	e8 8c e5 ff ff       	call   2350 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3dc4:	48 8d 35 34 46 00 00 	lea    0x4634(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3dcb:	48 8d 3d 69 47 00 00 	lea    0x4769(%rip),%rdi        # 853b <_IO_stdin_used+0x53b>
    3dd2:	e8 49 e7 ff ff       	call   2520 <fopen@plt>
    3dd7:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas2_size; x++) {
    3dda:	45 85 e4             	test   %r12d,%r12d
    3ddd:	7e 77                	jle    3e56 <main+0x17a6>
    3ddf:	4d 63 e4             	movslq %r12d,%r12
    3de2:	4c 8d 2d f5 45 00 00 	lea    0x45f5(%rip),%r13        # 83de <_IO_stdin_used+0x3de>
    3de9:	4b 8d 04 e6          	lea    (%r14,%r12,8),%rax
    3ded:	4c 8d 25 2e 46 00 00 	lea    0x462e(%rip),%r12        # 8422 <_IO_stdin_used+0x422>
    3df4:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    char * c = calloc(250, sizeof(char));
    3df8:	be 01 00 00 00       	mov    $0x1,%esi
    3dfd:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3e02:	49 83 c6 08          	add    $0x8,%r14
    char * c = calloc(250, sizeof(char));
    3e06:	e8 15 e6 ff ff       	call   2420 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3e0b:	4c 89 e9             	mov    %r13,%rcx
    3e0e:	ba fa 00 00 00       	mov    $0xfa,%edx
    3e13:	be 01 00 00 00       	mov    $0x1,%esi
    3e18:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3e1b:	49 8b 46 f8          	mov    -0x8(%r14),%rax
    3e1f:	48 89 df             	mov    %rbx,%rdi
    3e22:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3e29:	31 c0                	xor    %eax,%eax
    3e2b:	e8 b0 e7 ff ff       	call   25e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3e30:	48 89 da             	mov    %rbx,%rdx
    3e33:	4c 89 e6             	mov    %r12,%rsi
    3e36:	bf 01 00 00 00       	mov    $0x1,%edi
    3e3b:	31 c0                	xor    %eax,%eax
    3e3d:	e8 9e e6 ff ff       	call   24e0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3e42:	4c 89 fe             	mov    %r15,%rsi
    3e45:	48 89 df             	mov    %rbx,%rdi
    3e48:	e8 93 e5 ff ff       	call   23e0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3e4d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    3e51:	49 39 c6             	cmp    %rax,%r14
    3e54:	75 a2                	jne    3df8 <main+0x1748>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    3e56:	4c 89 ff             	mov    %r15,%rdi
    3e59:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    3e5f:	31 db                	xor    %ebx,%ebx
  fclose(m2);
    3e61:	e8 1a e5 ff ff       	call   2380 <fclose@plt>
  long sents = 0;
    3e66:	48 c7 45 98 00 00 00 00 	movq   $0x0,-0x68(%rbp)
  long sends = 0;
    3e6e:	48 c7 45 a0 00 00 00 00 	movq   $0x0,-0x60(%rbp)
  long ingests = 0;
    3e76:	48 c7 45 a8 00 00 00 00 	movq   $0x0,-0x58(%rbp)
  long total = 0;
    3e7e:	48 c7 45 90 00 00 00 00 	movq   $0x0,-0x70(%rbp)
  int datas2_size = 0; 
    3e86:	48 8b 85 28 ff ff ff 	mov    -0xd8(%rbp),%rax
    3e8d:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    3e92:	4c 8b b5 18 ff ff ff 	mov    -0xe8(%rbp),%r14
    3e99:	45 89 e5             	mov    %r12d,%r13d
    3e9c:	44 89 85 78 ff ff ff 	mov    %r8d,-0x88(%rbp)
    3ea3:	48 89 45 80          	mov    %rax,-0x80(%rbp)
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
    3ea7:	44 89 e8             	mov    %r13d,%eax
    3eaa:	41 83 c5 01          	add    $0x1,%r13d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3eae:	bf 0a 00 00 00       	mov    $0xa,%edi
      long v = 0;
      
      int other = -1;
      int me = x;
      if (x % 2 == 1) {
        other = abs(x - 1) % total_threads;
    3eb3:	41 f6 c5 01          	test   $0x1,%r13b
    3eb7:	8d 50 02             	lea    0x2(%rax),%edx
    3eba:	0f 44 c2             	cmove  %edx,%eax
    3ebd:	4c 63 e0             	movslq %eax,%r12
    3ec0:	e8 6b e4 ff ff       	call   2330 <putchar@plt>
    3ec5:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    3ec9:	bf 01 00 00 00       	mov    $0x1,%edi
    3ece:	48 8d 35 6f 46 00 00 	lea    0x466f(%rip),%rsi        # 8544 <_IO_stdin_used+0x544>
    3ed5:	48 8b 10             	mov    (%rax),%rdx
    3ed8:	31 c0                	xor    %eax,%eax
    3eda:	e8 01 e6 ff ff       	call   24e0 <__printf_chk@plt>
        other = (x + 1) % total_threads;
      }
      printf("\n");
      printf("Total Protected %ld\n", protected_state[me].protected);

      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3edf:	41 8b 56 40          	mov    0x40(%r14),%edx
    3ee3:	85 d2                	test   %edx,%edx
    3ee5:	0f 8e 1d 05 00 00    	jle    4408 <main+0x1d58>
    3eeb:	48 63 ca             	movslq %edx,%rcx
    3eee:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    3ef2:	31 d2                	xor    %edx,%edx
    3ef4:	48 c1 e1 09          	shl    $0x9,%rcx
    3ef8:	48 01 c1             	add    %rax,%rcx
    3efb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3f00:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3f07:	48 05 00 02 00 00    	add    $0x200,%rax
    3f0d:	48 39 c8             	cmp    %rcx,%rax
    3f10:	75 ee                	jne    3f00 <main+0x1850>
      }
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3f12:	4a 8d 04 e5 00 00 00 00 	lea    0x0(,%r12,8),%rax
    3f1a:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
    3f1e:	4c 29 e0             	sub    %r12,%rax
    3f21:	48 c1 e0 05          	shl    $0x5,%rax
    3f25:	48 01 f8             	add    %rdi,%rax
    3f28:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3f2c:	85 c9                	test   %ecx,%ecx
    3f2e:	7e 22                	jle    3f52 <main+0x18a2>
    3f30:	48 8b 40 38          	mov    0x38(%rax),%rax
    3f34:	48 c1 e1 09          	shl    $0x9,%rcx
    3f38:	48 01 c1             	add    %rax,%rcx
    3f3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3f40:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3f47:	48 05 00 02 00 00    	add    $0x200,%rax
    3f4d:	48 39 c8             	cmp    %rcx,%rax
    3f50:	75 ee                	jne    3f40 <main+0x1890>
    3f52:	48 8d 35 00 46 00 00 	lea    0x4600(%rip),%rsi        # 8559 <_IO_stdin_used+0x559>
    3f59:	bf 01 00 00 00       	mov    $0x1,%edi
    3f5e:	31 c0                	xor    %eax,%eax
    3f60:	e8 7b e5 ff ff       	call   24e0 <__printf_chk@plt>
      }
      printf("Total V %ld\n", v);
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3f65:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    3f69:	bf 01 00 00 00       	mov    $0x1,%edi
    3f6e:	48 8d 35 b3 48 00 00 	lea    0x48b3(%rip),%rsi        # 8828 <_IO_stdin_used+0x828>
    3f75:	48 8b 08             	mov    (%rax),%rcx
    3f78:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3f82:	48 f7 e9             	imul   %rcx
    3f85:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3f89:	31 c0                	xor    %eax,%eax
    3f8b:	48 d1 fa             	sar    %rdx
    3f8e:	48 29 ca             	sub    %rcx,%rdx
    3f91:	e8 4a e5 ff ff       	call   24e0 <__printf_chk@plt>
    3f96:	bf 0a 00 00 00       	mov    $0xa,%edi
    3f9b:	e8 90 e3 ff ff       	call   2330 <putchar@plt>
      printf("\n");
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3fa0:	45 8b 66 40          	mov    0x40(%r14),%r12d
    3fa4:	45 85 e4             	test   %r12d,%r12d
    3fa7:	0f 8e 2d 01 00 00    	jle    40da <main+0x1a2a>
    3fad:	4c 8b 55 90          	mov    -0x70(%rbp),%r10
    3fb1:	48 8b 4d a8          	mov    -0x58(%rbp),%rcx
    3fb5:	44 89 6d b8          	mov    %r13d,-0x48(%rbp)
    3fb9:	31 d2                	xor    %edx,%edx
    3fbb:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
    3fbf:	4c 8b 7d 98          	mov    -0x68(%rbp),%r15
    3fc3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        total += thread_data[x].tasks[n].n;
    3fc8:	49 8b 46 38          	mov    0x38(%r14),%rax
    3fcc:	49 89 d1             	mov    %rdx,%r9
        ingests += thread_data[x].tasks[n].ingest_count;
        sends += thread_data[x].tasks[n].sends;
    3fcf:	48 89 55 90          	mov    %rdx,-0x70(%rbp)
    3fd3:	41 89 d5             	mov    %edx,%r13d
        total += thread_data[x].tasks[n].n;
    3fd6:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    3fda:	45 31 e4             	xor    %r12d,%r12d
        total += thread_data[x].tasks[n].n;
    3fdd:	4c 01 c8             	add    %r9,%rax
        sends += thread_data[x].tasks[n].sends;
    3fe0:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
        total += thread_data[x].tasks[n].n;
    3fe4:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
        ingests += thread_data[x].tasks[n].ingest_count;
    3feb:	48 03 88 68 01 00 00 	add    0x168(%rax),%rcx
        sends += thread_data[x].tasks[n].sends;
    3ff2:	48 03 b0 78 01 00 00 	add    0x178(%rax),%rsi
    3ff9:	4c 89 55 a8          	mov    %r10,-0x58(%rbp)
    3ffd:	48 89 4d a0          	mov    %rcx,-0x60(%rbp)
    4001:	48 89 75 98          	mov    %rsi,-0x68(%rbp)
    4005:	0f 1f 00             	nopl   (%rax)
    4008:	8b 55 b8             	mov    -0x48(%rbp),%edx
    400b:	45 89 e0             	mov    %r12d,%r8d
    400e:	44 89 e9             	mov    %r13d,%ecx
    4011:	48 8d 35 4e 45 00 00 	lea    0x454e(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    4018:	bf 01 00 00 00       	mov    $0x1,%edi
    401d:	31 c0                	xor    %eax,%eax
    401f:	e8 bc e4 ff ff       	call   24e0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          printf("combo %d %d %d\n", x, n, kk);
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4024:	49 8b 56 38          	mov    0x38(%r14),%rdx
    4028:	48 8b 7d b0          	mov    -0x50(%rbp),%rdi
    402c:	45 89 e0             	mov    %r12d,%r8d
    402f:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
    4033:	48 83 ec 08          	sub    $0x8,%rsp
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    4037:	49 83 c4 01          	add    $0x1,%r12
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    403b:	48 c1 e0 07          	shl    $0x7,%rax
    403f:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    4047:	48 8b 38             	mov    (%rax),%rdi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    404a:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi

          long tempsent = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4051:	48 8b 87 10 03 00 00 	mov    0x310(%rdi),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4058:	48 8b 96 08 03 00 00 	mov    0x308(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    405f:	48 8b b6 10 03 00 00 	mov    0x310(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4066:	48 8b 8f 08 03 00 00 	mov    0x308(%rdi),%rcx
    406d:	bf 01 00 00 00       	mov    $0x1,%edi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    4072:	48 01 c3             	add    %rax,%rbx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4075:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4078:	49 01 cf             	add    %rcx,%r15
    407b:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    407f:	48 01 f3             	add    %rsi,%rbx
    4082:	50                   	push   %rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4083:	49 01 d7             	add    %rdx,%r15
    4086:	8b 55 b8             	mov    -0x48(%rbp),%edx
    4089:	44 89 e9             	mov    %r13d,%ecx
    408c:	48 8d 35 b5 47 00 00 	lea    0x47b5(%rip),%rsi        # 8848 <_IO_stdin_used+0x848>
    4093:	31 c0                	xor    %eax,%eax
    4095:	e8 46 e4 ff ff       	call   24e0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    409a:	41 5a                	pop    %r10
    409c:	41 5b                	pop    %r11
    409e:	49 83 fc 06          	cmp    $0x6,%r12
    40a2:	0f 85 60 ff ff ff    	jne    4008 <main+0x1958>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    40a8:	48 8b 55 90          	mov    -0x70(%rbp),%rdx
    40ac:	4c 8b 55 a8          	mov    -0x58(%rbp),%r10
    40b0:	48 8b 4d a0          	mov    -0x60(%rbp),%rcx
    40b4:	48 8b 75 98          	mov    -0x68(%rbp),%rsi
    40b8:	48 83 c2 01          	add    $0x1,%rdx
    40bc:	41 39 56 40          	cmp    %edx,0x40(%r14)
    40c0:	0f 8f 02 ff ff ff    	jg     3fc8 <main+0x1918>
    40c6:	4c 89 55 90          	mov    %r10,-0x70(%rbp)
    40ca:	44 8b 6d b8          	mov    -0x48(%rbp),%r13d
    40ce:	48 89 4d a8          	mov    %rcx,-0x58(%rbp)
    40d2:	48 89 75 a0          	mov    %rsi,-0x60(%rbp)
    40d6:	4c 89 7d 98          	mov    %r15,-0x68(%rbp)
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        // printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
        // printf("%ld iterations\n", thread_data[x].iteration_count);
      }
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    40da:	45 31 ff             	xor    %r15d,%r15d
    40dd:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    40e5:	4c 8d 25 7c 47 00 00 	lea    0x477c(%rip),%r12        # 8868 <_IO_stdin_used+0x868>
    40ec:	7e 61                	jle    414f <main+0x1a9f>
    40ee:	66 90                	xchg   %ax,%ax
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    40f0:	49 8b 86 90 00 00 00 	mov    0x90(%r14),%rax
    40f7:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    40fb:	48 83 ec 08          	sub    $0x8,%rsp
    40ff:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    4104:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4108:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    410c:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    4116:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    411a:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    411e:	48 f7 e6             	mul    %rsi
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4121:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    4125:	4c 2b 01             	sub    (%rcx),%r8
    4128:	31 c0                	xor    %eax,%eax
    412a:	8b 49 20             	mov    0x20(%rcx),%ecx
    412d:	56                   	push   %rsi
    412e:	4c 89 e6             	mov    %r12,%rsi
    4131:	48 c1 ea 12          	shr    $0x12,%rdx
    4135:	49 89 d1             	mov    %rdx,%r9
    4138:	ba 02 00 00 00       	mov    $0x2,%edx
    413d:	e8 9e e3 ff ff       	call   24e0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    4142:	41 58                	pop    %r8
    4144:	41 59                	pop    %r9
    4146:	4d 39 be a0 00 00 00 	cmp    %r15,0xa0(%r14)
    414d:	7f a1                	jg     40f0 <main+0x1a40>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    414f:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    4156:	85 d2                	test   %edx,%edx
    4158:	0f 8e 14 01 00 00    	jle    4272 <main+0x1bc2>
    415e:	48 89 9d 70 ff ff ff 	mov    %rbx,-0x90(%rbp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4165:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4169:	45 31 ff             	xor    %r15d,%r15d
    416c:	44 89 ad 68 ff ff ff 	mov    %r13d,-0x98(%rbp)
    4173:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4178:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    417c:	44 89 fb             	mov    %r15d,%ebx
    417f:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    4187:	8b 30                	mov    (%rax),%esi
    4189:	85 f6                	test   %esi,%esi
    418b:	0f 8e c6 00 00 00    	jle    4257 <main+0x1ba7>
    4191:	4c 89 7d b0          	mov    %r15,-0x50(%rbp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    4195:	31 d2                	xor    %edx,%edx
    4197:	48 8b 48 08          	mov    0x8(%rax),%rcx
    419b:	49 89 f8             	mov    %rdi,%r8
    419e:	48 89 d7             	mov    %rdx,%rdi
    41a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    41a8:	49 89 fc             	mov    %rdi,%r12
    41ab:	45 31 ff             	xor    %r15d,%r15d
    41ae:	49 c1 e4 08          	shl    $0x8,%r12
    41b2:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    41b6:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    41bc:	85 d2                	test   %edx,%edx
    41be:	7e 7d                	jle    423d <main+0x1b8d>
    41c0:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)
    41c4:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    41c8:	4c 89 f9             	mov    %r15,%rcx
    41cb:	48 83 ec 08          	sub    $0x8,%rsp
    41cf:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    41d4:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    41d8:	48 c1 e1 05          	shl    $0x5,%rcx
    41dc:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    41e3:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    41ed:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    41f1:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    41f5:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    41f8:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    41fc:	4c 2b 01             	sub    (%rcx),%r8
    41ff:	56                   	push   %rsi
    4200:	89 d9                	mov    %ebx,%ecx
    4202:	48 8d 35 af 46 00 00 	lea    0x46af(%rip),%rsi        # 88b8 <_IO_stdin_used+0x8b8>
    4209:	31 c0                	xor    %eax,%eax
    420b:	48 c1 ea 12          	shr    $0x12,%rdx
    420f:	49 89 d1             	mov    %rdx,%r9
    4212:	ba 02 00 00 00       	mov    $0x2,%edx
    4217:	e8 c4 e2 ff ff       	call   24e0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    421c:	4d 8b 46 50          	mov    0x50(%r14),%r8
    4220:	5e                   	pop    %rsi
    4221:	5f                   	pop    %rdi
    4222:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    4226:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    422a:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    422e:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    4235:	7f 91                	jg     41c8 <main+0x1b18>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4237:	48 8b 7d b8          	mov    -0x48(%rbp),%rdi
    423b:	8b 32                	mov    (%rdx),%esi
    423d:	48 83 c7 01          	add    $0x1,%rdi
    4241:	39 fe                	cmp    %edi,%esi
    4243:	0f 8f 5f ff ff ff    	jg     41a8 <main+0x1af8>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4249:	4c 8b 7d b0          	mov    -0x50(%rbp),%r15
    424d:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    4254:	4c 89 c7             	mov    %r8,%rdi
    4257:	49 83 c7 01          	add    $0x1,%r15
    425b:	44 39 fa             	cmp    %r15d,%edx
    425e:	0f 8f 14 ff ff ff    	jg     4178 <main+0x1ac8>
    4264:	48 8b 9d 70 ff ff ff 	mov    -0x90(%rbp),%rbx
    426b:	44 8b ad 68 ff ff ff 	mov    -0x98(%rbp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    4272:	48 83 45 80 18       	addq   $0x18,-0x80(%rbp)
    4277:	49 81 c6 e0 00 00 00 	add    $0xe0,%r14
    427e:	44 39 ad 78 ff ff ff 	cmp    %r13d,-0x88(%rbp)
    4285:	0f 85 1c fc ff ff    	jne    3ea7 <main+0x17f7>
  for (int k = 0 ; k < group_count ; k++) {
    428b:	44 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%r8d
    4292:	48 83 85 28 ff ff ff 30 	addq   $0x30,-0xd8(%rbp)
    429a:	48 81 85 18 ff ff ff c0 01 00 00 	addq   $0x1c0,-0xe8(%rbp)
    42a5:	41 83 f8 05          	cmp    $0x5,%r8d
    42a9:	74 08                	je     42b3 <main+0x1c03>
    42ab:	45 89 c4             	mov    %r8d,%r12d
    42ae:	e9 d3 fb ff ff       	jmp    3e86 <main+0x17d6>
    42b3:	4c 8b 75 90          	mov    -0x70(%rbp),%r14
    42b7:	48 8d 35 b8 42 00 00 	lea    0x42b8(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    42be:	31 c0                	xor    %eax,%eax
    42c0:	49 89 df             	mov    %rbx,%r15
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    42c3:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    42cd:	bf 01 00 00 00       	mov    $0x1,%edi
    42d2:	4c 89 f2             	mov    %r14,%rdx
    42d5:	e8 06 e2 ff ff       	call   24e0 <__printf_chk@plt>
    42da:	bf 0a 00 00 00       	mov    $0xa,%edi
    42df:	e8 4c e0 ff ff       	call   2330 <putchar@plt>
    42e4:	48 8b bd 20 ff ff ff 	mov    -0xe0(%rbp),%rdi
    42eb:	48 8d 35 1e 46 00 00 	lea    0x461e(%rip),%rsi        # 8910 <_IO_stdin_used+0x910>
    42f2:	31 c0                	xor    %eax,%eax
    42f4:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    42f8:	bf 01 00 00 00       	mov    $0x1,%edi
    42fd:	e8 de e1 ff ff       	call   24e0 <__printf_chk@plt>
    4302:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
    4306:	48 8b 7d a8          	mov    -0x58(%rbp),%rdi
    430a:	48 8d 35 27 46 00 00 	lea    0x4627(%rip),%rsi        # 8938 <_IO_stdin_used+0x938>
    4311:	48 f7 eb             	imul   %rbx
    4314:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4318:	31 c0                	xor    %eax,%eax
    431a:	48 d1 fa             	sar    %rdx
    431d:	48 29 fa             	sub    %rdi,%rdx
    4320:	bf 01 00 00 00       	mov    $0x1,%edi
    4325:	e8 b6 e1 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    432a:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
    432e:	48 8b 7d a0          	mov    -0x60(%rbp),%rdi
    4332:	48 8d 35 2f 46 00 00 	lea    0x462f(%rip),%rsi        # 8968 <_IO_stdin_used+0x968>
    4339:	48 f7 eb             	imul   %rbx
    433c:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4340:	31 c0                	xor    %eax,%eax
    4342:	48 d1 fa             	sar    %rdx
    4345:	48 29 fa             	sub    %rdi,%rdx
    4348:	bf 01 00 00 00       	mov    $0x1,%edi
    434d:	e8 8e e1 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    4352:	4c 89 f0             	mov    %r14,%rax
    4355:	bf 01 00 00 00       	mov    $0x1,%edi
    435a:	48 8d 35 37 46 00 00 	lea    0x4637(%rip),%rsi        # 8998 <_IO_stdin_used+0x998>
    4361:	48 f7 eb             	imul   %rbx
    4364:	4c 89 f0             	mov    %r14,%rax
    4367:	48 c1 f8 3f          	sar    $0x3f,%rax
    436b:	48 d1 fa             	sar    %rdx
    436e:	48 29 c2             	sub    %rax,%rdx
    4371:	31 c0                	xor    %eax,%eax
    4373:	e8 68 e1 ff ff       	call   24e0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    4378:	48 8b 45 98          	mov    -0x68(%rbp),%rax
    437c:	bf 01 00 00 00       	mov    $0x1,%edi
    4381:	48 8d 35 02 42 00 00 	lea    0x4202(%rip),%rsi        # 858a <_IO_stdin_used+0x58a>
    4388:	48 f7 eb             	imul   %rbx
    438b:	48 8b 45 98          	mov    -0x68(%rbp),%rax
    438f:	48 c1 f8 3f          	sar    $0x3f,%rax
    4393:	48 d1 fa             	sar    %rdx
    4396:	48 29 c2             	sub    %rax,%rdx
    4399:	31 c0                	xor    %eax,%eax
    439b:	49 89 d4             	mov    %rdx,%r12
    439e:	e8 3d e1 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
    43a3:	4c 89 f8             	mov    %r15,%rax
    43a6:	bf 01 00 00 00       	mov    $0x1,%edi
    43ab:	48 8d 35 06 46 00 00 	lea    0x4606(%rip),%rsi        # 89b8 <_IO_stdin_used+0x9b8>
    43b2:	48 f7 eb             	imul   %rbx
    43b5:	4c 89 f8             	mov    %r15,%rax
    43b8:	48 c1 f8 3f          	sar    $0x3f,%rax
    43bc:	48 89 d3             	mov    %rdx,%rbx
    43bf:	48 d1 fb             	sar    %rbx
    43c2:	48 29 c3             	sub    %rax,%rbx
    43c5:	31 c0                	xor    %eax,%eax
    43c7:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    43ca:	4c 29 e3             	sub    %r12,%rbx
    43cd:	e8 0e e1 ff ff       	call   24e0 <__printf_chk@plt>
    43d2:	31 c0                	xor    %eax,%eax
    43d4:	48 89 da             	mov    %rbx,%rdx
    43d7:	bf 01 00 00 00       	mov    $0x1,%edi
    43dc:	48 8d 35 c3 41 00 00 	lea    0x41c3(%rip),%rsi        # 85a6 <_IO_stdin_used+0x5a6>
    43e3:	e8 f8 e0 ff ff       	call   24e0 <__printf_chk@plt>
  return 0;

}
    43e8:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    43ec:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    43f5:	75 22                	jne    4419 <main+0x1d69>
    43f7:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    43fb:	31 c0                	xor    %eax,%eax
    43fd:	5b                   	pop    %rbx
    43fe:	41 5c                	pop    %r12
    4400:	41 5d                	pop    %r13
    4402:	41 5e                	pop    %r14
    4404:	41 5f                	pop    %r15
    4406:	5d                   	pop    %rbp
    4407:	c3                   	ret
      long v = 0;
    4408:	31 d2                	xor    %edx,%edx
    440a:	e9 03 fb ff ff       	jmp    3f12 <main+0x1862>
            exit(1);
    440f:	bf 01 00 00 00       	mov    $0x1,%edi
    4414:	e8 37 e1 ff ff       	call   2550 <exit@plt>
}
    4419:	e8 82 df ff ff       	call   23a0 <__stack_chk_fail@plt>
    441e:	66 90                	xchg   %ax,%ax

0000000000004420 <_start>:
    4420:	f3 0f 1e fa          	endbr64
    4424:	31 ed                	xor    %ebp,%ebp
    4426:	49 89 d1             	mov    %rdx,%r9
    4429:	5e                   	pop    %rsi
    442a:	48 89 e2             	mov    %rsp,%rdx
    442d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4431:	50                   	push   %rax
    4432:	54                   	push   %rsp
    4433:	45 31 c0             	xor    %r8d,%r8d
    4436:	31 c9                	xor    %ecx,%ecx
    4438:	48 8d 3d 71 e2 ff ff 	lea    -0x1d8f(%rip),%rdi        # 26b0 <main>
    443f:	ff 15 8b 6b 00 00    	call   *0x6b8b(%rip)        # afd0 <__libc_start_main@GLIBC_2.34>
    4445:	f4                   	hlt
    4446:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004450 <__gmon_start__>:
    4450:	f3 0f 1e fa          	endbr64
    4454:	8b 05 ce 6b 00 00    	mov    0x6bce(%rip),%eax        # b028 <called.0>
    445a:	85 c0                	test   %eax,%eax
    445c:	74 02                	je     4460 <__gmon_start__+0x10>
    445e:	c3                   	ret
    445f:	90                   	nop
    4460:	48 83 ec 08          	sub    $0x8,%rsp
    4464:	48 8d 35 92 32 00 00 	lea    0x3292(%rip),%rsi        # 76fd <etext>
    446b:	48 8d 3d 8e bb ff ff 	lea    -0x4472(%rip),%rdi        # 0 <__executable_start>
    4472:	c7 05 ac 6b 00 00 01 00 00 00 	movl   $0x1,0x6bac(%rip)        # b028 <called.0>
    447c:	e8 bf df ff ff       	call   2440 <__monstartup@plt>
    4481:	48 8b 3d 58 6b 00 00 	mov    0x6b58(%rip),%rdi        # afe0 <_mcleanup@GLIBC_2.2.5>
    4488:	48 83 c4 08          	add    $0x8,%rsp
    448c:	e9 2f 32 00 00       	jmp    76c0 <atexit>
    4491:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    449b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000044a0 <_dl_relocate_static_pie>:
    44a0:	f3 0f 1e fa          	endbr64
    44a4:	c3                   	ret
    44a5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    44af:	90                   	nop

00000000000044b0 <deregister_tm_clones>:
    44b0:	48 8d 3d 69 6b 00 00 	lea    0x6b69(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    44b7:	48 8d 05 62 6b 00 00 	lea    0x6b62(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    44be:	48 39 f8             	cmp    %rdi,%rax
    44c1:	74 15                	je     44d8 <deregister_tm_clones+0x28>
    44c3:	48 8b 05 0e 6b 00 00 	mov    0x6b0e(%rip),%rax        # afd8 <_ITM_deregisterTMCloneTable@Base>
    44ca:	48 85 c0             	test   %rax,%rax
    44cd:	74 09                	je     44d8 <deregister_tm_clones+0x28>
    44cf:	ff e0                	jmp    *%rax
    44d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    44d8:	c3                   	ret
    44d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044e0 <register_tm_clones>:
    44e0:	48 8d 3d 39 6b 00 00 	lea    0x6b39(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    44e7:	48 8d 35 32 6b 00 00 	lea    0x6b32(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    44ee:	48 29 fe             	sub    %rdi,%rsi
    44f1:	48 89 f0             	mov    %rsi,%rax
    44f4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    44f8:	48 c1 f8 03          	sar    $0x3,%rax
    44fc:	48 01 c6             	add    %rax,%rsi
    44ff:	48 d1 fe             	sar    %rsi
    4502:	74 14                	je     4518 <register_tm_clones+0x38>
    4504:	48 8b 05 e5 6a 00 00 	mov    0x6ae5(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    450b:	48 85 c0             	test   %rax,%rax
    450e:	74 08                	je     4518 <register_tm_clones+0x38>
    4510:	ff e0                	jmp    *%rax
    4512:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4518:	c3                   	ret
    4519:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004520 <__do_global_dtors_aux>:
    4520:	f3 0f 1e fa          	endbr64
    4524:	80 3d 01 6b 00 00 00 	cmpb   $0x0,0x6b01(%rip)        # b02c <completed.0>
    452b:	75 2b                	jne    4558 <__do_global_dtors_aux+0x38>
    452d:	55                   	push   %rbp
    452e:	48 83 3d c2 6a 00 00 00 	cmpq   $0x0,0x6ac2(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    4536:	48 89 e5             	mov    %rsp,%rbp
    4539:	74 0c                	je     4547 <__do_global_dtors_aux+0x27>
    453b:	48 8b 3d c6 6a 00 00 	mov    0x6ac6(%rip),%rdi        # b008 <__dso_handle>
    4542:	e8 c9 dd ff ff       	call   2310 <__cxa_finalize@plt>
    4547:	e8 64 ff ff ff       	call   44b0 <deregister_tm_clones>
    454c:	c6 05 d9 6a 00 00 01 	movb   $0x1,0x6ad9(%rip)        # b02c <completed.0>
    4553:	5d                   	pop    %rbp
    4554:	c3                   	ret
    4555:	0f 1f 00             	nopl   (%rax)
    4558:	c3                   	ret
    4559:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004560 <frame_dummy>:
    4560:	f3 0f 1e fa          	endbr64
    4564:	e9 77 ff ff ff       	jmp    44e0 <register_tm_clones>
    4569:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004570 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4570:	f3 0f 1e fa          	endbr64
    4574:	55                   	push   %rbp
    4575:	48 89 e5             	mov    %rsp,%rbp
    4578:	ff 15 6a 6a 00 00    	call   *0x6a6a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  struct ProtectedState *protected = data->thread->protected_state;
    457e:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4585:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    4589:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4591:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    4595:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    4599:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    45a0:	48 85 c9             	test   %rcx,%rcx
    45a3:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    45aa:	48 0f 4f d6          	cmovg  %rsi,%rdx
    45ae:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    45b2:	31 c0                	xor    %eax,%eax
    45b4:	5d                   	pop    %rbp
    45b5:	c3                   	ret
    45b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000045c0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	55                   	push   %rbp
    45c5:	48 89 e5             	mov    %rsp,%rbp
    45c8:	ff 15 1a 6a 00 00    	call   *0x6a1a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    for (int x = 0 ; x < data->task_count ; x++) {
    45ce:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    45d5:	85 c9                	test   %ecx,%ecx
    45d7:	7e 4d                	jle    4626 <barriered_reset+0x66>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    45d9:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    45e0:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    45e7:	48 c1 e1 09          	shl    $0x9,%rcx
    45eb:	48 8b 50 18          	mov    0x18(%rax),%rdx
    45ef:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    45f3:	48 8b 70 38          	mov    0x38(%rax),%rsi
    45f7:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    45f9:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    45fd:	0f 1f 00             	nopl   (%rax)
    4600:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4608:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4610:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    461b:	48 05 00 02 00 00    	add    $0x200,%rax
    4621:	48 39 c1             	cmp    %rax,%rcx
    4624:	75 da                	jne    4600 <barriered_reset+0x40>
  asm volatile ("sfence" ::: "memory");
    4626:	0f ae f8             	sfence
}
    4629:	31 c0                	xor    %eax,%eax
    462b:	5d                   	pop    %rbp
    462c:	c3                   	ret
    462d:	0f 1f 00             	nopl   (%rax)

0000000000004630 <external_thread>:
void * external_thread(void *arg) {
    4630:	f3 0f 1e fa          	endbr64
    4634:	55                   	push   %rbp
    4635:	48 89 e5             	mov    %rsp,%rbp
    4638:	41 57                	push   %r15
    463a:	41 56                	push   %r14
    463c:	41 55                	push   %r13
    463e:	41 54                	push   %r12
    4640:	53                   	push   %rbx
    4641:	48 83 ec 08          	sub    $0x8,%rsp
    4645:	ff 15 9d 69 00 00    	call   *0x699d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  while (data->running == 1) {
    464b:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
void * external_thread(void *arg) {
    464f:	49 89 fe             	mov    %rdi,%r14
  while (data->running == 1) {
    4652:	75 6b                	jne    46bf <external_thread+0x8f>
    for (int b = 0; b < data->buffers_count; b++) {
    4654:	8b b7 bc 00 00 00    	mov    0xbc(%rdi),%esi
    465a:	4c 8b 47 50          	mov    0x50(%rdi),%r8
    465e:	66 90                	xchg   %ax,%ax
    4660:	85 f6                	test   %esi,%esi
    4662:	7e 6c                	jle    46d0 <external_thread+0xa0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4664:	45 31 ed             	xor    %r13d,%r13d
    4667:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4670:	4e 8d 3c ed 00 00 00 00 	lea    0x0(,%r13,8),%r15
    4678:	31 db                	xor    %ebx,%ebx
    467a:	4b 8d 3c 38          	lea    (%r8,%r15,1),%rdi
    467e:	48 8b 07             	mov    (%rdi),%rax
    4681:	8b 10                	mov    (%rax),%edx
    4683:	85 d2                	test   %edx,%edx
    4685:	7e 28                	jle    46af <external_thread+0x7f>
    4687:	48 8b 70 08          	mov    0x8(%rax),%rsi
				if (data->buffers[b]->buffer[x].available == 0) {
    468b:	49 89 dc             	mov    %rbx,%r12
    468e:	49 c1 e4 08          	shl    $0x8,%r12
    4692:	4a 8d 04 26          	lea    (%rsi,%r12,1),%rax
    4696:	8b 88 80 00 00 00    	mov    0x80(%rax),%ecx
    469c:	85 c9                	test   %ecx,%ecx
    469e:	74 38                	je     46d8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    46a0:	48 83 c3 01          	add    $0x1,%rbx
    46a4:	39 da                	cmp    %ebx,%edx
    46a6:	7f e3                	jg     468b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    46a8:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    46af:	49 83 c5 01          	add    $0x1,%r13
    46b3:	44 39 ee             	cmp    %r13d,%esi
    46b6:	7f b8                	jg     4670 <external_thread+0x40>
  while (data->running == 1) {
    46b8:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    46bd:	74 a1                	je     4660 <external_thread+0x30>
}
    46bf:	48 83 c4 08          	add    $0x8,%rsp
    46c3:	31 c0                	xor    %eax,%eax
    46c5:	5b                   	pop    %rbx
    46c6:	41 5c                	pop    %r12
    46c8:	41 5d                	pop    %r13
    46ca:	41 5e                	pop    %r14
    46cc:	41 5f                	pop    %r15
    46ce:	5d                   	pop    %rbp
    46cf:	c3                   	ret
  while (data->running == 1) {
    46d0:	eb fe                	jmp    46d0 <external_thread+0xa0>
    46d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    46d8:	48 8d 0d 25 39 00 00 	lea    0x3925(%rip),%rcx        # 8004 <_IO_stdin_used+0x4>
    46df:	48 89 08             	mov    %rcx,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    46e2:	48 8b 07             	mov    (%rdi),%rax
    46e5:	bf 04 00 00 00       	mov    $0x4,%edi
    46ea:	48 8b 48 08          	mov    0x8(%rax),%rcx
    46ee:	4c 01 e1             	add    %r12,%rcx
    46f1:	48 63 b1 94 00 00 00 	movslq 0x94(%rcx),%rsi
    46f8:	48 c1 e6 05          	shl    $0x5,%rsi
    46fc:	48 03 b1 88 00 00 00 	add    0x88(%rcx),%rsi
    4703:	e8 68 dc ff ff       	call   2370 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4708:	49 8b 46 50          	mov    0x50(%r14),%rax
    470c:	4a 8b 04 38          	mov    (%rax,%r15,1),%rax
    4710:	48 8b 40 08          	mov    0x8(%rax),%rax
    4714:	42 c7 84 20 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%r12,1)
          asm volatile ("sfence" ::: "memory");
    4720:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4723:	4d 8b 46 50          	mov    0x50(%r14),%r8
    4727:	48 83 c3 01          	add    $0x1,%rbx
    472b:	4b 8d 3c 38          	lea    (%r8,%r15,1),%rdi
    472f:	48 8b 07             	mov    (%rdi),%rax
    4732:	8b 10                	mov    (%rax),%edx
    4734:	39 da                	cmp    %ebx,%edx
    4736:	0f 8f 4b ff ff ff    	jg     4687 <external_thread+0x57>
    473c:	e9 67 ff ff ff       	jmp    46a8 <external_thread+0x78>
    4741:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    474c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004750 <timer_thread>:
void* timer_thread(void *arg) {
    4750:	f3 0f 1e fa          	endbr64
    4754:	55                   	push   %rbp
    4755:	48 89 e5             	mov    %rsp,%rbp
    4758:	41 57                	push   %r15
    475a:	41 56                	push   %r14
    475c:	41 55                	push   %r13
    475e:	41 54                	push   %r12
    4760:	53                   	push   %rbx
    4761:	48 83 ec 68          	sub    $0x68,%rsp
    4765:	ff 15 7d 68 00 00    	call   *0x687d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    476b:	48 8d 35 9e 38 00 00 	lea    0x389e(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    4772:	8b 57 04             	mov    0x4(%rdi),%edx
    4775:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    477e:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    4782:	31 c0                	xor    %eax,%eax
    4784:	49 89 ff             	mov    %rdi,%r15
    4787:	bf 01 00 00 00       	mov    $0x1,%edi
    478c:	e8 4f dd ff ff       	call   24e0 <__printf_chk@plt>
  struct timespec preempt = {
    4791:	66 0f 6f 05 37 44 00 00 	movdqa 0x4437(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4799:	ba 88 13 00 00       	mov    $0x1388,%edx
    479e:	31 c0                	xor    %eax,%eax
    47a0:	48 8d 35 7b 38 00 00 	lea    0x387b(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    47a7:	bf 01 00 00 00       	mov    $0x1,%edi
    47ac:	0f 29 45 90          	movaps %xmm0,-0x70(%rbp)
    47b0:	e8 2b dd ff ff       	call   24e0 <__printf_chk@plt>
  while (data->running && n < times) {
    47b5:	41 8b 5f 44          	mov    0x44(%r15),%ebx
    47b9:	85 db                	test   %ebx,%ebx
    47bb:	0f 84 9d 00 00 00    	je     485e <timer_thread+0x10e>
  int n = 0;
    47c1:	45 31 e4             	xor    %r12d,%r12d
    47c4:	4c 8d 75 80          	lea    -0x80(%rbp),%r14
    47c8:	4c 8d 6d 90          	lea    -0x70(%rbp),%r13
  int y = 0;
    47cc:	31 db                	xor    %ebx,%ebx
    nanosleep(&preempt , &rem2);
    47ce:	4c 89 ef             	mov    %r13,%rdi
    47d1:	4c 89 f6             	mov    %r14,%rsi
    n++;
    47d4:	41 83 c4 01          	add    $0x1,%r12d
    nanosleep(&preempt , &rem2);
    47d8:	e8 e3 db ff ff       	call   23c0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    47dd:	49 63 47 30          	movslq 0x30(%r15),%rax
    y++;
    47e1:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    47e4:	85 c0                	test   %eax,%eax
    47e6:	7e 4f                	jle    4837 <timer_thread+0xe7>
    47e8:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    47ec:	4c 63 c3             	movslq %ebx,%r8
    47ef:	49 c1 e0 09          	shl    $0x9,%r8
    47f3:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    47f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count - 1;
    4800:	48 8b 19             	mov    (%rcx),%rbx
    4803:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4805:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1;
    4809:	99                   	cltd
    480a:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    480d:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1;
    4811:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    4814:	48 63 d2             	movslq %edx,%rdx
    4817:	48 c1 e2 09          	shl    $0x9,%rdx
    481b:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4826:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4832:	49 39 c9             	cmp    %rcx,%r9
    4835:	75 c9                	jne    4800 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    4837:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    483a:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
    483e:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    y++;
    4842:	31 db                	xor    %ebx,%ebx
    if (y >= data->threads[0]->task_count) {
    4844:	48 8b 00             	mov    (%rax),%rax
    y++;
    4847:	39 78 40             	cmp    %edi,0x40(%rax)
    484a:	0f 4f df             	cmovg  %edi,%ebx
  while (data->running && n < times) {
    484d:	85 c9                	test   %ecx,%ecx
    484f:	74 0d                	je     485e <timer_thread+0x10e>
    4851:	41 81 fc 88 13 00 00 	cmp    $0x1388,%r12d
    4858:	0f 85 70 ff ff ff    	jne    47ce <timer_thread+0x7e>
    485e:	48 8d 3d d3 37 00 00 	lea    0x37d3(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    4865:	e8 e6 da ff ff       	call   2350 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    486a:	49 63 57 30          	movslq 0x30(%r15),%rdx
    486e:	85 d2                	test   %edx,%edx
    4870:	7e 73                	jle    48e5 <timer_thread+0x195>
    for (int y = 0 ; y < data->task_count ; y++) {
    4872:	49 63 47 40          	movslq 0x40(%r15),%rax
    4876:	85 c0                	test   %eax,%eax
    4878:	7e 6b                	jle    48e5 <timer_thread+0x195>
    487a:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    487e:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4882:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    488a:	31 c9                	xor    %ecx,%ecx
    488c:	48 89 c6             	mov    %rax,%rsi
    488f:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4893:	48 8b 40 38          	mov    0x38(%rax),%rax
    4897:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    489b:	f7 c6 00 02 00 00    	test   $0x200,%esi
    48a1:	74 1d                	je     48c0 <timer_thread+0x170>
    48a3:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    48ad:	48 05 00 02 00 00    	add    $0x200,%rax
    48b3:	48 39 c2             	cmp    %rax,%rdx
    48b6:	74 24                	je     48dc <timer_thread+0x18c>
    48b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    48c0:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    48ca:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    48d0:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    48d7:	48 39 c2             	cmp    %rax,%rdx
    48da:	75 e4                	jne    48c0 <timer_thread+0x170>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    48dc:	48 83 c1 08          	add    $0x8,%rcx
    48e0:	48 39 cf             	cmp    %rcx,%rdi
    48e3:	75 aa                	jne    488f <timer_thread+0x13f>
  asm volatile ("mfence" ::: "memory");
    48e5:	0f ae f0             	mfence
  struct timespec drain = {
    48e8:	66 0f 6f 05 f0 42 00 00 	movdqa 0x42f0(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    48f0:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    48f4:	49 63 47 28          	movslq 0x28(%r15),%rax
    y++;
    48f8:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    48fb:	85 c0                	test   %eax,%eax
    48fd:	7e 48                	jle    4947 <timer_thread+0x1f7>
    48ff:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4903:	4c 63 c3             	movslq %ebx,%r8
    4906:	49 c1 e0 09          	shl    $0x9,%r8
    490a:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    490e:	66 90                	xchg   %ax,%ax
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4910:	48 8b 19             	mov    (%rcx),%rbx
    4913:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    4915:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4919:	99                   	cltd
    491a:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    491d:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4921:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    4924:	48 63 d2             	movslq %edx,%rdx
    4927:	48 c1 e2 09          	shl    $0x9,%rdx
    492b:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4936:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4942:	49 39 c9             	cmp    %rcx,%r9
    4945:	75 c9                	jne    4910 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    4947:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    494a:	49 8b 77 18          	mov    0x18(%r15),%rsi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    494e:	45 8b 57 30          	mov    0x30(%r15),%r10d
    y++;
    4952:	31 db                	xor    %ebx,%ebx
    if (y >= data->threads[0]->task_count) {
    4954:	48 8b 06             	mov    (%rsi),%rax
    y++;
    4957:	39 78 40             	cmp    %edi,0x40(%rax)
    495a:	0f 4f df             	cmovg  %edi,%ebx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    495d:	45 85 d2             	test   %r10d,%r10d
    4960:	0f 8e 1d 02 00 00    	jle    4b83 <timer_thread+0x433>
    int all_empty = 1;
    4966:	89 9d 78 ff ff ff    	mov    %ebx,-0x88(%rbp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    496c:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    496f:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    4975:	0f 1f 00             	nopl   (%rax)
      for (int y = 0 ; y < 2 ; y++) {
    4978:	45 31 ed             	xor    %r13d,%r13d
    497b:	44 89 f3             	mov    %r14d,%ebx
    497e:	4e 8d 24 f5 00 00 00 00 	lea    0x0(,%r14,8),%r12
    4986:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4989:	45 85 d2             	test   %r10d,%r10d
    498c:	0f 8e cd 00 00 00    	jle    4a5f <timer_thread+0x30f>
    4992:	44 89 9d 7c ff ff ff 	mov    %r11d,-0x84(%rbp)
    4999:	4d 89 eb             	mov    %r13,%r11
      y = 0;
    499c:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    499e:	45 31 c0             	xor    %r8d,%r8d
    49a1:	49 c1 e3 09          	shl    $0x9,%r11
    49a5:	0f 1f 00             	nopl   (%rax)
          if (x == k) { continue; }
    49a8:	45 39 f0             	cmp    %r14d,%r8d
    49ab:	74 39                	je     49e6 <timer_thread+0x296>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    49ad:	49 8b 57 18          	mov    0x18(%r15),%rdx
    49b1:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    49b5:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    49b9:	4a 8b 8c 1a 70 01 00 00 	mov    0x170(%rdx,%r11,1),%rcx
    49c1:	48 01 c1             	add    %rax,%rcx
    49c4:	48 8b 11             	mov    (%rcx),%rdx
    49c7:	48 8b 89 80 00 00 00 	mov    0x80(%rcx),%rcx
    49ce:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    49d5:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    49dc:	4d 85 c9             	test   %r9,%r9
    49df:	7f 2f                	jg     4a10 <timer_thread+0x2c0>
    49e1:	48 85 f6             	test   %rsi,%rsi
    49e4:	7f 2a                	jg     4a10 <timer_thread+0x2c0>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    49e6:	41 83 c0 01          	add    $0x1,%r8d
    49ea:	48 05 80 01 00 00    	add    $0x180,%rax
    49f0:	45 39 c2             	cmp    %r8d,%r10d
    49f3:	75 b3                	jne    49a8 <timer_thread+0x258>
      for (int y = 0 ; y < 2 ; y++) {
    49f5:	49 83 fd 01          	cmp    $0x1,%r13
    49f9:	0f 84 61 01 00 00    	je     4b60 <timer_thread+0x410>
    49ff:	49 83 c5 01          	add    $0x1,%r13
    4a03:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4a06:	eb 91                	jmp    4999 <timer_thread+0x249>
    4a08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4a10:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    4a16:	48 83 ec 08          	sub    $0x8,%rsp
    4a1a:	89 f9                	mov    %edi,%ecx
    4a1c:	bf 01 00 00 00       	mov    $0x1,%edi
    4a21:	50                   	push   %rax
    4a22:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    4a28:	89 da                	mov    %ebx,%edx
    4a2a:	50                   	push   %rax
    4a2b:	31 c0                	xor    %eax,%eax
    4a2d:	56                   	push   %rsi
    4a2e:	48 8d 35 28 36 00 00 	lea    0x3628(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    4a35:	e8 a6 da ff ff       	call   24e0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4a3a:	45 8b 57 30          	mov    0x30(%r15),%r10d
      for (int y = 0 ; y < 2 ; y++) {
    4a3e:	48 83 c4 20          	add    $0x20,%rsp
    4a42:	49 83 fd 01          	cmp    $0x1,%r13
    4a46:	0f 84 94 00 00 00    	je     4ae0 <timer_thread+0x390>
    4a4c:	49 83 c5 01          	add    $0x1,%r13
    4a50:	45 31 db             	xor    %r11d,%r11d
    4a53:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4a56:	45 85 d2             	test   %r10d,%r10d
    4a59:	0f 8f 33 ff ff ff    	jg     4992 <timer_thread+0x242>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4a5f:	49 83 c6 01          	add    $0x1,%r14
    4a63:	45 39 f2             	cmp    %r14d,%r10d
    4a66:	0f 8f 0c ff ff ff    	jg     4978 <timer_thread+0x228>
    4a6c:	8b 9d 78 ff ff ff    	mov    -0x88(%rbp),%ebx
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4a72:	45 85 d2             	test   %r10d,%r10d
    4a75:	7e 49                	jle    4ac0 <timer_thread+0x370>
    4a77:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4a7b:	41 8b 57 40          	mov    0x40(%r15),%edx
    4a7f:	45 31 e4             	xor    %r12d,%r12d
    int all_waited = 1;
    4a82:	bf 01 00 00 00       	mov    $0x1,%edi
    4a87:	45 89 dd             	mov    %r11d,%r13d
    4a8a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4a90:	4a 8b 04 e6          	mov    (%rsi,%r12,8),%rax
    4a94:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a98:	8b 88 9c 01 00 00    	mov    0x19c(%rax),%ecx
    4a9e:	39 d1                	cmp    %edx,%ecx
    4aa0:	0f 8c 8a 00 00 00    	jl     4b30 <timer_thread+0x3e0>
    4aa6:	8b 80 9c 03 00 00    	mov    0x39c(%rax),%eax
    4aac:	39 d0                	cmp    %edx,%eax
    4aae:	7c 48                	jl     4af8 <timer_thread+0x3a8>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4ab0:	49 83 c4 01          	add    $0x1,%r12
    4ab4:	45 39 67 30          	cmp    %r12d,0x30(%r15)
    4ab8:	7f d6                	jg     4a90 <timer_thread+0x340>
    4aba:	45 89 eb             	mov    %r13d,%r11d
    4abd:	41 21 fb             	and    %edi,%r11d
    if (all_empty == 1 && all_waited == 1) {
    4ac0:	45 85 db             	test   %r11d,%r11d
    4ac3:	0f 85 ba 00 00 00    	jne    4b83 <timer_thread+0x433>
      nanosleep(&drain , &drainrem);
    4ac9:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    4acd:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    4ad1:	e8 ea d8 ff ff       	call   23c0 <nanosleep@plt>
    4ad6:	e9 19 fe ff ff       	jmp    48f4 <timer_thread+0x1a4>
    4adb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4ae0:	49 83 c6 01          	add    $0x1,%r14
    4ae4:	45 31 db             	xor    %r11d,%r11d
    4ae7:	45 39 f2             	cmp    %r14d,%r10d
    4aea:	0f 8f 88 fe ff ff    	jg     4978 <timer_thread+0x228>
    4af0:	e9 77 ff ff ff       	jmp    4a6c <timer_thread+0x31c>
    4af5:	0f 1f 00             	nopl   (%rax)
    4af8:	89 c2                	mov    %eax,%edx
    4afa:	bf 01 00 00 00       	mov    $0x1,%edi
    4aff:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4b01:	49 83 c4 01          	add    $0x1,%r12
    4b05:	48 8d 35 f9 37 00 00 	lea    0x37f9(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4b0c:	e8 cf d9 ff ff       	call   24e0 <__printf_chk@plt>
    4b11:	45 39 67 30          	cmp    %r12d,0x30(%r15)
    4b15:	7e 62                	jle    4b79 <timer_thread+0x429>
    4b17:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4b1b:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    4b1f:	31 ff                	xor    %edi,%edi
    4b21:	e9 6a ff ff ff       	jmp    4a90 <timer_thread+0x340>
    4b26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    4b30:	89 ca                	mov    %ecx,%edx
    4b32:	48 8d 35 cc 37 00 00 	lea    0x37cc(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4b39:	bf 01 00 00 00       	mov    $0x1,%edi
    4b3e:	31 c0                	xor    %eax,%eax
    4b40:	e8 9b d9 ff ff       	call   24e0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4b45:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4b49:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    4b4d:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4b4f:	4a 8b 04 e6          	mov    (%rsi,%r12,8),%rax
    4b53:	48 8b 40 38          	mov    0x38(%rax),%rax
    4b57:	e9 4a ff ff ff       	jmp    4aa6 <timer_thread+0x356>
    4b5c:	0f 1f 40 00          	nopl   0x0(%rax)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4b60:	49 83 c6 01          	add    $0x1,%r14
    4b64:	44 8b 9d 7c ff ff ff 	mov    -0x84(%rbp),%r11d
    4b6b:	45 39 f2             	cmp    %r14d,%r10d
    4b6e:	0f 8f 04 fe ff ff    	jg     4978 <timer_thread+0x228>
    4b74:	e9 f3 fe ff ff       	jmp    4a6c <timer_thread+0x31c>
          all_waited = 0; 
    4b79:	45 89 eb             	mov    %r13d,%r11d
    4b7c:	31 ff                	xor    %edi,%edi
    4b7e:	e9 3a ff ff ff       	jmp    4abd <timer_thread+0x36d>
    4b83:	48 8d 3d ca 34 00 00 	lea    0x34ca(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4b8a:	e8 c1 d7 ff ff       	call   2350 <puts@plt>
  while (data->running) {
    4b8f:	41 8b 57 44          	mov    0x44(%r15),%edx
    4b93:	85 d2                	test   %edx,%edx
    4b95:	0f 84 ec 00 00 00    	je     4c87 <timer_thread+0x537>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4b9b:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4b9f:	31 db                	xor    %ebx,%ebx
    4ba1:	4c 8d 25 d2 34 00 00 	lea    0x34d2(%rip),%r12        # 807a <_IO_stdin_used+0x7a>
    4ba8:	4c 8d 2d e6 34 00 00 	lea    0x34e6(%rip),%r13        # 8095 <_IO_stdin_used+0x95>
    4baf:	85 c0                	test   %eax,%eax
    4bb1:	7e 39                	jle    4bec <timer_thread+0x49c>
    4bb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4bb8:	31 c0                	xor    %eax,%eax
    4bba:	89 da                	mov    %ebx,%edx
    4bbc:	4c 89 e6             	mov    %r12,%rsi
    4bbf:	bf 01 00 00 00       	mov    $0x1,%edi
    4bc4:	e8 17 d9 ff ff       	call   24e0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4bc9:	49 8b 47 18          	mov    0x18(%r15),%rax
    4bcd:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4bd1:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4bd5:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4bdc:	0f 84 d1 00 00 00    	je     4cb3 <timer_thread+0x563>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4be2:	48 83 c3 01          	add    $0x1,%rbx
    4be6:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4bea:	7f cc                	jg     4bb8 <timer_thread+0x468>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4bec:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4bf0:	85 d2                	test   %edx,%edx
    4bf2:	7e 7c                	jle    4c70 <timer_thread+0x520>
      for (int y = 0 ; y < data->task_count ; y++) {
    4bf4:	41 8b 47 40          	mov    0x40(%r15),%eax
    4bf8:	85 c0                	test   %eax,%eax
    4bfa:	7e 74                	jle    4c70 <timer_thread+0x520>
    4bfc:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4bff:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4c03:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4c0b:	31 c9                	xor    %ecx,%ecx
    4c0d:	48 c1 e6 09          	shl    $0x9,%rsi
    4c11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c18:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4c1c:	48 8b 40 38          	mov    0x38(%rax),%rax
    4c20:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4c24:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4c2a:	74 1c                	je     4c48 <timer_thread+0x4f8>
    4c2c:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4c36:	48 05 00 02 00 00    	add    $0x200,%rax
    4c3c:	48 39 d0             	cmp    %rdx,%rax
    4c3f:	74 26                	je     4c67 <timer_thread+0x517>
    4c41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4c48:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4c52:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4c58:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4c62:	48 39 d0             	cmp    %rdx,%rax
    4c65:	75 e1                	jne    4c48 <timer_thread+0x4f8>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c67:	48 83 c1 08          	add    $0x8,%rcx
    4c6b:	48 39 cf             	cmp    %rcx,%rdi
    4c6e:	75 a8                	jne    4c18 <timer_thread+0x4c8>
    asm volatile ("mfence" ::: "memory");
    4c70:	0f ae f0             	mfence
    4c73:	48 8d 3d 2d 34 00 00 	lea    0x342d(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4c7a:	e8 d1 d6 ff ff       	call   2350 <puts@plt>
    data->running = 0;
    4c7f:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4c87:	48 8d 3d 20 34 00 00 	lea    0x3420(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4c8e:	e8 bd d6 ff ff       	call   2350 <puts@plt>
}
    4c93:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4c97:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ca0:	75 41                	jne    4ce3 <timer_thread+0x593>
    4ca2:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    4ca6:	31 c0                	xor    %eax,%eax
    4ca8:	5b                   	pop    %rbx
    4ca9:	41 5c                	pop    %r12
    4cab:	41 5d                	pop    %r13
    4cad:	41 5e                	pop    %r14
    4caf:	41 5f                	pop    %r15
    4cb1:	5d                   	pop    %rbp
    4cb2:	c3                   	ret
    4cb3:	4c 89 ef             	mov    %r13,%rdi
    4cb6:	e8 95 d6 ff ff       	call   2350 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4cbb:	49 8b 47 18          	mov    0x18(%r15),%rax
    4cbf:	be 01 00 00 00       	mov    $0x1,%esi
    4cc4:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4cc8:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4ccc:	8b 78 60             	mov    0x60(%rax),%edi
    4ccf:	e8 bc d7 ff ff       	call   2490 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4cd4:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4cd8:	0f 8f da fe ff ff    	jg     4bb8 <timer_thread+0x468>
    4cde:	e9 09 ff ff ff       	jmp    4bec <timer_thread+0x49c>
}
    4ce3:	e8 b8 d6 ff ff       	call   23a0 <__stack_chk_fail@plt>
    4ce8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000004cf0 <minf>:
int minf(int a, int b) {
    4cf0:	f3 0f 1e fa          	endbr64
    4cf4:	55                   	push   %rbp
    4cf5:	48 89 e5             	mov    %rsp,%rbp
    4cf8:	ff 15 ea 62 00 00    	call   *0x62ea(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    4cfe:	5d                   	pop    %rbp
  if (b < a) { return b; }
    4cff:	39 f7                	cmp    %esi,%edi
    4d01:	89 f0                	mov    %esi,%eax
    4d03:	0f 4e c7             	cmovle %edi,%eax
}
    4d06:	c3                   	ret
    4d07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004d10 <maxf>:
int maxf(int a, int b) {
    4d10:	f3 0f 1e fa          	endbr64
    4d14:	55                   	push   %rbp
    4d15:	48 89 e5             	mov    %rsp,%rbp
    4d18:	ff 15 ca 62 00 00    	call   *0x62ca(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    4d1e:	5d                   	pop    %rbp
  if (b > a) { return b; }
    4d1f:	39 f7                	cmp    %esi,%edi
    4d21:	89 f0                	mov    %esi,%eax
    4d23:	0f 4d c7             	cmovge %edi,%eax
}
    4d26:	c3                   	ret
    4d27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004d30 <strtolower>:
void strtolower(char *str) {
    4d30:	f3 0f 1e fa          	endbr64
    4d34:	55                   	push   %rbp
    4d35:	48 89 e5             	mov    %rsp,%rbp
    4d38:	41 54                	push   %r12
    4d3a:	53                   	push   %rbx
    4d3b:	ff 15 a7 62 00 00    	call   *0x62a7(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    for (; *str; ++str)
    4d41:	48 0f be 1f          	movsbq (%rdi),%rbx
void strtolower(char *str) {
    4d45:	49 89 fc             	mov    %rdi,%r12
    for (; *str; ++str)
    4d48:	84 db                	test   %bl,%bl
    4d4a:	74 24                	je     4d70 <strtolower+0x40>
        *str = (char)tolower(*str);
    4d4c:	e8 7f d8 ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    4d51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4d58:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4d5b:	49 83 c4 01          	add    $0x1,%r12
        *str = (char)tolower(*str);
    4d5f:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4d62:	41 88 54 24 ff       	mov    %dl,-0x1(%r12)
    for (; *str; ++str)
    4d67:	49 0f be 1c 24       	movsbq (%r12),%rbx
    4d6c:	84 db                	test   %bl,%bl
    4d6e:	75 e8                	jne    4d58 <strtolower+0x28>
}
    4d70:	5b                   	pop    %rbx
    4d71:	41 5c                	pop    %r12
    4d73:	5d                   	pop    %rbp
    4d74:	c3                   	ret
    4d75:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004d80 <zh_malloc>:
void *zh_malloc(size_t size) {
    4d80:	f3 0f 1e fa          	endbr64
    4d84:	55                   	push   %rbp
    4d85:	48 89 e5             	mov    %rsp,%rbp
    4d88:	ff 15 5a 62 00 00    	call   *0x625a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    void *buf = malloc(size);
    4d8e:	e8 0d d7 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4d93:	48 85 c0             	test   %rax,%rax
    4d96:	74 02                	je     4d9a <zh_malloc+0x1a>
}
    4d98:	5d                   	pop    %rbp
    4d99:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4d9a:	48 8b 0d 7f 62 00 00 	mov    0x627f(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4da1:	ba 28 00 00 00       	mov    $0x28,%edx
    4da6:	be 01 00 00 00       	mov    $0x1,%esi
    4dab:	48 8d 3d 06 38 00 00 	lea    0x3806(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    4db2:	e8 b9 d7 ff ff       	call   2570 <fwrite@plt>
        exit(1);
    4db7:	bf 01 00 00 00       	mov    $0x1,%edi
    4dbc:	e8 8f d7 ff ff       	call   2550 <exit@plt>
    4dc1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4dcc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004dd0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4dd0:	f3 0f 1e fa          	endbr64
    4dd4:	55                   	push   %rbp
    4dd5:	48 89 e5             	mov    %rsp,%rbp
    4dd8:	53                   	push   %rbx
    4dd9:	48 83 ec 08          	sub    $0x8,%rsp
    4ddd:	ff 15 05 62 00 00    	call   *0x6205(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    const char *dot = strrchr(filename, '.');
    4de3:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4de8:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4deb:	e8 e0 d5 ff ff       	call   23d0 <strrchr@plt>
    if (!dot || dot == filename)
    4df0:	48 85 c0             	test   %rax,%rax
    4df3:	74 13                	je     4e08 <get_filename_ext+0x38>
    4df5:	48 39 c3             	cmp    %rax,%rbx
    4df8:	74 0e                	je     4e08 <get_filename_ext+0x38>
}
    4dfa:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    return dot + 1;
    4dfe:	48 83 c0 01          	add    $0x1,%rax
}
    4e02:	c9                   	leave
    4e03:	c3                   	ret
    4e04:	0f 1f 40 00          	nopl   0x0(%rax)
    4e08:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
        return "";
    4e0c:	48 8d 05 e3 32 00 00 	lea    0x32e3(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4e13:	c9                   	leave
    4e14:	c3                   	ret
    4e15:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004e20 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4e20:	f3 0f 1e fa          	endbr64
    4e24:	55                   	push   %rbp
    4e25:	48 89 e5             	mov    %rsp,%rbp
    4e28:	41 56                	push   %r14
    4e2a:	41 55                	push   %r13
    4e2c:	41 54                	push   %r12
    4e2e:	53                   	push   %rbx
    4e2f:	48 81 ec 10 08 00 00 	sub    $0x810,%rsp
    4e36:	ff 15 ac 61 00 00    	call   *0x61ac(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    4e3c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4e45:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    4e49:	31 c0                	xor    %eax,%eax
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4e4b:	4c 8d ad d0 f7 ff ff 	lea    -0x830(%rbp),%r13
    4e52:	49 89 f6             	mov    %rsi,%r14
    4e55:	49 89 d4             	mov    %rdx,%r12
    4e58:	48 89 fe             	mov    %rdi,%rsi
    4e5b:	ba 00 04 00 00       	mov    $0x400,%edx
    4e60:	4c 89 ef             	mov    %r13,%rdi
    4e63:	e8 58 d6 ff ff       	call   24c0 <__strcpy_chk@plt>
    for (; *str; ++str)
    4e68:	48 0f be 9d d0 f7 ff ff 	movsbq -0x830(%rbp),%rbx
    4e70:	84 db                	test   %bl,%bl
    4e72:	74 1e                	je     4e92 <send_headers+0x72>
        *str = (char)tolower(*str);
    4e74:	e8 57 d7 ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    4e79:	48 8b 08             	mov    (%rax),%rcx
    4e7c:	4c 89 e8             	mov    %r13,%rax
    4e7f:	90                   	nop
    4e80:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4e83:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4e87:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4e8a:	48 0f be 18          	movsbq (%rax),%rbx
    4e8e:	84 db                	test   %bl,%bl
    4e90:	75 ee                	jne    4e80 <send_headers+0x60>
    void *buf = malloc(size);
    4e92:	bf 11 00 00 00       	mov    $0x11,%edi
    4e97:	e8 04 d6 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4e9c:	48 85 c0             	test   %rax,%rax
    4e9f:	0f 84 72 04 00 00    	je     5317 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ea5:	66 0f 6f 05 43 3d 00 00 	movdqa 0x3d43(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    iov[0].iov_base = zh_malloc(slen);
    4ead:	49 89 04 24          	mov    %rax,(%r12)
    void *buf = malloc(size);
    4eb1:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4eb6:	49 c7 44 24 08 11 00 00 00 	movq   $0x11,0x8(%r12)
    4ebf:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4ec3:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4ec6:	e8 d5 d5 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4ecb:	48 85 c0             	test   %rax,%rax
    4ece:	0f 84 43 04 00 00    	je     5317 <send_headers+0x4f7>
    4ed4:	66 0f 6f 05 24 3d 00 00 	movdqa 0x3d24(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    iov[1].iov_base = zh_malloc(slen);
    4edc:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    const char *dot = strrchr(filename, '.');
    4ee1:	4c 89 ef             	mov    %r13,%rdi
    4ee4:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4eee:	49 c7 44 24 18 17 00 00 00 	movq   $0x17,0x18(%r12)
    4ef7:	0f 11 00             	movups %xmm0,(%rax)
    4efa:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4efe:	be 2e 00 00 00       	mov    $0x2e,%esi
    4f03:	e8 c8 d4 ff ff       	call   23d0 <strrchr@plt>
    if (!dot || dot == filename)
    4f08:	48 85 c0             	test   %rax,%rax
    4f0b:	0f 84 df 02 00 00    	je     51f0 <send_headers+0x3d0>
    4f11:	4c 39 e8             	cmp    %r13,%rax
    4f14:	0f 84 d6 02 00 00    	je     51f0 <send_headers+0x3d0>
    return dot + 1;
    4f1a:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4f1e:	48 8d 3d 9f 31 00 00 	lea    0x319f(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4f25:	48 89 de             	mov    %rbx,%rsi
    4f28:	e8 03 d5 ff ff       	call   2430 <strcmp@plt>
    4f2d:	85 c0                	test   %eax,%eax
    4f2f:	75 1e                	jne    4f4f <send_headers+0x12f>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f31:	66 0f 6f 05 d7 3c 00 00 	movdqa 0x3cd7(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4f39:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4f40:	66 0f 6f 05 d8 3c 00 00 	movdqa 0x3cd8(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4f48:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("jpeg", file_ext) == 0)
    4f4f:	48 89 de             	mov    %rbx,%rsi
    4f52:	48 8d 3d 6f 31 00 00 	lea    0x316f(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4f59:	e8 d2 d4 ff ff       	call   2430 <strcmp@plt>
    4f5e:	85 c0                	test   %eax,%eax
    4f60:	75 1e                	jne    4f80 <send_headers+0x160>
    4f62:	66 0f 6f 05 a6 3c 00 00 	movdqa 0x3ca6(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4f6a:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4f71:	66 0f 6f 05 a7 3c 00 00 	movdqa 0x3ca7(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4f79:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("png", file_ext) == 0)
    4f80:	48 89 de             	mov    %rbx,%rsi
    4f83:	48 8d 3d 43 31 00 00 	lea    0x3143(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4f8a:	e8 a1 d4 ff ff       	call   2430 <strcmp@plt>
    4f8f:	85 c0                	test   %eax,%eax
    4f91:	0f 84 09 02 00 00    	je     51a0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4f97:	48 89 de             	mov    %rbx,%rsi
    4f9a:	48 8d 3d 30 31 00 00 	lea    0x3130(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4fa1:	e8 8a d4 ff ff       	call   2430 <strcmp@plt>
    4fa6:	85 c0                	test   %eax,%eax
    4fa8:	0f 84 a2 02 00 00    	je     5250 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4fae:	48 89 de             	mov    %rbx,%rsi
    4fb1:	48 8d 3d 1d 31 00 00 	lea    0x311d(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4fb8:	e8 73 d4 ff ff       	call   2430 <strcmp@plt>
    4fbd:	85 c0                	test   %eax,%eax
    4fbf:	0f 84 63 02 00 00    	je     5228 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4fc5:	48 89 de             	mov    %rbx,%rsi
    4fc8:	48 8d 3d 49 31 00 00 	lea    0x3149(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4fcf:	e8 5c d4 ff ff       	call   2430 <strcmp@plt>
    4fd4:	85 c0                	test   %eax,%eax
    4fd6:	0f 84 24 02 00 00    	je     5200 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4fdc:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4fdf:	0f 84 53 01 00 00    	je     5138 <send_headers+0x318>
    if (strcmp("css", file_ext) == 0)
    4fe5:	48 89 de             	mov    %rbx,%rsi
    4fe8:	48 8d 3d ea 30 00 00 	lea    0x30ea(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4fef:	e8 3c d4 ff ff       	call   2430 <strcmp@plt>
    4ff4:	85 c0                	test   %eax,%eax
    4ff6:	0f 84 a4 02 00 00    	je     52a0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4ffc:	48 89 de             	mov    %rbx,%rsi
    4fff:	48 8d 3d d7 30 00 00 	lea    0x30d7(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    5006:	e8 25 d4 ff ff       	call   2430 <strcmp@plt>
    500b:	85 c0                	test   %eax,%eax
    500d:	0f 84 65 02 00 00    	je     5278 <send_headers+0x458>
    slen = strlen(send_buffer);
    5013:	4c 8d ad d0 fb ff ff 	lea    -0x430(%rbp),%r13
    501a:	4c 89 ef             	mov    %r13,%rdi
    501d:	e8 6e d3 ff ff       	call   2390 <strlen@plt>
    void *buf = malloc(size);
    5022:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    5025:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    5028:	e8 73 d4 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    502d:	48 85 c0             	test   %rax,%rax
    5030:	0f 84 e1 02 00 00    	je     5317 <send_headers+0x4f7>
    iov[2].iov_base = zh_malloc(slen);
    5036:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    iov[2].iov_len = slen;
    503b:	49 89 5c 24 28       	mov    %rbx,0x28(%r12)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5040:	83 fb 08             	cmp    $0x8,%ebx
    5043:	0f 83 37 01 00 00    	jae    5180 <send_headers+0x360>
    5049:	f6 c3 04             	test   $0x4,%bl
    504c:	0f 85 71 02 00 00    	jne    52c3 <send_headers+0x4a3>
    5052:	85 db                	test   %ebx,%ebx
    5054:	74 12                	je     5068 <send_headers+0x248>
    5056:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    505d:	88 10                	mov    %dl,(%rax)
    505f:	f6 c3 02             	test   $0x2,%bl
    5062:	0f 85 8b 02 00 00    	jne    52f3 <send_headers+0x4d3>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    5068:	4d 89 f0             	mov    %r14,%r8
    506b:	48 8d 0d 6f 30 00 00 	lea    0x306f(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    5072:	4c 89 ef             	mov    %r13,%rdi
    5075:	31 c0                	xor    %eax,%eax
    5077:	ba 00 04 00 00       	mov    $0x400,%edx
    507c:	be 01 00 00 00       	mov    $0x1,%esi
    5081:	e8 5a d5 ff ff       	call   25e0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    5086:	4c 89 ef             	mov    %r13,%rdi
    5089:	e8 02 d3 ff ff       	call   2390 <strlen@plt>
    void *buf = malloc(size);
    508e:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    5091:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    5094:	e8 07 d4 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    5099:	48 85 c0             	test   %rax,%rax
    509c:	0f 84 75 02 00 00    	je     5317 <send_headers+0x4f7>
    iov[3].iov_base = zh_malloc(slen);
    50a2:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    iov[3].iov_len = slen;
    50a7:	49 89 5c 24 38       	mov    %rbx,0x38(%r12)
    50ac:	83 fb 08             	cmp    $0x8,%ebx
    50af:	0f 83 13 01 00 00    	jae    51c8 <send_headers+0x3a8>
    50b5:	f6 c3 04             	test   $0x4,%bl
    50b8:	0f 85 1d 02 00 00    	jne    52db <send_headers+0x4bb>
    50be:	85 db                	test   %ebx,%ebx
    50c0:	74 12                	je     50d4 <send_headers+0x2b4>
    50c2:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    50c9:	88 10                	mov    %dl,(%rax)
    50cb:	f6 c3 02             	test   $0x2,%bl
    50ce:	0f 85 31 02 00 00    	jne    5305 <send_headers+0x4e5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    50d4:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    50d9:	bf 02 00 00 00       	mov    $0x2,%edi
    50de:	c6 85 d2 fb ff ff 00 	movb   $0x0,-0x42e(%rbp)
    50e5:	66 89 85 d0 fb ff ff 	mov    %ax,-0x430(%rbp)
    50ec:	e8 af d3 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    50f1:	48 85 c0             	test   %rax,%rax
    50f4:	0f 84 1d 02 00 00    	je     5317 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    50fa:	0f b7 95 d0 fb ff ff 	movzwl -0x430(%rbp),%edx
    iov[4].iov_base = zh_malloc(slen);
    5101:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    iov[4].iov_len = slen;
    5106:	49 c7 44 24 48 02 00 00 00 	movq   $0x2,0x48(%r12)
    510f:	66 89 10             	mov    %dx,(%rax)
}
    5112:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    5116:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    511f:	0f 85 19 02 00 00    	jne    533e <send_headers+0x51e>
    5125:	48 81 c4 10 08 00 00 	add    $0x810,%rsp
    512c:	5b                   	pop    %rbx
    512d:	41 5c                	pop    %r12
    512f:	41 5d                	pop    %r13
    5131:	41 5e                	pop    %r14
    5133:	5d                   	pop    %rbp
    5134:	c3                   	ret
    5135:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
    5138:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    513c:	0f 85 a3 fe ff ff    	jne    4fe5 <send_headers+0x1c5>
    5142:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    5146:	0f 85 99 fe ff ff    	jne    4fe5 <send_headers+0x1c5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    514c:	66 0f 6f 05 1c 3b 00 00 	movdqa 0x3b1c(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    5154:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    515e:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    5165:	66 0f 6f 05 13 3b 00 00 	movdqa 0x3b13(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    516d:	0f 29 85 e0 fb ff ff 	movaps %xmm0,-0x420(%rbp)
    5174:	48 89 85 ef fb ff ff 	mov    %rax,-0x411(%rbp)
    517b:	e9 65 fe ff ff       	jmp    4fe5 <send_headers+0x1c5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5180:	89 da                	mov    %ebx,%edx
    5182:	48 89 c7             	mov    %rax,%rdi
    5185:	4c 89 ee             	mov    %r13,%rsi
    5188:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    518d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5192:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5195:	c1 e9 03             	shr    $0x3,%ecx
    5198:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    519b:	e9 c8 fe ff ff       	jmp    5068 <send_headers+0x248>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    51a0:	66 0f 6f 05 68 3a 00 00 	movdqa 0x3a68(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    51a8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    51af:	66 0f 6f 05 79 3a 00 00 	movdqa 0x3a79(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    51b7:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    51be:	e9 d4 fd ff ff       	jmp    4f97 <send_headers+0x177>
    51c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    51c8:	89 da                	mov    %ebx,%edx
    51ca:	48 89 c7             	mov    %rax,%rdi
    51cd:	4c 89 ee             	mov    %r13,%rsi
    51d0:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    51d5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    51da:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    51dd:	c1 e9 03             	shr    $0x3,%ecx
    51e0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    51e3:	e9 ec fe ff ff       	jmp    50d4 <send_headers+0x2b4>
    51e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    51f0:	48 8d 1d ff 2e 00 00 	lea    0x2eff(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    51f7:	e9 9b fd ff ff       	jmp    4f97 <send_headers+0x177>
    51fc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5200:	66 0f 6f 05 48 3a 00 00 	movdqa 0x3a48(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5208:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    520f:	66 0f 6f 05 49 3a 00 00 	movdqa 0x3a49(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5217:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    521e:	e9 b9 fd ff ff       	jmp    4fdc <send_headers+0x1bc>
    5223:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5228:	66 0f 6f 05 20 3a 00 00 	movdqa 0x3a20(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5230:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    5237:	66 0f 6f 05 21 3a 00 00 	movdqa 0x3a21(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    523f:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    5246:	e9 7a fd ff ff       	jmp    4fc5 <send_headers+0x1a5>
    524b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5250:	66 0f 6f 05 b8 39 00 00 	movdqa 0x39b8(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    5258:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    525f:	66 0f 6f 05 d9 39 00 00 	movdqa 0x39d9(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    5267:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    526e:	e9 3b fd ff ff       	jmp    4fae <send_headers+0x18e>
    5273:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5278:	66 0f 6f 05 d0 39 00 00 	movdqa 0x39d0(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5280:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    5287:	66 0f 6f 05 11 3a 00 00 	movdqa 0x3a11(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    528f:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    5296:	e9 78 fd ff ff       	jmp    5013 <send_headers+0x1f3>
    529b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    52a0:	66 0f 6f 05 a8 39 00 00 	movdqa 0x39a8(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    52a8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    52af:	66 0f 6f 05 d9 39 00 00 	movdqa 0x39d9(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    52b7:	0f 11 85 d9 fb ff ff 	movups %xmm0,-0x427(%rbp)
    52be:	e9 39 fd ff ff       	jmp    4ffc <send_headers+0x1dc>
  return __builtin___memcpy_chk (__dest, __src, __len,
    52c3:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    52c9:	89 db                	mov    %ebx,%ebx
    52cb:	89 10                	mov    %edx,(%rax)
    52cd:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    52d2:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    52d6:	e9 8d fd ff ff       	jmp    5068 <send_headers+0x248>
    52db:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    52e1:	89 db                	mov    %ebx,%ebx
    52e3:	89 10                	mov    %edx,(%rax)
    52e5:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    52ea:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    52ee:	e9 e1 fd ff ff       	jmp    50d4 <send_headers+0x2b4>
    52f3:	89 db                	mov    %ebx,%ebx
    52f5:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    52fb:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5300:	e9 63 fd ff ff       	jmp    5068 <send_headers+0x248>
    5305:	89 db                	mov    %ebx,%ebx
    5307:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    530d:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5312:	e9 bd fd ff ff       	jmp    50d4 <send_headers+0x2b4>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5317:	48 8b 0d 02 5d 00 00 	mov    0x5d02(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    531e:	ba 28 00 00 00       	mov    $0x28,%edx
    5323:	be 01 00 00 00       	mov    $0x1,%esi
    5328:	48 8d 3d 89 32 00 00 	lea    0x3289(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    532f:	e8 3c d2 ff ff       	call   2570 <fwrite@plt>
        exit(1);
    5334:	bf 01 00 00 00       	mov    $0x1,%edi
    5339:	e8 12 d2 ff ff       	call   2550 <exit@plt>
}
    533e:	e8 5d d0 ff ff       	call   23a0 <__stack_chk_fail@plt>
    5343:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    534e:	66 90                	xchg   %ax,%ax

0000000000005350 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5350:	f3 0f 1e fa          	endbr64
    5354:	55                   	push   %rbp
    5355:	48 89 e5             	mov    %rsp,%rbp
    5358:	41 56                	push   %r14
    535a:	41 55                	push   %r13
    535c:	41 54                	push   %r12
    535e:	53                   	push   %rbx
    535f:	ff 15 83 5c 00 00    	call   *0x5c83(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    5365:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    5368:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    536b:	48 89 f3             	mov    %rsi,%rbx
    536e:	49 89 d6             	mov    %rdx,%r14
    void *buf = malloc(size);
    5371:	e8 2a d1 ff ff       	call   24a0 <malloc@plt>
    5376:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    5379:	48 85 c0             	test   %rax,%rax
    537c:	74 69                	je     53e7 <copy_file_contents+0x97>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    537e:	4c 89 ef             	mov    %r13,%rdi
    5381:	31 f6                	xor    %esi,%esi
    5383:	31 c0                	xor    %eax,%eax
    5385:	e8 86 d1 ff ff       	call   2510 <open@plt>
    538a:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    538d:	85 c0                	test   %eax,%eax
    538f:	0f 88 88 d2 ff ff    	js     261d <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    5395:	48 89 da             	mov    %rbx,%rdx
    5398:	4c 89 e6             	mov    %r12,%rsi
    539b:	89 c7                	mov    %eax,%edi
    539d:	e8 6e d0 ff ff       	call   2410 <read@plt>
    if (ret < file_size) {
    53a2:	48 98                	cltq
    53a4:	48 39 d8             	cmp    %rbx,%rax
    53a7:	7c 1f                	jl     53c8 <copy_file_contents+0x78>
    close(fd);
    53a9:	44 89 ef             	mov    %r13d,%edi
    53ac:	e8 3f d0 ff ff       	call   23f0 <close@plt>
    iov->iov_base = buf;
    53b1:	4d 89 26             	mov    %r12,(%r14)
    iov->iov_len = file_size;
    53b4:	49 89 5e 08          	mov    %rbx,0x8(%r14)
}
    53b8:	5b                   	pop    %rbx
    53b9:	41 5c                	pop    %r12
    53bb:	41 5d                	pop    %r13
    53bd:	41 5e                	pop    %r14
    53bf:	5d                   	pop    %rbp
    53c0:	c3                   	ret
    53c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    53c8:	48 8b 0d 51 5c 00 00 	mov    0x5c51(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    53cf:	ba 1a 00 00 00       	mov    $0x1a,%edx
    53d4:	be 01 00 00 00       	mov    $0x1,%esi
    53d9:	48 8d 3d 17 2d 00 00 	lea    0x2d17(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    53e0:	e8 8b d1 ff ff       	call   2570 <fwrite@plt>
    53e5:	eb c2                	jmp    53a9 <copy_file_contents+0x59>
    53e7:	48 8b 0d 32 5c 00 00 	mov    0x5c32(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    53ee:	ba 28 00 00 00       	mov    $0x28,%edx
    53f3:	be 01 00 00 00       	mov    $0x1,%esi
    53f8:	48 8d 3d b9 31 00 00 	lea    0x31b9(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    53ff:	e8 6c d1 ff ff       	call   2570 <fwrite@plt>
        exit(1);
    5404:	bf 01 00 00 00       	mov    $0x1,%edi
    5409:	e8 42 d1 ff ff       	call   2550 <exit@plt>
    540e:	66 90                	xchg   %ax,%ax

0000000000005410 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    5410:	f3 0f 1e fa          	endbr64
    5414:	55                   	push   %rbp
    5415:	48 89 e5             	mov    %rsp,%rbp
    5418:	ff 15 ca 5b 00 00    	call   *0x5bca(%rip)        # afe8 <mcount@GLIBC_2.2.5>
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    541e:	8b 46 44             	mov    0x44(%rsi),%eax
    5421:	48 89 fa             	mov    %rdi,%rdx
    5424:	48 89 f7             	mov    %rsi,%rdi
    5427:	8d 70 01             	lea    0x1(%rax),%esi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    542a:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5430:	48 8b 07             	mov    (%rdi),%rax
    5433:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5436:	f6 c1 02             	test   $0x2,%cl
    5439:	74 00                	je     543b <add_write_request+0x2b>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    543b:	89 f0                	mov    %esi,%eax
    543d:	44 29 c0             	sub    %r8d,%eax
    5440:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5443:	0f 82 e0 d1 ff ff    	jb     2629 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5449:	c1 e9 0a             	shr    $0xa,%ecx
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    544c:	8b 47 44             	mov    0x44(%rdi),%eax
    544f:	23 47 58             	and    0x58(%rdi),%eax
		sq->sqe_tail = next;
    5452:	89 77 44             	mov    %esi,0x44(%rdi)
	if (ring->flags & IORING_SETUP_SQE128)
    5455:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5458:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    545b:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    545f:	d3 e0                	shl    %cl,%eax
    5461:	8b 4a 04             	mov    0x4(%rdx),%ecx
    5464:	48 c1 e0 06          	shl    $0x6,%rax
    5468:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    546c:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    5472:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5475:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    5479:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    547f:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5487:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    548b:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    548e:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    5495:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    549d:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    54a1:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    54a5:	e8 06 cf ff ff       	call   23b0 <io_uring_submit@plt>
}
    54aa:	31 c0                	xor    %eax,%eax
    54ac:	5d                   	pop    %rbp
    54ad:	c3                   	ret
    54ae:	66 90                	xchg   %ax,%ax

00000000000054b0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    54b0:	f3 0f 1e fa          	endbr64
    54b4:	55                   	push   %rbp
    54b5:	48 89 e5             	mov    %rsp,%rbp
    54b8:	41 56                	push   %r14
    54ba:	41 55                	push   %r13
    54bc:	41 54                	push   %r12
    54be:	53                   	push   %rbx
    54bf:	ff 15 23 5b 00 00    	call   *0x5b23(%rip)        # afe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    54c5:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    54c8:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    54ce:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    54d1:	83 c0 01             	add    $0x1,%eax
    54d4:	48 89 f3             	mov    %rsi,%rbx
    54d7:	41 89 fe             	mov    %edi,%r14d
		head = IO_URING_READ_ONCE(*sq->khead);
    54da:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    54dc:	f6 c1 02             	test   $0x2,%cl
    54df:	74 00                	je     54e1 <add_read_request+0x31>
	if (next - head <= sq->ring_entries) {
    54e1:	89 c2                	mov    %eax,%edx
    54e3:	29 f2                	sub    %esi,%edx
    54e5:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    54e8:	0f 82 4b d1 ff ff    	jb     2639 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    54ee:	44 8b 63 44          	mov    0x44(%rbx),%r12d
	if (ring->flags & IORING_SETUP_SQE128)
    54f2:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    54f5:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    54f8:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    54fd:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5500:	44 23 63 58          	and    0x58(%rbx),%r12d
    5504:	41 d3 e4             	shl    %cl,%r12d
    5507:	49 c1 e4 06          	shl    $0x6,%r12
    550b:	4c 03 63 38          	add    0x38(%rbx),%r12
    550f:	e8 8c cf ff ff       	call   24a0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    5514:	be 01 00 00 00       	mov    $0x1,%esi
    5519:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    551e:	49 89 c5             	mov    %rax,%r13
    req->iov[0].iov_base = malloc(READ_SZ);
    5521:	e8 fa ce ff ff       	call   2420 <calloc@plt>
    req->client_socket = client_socket;
    5526:	45 89 75 08          	mov    %r14d,0x8(%r13)
	sqe->addr3 = 0;
    552a:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    552e:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5531:	49 89 45 10          	mov    %rax,0x10(%r13)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    5535:	49 8d 45 10          	lea    0x10(%r13),%rax
    req->iov[0].iov_len = READ_SZ;
    5539:	49 c7 45 18 00 20 00 00 	movq   $0x2000,0x18(%r13)
    req->event_type = EVENT_TYPE_READ;
    5541:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
	sqe->fd = fd;
    5549:	45 89 74 24 04       	mov    %r14d,0x4(%r12)
	sqe->user_data = (unsigned long) data;
    554e:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
	sqe->opcode = (__u8) op;
    5553:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->off = offset;
    555b:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    5564:	49 89 44 24 10       	mov    %rax,0x10(%r12)
	sqe->len = len;
    5569:	49 c7 44 24 18 01 00 00 00 	movq   $0x1,0x18(%r12)
	sqe->buf_index = 0;
    5572:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->addr3 = 0;
    557b:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    io_uring_submit(ring);
    5581:	e8 2a ce ff ff       	call   23b0 <io_uring_submit@plt>
}
    5586:	5b                   	pop    %rbx
    5587:	31 c0                	xor    %eax,%eax
    5589:	41 5c                	pop    %r12
    558b:	41 5d                	pop    %r13
    558d:	41 5e                	pop    %r14
    558f:	5d                   	pop    %rbp
    5590:	c3                   	ret
    5591:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    559c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000055a0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    55a0:	f3 0f 1e fa          	endbr64
    55a4:	55                   	push   %rbp
    55a5:	48 89 e5             	mov    %rsp,%rbp
    55a8:	41 57                	push   %r15
    55aa:	41 56                	push   %r14
    55ac:	41 55                	push   %r13
    55ae:	41 54                	push   %r12
    55b0:	53                   	push   %rbx
    55b1:	48 83 ec 08          	sub    $0x8,%rsp
    55b5:	ff 15 2d 5a 00 00    	call   *0x5a2d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    55bb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    55be:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    55c3:	41 89 f7             	mov    %esi,%r15d
    55c6:	49 89 d4             	mov    %rdx,%r12
    void *buf = malloc(size);
    55c9:	e8 d2 ce ff ff       	call   24a0 <malloc@plt>
    55ce:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    55d1:	48 85 c0             	test   %rax,%rax
    55d4:	0f 84 eb 00 00 00    	je     56c5 <_send_static_string_content+0x125>
    unsigned long slen = strlen(str);
    55da:	4c 89 ef             	mov    %r13,%rdi
    55dd:	e8 ae cd ff ff       	call   2390 <strlen@plt>
    req->iovec_count = 1;
    55e2:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    55e9:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
    void *buf = malloc(size);
    55ed:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    55f0:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    55f3:	e8 a8 ce ff ff       	call   24a0 <malloc@plt>
    55f8:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    55fb:	48 85 c0             	test   %rax,%rax
    55fe:	0f 84 c1 00 00 00    	je     56c5 <_send_static_string_content+0x125>
    req->iov[0].iov_base = zh_malloc(slen);
    5604:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5608:	4c 89 f2             	mov    %r14,%rdx
    560b:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    560e:	4c 89 73 18          	mov    %r14,0x18(%rbx)
    5612:	e8 59 ce ff ff       	call   2470 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5617:	41 8b 44 24 44       	mov    0x44(%r12),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    561c:	41 8b 8c 24 c0 00 00 00 	mov    0xc0(%r12),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5624:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5627:	49 8b 04 24          	mov    (%r12),%rax
    562b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    562d:	f6 c1 02             	test   $0x2,%cl
    5630:	0f 85 8a 00 00 00    	jne    56c0 <_send_static_string_content+0x120>
	if (next - head <= sq->ring_entries) {
    5636:	89 d0                	mov    %edx,%eax
    5638:	29 f0                	sub    %esi,%eax
    563a:	41 39 44 24 5c       	cmp    %eax,0x5c(%r12)
    563f:	0f 82 fe cf ff ff    	jb     2643 <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5645:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5648:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    564d:	41 23 44 24 58       	and    0x58(%r12),%eax
    io_uring_submit(ring);
    5652:	4c 89 e7             	mov    %r12,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    5655:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5658:	41 89 54 24 44       	mov    %edx,0x44(%r12)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    565d:	8b 53 04             	mov    0x4(%rbx),%edx
	sqe->addr3 = 0;
    5660:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5664:	d3 e0                	shl    %cl,%eax
    5666:	8b 4b 08             	mov    0x8(%rbx),%ecx
    req->event_type = EVENT_TYPE_WRITE;
    5669:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    566f:	48 c1 e0 06          	shl    $0x6,%rax
    5673:	49 03 44 24 38       	add    0x38(%r12),%rax
	sqe->fd = fd;
    5678:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    567b:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    567f:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5685:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    568d:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5691:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5694:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    569b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    56a3:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    56a7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    56ab:	48 83 c4 08          	add    $0x8,%rsp
    56af:	5b                   	pop    %rbx
    56b0:	41 5c                	pop    %r12
    56b2:	41 5d                	pop    %r13
    56b4:	41 5e                	pop    %r14
    56b6:	41 5f                	pop    %r15
    56b8:	5d                   	pop    %rbp
    io_uring_submit(ring);
    56b9:	e9 f2 cc ff ff       	jmp    23b0 <io_uring_submit@plt>
    56be:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    56c0:	e9 71 ff ff ff       	jmp    5636 <_send_static_string_content+0x96>
    56c5:	48 8b 0d 54 59 00 00 	mov    0x5954(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    56cc:	ba 28 00 00 00       	mov    $0x28,%edx
    56d1:	be 01 00 00 00       	mov    $0x1,%esi
    56d6:	48 8d 3d db 2e 00 00 	lea    0x2edb(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    56dd:	e8 8e ce ff ff       	call   2570 <fwrite@plt>
        exit(1);
    56e2:	bf 01 00 00 00       	mov    $0x1,%edi
    56e7:	e8 64 ce ff ff       	call   2550 <exit@plt>
    56ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000056f0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    56f0:	f3 0f 1e fa          	endbr64
    56f4:	55                   	push   %rbp
    56f5:	48 89 e5             	mov    %rsp,%rbp
    56f8:	ff 15 ea 58 00 00    	call   *0x58ea(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    56fe:	5d                   	pop    %rbp
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    56ff:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5702:	89 fe                	mov    %edi,%esi
    5704:	48 8b 3d 0d 59 00 00 	mov    0x590d(%rip),%rdi        # b018 <unimplemented_content>
    570b:	e9 90 fe ff ff       	jmp    55a0 <_send_static_string_content>

0000000000005710 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5710:	f3 0f 1e fa          	endbr64
    5714:	55                   	push   %rbp
    5715:	48 89 e5             	mov    %rsp,%rbp
    5718:	ff 15 ca 58 00 00    	call   *0x58ca(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    571e:	5d                   	pop    %rbp
void handle_http_404(int client_socket, struct io_uring *ring) {
    571f:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5722:	89 fe                	mov    %edi,%esi
    5724:	48 8b 3d e5 58 00 00 	mov    0x58e5(%rip),%rdi        # b010 <http_404_content>
    572b:	e9 70 fe ff ff       	jmp    55a0 <_send_static_string_content>

0000000000005730 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    5730:	f3 0f 1e fa          	endbr64
    5734:	55                   	push   %rbp
    5735:	48 89 e5             	mov    %rsp,%rbp
    5738:	41 57                	push   %r15
    573a:	41 56                	push   %r14
    573c:	41 55                	push   %r13
    573e:	41 54                	push   %r12
    5740:	53                   	push   %rbx
    5741:	48 81 ec a8 04 00 00 	sub    $0x4a8,%rsp
    5748:	ff 15 9a 58 00 00    	call   *0x589a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    574e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5757:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    575b:	31 c0                	xor    %eax,%eax
    575d:	49 89 fc             	mov    %rdi,%r12
    5760:	41 89 f5             	mov    %esi,%r13d
    5763:	49 89 d6             	mov    %rdx,%r14
    if (path[strlen(path) - 1] == '/') {
    5766:	e8 25 cc ff ff       	call   2390 <strlen@plt>
    576b:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
    5771:	48 89 c3             	mov    %rax,%rbx
    5774:	0f 84 b6 00 00 00    	je     5830 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    577a:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    577f:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    5783:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5788:	4c 89 e6             	mov    %r12,%rsi
    578b:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5792:	66 89 85 c4 fb ff ff 	mov    %ax,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5799:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    57a0:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    57aa:	e8 a1 cc ff ff       	call   2450 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    57af:	48 8d b5 30 fb ff ff 	lea    -0x4d0(%rbp),%rsi
    57b6:	4c 89 ff             	mov    %r15,%rdi
    57b9:	e8 a2 cc ff ff       	call   2460 <stat@plt>
    57be:	83 f8 ff             	cmp    $0xffffffff,%eax
    57c1:	0f 84 41 01 00 00    	je     5908 <handle_get_method+0x1d8>
        if (S_ISREG(path_stat.st_mode)) {
    57c7:	8b 85 48 fb ff ff    	mov    -0x4b8(%rbp),%eax
    57cd:	25 00 f0 00 00       	and    $0xf000,%eax
    57d2:	3d 00 80 00 00       	cmp    $0x8000,%eax
    57d7:	0f 84 b3 00 00 00    	je     5890 <handle_get_method+0x160>
    _send_static_string_content(http_404_content, client_socket, ring);
    57dd:	48 8b 3d 2c 58 00 00 	mov    0x582c(%rip),%rdi        # b010 <http_404_content>
    57e4:	4c 89 f2             	mov    %r14,%rdx
    57e7:	44 89 ee             	mov    %r13d,%esi
    57ea:	e8 b1 fd ff ff       	call   55a0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    57ef:	4c 89 fa             	mov    %r15,%rdx
    57f2:	bf 01 00 00 00       	mov    $0x1,%edi
    57f7:	31 c0                	xor    %eax,%eax
    57f9:	48 8d 35 47 29 00 00 	lea    0x2947(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5800:	e8 db cc ff ff       	call   24e0 <__printf_chk@plt>
}
    5805:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5809:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5812:	0f 85 20 01 00 00    	jne    5938 <handle_get_method+0x208>
    5818:	48 81 c4 a8 04 00 00 	add    $0x4a8,%rsp
    581f:	5b                   	pop    %rbx
    5820:	41 5c                	pop    %r12
    5822:	41 5d                	pop    %r13
    5824:	41 5e                	pop    %r14
    5826:	41 5f                	pop    %r15
    5828:	5d                   	pop    %rbp
    5829:	c3                   	ret
    582a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5830:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5835:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
    583c:	4c 89 e6             	mov    %r12,%rsi
    583f:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5844:	66 89 95 c4 fb ff ff 	mov    %dx,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    584b:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    584e:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
    5855:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    585f:	e8 ec cb ff ff       	call   2450 <__memcpy_chk@plt>
    5864:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5869:	49 8d 7c 1f 06       	lea    0x6(%r15,%rbx,1),%rdi
    586e:	ba 0b 00 00 00       	mov    $0xb,%edx
    5873:	48 29 d9             	sub    %rbx,%rcx
    5876:	48 8d 35 95 28 00 00 	lea    0x2895(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    587d:	e8 ce cb ff ff       	call   2450 <__memcpy_chk@plt>
    5882:	e9 28 ff ff ff       	jmp    57af <handle_get_method+0x7f>
    5887:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5890:	bf 70 00 00 00       	mov    $0x70,%edi
    5895:	e8 06 cc ff ff       	call   24a0 <malloc@plt>
    589a:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    589d:	48 85 c0             	test   %rax,%rax
    58a0:	0f 84 97 00 00 00    	je     593d <handle_get_method+0x20d>
            req->client_socket = client_socket;
    58a6:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    58aa:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    58b1:	48 8d 50 10          	lea    0x10(%rax),%rdx
    58b5:	4c 89 ff             	mov    %r15,%rdi
            req->iovec_count = 6;
    58b8:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    58bf:	e8 5c f5 ff ff       	call   4e20 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    58c4:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    58cb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    58cf:	4c 89 ff             	mov    %r15,%rdi
    58d2:	e8 79 fa ff ff       	call   5350 <copy_file_contents>
    58d7:	4c 89 fa             	mov    %r15,%rdx
    58da:	bf 01 00 00 00       	mov    $0x1,%edi
    58df:	31 c0                	xor    %eax,%eax
    58e1:	48 8b 8d 60 fb ff ff 	mov    -0x4a0(%rbp),%rcx
    58e8:	48 8d 35 46 28 00 00 	lea    0x2846(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    58ef:	e8 ec cb ff ff       	call   24e0 <__printf_chk@plt>
            add_write_request(req, ring);
    58f4:	4c 89 f6             	mov    %r14,%rsi
    58f7:	48 89 df             	mov    %rbx,%rdi
    58fa:	e8 11 fb ff ff       	call   5410 <add_write_request>
    58ff:	e9 01 ff ff ff       	jmp    5805 <handle_get_method+0xd5>
    5904:	0f 1f 40 00          	nopl   0x0(%rax)
    5908:	4c 89 fa             	mov    %r15,%rdx
    590b:	4c 89 e1             	mov    %r12,%rcx
    590e:	48 8d 35 08 28 00 00 	lea    0x2808(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    5915:	31 c0                	xor    %eax,%eax
    5917:	bf 01 00 00 00       	mov    $0x1,%edi
    591c:	e8 bf cb ff ff       	call   24e0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    5921:	48 8b 3d e8 56 00 00 	mov    0x56e8(%rip),%rdi        # b010 <http_404_content>
    5928:	4c 89 f2             	mov    %r14,%rdx
    592b:	44 89 ee             	mov    %r13d,%esi
    592e:	e8 6d fc ff ff       	call   55a0 <_send_static_string_content>
}
    5933:	e9 cd fe ff ff       	jmp    5805 <handle_get_method+0xd5>
}
    5938:	e8 63 ca ff ff       	call   23a0 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    593d:	48 8b 0d dc 56 00 00 	mov    0x56dc(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5944:	ba 28 00 00 00       	mov    $0x28,%edx
    5949:	be 01 00 00 00       	mov    $0x1,%esi
    594e:	48 8d 3d 63 2c 00 00 	lea    0x2c63(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    5955:	e8 16 cc ff ff       	call   2570 <fwrite@plt>
        exit(1);
    595a:	bf 01 00 00 00       	mov    $0x1,%edi
    595f:	e8 ec cb ff ff       	call   2550 <exit@plt>
    5964:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    596f:	90                   	nop

0000000000005970 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5970:	f3 0f 1e fa          	endbr64
    5974:	55                   	push   %rbp
    5975:	48 89 e5             	mov    %rsp,%rbp
    5978:	41 57                	push   %r15
    597a:	41 56                	push   %r14
    597c:	41 55                	push   %r13
    597e:	41 54                	push   %r12
    5980:	53                   	push   %rbx
    5981:	48 83 ec 28          	sub    $0x28,%rsp
    5985:	ff 15 5d 56 00 00    	call   *0x565d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    method = strtok_r(method_buffer, " ", &saveptr);
    598b:	4c 8d 35 1a 27 00 00 	lea    0x271a(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5992:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    599b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    599f:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    59a1:	4c 8d 7d c0          	lea    -0x40(%rbp),%r15
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    59a5:	41 89 f4             	mov    %esi,%r12d
    59a8:	49 89 d5             	mov    %rdx,%r13
    method = strtok_r(method_buffer, " ", &saveptr);
    59ab:	4c 89 f6             	mov    %r14,%rsi
    59ae:	4c 89 fa             	mov    %r15,%rdx
    59b1:	e8 4a ca ff ff       	call   2400 <strtok_r@plt>
    for (; *str; ++str)
    59b6:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    59b9:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    59bc:	84 d2                	test   %dl,%dl
    59be:	88 55 bf             	mov    %dl,-0x41(%rbp)
    59c1:	74 22                	je     59e5 <handle_http_method+0x75>
        *str = (char)tolower(*str);
    59c3:	e8 08 cc ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    59c8:	48 0f be 55 bf       	movsbq -0x41(%rbp),%rdx
    59cd:	48 89 d9             	mov    %rbx,%rcx
    59d0:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    59d3:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    59d7:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    59da:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    59dd:	48 0f be 11          	movsbq (%rcx),%rdx
    59e1:	84 d2                	test   %dl,%dl
    59e3:	75 eb                	jne    59d0 <handle_http_method+0x60>
    path = strtok_r(NULL, " ", &saveptr);
    59e5:	4c 89 fa             	mov    %r15,%rdx
    59e8:	4c 89 f6             	mov    %r14,%rsi
    59eb:	31 ff                	xor    %edi,%edi
    59ed:	e8 0e ca ff ff       	call   2400 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    59f2:	48 8d 35 61 27 00 00 	lea    0x2761(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    59f9:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    59fc:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    59ff:	e8 2c ca ff ff       	call   2430 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5a04:	4c 89 ea             	mov    %r13,%rdx
    5a07:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    5a0a:	85 c0                	test   %eax,%eax
    5a0c:	75 2a                	jne    5a38 <handle_http_method+0xc8>
        handle_get_method(path, client_socket, ring);
    5a0e:	4c 89 f7             	mov    %r14,%rdi
    5a11:	e8 1a fd ff ff       	call   5730 <handle_get_method>
}
    5a16:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5a1a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5a23:	75 21                	jne    5a46 <handle_http_method+0xd6>
    5a25:	48 83 c4 28          	add    $0x28,%rsp
    5a29:	5b                   	pop    %rbx
    5a2a:	41 5c                	pop    %r12
    5a2c:	41 5d                	pop    %r13
    5a2e:	41 5e                	pop    %r14
    5a30:	41 5f                	pop    %r15
    5a32:	5d                   	pop    %rbp
    5a33:	c3                   	ret
    5a34:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5a38:	48 8b 3d d9 55 00 00 	mov    0x55d9(%rip),%rdi        # b018 <unimplemented_content>
    5a3f:	e8 5c fb ff ff       	call   55a0 <_send_static_string_content>
}
    5a44:	eb d0                	jmp    5a16 <handle_http_method+0xa6>
    5a46:	e8 55 c9 ff ff       	call   23a0 <__stack_chk_fail@plt>
    5a4b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005a50 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5a50:	f3 0f 1e fa          	endbr64
    5a54:	55                   	push   %rbp
    5a55:	48 89 e5             	mov    %rsp,%rbp
    5a58:	ff 15 8a 55 00 00    	call   *0x558a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    for (int i = 0; i < dest_sz; i++) {
    5a5e:	85 d2                	test   %edx,%edx
    5a60:	7e 36                	jle    5a98 <get_line+0x48>
    5a62:	48 63 d2             	movslq %edx,%rdx
    5a65:	48 83 c7 01          	add    $0x1,%rdi
    5a69:	48 01 f2             	add    %rsi,%rdx
    5a6c:	eb 0f                	jmp    5a7d <get_line+0x2d>
    5a6e:	66 90                	xchg   %ax,%ax
    5a70:	48 83 c6 01          	add    $0x1,%rsi
    5a74:	48 83 c7 01          	add    $0x1,%rdi
    5a78:	48 39 d6             	cmp    %rdx,%rsi
    5a7b:	74 1b                	je     5a98 <get_line+0x48>
        dest[i] = src[i];
    5a7d:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5a81:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5a83:	3c 0d                	cmp    $0xd,%al
    5a85:	75 e9                	jne    5a70 <get_line+0x20>
    5a87:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5a8a:	75 e4                	jne    5a70 <get_line+0x20>
            return 0;
    5a8c:	31 c0                	xor    %eax,%eax
            dest[i] = '\0';
    5a8e:	c6 06 00             	movb   $0x0,(%rsi)
}
    5a91:	5d                   	pop    %rbp
    5a92:	c3                   	ret
    5a93:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return 1;
    5a98:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5a9d:	5d                   	pop    %rbp
    5a9e:	c3                   	ret
    5a9f:	90                   	nop

0000000000005aa0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5aa0:	f3 0f 1e fa          	endbr64
    5aa4:	55                   	push   %rbp
    5aa5:	48 89 e5             	mov    %rsp,%rbp
    5aa8:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    5aaf:	ff 15 33 55 00 00    	call   *0x5533(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    5ab5:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    5ab9:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5ac2:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
    5ac6:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5ac8:	4c 8d 95 f0 fb ff ff 	lea    -0x410(%rbp),%r10
    5acf:	4c 8d 4d f0          	lea    -0x10(%rbp),%r9
    5ad3:	4c 89 d0             	mov    %r10,%rax
    5ad6:	eb 15                	jmp    5aed <handle_client_request+0x4d>
    5ad8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5ae0:	48 83 c0 01          	add    $0x1,%rax
    5ae4:	48 83 c1 01          	add    $0x1,%rcx
    5ae8:	4c 39 c8             	cmp    %r9,%rax
    5aeb:	74 43                	je     5b30 <handle_client_request+0x90>
        dest[i] = src[i];
    5aed:	44 0f b6 01          	movzbl (%rcx),%r8d
    5af1:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5af4:	41 80 f8 0d          	cmp    $0xd,%r8b
    5af8:	75 e6                	jne    5ae0 <handle_client_request+0x40>
    5afa:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5afe:	75 e0                	jne    5ae0 <handle_client_request+0x40>
            dest[i] = '\0';
    5b00:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5b03:	8b 47 08             	mov    0x8(%rdi),%eax
    5b06:	48 89 f2             	mov    %rsi,%rdx
    5b09:	4c 89 d7             	mov    %r10,%rdi
    5b0c:	89 c6                	mov    %eax,%esi
    5b0e:	e8 5d fe ff ff       	call   5970 <handle_http_method>
}
    5b13:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    5b17:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5b20:	75 35                	jne    5b57 <handle_client_request+0xb7>
    5b22:	c9                   	leave
    5b23:	31 c0                	xor    %eax,%eax
    5b25:	c3                   	ret
    5b26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5b30:	48 8b 0d e9 54 00 00 	mov    0x54e9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5b37:	ba 12 00 00 00       	mov    $0x12,%edx
    5b3c:	be 01 00 00 00       	mov    $0x1,%esi
    5b41:	48 8d 3d 16 26 00 00 	lea    0x2616(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5b48:	e8 23 ca ff ff       	call   2570 <fwrite@plt>
        exit(1);
    5b4d:	bf 01 00 00 00       	mov    $0x1,%edi
    5b52:	e8 f9 c9 ff ff       	call   2550 <exit@plt>
}
    5b57:	e8 44 c8 ff ff       	call   23a0 <__stack_chk_fail@plt>
    5b5c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005b60 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5b60:	f3 0f 1e fa          	endbr64
    5b64:	55                   	push   %rbp
    5b65:	48 89 e5             	mov    %rsp,%rbp
    5b68:	41 54                	push   %r12
    5b6a:	53                   	push   %rbx
    5b6b:	ff 15 77 54 00 00    	call   *0x5477(%rip)        # afe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    5b71:	8b 41 44             	mov    0x44(%rcx),%eax
    5b74:	83 c0 01             	add    $0x1,%eax
    5b77:	48 89 cb             	mov    %rcx,%rbx
	if (ring->flags & IORING_SETUP_SQE128)
    5b7a:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    5b80:	4c 8b 03             	mov    (%rbx),%r8
    5b83:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5b86:	f6 c1 02             	test   $0x2,%cl
    5b89:	74 00                	je     5b8b <add_accept_request+0x2b>
	if (next - head <= sq->ring_entries) {
    5b8b:	41 89 c0             	mov    %eax,%r8d
    5b8e:	45 29 c8             	sub    %r9d,%r8d
    5b91:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    5b95:	0f 82 b8 ca ff ff    	jb     2653 <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5b9b:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5b9e:	44 8b 63 44          	mov    0x44(%rbx),%r12d
    5ba2:	44 23 63 58          	and    0x58(%rbx),%r12d
		sq->sqe_tail = next;
    5ba6:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5ba9:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5bac:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5bb0:	41 d3 e4             	shl    %cl,%r12d
    5bb3:	49 c1 e4 06          	shl    $0x6,%r12
    5bb7:	4c 03 63 38          	add    0x38(%rbx),%r12
	sqe->fd = fd;
    5bbb:	41 89 7c 24 04       	mov    %edi,0x4(%r12)
  struct Request *req = malloc(sizeof(*req));
    5bc0:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5bc5:	41 c7 04 24 0d 00 00 00 	movl   $0xd,(%r12)
	sqe->off = offset;
    5bcd:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
	sqe->addr = (unsigned long) addr;
    5bd2:	49 89 74 24 10       	mov    %rsi,0x10(%r12)
	sqe->buf_index = 0;
    5bd7:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->len = len;
    5be0:	49 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%r12)
	sqe->addr3 = 0;
    5be9:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    5bef:	e8 ac c8 ff ff       	call   24a0 <malloc@plt>
  io_uring_submit(ring);
    5bf4:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5bf7:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    5bfd:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
    5c02:	5b                   	pop    %rbx
    5c03:	41 5c                	pop    %r12
    5c05:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5c06:	e9 a5 c7 ff ff       	jmp    23b0 <io_uring_submit@plt>
    5c0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005c10 <io_thread>:
void* io_thread(void *arg) {
    5c10:	f3 0f 1e fa          	endbr64
    5c14:	55                   	push   %rbp
    5c15:	48 89 e5             	mov    %rsp,%rbp
    5c18:	41 57                	push   %r15
    5c1a:	41 56                	push   %r14
    5c1c:	41 55                	push   %r13
    5c1e:	41 54                	push   %r12
    5c20:	53                   	push   %rbx
    5c21:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    5c28:	ff 15 ba 53 00 00    	call   *0x53ba(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5c2e:	31 d2                	xor    %edx,%edx
  struct io_uring ring = *data->ring;
    5c30:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5c39:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    5c3d:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5c41:	48 8d 9d e0 fa ff ff 	lea    -0x520(%rbp),%rbx
void* io_thread(void *arg) {
    5c48:	49 89 fc             	mov    %rdi,%r12
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5c4b:	bf 00 01 00 00       	mov    $0x100,%edi
    5c50:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    5c53:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5c57:	0f 29 8d e0 fa ff ff 	movaps %xmm1,-0x520(%rbp)
    5c5e:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5c63:	0f 29 95 f0 fa ff ff 	movaps %xmm2,-0x510(%rbp)
    5c6a:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5c6f:	0f 29 9d 00 fb ff ff 	movaps %xmm3,-0x500(%rbp)
    5c76:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5c7b:	0f 29 a5 10 fb ff ff 	movaps %xmm4,-0x4f0(%rbp)
    5c82:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5c87:	0f 29 ad 20 fb ff ff 	movaps %xmm5,-0x4e0(%rbp)
    5c8e:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5c93:	0f 29 b5 30 fb ff ff 	movaps %xmm6,-0x4d0(%rbp)
    5c9a:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5c9f:	0f 29 bd 40 fb ff ff 	movaps %xmm7,-0x4c0(%rbp)
    5ca6:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5cab:	0f 29 8d 50 fb ff ff 	movaps %xmm1,-0x4b0(%rbp)
    5cb2:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5cba:	0f 29 95 60 fb ff ff 	movaps %xmm2,-0x4a0(%rbp)
    5cc1:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5cc9:	0f 29 9d 70 fb ff ff 	movaps %xmm3,-0x490(%rbp)
    5cd0:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5cd8:	0f 29 a5 80 fb ff ff 	movaps %xmm4,-0x480(%rbp)
    5cdf:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5ce7:	0f 29 ad 90 fb ff ff 	movaps %xmm5,-0x470(%rbp)
    5cee:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5cf6:	0f 29 b5 a0 fb ff ff 	movaps %xmm6,-0x460(%rbp)
    5cfd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5d04:	48 89 85 b0 fb ff ff 	mov    %rax,-0x450(%rbp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5d0b:	e8 70 c7 ff ff       	call   2480 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5d10:	49 8b 7c 24 58       	mov    0x58(%r12),%rdi
    5d15:	31 f6                	xor    %esi,%esi
    5d17:	e8 74 c8 ff ff       	call   2590 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5d1c:	31 d2                	xor    %edx,%edx
    5d1e:	be 01 00 00 00       	mov    $0x1,%esi
    5d23:	bf 02 00 00 00       	mov    $0x2,%edi
    5d28:	e8 c3 c8 ff ff       	call   25f0 <socket@plt>
    5d2d:	89 85 ac fa ff ff    	mov    %eax,-0x554(%rbp)
  if (sock == -1)
    5d33:	83 f8 ff             	cmp    $0xffffffff,%eax
    5d36:	0f 84 59 c9 ff ff    	je     2695 <io_thread.cold+0x38>
    5d3c:	89 c7                	mov    %eax,%edi
  if (setsockopt(sock,
    5d3e:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5d44:	ba 02 00 00 00       	mov    $0x2,%edx
    5d49:	be 01 00 00 00       	mov    $0x1,%esi
    5d4e:	48 8d 8d b0 fa ff ff 	lea    -0x550(%rbp),%rcx
  int enable = 1;
    5d55:	c7 85 b0 fa ff ff 01 00 00 00 	movl   $0x1,-0x550(%rbp)
  if (setsockopt(sock,
    5d5f:	e8 fc c5 ff ff       	call   2360 <setsockopt@plt>
    5d64:	85 c0                	test   %eax,%eax
    5d66:	0f 88 fd c8 ff ff    	js     2669 <io_thread.cold+0xc>
  if (bind(sock,
    5d6c:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5d72:	ba 10 00 00 00       	mov    $0x10,%edx
  return __builtin___memset_chk (__dest, __ch, __len,
    5d77:	48 8d b5 c0 fa ff ff 	lea    -0x540(%rbp),%rsi
    5d7e:	48 c7 85 c4 fa ff ff 00 00 00 00 	movq   $0x0,-0x53c(%rbp)
    5d89:	c7 85 cc fa ff ff 00 00 00 00 	movl   $0x0,-0x534(%rbp)
  srv_addr.sin_family = AF_INET;
    5d93:	c7 85 c0 fa ff ff 02 00 18 db 	movl   $0xdb180002,-0x540(%rbp)
  if (bind(sock,
    5d9d:	e8 4e c7 ff ff       	call   24f0 <bind@plt>
    5da2:	85 c0                	test   %eax,%eax
    5da4:	0f 88 f7 c8 ff ff    	js     26a1 <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5daa:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5db0:	be 0a 00 00 00       	mov    $0xa,%esi
    5db5:	e8 f6 c6 ff ff       	call   24b0 <listen@plt>
    5dba:	85 c0                	test   %eax,%eax
    5dbc:	0f 88 b3 c8 ff ff    	js     2675 <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5dc2:	ba db 18 00 00       	mov    $0x18db,%edx
    5dc7:	48 8d 35 d5 23 00 00 	lea    0x23d5(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5dce:	bf 01 00 00 00       	mov    $0x1,%edi
    5dd3:	31 c0                	xor    %eax,%eax
    5dd5:	e8 06 c7 ff ff       	call   24e0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5dda:	48 8d 85 d0 fa ff ff 	lea    -0x530(%rbp),%rax
    5de1:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5de7:	48 89 d9             	mov    %rbx,%rcx
    5dea:	48 8d 95 b4 fa ff ff 	lea    -0x54c(%rbp),%rdx
    5df1:	48 89 c6             	mov    %rax,%rsi
  socklen_t client_addr_len = sizeof(client_addr);
    5df4:	c7 85 b4 fa ff ff 10 00 00 00 	movl   $0x10,-0x54c(%rbp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5dfe:	48 89 95 88 fa ff ff 	mov    %rdx,-0x578(%rbp)
    5e05:	48 89 85 90 fa ff ff 	mov    %rax,-0x570(%rbp)
    5e0c:	e8 4f fd ff ff       	call   5b60 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5e11:	bf 01 00 00 00       	mov    $0x1,%edi
    5e16:	be 10 00 00 00       	mov    $0x10,%esi
    5e1b:	e8 00 c6 ff ff       	call   2420 <calloc@plt>
    void *buf = malloc(size);
    5e20:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5e25:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    5e28:	e8 73 c6 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    5e2d:	48 85 c0             	test   %rax,%rax
    5e30:	0f 84 cf 04 00 00    	je     6305 <io_thread+0x6f5>
  iov->iov_base = zh_malloc(10);
    5e36:	49 89 06             	mov    %rax,(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    5e39:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5e3f:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
  iov->iov_len = 10;
    5e45:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    5e4d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5e50:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    5e57:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5e59:	f6 c1 02             	test   $0x2,%cl
    5e5c:	0f 85 2e 04 00 00    	jne    6290 <io_thread+0x680>
	if (next - head <= sq->ring_entries) {
    5e62:	89 d0                	mov    %edx,%eax
    5e64:	29 f0                	sub    %esi,%eax
    5e66:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    5e6c:	0f 82 19 c8 ff ff    	jb     268b <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5e72:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e75:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    5e7b:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5e7f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e82:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5e88:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5e8b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5e91:	49 8d 74 24 60       	lea    0x60(%r12),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5e96:	41 8b 54 24 60       	mov    0x60(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e9b:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5e9d:	48 89 b5 98 fa ff ff 	mov    %rsi,-0x568(%rbp)
    5ea4:	48 c1 e0 06          	shl    $0x6,%rax
    5ea8:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    5eaf:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5eb5:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5eb8:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5ec0:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    5ec4:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5ecc:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5ed4:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5ed8:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5edc:	e8 cf c4 ff ff       	call   23b0 <io_uring_submit@plt>
  while (data->running == 1) {
    5ee1:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5ee7:	4c 8d 8d b8 fa ff ff 	lea    -0x548(%rbp),%r9
    5eee:	4c 8d 95 c0 fb ff ff 	lea    -0x440(%rbp),%r10
    5ef5:	0f 85 ed 01 00 00    	jne    60e8 <io_thread+0x4d8>
    5efb:	4c 89 8d a0 fa ff ff 	mov    %r9,-0x560(%rbp)
    5f02:	4c 89 95 80 fa ff ff 	mov    %r10,-0x580(%rbp)
    5f09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f10:	48 8d 3d a2 22 00 00 	lea    0x22a2(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5f17:	e8 34 c4 ff ff       	call   2350 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5f1c:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5f22:	8b bd 90 fb ff ff    	mov    -0x470(%rbp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5f28:	c1 e9 0b             	shr    $0xb,%ecx
    5f2b:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5f2e:	48 8b 85 50 fb ff ff 	mov    -0x4b0(%rbp),%rax
    5f35:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5f37:	48 8b b5 48 fb ff ff 	mov    -0x4b8(%rbp),%rsi
    5f3e:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5f40:	39 d0                	cmp    %edx,%eax
    5f42:	74 34                	je     5f78 <io_thread+0x368>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5f44:	89 f8                	mov    %edi,%eax
    5f46:	21 d0                	and    %edx,%eax
    5f48:	d3 e0                	shl    %cl,%eax
    5f4a:	48 c1 e0 04          	shl    $0x4,%rax
    5f4e:	48 03 85 78 fb ff ff 	add    -0x488(%rbp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5f55:	f6 85 a9 fb ff ff 01 	testb  $0x1,-0x457(%rbp)
    5f5c:	0f 85 be 01 00 00    	jne    6120 <io_thread+0x510>
    5f62:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5f66:	0f 85 2c 03 00 00    	jne    6298 <io_thread+0x688>
			if (cqe->res < 0)
    5f6c:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5f6f:	83 c2 01             	add    $0x1,%edx
    5f72:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5f74:	85 c0                	test   %eax,%eax
    5f76:	79 b6                	jns    5f2e <io_thread+0x31e>
	*cqe_ptr = cqe;
    5f78:	48 c7 85 b8 fa ff ff 00 00 00 00 	movq   $0x0,-0x548(%rbp)
	return err;
    5f83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5f88:	48 8b b5 a0 fa ff ff 	mov    -0x560(%rbp),%rsi
    5f8f:	45 31 c0             	xor    %r8d,%r8d
    5f92:	31 d2                	xor    %edx,%edx
    5f94:	48 89 df             	mov    %rbx,%rdi
    5f97:	b9 01 00 00 00       	mov    $0x1,%ecx
    5f9c:	e8 2f c5 ff ff       	call   24d0 <__io_uring_get_cqe@plt>
    5fa1:	41 89 c5             	mov    %eax,%r13d
      if (cqe->user_data == 1) {
    5fa4:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    5fab:	48 83 38 01          	cmpq   $0x1,(%rax)
    5faf:	0f 84 f3 02 00 00    	je     62a8 <io_thread+0x698>
    5fb5:	48 8d 3d 23 22 00 00 	lea    0x2223(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5fbc:	e8 8f c3 ff ff       	call   2350 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5fc1:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    5fc8:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    5fcb:	45 85 ed             	test   %r13d,%r13d
    5fce:	0f 88 89 c6 ff ff    	js     265d <io_thread.cold>
      if (cqe->res < 0) {
    5fd4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5fd7:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
    5fda:	85 c0                	test   %eax,%eax
    5fdc:	0f 88 e5 02 00 00    	js     62c7 <io_thread+0x6b7>
      switch (req->event_type) {
    5fe2:	41 83 f8 01          	cmp    $0x1,%r8d
    5fe6:	0f 84 84 01 00 00    	je     6170 <io_thread+0x560>
    5fec:	41 83 f8 02          	cmp    $0x2,%r8d
    5ff0:	0f 84 aa 01 00 00    	je     61a0 <io_thread+0x590>
    5ff6:	45 85 c0             	test   %r8d,%r8d
    5ff9:	0f 85 59 01 00 00    	jne    6158 <io_thread+0x548>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5fff:	48 8b 95 88 fa ff ff 	mov    -0x578(%rbp),%rdx
    6006:	48 8b b5 90 fa ff ff 	mov    -0x570(%rbp),%rsi
    600d:	48 89 d9             	mov    %rbx,%rcx
    6010:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    6016:	e8 45 fb ff ff       	call   5b60 <add_accept_request>
              add_read_request(cqe->res, &ring);
    601b:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    6022:	48 89 de             	mov    %rbx,%rsi
    6025:	8b 78 08             	mov    0x8(%rax),%edi
    6028:	e8 83 f4 ff ff       	call   54b0 <add_read_request>
              free(req);
    602d:	4c 89 ff             	mov    %r15,%rdi
    6030:	e8 eb c2 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    6035:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
	if (cqe)
    603c:	48 85 c0             	test   %rax,%rax
    603f:	0f 85 13 01 00 00    	jne    6158 <io_thread+0x548>
	unsigned int head, next = sq->sqe_tail + 1;
    6045:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    604b:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    6051:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    6054:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    605b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    605d:	f6 c1 02             	test   $0x2,%cl
    6060:	74 00                	je     6062 <io_thread+0x452>
	if (next - head <= sq->ring_entries) {
    6062:	89 d0                	mov    %edx,%eax
    6064:	29 f0                	sub    %esi,%eax
    6066:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    606c:	0f 82 0f c6 ff ff    	jb     2681 <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    6072:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6075:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    607b:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    607f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6082:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6088:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    608b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6091:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6093:	41 8b 54 24 60       	mov    0x60(%r12),%edx
	sqe->user_data = (unsigned long) data;
    6098:	48 8b b5 98 fa ff ff 	mov    -0x568(%rbp),%rsi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    609f:	48 c1 e0 06          	shl    $0x6,%rax
    60a3:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    60aa:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    60b0:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    60b3:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    60bb:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    60bf:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    60c7:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    60cf:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    60d3:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    60d7:	e8 d4 c2 ff ff       	call   23b0 <io_uring_submit@plt>
  while (data->running == 1) {
    60dc:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    60e2:	0f 84 28 fe ff ff    	je     5f10 <io_thread+0x300>
    60e8:	48 8d 3d 29 21 00 00 	lea    0x2129(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    60ef:	e8 5c c2 ff ff       	call   2350 <puts@plt>
}
    60f4:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    60f8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    6101:	0f 85 25 02 00 00    	jne    632c <io_thread+0x71c>
    6107:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    610e:	31 c0                	xor    %eax,%eax
    6110:	5b                   	pop    %rbx
    6111:	41 5c                	pop    %r12
    6113:	41 5d                	pop    %r13
    6115:	41 5e                	pop    %r14
    6117:	41 5f                	pop    %r15
    6119:	5d                   	pop    %rbp
    611a:	c3                   	ret
    611b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    6120:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    6127:	48 85 c0             	test   %rax,%rax
    612a:	0f 84 58 fe ff ff    	je     5f88 <io_thread+0x378>
      if (cqe->user_data == 1) {
    6130:	48 83 38 01          	cmpq   $0x1,(%rax)
    6134:	0f 84 6e 01 00 00    	je     62a8 <io_thread+0x698>
    613a:	48 8d 3d 9e 20 00 00 	lea    0x209e(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    6141:	e8 0a c2 ff ff       	call   2350 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    6146:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    614d:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    6150:	e9 7f fe ff ff       	jmp    5fd4 <io_thread+0x3c4>
    6155:	0f 1f 00             	nopl   (%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6158:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
    615f:	8b 02                	mov    (%rdx),%eax
    6161:	83 c0 01             	add    $0x1,%eax
    6164:	89 02                	mov    %eax,(%rdx)
}
    6166:	e9 da fe ff ff       	jmp    6045 <io_thread+0x435>
    616b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
    6170:	85 c0                	test   %eax,%eax
    6172:	75 7c                	jne    61f0 <io_thread+0x5e0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6174:	48 8b 0d a5 4e 00 00 	mov    0x4ea5(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    617b:	ba 0f 00 00 00       	mov    $0xf,%edx
    6180:	be 01 00 00 00       	mov    $0x1,%esi
    6185:	48 8d 3d 7c 20 00 00 	lea    0x207c(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    618c:	e8 df c3 ff ff       	call   2570 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    6191:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    6198:	e9 9f fe ff ff       	jmp    603c <io_thread+0x42c>
    619d:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    61a0:	41 8b 47 04          	mov    0x4(%r15),%eax
    61a4:	45 31 ed             	xor    %r13d,%r13d
    61a7:	85 c0                	test   %eax,%eax
    61a9:	7e 20                	jle    61cb <io_thread+0x5bb>
    61ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
    61b0:	4c 89 e8             	mov    %r13,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    61b3:	49 83 c5 01          	add    $0x1,%r13
                  free(req->iov[i].iov_base);
    61b7:	48 c1 e0 04          	shl    $0x4,%rax
    61bb:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    61c0:	e8 5b c1 ff ff       	call   2320 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    61c5:	45 39 6f 04          	cmp    %r13d,0x4(%r15)
    61c9:	7f e5                	jg     61b0 <io_thread+0x5a0>
              close(req->client_socket);
    61cb:	41 8b 7f 08          	mov    0x8(%r15),%edi
    61cf:	e8 1c c2 ff ff       	call   23f0 <close@plt>
              free(req);
    61d4:	4c 89 ff             	mov    %r15,%rdi
    61d7:	e8 44 c1 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    61dc:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    61e3:	e9 54 fe ff ff       	jmp    603c <io_thread+0x42c>
    61e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    61f0:	49 8b 57 10          	mov    0x10(%r15),%rdx
    61f4:	48 8b 85 80 fa ff ff 	mov    -0x580(%rbp),%rax
    61fb:	48 8d 75 c0          	lea    -0x40(%rbp),%rsi
    61ff:	eb 14                	jmp    6215 <io_thread+0x605>
    6201:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6208:	48 83 c0 01          	add    $0x1,%rax
    620c:	48 83 c2 01          	add    $0x1,%rdx
    6210:	48 39 c6             	cmp    %rax,%rsi
    6213:	74 4b                	je     6260 <io_thread+0x650>
        dest[i] = src[i];
    6215:	0f b6 0a             	movzbl (%rdx),%ecx
    6218:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    621a:	80 f9 0d             	cmp    $0xd,%cl
    621d:	75 e9                	jne    6208 <io_thread+0x5f8>
    621f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    6223:	75 e3                	jne    6208 <io_thread+0x5f8>
            dest[i] = '\0';
    6225:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    6228:	48 8b bd 80 fa ff ff 	mov    -0x580(%rbp),%rdi
    622f:	48 89 da             	mov    %rbx,%rdx
    6232:	41 8b 77 08          	mov    0x8(%r15),%esi
    6236:	e8 35 f7 ff ff       	call   5970 <handle_http_method>
              free(req->iov[0].iov_base);
    623b:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    623f:	e8 dc c0 ff ff       	call   2320 <free@plt>
              free(req);
    6244:	4c 89 ff             	mov    %r15,%rdi
    6247:	e8 d4 c0 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    624c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    6253:	e9 e4 fd ff ff       	jmp    603c <io_thread+0x42c>
    6258:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6260:	48 8b 0d b9 4d 00 00 	mov    0x4db9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6267:	ba 12 00 00 00       	mov    $0x12,%edx
    626c:	be 01 00 00 00       	mov    $0x1,%esi
    6271:	48 8d 3d e6 1e 00 00 	lea    0x1ee6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6278:	e8 f3 c2 ff ff       	call   2570 <fwrite@plt>
        exit(1);
    627d:	bf 01 00 00 00       	mov    $0x1,%edi
    6282:	e8 c9 c2 ff ff       	call   2550 <exit@plt>
    6287:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    6290:	e9 cd fb ff ff       	jmp    5e62 <io_thread+0x252>
    6295:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    6298:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	return err;
    629f:	e9 8c fe ff ff       	jmp    6130 <io_thread+0x520>
    62a4:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    62a8:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    62af:	48 8d 3d 15 1f 00 00 	lea    0x1f15(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    62b6:	8b 02                	mov    (%rdx),%eax
    62b8:	83 c0 01             	add    $0x1,%eax
    62bb:	89 02                	mov    %eax,(%rdx)
    62bd:	e8 8e c0 ff ff       	call   2350 <puts@plt>
    62c2:	e9 21 fe ff ff       	jmp    60e8 <io_thread+0x4d8>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    62c7:	f7 d8                	neg    %eax
    62c9:	44 89 85 ac fa ff ff 	mov    %r8d,-0x554(%rbp)
    62d0:	89 c7                	mov    %eax,%edi
    62d2:	e8 d9 c2 ff ff       	call   25b0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    62d7:	48 8b 3d 42 4d 00 00 	mov    0x4d42(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    62de:	be 01 00 00 00       	mov    $0x1,%esi
    62e3:	44 8b 85 ac fa ff ff 	mov    -0x554(%rbp),%r8d
    62ea:	48 89 c1             	mov    %rax,%rcx
    62ed:	48 8d 15 f4 22 00 00 	lea    0x22f4(%rip),%rdx        # 85e8 <_IO_stdin_used+0x5e8>
    62f4:	31 c0                	xor    %eax,%eax
    62f6:	e8 85 c2 ff ff       	call   2580 <__fprintf_chk@plt>
          exit(1);
    62fb:	bf 01 00 00 00       	mov    $0x1,%edi
    6300:	e8 4b c2 ff ff       	call   2550 <exit@plt>
    6305:	48 8b 0d 14 4d 00 00 	mov    0x4d14(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    630c:	ba 28 00 00 00       	mov    $0x28,%edx
    6311:	be 01 00 00 00       	mov    $0x1,%esi
    6316:	48 8d 3d 9b 22 00 00 	lea    0x229b(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    631d:	e8 4e c2 ff ff       	call   2570 <fwrite@plt>
        exit(1);
    6322:	bf 01 00 00 00       	mov    $0x1,%edi
    6327:	e8 24 c2 ff ff       	call   2550 <exit@plt>
}
    632c:	e8 6f c0 ff ff       	call   23a0 <__stack_chk_fail@plt>
    6331:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    633c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006340 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    6340:	f3 0f 1e fa          	endbr64
    6344:	55                   	push   %rbp
    6345:	48 89 e5             	mov    %rsp,%rbp
    6348:	41 57                	push   %r15
    634a:	41 56                	push   %r14
    634c:	41 55                	push   %r13
    634e:	41 54                	push   %r12
    6350:	53                   	push   %rbx
    6351:	48 83 ec 08          	sub    $0x8,%rsp
    6355:	ff 15 8d 4c 00 00    	call   *0x4c8d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    635b:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    6362:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
int barriered_work_ingest(struct BarrierTask *data) {
    6368:	49 89 fd             	mov    %rdi,%r13
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    636b:	85 c9                	test   %ecx,%ecx
    636d:	7e 54                	jle    63c3 <barriered_work_ingest+0x83>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    636f:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6373:	45 31 f6             	xor    %r14d,%r14d
    6376:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6380:	4a 8b 04 f7          	mov    (%rdi,%r14,8),%rax
    6384:	4e 8d 3c f5 00 00 00 00 	lea    0x0(,%r14,8),%r15
    638c:	31 db                	xor    %ebx,%ebx
    638e:	8b 10                	mov    (%rax),%edx
    6390:	85 d2                	test   %edx,%edx
    6392:	7e 26                	jle    63ba <barriered_work_ingest+0x7a>
    6394:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    6398:	49 89 dc             	mov    %rbx,%r12
    639b:	49 c1 e4 08          	shl    $0x8,%r12
    639f:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    63a3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    63aa:	74 2c                	je     63d8 <barriered_work_ingest+0x98>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    63ac:	48 83 c3 01          	add    $0x1,%rbx
    63b0:	39 da                	cmp    %ebx,%edx
    63b2:	7f e4                	jg     6398 <barriered_work_ingest+0x58>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    63b4:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    63ba:	49 83 c6 01          	add    $0x1,%r14
    63be:	44 39 f1             	cmp    %r14d,%ecx
    63c1:	7f bd                	jg     6380 <barriered_work_ingest+0x40>
}
    63c3:	48 83 c4 08          	add    $0x8,%rsp
    63c7:	31 c0                	xor    %eax,%eax
    63c9:	5b                   	pop    %rbx
    63ca:	41 5c                	pop    %r12
    63cc:	41 5d                	pop    %r13
    63ce:	41 5e                	pop    %r14
    63d0:	41 5f                	pop    %r15
    63d2:	5d                   	pop    %rbp
    63d3:	c3                   	ret
    63d4:	0f 1f 40 00          	nopl   0x0(%rax)
        data->ingest_count++;
    63d8:	49 83 85 68 01 00 00 01 	addq   $0x1,0x168(%r13)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    63e0:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    63e7:	bf 04 00 00 00       	mov    $0x4,%edi
    63ec:	48 c1 e6 05          	shl    $0x5,%rsi
    63f0:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    63f7:	48 83 c6 10          	add    $0x10,%rsi
    63fb:	e8 70 bf ff ff       	call   2370 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6400:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
    6407:	48 8b 40 50          	mov    0x50(%rax),%rax
    640b:	4a 8b 04 38          	mov    (%rax,%r15,1),%rax
    640f:	4c 03 60 08          	add    0x8(%rax),%r12
    6413:	41 8b 84 24 94 00 00 00 	mov    0x94(%r12),%eax
        data->thread->buffers[b]->buffer[x].available = 0;
    641b:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6427:	83 c0 01             	add    $0x1,%eax
    642a:	99                   	cltd
    642b:	41 f7 bc 24 90 00 00 00 	idivl  0x90(%r12)
    6433:	41 89 94 24 94 00 00 00 	mov    %edx,0x94(%r12)
        asm volatile ("sfence" ::: "memory");
    643b:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    643e:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
    6445:	48 83 c3 01          	add    $0x1,%rbx
    6449:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    644d:	4a 8b 04 3f          	mov    (%rdi,%r15,1),%rax
    6451:	8b 10                	mov    (%rax),%edx
    6453:	39 da                	cmp    %ebx,%edx
    6455:	0f 8f 39 ff ff ff    	jg     6394 <barriered_work_ingest+0x54>
    645b:	e9 54 ff ff ff       	jmp    63b4 <barriered_work_ingest+0x74>

0000000000006460 <barriered_thread>:
void* barriered_thread(void *arg) {
    6460:	f3 0f 1e fa          	endbr64
    6464:	55                   	push   %rbp
    6465:	48 89 e5             	mov    %rsp,%rbp
    6468:	41 57                	push   %r15
    646a:	41 56                	push   %r14
    646c:	41 55                	push   %r13
    646e:	41 54                	push   %r12
    6470:	53                   	push   %rbx
    6471:	48 83 ec 08          	sub    $0x8,%rsp
    6475:	ff 15 6d 4b 00 00    	call   *0x4b6d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  int waiting = 0;
    647b:	45 31 e4             	xor    %r12d,%r12d
  int t = 0;
    647e:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
    6481:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    6484:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6488:	0f 85 1c 02 00 00    	jne    66aa <barriered_thread+0x24a>
    if (t >= data->task_count) {
    648e:	8b 43 40             	mov    0x40(%rbx),%eax
    6491:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6498:	41 39 c5             	cmp    %eax,%r13d
    649b:	0f 8d 6f 01 00 00    	jge    6610 <barriered_thread+0x1b0>
    64a1:	49 63 fd             	movslq %r13d,%rdi
    64a4:	48 c1 e7 09          	shl    $0x9,%rdi
    64a8:	49 89 fe             	mov    %rdi,%r14
    64ab:	eb 32                	jmp    64df <barriered_thread+0x7f>
    64ad:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    64b0:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    64b4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    64b8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    64bc:	48 8b 78 38          	mov    0x38(%rax),%rdi
    64c0:	4c 01 f7             	add    %r14,%rdi
    64c3:	e8 78 fe ff ff       	call   6340 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    64c8:	8b 43 40             	mov    0x40(%rbx),%eax
    64cb:	41 83 c5 01          	add    $0x1,%r13d
    64cf:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    64d6:	44 39 e8             	cmp    %r13d,%eax
    64d9:	0f 8e c1 01 00 00    	jle    66a0 <barriered_thread+0x240>
      if (data->tasks[t].available == 1) {
    64df:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    64e3:	4a 8d 34 32          	lea    (%rdx,%r14,1),%rsi
    64e7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    64ee:	75 c0                	jne    64b0 <barriered_thread+0x50>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    64f0:	8b 7b 28             	mov    0x28(%rbx),%edi
          previous = t - 1;
    64f3:	83 e8 01             	sub    $0x1,%eax
    64f6:	41 8d 4d ff          	lea    -0x1(%r13),%ecx
    64fa:	45 85 ed             	test   %r13d,%r13d
    64fd:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6500:	85 ff                	test   %edi,%edi
    6502:	0f 8e d8 01 00 00    	jle    66e0 <barriered_thread+0x280>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6508:	48 63 c8             	movslq %eax,%rcx
    650b:	48 8b 43 18          	mov    0x18(%rbx),%rax
    650f:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    6512:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6515:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    651c:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6523:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    6527:	45 31 ff             	xor    %r15d,%r15d
    652a:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    652e:	66 90                	xchg   %ax,%ax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6530:	48 8b 10             	mov    (%rax),%rdx
    6533:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6537:	49 01 cb             	add    %rcx,%r11
    653a:	4c 89 da             	mov    %r11,%rdx
    653d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6544:	75 04                	jne    654a <barriered_thread+0xea>
            arrived++;
    6546:	41 83 c7 01          	add    $0x1,%r15d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    654a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    6551:	75 04                	jne    6557 <barriered_thread+0xf7>
            prearrive++;
    6553:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6557:	48 83 c0 08          	add    $0x8,%rax
    655b:	48 39 c6             	cmp    %rax,%rsi
    655e:	75 d0                	jne    6530 <barriered_thread+0xd0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    6560:	45 85 d2             	test   %r10d,%r10d
    6563:	0f 84 bf 00 00 00    	je     6628 <barriered_thread+0x1c8>
    6569:	44 39 d7             	cmp    %r10d,%edi
    656c:	0f 84 b6 00 00 00    	je     6628 <barriered_thread+0x1c8>
        if (arrived == 0 || arrived == data->thread_count) {
    6572:	45 85 ff             	test   %r15d,%r15d
    6575:	74 0a                	je     6581 <barriered_thread+0x121>
    6577:	44 39 7b 28          	cmp    %r15d,0x28(%rbx)
    657b:	0f 85 b0 01 00 00    	jne    6731 <barriered_thread+0x2d1>
    6581:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    6585:	4c 01 f2             	add    %r14,%rdx
    6588:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    658f:	45 85 ed             	test   %r13d,%r13d
    6592:	75 14                	jne    65a8 <barriered_thread+0x148>
    6594:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    659b:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    65a2:	0f 8c 18 01 00 00    	jl     66c0 <barriered_thread+0x260>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    65a8:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    65ac:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    65b0:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    65ba:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    65be:	48 8b 78 38          	mov    0x38(%rax),%rdi
    65c2:	4c 01 f7             	add    %r14,%rdi
    65c5:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    65cb:	48 8b 43 38          	mov    0x38(%rbx),%rax
    65cf:	4c 01 f0             	add    %r14,%rax
    65d2:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    65d9:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    65dc:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    65e1:	83 e8 01             	sub    $0x1,%eax
    65e4:	44 39 e8             	cmp    %r13d,%eax
    65e7:	74 57                	je     6640 <barriered_thread+0x1e0>
          asm volatile ("sfence" ::: "memory");
    65e9:	0f ae f8             	sfence
          if (waiting == 0) {
    65ec:	45 85 e4             	test   %r12d,%r12d
    65ef:	74 7f                	je     6670 <barriered_thread+0x210>
        int arrived = 0; 
    65f1:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    65f7:	e9 cc fe ff ff       	jmp    64c8 <barriered_thread+0x68>
  while (data->running == 1) {
    65fc:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6600:	0f 85 a4 00 00 00    	jne    66aa <barriered_thread+0x24a>
    6606:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->cycles++;
    6610:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    6618:	85 c0                	test   %eax,%eax
    661a:	7e e0                	jle    65fc <barriered_thread+0x19c>
    661c:	45 31 ed             	xor    %r13d,%r13d
    661f:	e9 7d fe ff ff       	jmp    64a1 <barriered_thread+0x41>
    6624:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6628:	41 83 fc 01          	cmp    $0x1,%r12d
    662c:	0f 84 be 00 00 00    	je     66f0 <barriered_thread+0x290>
        int arrived = 0; 
    6632:	45 31 e4             	xor    %r12d,%r12d
    6635:	e9 38 ff ff ff       	jmp    6572 <barriered_thread+0x112>
    663a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6640:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6647:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    664e:	7d 99                	jge    65e9 <barriered_thread+0x189>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    6650:	48 c1 e6 04          	shl    $0x4,%rsi
    6654:	bf 04 00 00 00       	mov    $0x4,%edi
    6659:	48 03 73 70          	add    0x70(%rbx),%rsi
    665d:	e8 0e bd ff ff       	call   2370 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6662:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    666a:	e9 7a ff ff ff       	jmp    65e9 <barriered_thread+0x189>
    666f:	90                   	nop
            data->task_snapshot[data->task_timestamp_count].task = t;
    6670:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6677:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    667c:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6680:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6687:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    668b:	44 89 6e 20          	mov    %r13d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    668f:	e8 dc bc ff ff       	call   2370 <clock_gettime@plt>
            waiting = 1;
    6694:	e9 58 ff ff ff       	jmp    65f1 <barriered_thread+0x191>
    6699:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    66a0:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    66a4:	0f 84 ee fd ff ff    	je     6498 <barriered_thread+0x38>
}
    66aa:	48 83 c4 08          	add    $0x8,%rsp
    66ae:	31 c0                	xor    %eax,%eax
    66b0:	5b                   	pop    %rbx
    66b1:	41 5c                	pop    %r12
    66b3:	41 5d                	pop    %r13
    66b5:	41 5e                	pop    %r14
    66b7:	41 5f                	pop    %r15
    66b9:	5d                   	pop    %rbp
    66ba:	c3                   	ret
    66bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    66c0:	48 c1 e6 04          	shl    $0x4,%rsi
    66c4:	bf 04 00 00 00       	mov    $0x4,%edi
    66c9:	48 03 73 68          	add    0x68(%rbx),%rsi
    66cd:	e8 9e bc ff ff       	call   2370 <clock_gettime@plt>
          data->tasks[t].available = 0;
    66d2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    66d6:	4c 01 f2             	add    %r14,%rdx
    66d9:	e9 ca fe ff ff       	jmp    65a8 <barriered_thread+0x148>
    66de:	66 90                	xchg   %ax,%ax
          if (waiting == 1) {
    66e0:	41 83 fc 01          	cmp    $0x1,%r12d
    66e4:	0f 85 9b fe ff ff    	jne    6585 <barriered_thread+0x125>
        int arrived = 0; 
    66ea:	45 31 ff             	xor    %r15d,%r15d
    66ed:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    66f0:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    66f7:	bf 04 00 00 00       	mov    $0x4,%edi
    66fc:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6700:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6707:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    670c:	e8 5f bc ff ff       	call   2370 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    6711:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6718:	48 83 c0 01          	add    $0x1,%rax
    671c:	48 99                	cqto
    671e:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    6725:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    672c:	e9 01 ff ff ff       	jmp    6632 <barriered_thread+0x1d2>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    6731:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6735:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6739:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    673d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6741:	4c 01 f7             	add    %r14,%rdi
    6744:	e8 f7 fb ff ff       	call   6340 <barriered_work_ingest>
          break;
    6749:	e9 36 fd ff ff       	jmp    6484 <barriered_thread+0x24>
    674e:	66 90                	xchg   %ax,%ax

0000000000006750 <receive>:
int receive(struct BarrierTask *data) {
    6750:	f3 0f 1e fa          	endbr64
    6754:	55                   	push   %rbp
    6755:	48 89 e5             	mov    %rsp,%rbp
    6758:	41 57                	push   %r15
    675a:	41 56                	push   %r14
    675c:	41 55                	push   %r13
    675e:	41 54                	push   %r12
    6760:	53                   	push   %rbx
    6761:	48 83 ec 18          	sub    $0x18,%rsp
    6765:	ff 15 7d 48 00 00    	call   *0x487d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    676b:	44 8b bf 40 01 00 00 	mov    0x140(%rdi),%r15d
int receive(struct BarrierTask *data) {
    6772:	48 89 fe             	mov    %rdi,%rsi
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6775:	45 85 ff             	test   %r15d,%r15d
    6778:	0f 8e 33 01 00 00    	jle    68b1 <receive+0x161>
    if (n == data->thread->real_thread_index) { continue; }
    677e:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    6785:	45 31 ed             	xor    %r13d,%r13d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6788:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    678a:	4c 63 60 08          	movslq 0x8(%rax),%r12
    678e:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    6792:	4d 89 e6             	mov    %r12,%r14
    6795:	0f 1f 00             	nopl   (%rax)
    6798:	41 39 de             	cmp    %ebx,%r14d
    679b:	0f 84 fd 00 00 00    	je     689e <receive+0x14e>
    struct Data *me = data->mailboxes[n].lower;
    67a1:	48 8b 86 70 01 00 00 	mov    0x170(%rsi),%rax
    67a8:	4a 8b 14 28          	mov    (%rax,%r13,1),%rdx
    if (me->available_reading == 1) {
    67ac:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    67b2:	83 f8 01             	cmp    $0x1,%eax
    67b5:	74 11                	je     67c8 <receive+0x78>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    67b7:	83 ba 18 03 00 00 02 	cmpl   $0x2,0x318(%rdx)
    67be:	75 08                	jne    67c8 <receive+0x78>
    67c0:	85 c0                	test   %eax,%eax
    67c2:	0f 84 d6 00 00 00    	je     689e <receive+0x14e>
    for (; me->messages_count > 0 ; ) {
    67c8:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    67cf:	48 85 ff             	test   %rdi,%rdi
    67d2:	0f 8e a8 00 00 00    	jle    6880 <receive+0x130>
    67d8:	4c 8b 8e 78 01 00 00 	mov    0x178(%rsi),%r9
    67df:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    67e6:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
    67ea:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    67ed:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    67f1:	49 01 f9             	add    %rdi,%r9
    67f4:	49 01 f8             	add    %rdi,%r8
    67f7:	48 03 ba 10 03 00 00 	add    0x310(%rdx),%rdi
    67fe:	eb 06                	jmp    6806 <receive+0xb6>
    for (; me->messages_count > 0 ; ) {
    6800:	48 83 e8 01          	sub    $0x1,%rax
    6804:	72 7a                	jb     6880 <receive+0x130>
      data->sends++;
    6806:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
    6809:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
    6810:	48 29 c1             	sub    %rax,%rcx
    6813:	48 89 8e 78 01 00 00 	mov    %rcx,0x178(%rsi)
      data->n++;
    681a:	4c 89 c1             	mov    %r8,%rcx
    681d:	48 29 c1             	sub    %rax,%rcx
    6820:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
    6827:	48 89 f9             	mov    %rdi,%rcx
    682a:	48 29 c1             	sub    %rax,%rcx
    682d:	48 89 8a 10 03 00 00 	mov    %rcx,0x310(%rdx)
      if (me->messages[x]->group == data->group) {
    6834:	48 63 c8             	movslq %eax,%rcx
    6837:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    683b:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    683f:	75 bf                	jne    6800 <receive+0xb0>
    6841:	4c 39 61 08          	cmp    %r12,0x8(%rcx)
    6845:	75 b9                	jne    6800 <receive+0xb0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    6847:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    684b:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    684d:	bf 01 00 00 00       	mov    $0x1,%edi
    6852:	ba 01 00 00 00       	mov    $0x1,%edx
    6857:	48 8d 35 b2 1d 00 00 	lea    0x1db2(%rip),%rsi        # 8610 <_IO_stdin_used+0x610>
    685e:	48 63 40 04          	movslq 0x4(%rax),%rax
    6862:	4c 39 e0             	cmp    %r12,%rax
    6865:	0f 94 c1             	sete   %cl
    6868:	31 c0                	xor    %eax,%eax
    686a:	e8 71 bc ff ff       	call   24e0 <__printf_chk@plt>
        exit(1);
    686f:	bf 01 00 00 00       	mov    $0x1,%edi
    6874:	e8 d7 bc ff ff       	call   2550 <exit@plt>
    6879:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      me->available_reading = 0;
    6880:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    688a:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
    6894:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    689e:	83 c3 01             	add    $0x1,%ebx
    68a1:	49 81 c5 80 01 00 00 	add    $0x180,%r13
    68a8:	44 39 fb             	cmp    %r15d,%ebx
    68ab:	0f 85 e7 fe ff ff    	jne    6798 <receive+0x48>
  asm volatile ("sfence" ::: "memory");
    68b1:	0f ae f8             	sfence
}
    68b4:	48 83 c4 18          	add    $0x18,%rsp
    68b8:	31 c0                	xor    %eax,%eax
    68ba:	5b                   	pop    %rbx
    68bb:	41 5c                	pop    %r12
    68bd:	41 5d                	pop    %r13
    68bf:	41 5e                	pop    %r14
    68c1:	41 5f                	pop    %r15
    68c3:	5d                   	pop    %rbp
    68c4:	c3                   	ret
    68c5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000068d0 <sendm>:
int sendm(struct BarrierTask *data) {
    68d0:	f3 0f 1e fa          	endbr64
    68d4:	55                   	push   %rbp
    68d5:	48 89 e5             	mov    %rsp,%rbp
    68d8:	41 57                	push   %r15
    68da:	41 56                	push   %r14
    68dc:	41 55                	push   %r13
    68de:	41 54                	push   %r12
    68e0:	53                   	push   %rbx
    68e1:	48 83 ec 28          	sub    $0x28,%rsp
    68e5:	ff 15 fd 46 00 00    	call   *0x46fd(%rip)        # afe8 <mcount@GLIBC_2.2.5>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    68eb:	31 f6                	xor    %esi,%esi
    68ed:	31 c0                	xor    %eax,%eax
    68ef:	8b 8f 40 01 00 00    	mov    0x140(%rdi),%ecx
int sendm(struct BarrierTask *data) {
    68f5:	48 89 fa             	mov    %rdi,%rdx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    68f8:	85 c9                	test   %ecx,%ecx
    68fa:	7f 2f                	jg     692b <sendm+0x5b>
    68fc:	e9 cf 00 00 00       	jmp    69d0 <sendm+0x100>
    6901:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6908:	48 c7 81 00 01 00 00 00 00 00 00 	movq   $0x0,0x100(%rcx)
    6913:	8b 8a 40 01 00 00    	mov    0x140(%rdx),%ecx
    6919:	83 c0 01             	add    $0x1,%eax
    691c:	48 81 c6 80 01 00 00 	add    $0x180,%rsi
    6923:	39 c8                	cmp    %ecx,%eax
    6925:	0f 8d a5 00 00 00    	jge    69d0 <sendm+0x100>
        if (n == data->thread->real_thread_index) { continue; }
    692b:	4c 8b 82 28 01 00 00 	mov    0x128(%rdx),%r8
    6932:	41 39 40 08          	cmp    %eax,0x8(%r8)
    6936:	74 e1                	je     6919 <sendm+0x49>
        struct Data *them = data->mailboxes[n].higher;
    6938:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    693f:	48 01 f1             	add    %rsi,%rcx
        data->mailboxes[n].counter++;
    6942:	48 8b 99 00 01 00 00 	mov    0x100(%rcx),%rbx
        struct Data *them = data->mailboxes[n].higher;
    6949:	48 8b b9 80 00 00 00 	mov    0x80(%rcx),%rdi
        data->mailboxes[n].counter++;
    6950:	4c 8d 4b 01          	lea    0x1(%rbx),%r9
        if (data->mailboxes[n].counter > limit) {
    6954:	49 83 f9 02          	cmp    $0x2,%r9
    6958:	7f ae                	jg     6908 <sendm+0x38>
    695a:	4c 89 89 00 01 00 00 	mov    %r9,0x100(%rcx)
        if (data->mailboxes[n].counter < limit) {
    6961:	75 55                	jne    69b8 <sendm+0xe8>
        if (them->messages_count > 0) {
    6963:	4c 8b 8f 80 00 00 00 	mov    0x80(%rdi),%r9
    696a:	4d 85 c9             	test   %r9,%r9
    696d:	7f 49                	jg     69b8 <sendm+0xe8>
        if (them->available_sending == 1) {
    696f:	44 8b 97 00 01 00 00 	mov    0x100(%rdi),%r10d
    6976:	41 83 fa 01          	cmp    $0x1,%r10d
    697a:	74 0e                	je     698a <sendm+0xba>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    697c:	83 bf 18 03 00 00 02 	cmpl   $0x2,0x318(%rdi)
    6983:	75 05                	jne    698a <sendm+0xba>
    6985:	45 85 d2             	test   %r10d,%r10d
    6988:	74 2e                	je     69b8 <sendm+0xe8>
        if (data->sending == 1) {
    698a:	83 ba 80 01 00 00 01 	cmpl   $0x1,0x180(%rdx)
    6991:	74 55                	je     69e8 <sendm+0x118>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter >= limit) {
    6993:	83 b9 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rcx)
    699a:	75 1c                	jne    69b8 <sendm+0xe8>
          data->mailboxes[n].counter = 0;
    699c:	48 c7 81 00 01 00 00 00 00 00 00 	movq   $0x0,0x100(%rcx)
          data->thread->have_foreign = 1;
    69a7:	41 c7 80 d8 00 00 00 01 00 00 00 	movl   $0x1,0xd8(%r8)
    69b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    69b8:	8b 8a 40 01 00 00    	mov    0x140(%rdx),%ecx
    69be:	83 c0 01             	add    $0x1,%eax
    69c1:	48 81 c6 80 01 00 00 	add    $0x180,%rsi
    69c8:	39 c8                	cmp    %ecx,%eax
    69ca:	0f 8c 5b ff ff ff    	jl     692b <sendm+0x5b>
      asm volatile ("sfence" ::: "memory");
    69d0:	0f ae f8             	sfence
}
    69d3:	48 83 c4 28          	add    $0x28,%rsp
    69d7:	31 c0                	xor    %eax,%eax
    69d9:	5b                   	pop    %rbx
    69da:	41 5c                	pop    %r12
    69dc:	41 5d                	pop    %r13
    69de:	41 5e                	pop    %r14
    69e0:	41 5f                	pop    %r15
    69e2:	5d                   	pop    %rbp
    69e3:	c3                   	ret
    69e4:	0f 1f 40 00          	nopl   0x0(%rax)
          for (; them->messages_count < min;) {
    69e8:	4c 63 af 88 00 00 00 	movslq 0x88(%rdi),%r13
    69ef:	4d 39 e9             	cmp    %r13,%r9
    69f2:	0f 8d b8 00 00 00    	jge    6ab0 <sendm+0x1e0>
    69f8:	48 8b 9a 08 01 00 00 	mov    0x108(%rdx),%rbx
    69ff:	4d 89 ec             	mov    %r13,%r12
    6a02:	4d 29 cc             	sub    %r9,%r12
    6a05:	48 89 5d b8          	mov    %rbx,-0x48(%rbp)
    6a09:	48 8b 9f 08 03 00 00 	mov    0x308(%rdi),%rbx
    6a10:	4d 8d 54 24 ff       	lea    -0x1(%r12),%r10
    6a15:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
            them->messages[them->messages_count++] = data->message; 
    6a19:	48 8b 1f             	mov    (%rdi),%rbx
    6a1c:	49 83 fa 02          	cmp    $0x2,%r10
    6a20:	0f 86 2a 01 00 00    	jbe    6b50 <sendm+0x280>
    6a26:	4e 8d 14 cd 00 00 00 00 	lea    0x0(,%r9,8),%r10
    6a2e:	4e 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%r11
    6a36:	4e 8d 34 13          	lea    (%rbx,%r10,1),%r14
    6a3a:	4c 8d ba 88 01 00 00 	lea    0x188(%rdx),%r15
    6a41:	4c 89 75 c8          	mov    %r14,-0x38(%rbp)
    6a45:	4e 8d 34 1b          	lea    (%rbx,%r11,1),%r14
    6a49:	4d 39 f7             	cmp    %r14,%r15
    6a4c:	0f 83 86 00 00 00    	jae    6ad8 <sendm+0x208>
    6a52:	4c 8d b2 90 01 00 00 	lea    0x190(%rdx),%r14
    6a59:	4c 39 75 c8          	cmp    %r14,-0x38(%rbp)
    6a5d:	73 79                	jae    6ad8 <sendm+0x208>
    6a5f:	49 01 da             	add    %rbx,%r10
    6a62:	4e 8d 0c 1b          	lea    (%rbx,%r11,1),%r9
    6a66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6a70:	4c 8b 9a 88 01 00 00 	mov    0x188(%rdx),%r11
          for (; them->messages_count < min;) {
    6a77:	49 83 c2 08          	add    $0x8,%r10
            them->messages[them->messages_count++] = data->message; 
    6a7b:	4d 89 5a f8          	mov    %r11,-0x8(%r10)
          for (; them->messages_count < min;) {
    6a7f:	4d 39 d1             	cmp    %r10,%r9
    6a82:	75 ec                	jne    6a70 <sendm+0x1a0>
    6a84:	0f 1f 40 00          	nopl   0x0(%rax)
    6a88:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
    6a8c:	4c 8b 7d c0          	mov    -0x40(%rbp),%r15
    6a90:	4d 01 e1             	add    %r12,%r9
    6a93:	4d 01 e7             	add    %r12,%r15
    6a96:	4c 89 8a 08 01 00 00 	mov    %r9,0x108(%rdx)
    6a9d:	4c 89 bf 08 03 00 00 	mov    %r15,0x308(%rdi)
    6aa4:	4c 89 af 80 00 00 00 	mov    %r13,0x80(%rdi)
    6aab:	4e 89 5c eb f8       	mov    %r11,-0x8(%rbx,%r13,8)
          them->available_sending = 0;
    6ab0:	c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdi)
          them->available_reading = 1;
    6aba:	c7 87 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdi)
          them->available_receiving = 1;
    6ac4:	c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdi)
    6ace:	e9 c0 fe ff ff       	jmp    6993 <sendm+0xc3>
    6ad3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6ad8:	4d 89 e6             	mov    %r12,%r14
    6adb:	4c 8b 9a 88 01 00 00 	mov    0x188(%rdx),%r11
    6ae2:	4c 8b 55 c8          	mov    -0x38(%rbp),%r10
    6ae6:	49 d1 ee             	shr    %r14
    6ae9:	49 c1 e6 04          	shl    $0x4,%r14
    6aed:	66 49 0f 6e c3       	movq   %r11,%xmm0
    6af2:	4f 8d 3c 32          	lea    (%r10,%r14,1),%r15
    6af6:	41 83 e6 10          	and    $0x10,%r14d
    6afa:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    6afe:	74 10                	je     6b10 <sendm+0x240>
            them->messages[them->messages_count++] = data->message; 
    6b00:	41 0f 11 02          	movups %xmm0,(%r10)
          for (; them->messages_count < min;) {
    6b04:	49 83 c2 10          	add    $0x10,%r10
    6b08:	4d 39 fa             	cmp    %r15,%r10
    6b0b:	74 15                	je     6b22 <sendm+0x252>
    6b0d:	0f 1f 00             	nopl   (%rax)
            them->messages[them->messages_count++] = data->message; 
    6b10:	41 0f 11 02          	movups %xmm0,(%r10)
    6b14:	49 83 c2 20          	add    $0x20,%r10
    6b18:	41 0f 11 42 f0       	movups %xmm0,-0x10(%r10)
          for (; them->messages_count < min;) {
    6b1d:	4d 39 fa             	cmp    %r15,%r10
    6b20:	75 ee                	jne    6b10 <sendm+0x240>
    6b22:	4d 89 e2             	mov    %r12,%r10
    6b25:	49 83 e2 fe          	and    $0xfffffffffffffffe,%r10
    6b29:	4d 01 d1             	add    %r10,%r9
    6b2c:	41 f6 c4 01          	test   $0x1,%r12b
    6b30:	0f 84 52 ff ff ff    	je     6a88 <sendm+0x1b8>
            them->messages[them->messages_count++] = data->message; 
    6b36:	4c 8b 9a 88 01 00 00 	mov    0x188(%rdx),%r11
    6b3d:	4e 89 1c cb          	mov    %r11,(%rbx,%r9,8)
          for (; them->messages_count < min;) {
    6b41:	e9 42 ff ff ff       	jmp    6a88 <sendm+0x1b8>
    6b46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6b50:	4e 8d 14 cd 00 00 00 00 	lea    0x0(,%r9,8),%r10
    6b58:	4e 8d 1c ed 00 00 00 00 	lea    0x0(,%r13,8),%r11
    6b60:	e9 fa fe ff ff       	jmp    6a5f <sendm+0x18f>
    6b65:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000006b70 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6b70:	f3 0f 1e fa          	endbr64
    6b74:	55                   	push   %rbp
    6b75:	48 89 e5             	mov    %rsp,%rbp
    6b78:	41 57                	push   %r15
    6b7a:	41 56                	push   %r14
    6b7c:	41 55                	push   %r13
    6b7e:	41 54                	push   %r12
    6b80:	53                   	push   %rbx
    6b81:	48 83 ec 58          	sub    $0x58,%rsp
    6b85:	ff 15 5d 44 00 00    	call   *0x445d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
        int t = data->task_index;
    6b8b:	44 8b 77 04          	mov    0x4(%rdi),%r14d
int barriered_work(struct BarrierTask *data) {
    6b8f:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    6b92:	44 39 b7 30 01 00 00 	cmp    %r14d,0x130(%rdi)
    6b99:	74 65                	je     6c00 <barriered_work+0x90>
    receive(data);
    6b9b:	e8 b0 fb ff ff       	call   6750 <receive>
    while (data->scheduled == 1) {
    6ba0:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6ba7:	75 1b                	jne    6bc4 <barriered_work+0x54>
    6ba9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    6bb0:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    6bb8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6bbb:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6bc2:	74 ec                	je     6bb0 <barriered_work+0x40>
    sendm(data);
    6bc4:	48 89 df             	mov    %rbx,%rdi
    6bc7:	e8 04 fd ff ff       	call   68d0 <sendm>
  if (t == data->thread_count - 1) {
    6bcc:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6bd2:	83 e8 01             	sub    $0x1,%eax
    6bd5:	44 39 f0             	cmp    %r14d,%eax
    6bd8:	0f 84 82 01 00 00    	je     6d60 <barriered_work+0x1f0>
  data->swap = 0;
    6bde:	c7 83 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbx)
  asm volatile ("sfence" ::: "memory");
    6be8:	0f ae f8             	sfence
}
    6beb:	48 83 c4 58          	add    $0x58,%rsp
    6bef:	31 c0                	xor    %eax,%eax
    6bf1:	5b                   	pop    %rbx
    6bf2:	41 5c                	pop    %r12
    6bf4:	41 5d                	pop    %r13
    6bf6:	41 5e                	pop    %r14
    6bf8:	41 5f                	pop    %r15
    6bfa:	5d                   	pop    %rbp
    6bfb:	c3                   	ret
    6bfc:	0f 1f 40 00          	nopl   0x0(%rax)
    receive(data);
    6c00:	e8 4b fb ff ff       	call   6750 <receive>
        if (data->thread->have_foreign == 1) {
    6c05:	4c 8b ab 28 01 00 00 	mov    0x128(%rbx),%r13
    6c0c:	41 83 bd d8 00 00 00 01 	cmpl   $0x1,0xd8(%r13)
    6c14:	0f 84 a6 02 00 00    	je     6ec0 <barriered_work+0x350>
            int y = (k * data->thread->threads_per_group) + data->thread_index;
    6c1a:	49 63 85 c4 00 00 00 	movslq 0xc4(%r13),%rax
    6c21:	8b 93 94 01 00 00    	mov    0x194(%rbx),%edx
    6c27:	8b 8b 30 01 00 00    	mov    0x130(%rbx),%ecx
    6c2d:	0f af d0             	imul   %eax,%edx
    6c30:	01 d1                	add    %edx,%ecx
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6c32:	85 c0                	test   %eax,%eax
    6c34:	0f 8e a6 01 00 00    	jle    6de0 <barriered_work+0x270>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6c3a:	48 63 c9             	movslq %ecx,%rcx
    6c3d:	4d 8b 4d 20          	mov    0x20(%r13),%r9
    6c41:	48 63 d2             	movslq %edx,%rdx
              int next_task = abs((t + 1) % (data->thread_count));
    6c44:	44 8b 83 34 01 00 00 	mov    0x134(%rbx),%r8d
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6c4b:	48 8d 34 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rsi
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6c53:	4c 8d 14 49          	lea    (%rcx,%rcx,2),%r10
    6c57:	48 01 d0             	add    %rdx,%rax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6c5a:	48 29 ce             	sub    %rcx,%rsi
    6c5d:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    6c65:	4c 8d 24 40          	lea    (%rax,%rax,2),%r12
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6c69:	49 c1 e2 07          	shl    $0x7,%r10
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6c6d:	48 c1 e6 05          	shl    $0x5,%rsi
    6c71:	48 29 d1             	sub    %rdx,%rcx
    6c74:	49 c1 e4 07          	shl    $0x7,%r12
    6c78:	4d 8b 5c 31 38       	mov    0x38(%r9,%rsi,1),%r11
    6c7d:	49 63 f6             	movslq %r14d,%rsi
    6c80:	48 c1 e1 05          	shl    $0x5,%rcx
    6c84:	48 c1 e6 09          	shl    $0x9,%rsi
    6c88:	49 01 c9             	add    %rcx,%r9
    6c8b:	4d 8b ac 33 70 01 00 00 	mov    0x170(%r11,%rsi,1),%r13
    6c93:	48 8d 34 52          	lea    (%rdx,%rdx,2),%rsi
    6c97:	48 c1 e6 07          	shl    $0x7,%rsi
    6c9b:	eb 1a                	jmp    6cb7 <barriered_work+0x147>
    6c9d:	0f 1f 00             	nopl   (%rax)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6ca0:	48 81 c6 80 01 00 00 	add    $0x180,%rsi
    6ca7:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    6cae:	49 39 f4             	cmp    %rsi,%r12
    6cb1:	0f 84 29 01 00 00    	je     6de0 <barriered_work+0x270>
              if (kind == MAILBOX_FRIEND) {
    6cb7:	41 83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%r13,%rsi,1)
    6cc0:	75 de                	jne    6ca0 <barriered_work+0x130>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6cc2:	49 8b 79 38          	mov    0x38(%r9),%rdi
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6cc6:	45 85 c0             	test   %r8d,%r8d
    6cc9:	7e d5                	jle    6ca0 <barriered_work+0x130>
    6ccb:	4c 89 6d c8          	mov    %r13,-0x38(%rbp)
    6ccf:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    6cd6:	31 c9                	xor    %ecx,%ecx
    6cd8:	4c 89 4d c0          	mov    %r9,-0x40(%rbp)
    6cdc:	eb 52                	jmp    6d30 <barriered_work+0x1c0>
    6cde:	66 90                	xchg   %ax,%ax
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6ce0:	48 63 d2             	movslq %edx,%rdx
    6ce3:	48 c1 e2 09          	shl    $0x9,%rdx
    6ce7:	4d 8b bc 13 70 01 00 00 	mov    0x170(%r11,%rdx,1),%r15
    6cef:	49 01 f7             	add    %rsi,%r15
    6cf2:	4c 89 fa             	mov    %r15,%rdx
    return mailbox->lower;
    6cf5:	4d 8b 3f             	mov    (%r15),%r15
                      if (dest->messages_count != 0) { 
    6cf8:	49 83 bf 80 00 00 00 00 	cmpq   $0x0,0x80(%r15)
    6d00:	75 22                	jne    6d24 <barriered_work+0x1b4>
    mailbox->lower = data;
    6d02:	4c 8b 88 80 00 00 00 	mov    0x80(%rax),%r9
    6d09:	4c 89 0a             	mov    %r9,(%rdx)
    6d0c:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    mailbox->higher = data;
    6d13:	4c 89 b8 80 00 00 00 	mov    %r15,0x80(%rax)
    mailbox->lower = data;
    6d1a:	4c 89 08             	mov    %r9,(%rax)
    mailbox->higher = data;
    6d1d:	4c 89 aa 80 00 00 00 	mov    %r13,0x80(%rdx)
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6d24:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    6d2b:	41 39 c8             	cmp    %ecx,%r8d
    6d2e:	74 1c                	je     6d4c <barriered_work+0x1dc>
                    int next_task = abs((nn + 1) % (data->thread_count));
    6d30:	83 c1 01             	add    $0x1,%ecx
    6d33:	89 c8                	mov    %ecx,%eax
    6d35:	99                   	cltd
    6d36:	41 f7 f8             	idiv   %r8d
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6d39:	48 8b 07             	mov    (%rdi),%rax
    6d3c:	4c 01 d0             	add    %r10,%rax
    return mailbox->lower;
    6d3f:	4c 8b 28             	mov    (%rax),%r13
                      if (source2->messages_count != 0) { 
    6d42:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    6d4a:	74 94                	je     6ce0 <barriered_work+0x170>
    6d4c:	4c 8b 6d c8          	mov    -0x38(%rbp),%r13
    6d50:	4c 8b 4d c0          	mov    -0x40(%rbp),%r9
    6d54:	e9 47 ff ff ff       	jmp    6ca0 <barriered_work+0x130>
    6d59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6d60:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    6d67:	85 d2                	test   %edx,%edx
    6d69:	0f 8e 6f fe ff ff    	jle    6bde <barriered_work+0x6e>
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6d6f:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    6d76:	48 c1 e2 09          	shl    $0x9,%rdx
    6d7a:	48 63 71 08          	movslq 0x8(%rcx),%rsi
    6d7e:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
    6d86:	48 29 f0             	sub    %rsi,%rax
    6d89:	48 c1 e0 05          	shl    $0x5,%rax
    6d8d:	48 03 41 20          	add    0x20(%rcx),%rax
    6d91:	48 8b 40 38          	mov    0x38(%rax),%rax
    6d95:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    6d99:	80 e6 02             	and    $0x2,%dh
    6d9c:	74 1a                	je     6db8 <barriered_work+0x248>
    6d9e:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6da5:	48 05 00 02 00 00    	add    $0x200,%rax
    6dab:	48 39 c8             	cmp    %rcx,%rax
    6dae:	0f 84 2a fe ff ff    	je     6bde <barriered_work+0x6e>
    6db4:	0f 1f 40 00          	nopl   0x0(%rax)
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6db8:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
    6dbf:	83 80 9c 03 00 00 01 	addl   $0x1,0x39c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6dc6:	48 05 00 04 00 00    	add    $0x400,%rax
    6dcc:	48 39 c8             	cmp    %rcx,%rax
    6dcf:	75 e7                	jne    6db8 <barriered_work+0x248>
    6dd1:	e9 08 fe ff ff       	jmp    6bde <barriered_work+0x6e>
    6dd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      receive(data);
    6de0:	48 89 df             	mov    %rbx,%rdi
    6de3:	e8 68 f9 ff ff       	call   6750 <receive>
      asm volatile ("sfence" ::: "memory");
    6de8:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6deb:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6df2:	31 ff                	xor    %edi,%edi
    6df4:	48 c1 e6 05          	shl    $0x5,%rsi
    6df8:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6dff:	e8 6c b5 ff ff       	call   2370 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6e04:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    6e0b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    6e12:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6e16:	8b 4a 10             	mov    0x10(%rdx),%ecx
    6e19:	44 8d 61 01          	lea    0x1(%rcx),%r12d
    6e1d:	44 89 62 10          	mov    %r12d,0x10(%rdx)
    while (data->scheduled == 1) {
    6e21:	75 57                	jne    6e7a <barriered_work+0x30a>
    6e23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6e28:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    6e2f:	48 8b 40 18          	mov    0x18(%rax),%rax
    6e33:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
      data->n++;
    6e37:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6e3f:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6e43:	48 c1 e7 09          	shl    $0x9,%rdi
    6e47:	48 03 78 38          	add    0x38(%rax),%rdi
    6e4b:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    6e51:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6e54:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    6e5b:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    6e62:	74 c4                	je     6e28 <barriered_work+0x2b8>
    if (modcount != data->thread->protected_state->modcount) {
    6e64:	48 8b 40 48          	mov    0x48(%rax),%rax
    6e68:	44 3b 60 10          	cmp    0x10(%rax),%r12d
    6e6c:	74 0c                	je     6e7a <barriered_work+0x30a>
    6e6e:	48 8d 3d d1 13 00 00 	lea    0x13d1(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6e75:	e8 d6 b4 ff ff       	call   2350 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6e7a:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6e81:	31 ff                	xor    %edi,%edi
    6e83:	48 c1 e6 05          	shl    $0x5,%rsi
    6e87:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6e8e:	48 83 c6 10          	add    $0x10,%rsi
    6e92:	e8 d9 b4 ff ff       	call   2370 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6e97:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6e9e:	48 83 c0 01          	add    $0x1,%rax
    6ea2:	48 99                	cqto
    6ea4:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6eab:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    6eb2:	e9 15 fd ff ff       	jmp    6bcc <barriered_work+0x5c>
    6eb7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6ec0:	8b 83 40 01 00 00    	mov    0x140(%rbx),%eax
          data->thread->have_foreign = 0;
    6ec6:	41 c7 85 d8 00 00 00 00 00 00 00 	movl   $0x0,0xd8(%r13)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6ed1:	85 c0                	test   %eax,%eax
    6ed3:	0f 8e 41 fd ff ff    	jle    6c1a <barriered_work+0xaa>
              int next_task = abs((t + 1) % (data->thread_count));
    6ed9:	8b 8b 34 01 00 00    	mov    0x134(%rbx),%ecx
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6edf:	49 63 d6             	movslq %r14d,%rdx
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6ee2:	44 89 75 bc          	mov    %r14d,-0x44(%rbp)
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6ee6:	45 31 ff             	xor    %r15d,%r15d
    6ee9:	48 c1 e2 09          	shl    $0x9,%rdx
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6eed:	48 89 5d b0          	mov    %rbx,-0x50(%rbp)
    6ef1:	41 89 c3             	mov    %eax,%r11d
              int next_task = abs((t + 1) % (data->thread_count));
    6ef4:	89 4d b8             	mov    %ecx,-0x48(%rbp)
        int b = data->thread->real_thread_index;
    6ef7:	49 63 4d 08          	movslq 0x8(%r13),%rcx
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6efb:	49 89 d2             	mov    %rdx,%r10
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6efe:	48 8d 34 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rsi
        int b = data->thread->real_thread_index;
    6f06:	49 89 cc             	mov    %rcx,%r12
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6f09:	48 29 ce             	sub    %rcx,%rsi
    6f0c:	48 8d 0c 49          	lea    (%rcx,%rcx,2),%rcx
    6f10:	48 c1 e6 05          	shl    $0x5,%rsi
    6f14:	48 c1 e1 07          	shl    $0x7,%rcx
    6f18:	48 89 f7             	mov    %rsi,%rdi
    6f1b:	48 89 4d c0          	mov    %rcx,-0x40(%rbp)
    6f1f:	31 f6                	xor    %esi,%esi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6f21:	31 c9                	xor    %ecx,%ecx
    6f23:	49 89 fe             	mov    %rdi,%r14
    6f26:	eb 22                	jmp    6f4a <barriered_work+0x3da>
    6f28:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6f30:	83 c1 01             	add    $0x1,%ecx
    6f33:	49 81 c7 80 01 00 00 	add    $0x180,%r15
    6f3a:	48 81 c6 e0 00 00 00 	add    $0xe0,%rsi
    6f41:	44 39 d9             	cmp    %r11d,%ecx
    6f44:	0f 84 c6 01 00 00    	je     7110 <barriered_work+0x5a0>
              if (y == b) { continue; }
    6f4a:	41 39 cc             	cmp    %ecx,%r12d
    6f4d:	74 e1                	je     6f30 <barriered_work+0x3c0>
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6f4f:	49 8b 55 20          	mov    0x20(%r13),%rdx
    6f53:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    6f58:	4a 8d 04 17          	lea    (%rdi,%r10,1),%rax
    6f5c:	44 8b 80 98 01 00 00 	mov    0x198(%rax),%r8d
    6f63:	45 85 c0             	test   %r8d,%r8d
    6f66:	75 c8                	jne    6f30 <barriered_work+0x3c0>
    6f68:	4e 8b 44 32 38       	mov    0x38(%rdx,%r14,1),%r8
    6f6d:	4b 8d 14 10          	lea    (%r8,%r10,1),%rdx
    6f71:	44 8b 8a 98 01 00 00 	mov    0x198(%rdx),%r9d
    6f78:	45 85 c9             	test   %r9d,%r9d
    6f7b:	75 b3                	jne    6f30 <barriered_work+0x3c0>
    6f7d:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    6f84:	42 83 bc 3a b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r15,1)
    6f8d:	75 a1                	jne    6f30 <barriered_work+0x3c0>
    6f8f:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6f96:	48 8b 5d c0          	mov    -0x40(%rbp),%rbx
    6f9a:	83 bc 18 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rbx,1)
    6fa2:	75 8c                	jne    6f30 <barriered_work+0x3c0>
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6fa4:	8b 55 b8             	mov    -0x48(%rbp),%edx
    6fa7:	85 d2                	test   %edx,%edx
    6fa9:	7e 85                	jle    6f30 <barriered_work+0x3c0>
    6fab:	48 63 c2             	movslq %edx,%rax
    6fae:	4c 89 6d a8          	mov    %r13,-0x58(%rbp)
    6fb2:	48 c1 e0 09          	shl    $0x9,%rax
    6fb6:	44 89 65 9c          	mov    %r12d,-0x64(%rbp)
    6fba:	48 89 c3             	mov    %rax,%rbx
    6fbd:	48 89 75 88          	mov    %rsi,-0x78(%rbp)
    6fc1:	48 8d 80 98 01 00 00 	lea    0x198(%rax),%rax
    6fc8:	48 89 5d 80          	mov    %rbx,-0x80(%rbp)
    6fcc:	48 8b 5d c0          	mov    -0x40(%rbp),%rbx
    6fd0:	4c 89 55 a0          	mov    %r10,-0x60(%rbp)
    6fd4:	41 ba 70 01 00 00    	mov    $0x170,%r10d
    6fda:	89 4d 98             	mov    %ecx,-0x68(%rbp)
    6fdd:	48 89 c1             	mov    %rax,%rcx
    6fe0:	44 89 5d 94          	mov    %r11d,-0x6c(%rbp)
    6fe4:	41 89 d3             	mov    %edx,%r11d
    6fe7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
                      int next_task = abs((nn + 1) % data->thread_count);
    6ff0:	41 83 c1 01          	add    $0x1,%r9d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6ff4:	4b 8b 34 10          	mov    (%r8,%r10,1),%rsi
                      int next_task = abs((nn + 1) % data->thread_count);
    6ff8:	44 89 c8             	mov    %r9d,%eax
    6ffb:	99                   	cltd
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6ffc:	4c 01 fe             	add    %r15,%rsi
                      int next_task = abs((nn + 1) % data->thread_count);
    6fff:	41 f7 fb             	idiv   %r11d
    return mailbox->lower;
    7002:	4c 8b 26             	mov    (%rsi),%r12
    7005:	4c 89 65 c8          	mov    %r12,-0x38(%rbp)
    mailbox->lower = data;
    7009:	4c 8b a6 80 00 00 00 	mov    0x80(%rsi),%r12
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    7010:	48 63 d2             	movslq %edx,%rdx
    7013:	48 c1 e2 09          	shl    $0x9,%rdx
    7017:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    701f:	48 01 d8             	add    %rbx,%rax
    return mailbox->lower;
    7022:	4c 8b 28             	mov    (%rax),%r13
    return mailbox->higher;
    7025:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    mailbox->lower = data;
    702c:	4c 89 20             	mov    %r12,(%rax)
    mailbox->higher = data;
    702f:	4c 8b 65 c8          	mov    -0x38(%rbp),%r12
    7033:	4c 89 a0 80 00 00 00 	mov    %r12,0x80(%rax)
    mailbox->lower = data;
    703a:	48 89 16             	mov    %rdx,(%rsi)
    mailbox->higher = data;
    703d:	4c 89 ae 80 00 00 00 	mov    %r13,0x80(%rsi)
    7044:	be 98 01 00 00       	mov    $0x198,%esi
    7049:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
    7050:	41 c7 04 30 01 00 00 00 	movl   $0x1,(%r8,%rsi,1)
                        data->thread->all_threads[t2].tasks[jj].swap = 1;
    7058:	c7 04 37 01 00 00 00 	movl   $0x1,(%rdi,%rsi,1)
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
    705f:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    7066:	48 39 f1             	cmp    %rsi,%rcx
    7069:	75 e5                	jne    7050 <barriered_work+0x4e0>
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    706b:	4a 8b 34 17          	mov    (%rdi,%r10,1),%rsi
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    706f:	48 8b 00             	mov    (%rax),%rax
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    7072:	41 c7 85 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r13)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    707d:	49 81 c2 00 02 00 00 	add    $0x200,%r10
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    7084:	48 8b b4 1e 80 00 00 00 	mov    0x80(%rsi,%rbx,1),%rsi
    708c:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    7096:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    70a0:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    70aa:	45 39 cb             	cmp    %r9d,%r11d
    70ad:	0f 85 3d ff ff ff    	jne    6ff0 <barriered_work+0x480>
    70b3:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    70b7:	48 8b 5d 80          	mov    -0x80(%rbp),%rbx
    70bb:	b8 70 01 00 00       	mov    $0x170,%eax
    70c0:	4c 8b 55 a0          	mov    -0x60(%rbp),%r10
    70c4:	44 8b 65 9c          	mov    -0x64(%rbp),%r12d
    70c8:	4c 89 6d c8          	mov    %r13,-0x38(%rbp)
    70cc:	8b 4d 98             	mov    -0x68(%rbp),%ecx
    70cf:	48 81 c3 70 01 00 00 	add    $0x170,%rbx
    70d6:	44 8b 5d 94          	mov    -0x6c(%rbp),%r11d
    70da:	48 8b 75 88          	mov    -0x78(%rbp),%rsi
    70de:	4c 8b 6d c0          	mov    -0x40(%rbp),%r13
    70e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    70e8:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    70ec:	4d 8b 0c 00          	mov    (%r8,%rax,1),%r9
    70f0:	4a 8b 14 2a          	mov    (%rdx,%r13,1),%rdx
    70f4:	4b 39 14 39          	cmp    %rdx,(%r9,%r15,1)
    70f8:	74 23                	je     711d <barriered_work+0x5ad>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    70fa:	48 05 00 02 00 00    	add    $0x200,%rax
    7100:	48 39 c3             	cmp    %rax,%rbx
    7103:	75 e3                	jne    70e8 <barriered_work+0x578>
    7105:	4c 8b 6d c8          	mov    -0x38(%rbp),%r13
    7109:	e9 22 fe ff ff       	jmp    6f30 <barriered_work+0x3c0>
    710e:	66 90                	xchg   %ax,%ax
    7110:	44 8b 75 bc          	mov    -0x44(%rbp),%r14d
    7114:	48 8b 5d b0          	mov    -0x50(%rbp),%rbx
    7118:	e9 fd fa ff ff       	jmp    6c1a <barriered_work+0xaa>
    711d:	bf 01 00 00 00       	mov    $0x1,%edi
    7122:	48 8d 35 02 11 00 00 	lea    0x1102(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    7129:	31 c0                	xor    %eax,%eax
    712b:	e8 b0 b3 ff ff       	call   24e0 <__printf_chk@plt>
                          exit(1);
    7130:	bf 01 00 00 00       	mov    $0x1,%edi
    7135:	e8 16 b4 ff ff       	call   2550 <exit@plt>
    713a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000007140 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    7140:	f3 0f 1e fa          	endbr64
    7144:	55                   	push   %rbp
    7145:	48 89 e5             	mov    %rsp,%rbp
    7148:	53                   	push   %rbx
    7149:	48 83 ec 08          	sub    $0x8,%rsp
    714d:	ff 15 95 3e 00 00    	call   *0x3e95(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    7153:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    7156:	e8 e5 f1 ff ff       	call   6340 <barriered_work_ingest>
  barriered_work(data);
    715b:	48 89 df             	mov    %rbx,%rdi
}
    715e:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    7162:	c9                   	leave
  barriered_work(data);
    7163:	e9 08 fa ff ff       	jmp    6b70 <barriered_work>
    7168:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000007170 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    7170:	f3 0f 1e fa          	endbr64
    7174:	55                   	push   %rbp
    7175:	48 89 e5             	mov    %rsp,%rbp
    7178:	ff 15 6a 3e 00 00    	call   *0x3e6a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  if (kind == 0) {
    717e:	85 f6                	test   %esi,%esi
    7180:	74 1e                	je     71a0 <mailboxkind+0x30>
  return NULL;
    7182:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    7184:	83 fe 01             	cmp    $0x1,%esi
    7187:	74 07                	je     7190 <mailboxkind+0x20>
}
    7189:	5d                   	pop    %rbp
    718a:	c3                   	ret
    718b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return mailbox->higher;
    7190:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
}
    7197:	5d                   	pop    %rbp
    7198:	c3                   	ret
    7199:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    return mailbox->lower;
    71a0:	48 8b 07             	mov    (%rdi),%rax
}
    71a3:	5d                   	pop    %rbp
    71a4:	c3                   	ret
    71a5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000071b0 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    71b0:	f3 0f 1e fa          	endbr64
    71b4:	55                   	push   %rbp
    71b5:	48 89 e5             	mov    %rsp,%rbp
    71b8:	ff 15 2a 3e 00 00    	call   *0x3e2a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  if (kind == 0) {
    71be:	85 d2                	test   %edx,%edx
    71c0:	75 0e                	jne    71d0 <setmailboxkind+0x20>
    mailbox->lower = data;
    71c2:	48 89 37             	mov    %rsi,(%rdi)
}
    71c5:	31 c0                	xor    %eax,%eax
    71c7:	5d                   	pop    %rbp
    71c8:	c3                   	ret
    71c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (kind == 1) {
    71d0:	83 fa 01             	cmp    $0x1,%edx
    71d3:	74 13                	je     71e8 <setmailboxkind+0x38>
  if (kind == 2) {
    71d5:	83 fa 02             	cmp    $0x2,%edx
    71d8:	75 1e                	jne    71f8 <setmailboxkind+0x48>
}
    71da:	31 c0                	xor    %eax,%eax
    mailbox->pending_lower = data;
    71dc:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
}
    71e3:	5d                   	pop    %rbp
    71e4:	c3                   	ret
    71e5:	0f 1f 00             	nopl   (%rax)
    71e8:	31 c0                	xor    %eax,%eax
    mailbox->higher = data;
    71ea:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
}
    71f1:	5d                   	pop    %rbp
    71f2:	c3                   	ret
    71f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  if (kind == 3) {
    71f8:	83 fa 03             	cmp    $0x3,%edx
    71fb:	75 c8                	jne    71c5 <setmailboxkind+0x15>
}
    71fd:	31 c0                	xor    %eax,%eax
    mailbox->pending_higher = data;
    71ff:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
}
    7206:	5d                   	pop    %rbp
    7207:	c3                   	ret
    7208:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000007210 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    7210:	f3 0f 1e fa          	endbr64
    7214:	55                   	push   %rbp
    7215:	48 89 e5             	mov    %rsp,%rbp
    7218:	ff 15 ca 3d 00 00    	call   *0x3dca(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    721e:	31 c0                	xor    %eax,%eax
    7220:	5d                   	pop    %rbp
    7221:	c3                   	ret
    7222:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    722d:	0f 1f 00             	nopl   (%rax)

0000000000007230 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    7230:	f3 0f 1e fa          	endbr64
    7234:	55                   	push   %rbp
    7235:	48 89 e5             	mov    %rsp,%rbp
    7238:	ff 15 aa 3d 00 00    	call   *0x3daa(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    723e:	31 c0                	xor    %eax,%eax
    7240:	5d                   	pop    %rbp
    7241:	c3                   	ret
    7242:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    724d:	0f 1f 00             	nopl   (%rax)

0000000000007250 <after>:
int after(struct timespec left, struct timespec right) {
    7250:	f3 0f 1e fa          	endbr64
    7254:	55                   	push   %rbp
    7255:	48 89 e5             	mov    %rsp,%rbp
    7258:	ff 15 8a 3d 00 00    	call   *0x3d8a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  return left.tv_sec > right.tv_sec &&
    725e:	31 c0                	xor    %eax,%eax
    7260:	48 39 d7             	cmp    %rdx,%rdi
    7263:	7e 08                	jle    726d <after+0x1d>
    7265:	31 c0                	xor    %eax,%eax
    7267:	48 39 ce             	cmp    %rcx,%rsi
    726a:	0f 9f c0             	setg   %al
}
    726d:	5d                   	pop    %rbp
    726e:	c3                   	ret
    726f:	90                   	nop

0000000000007270 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    7270:	f3 0f 1e fa          	endbr64
    7274:	55                   	push   %rbp
    7275:	48 89 e5             	mov    %rsp,%rbp
    7278:	ff 15 6a 3d 00 00    	call   *0x3d6a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  return 0;
    727e:	31 c0                	xor    %eax,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    7280:	4c 8b 5d 10          	mov    0x10(%rbp),%r11
    7284:	4c 8b 55 18          	mov    0x18(%rbp),%r10
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7288:	48 39 d7             	cmp    %rdx,%rdi
    728b:	7f 18                	jg     72a5 <within+0x35>
    728d:	4d 39 d8             	cmp    %r11,%r8
    7290:	0f 9e c2             	setle  %dl
    7293:	48 39 ce             	cmp    %rcx,%rsi
    7296:	0f 9e c0             	setle  %al
    7299:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    729b:	31 c0                	xor    %eax,%eax
    729d:	4d 39 d1             	cmp    %r10,%r9
    72a0:	0f 9e c0             	setle  %al
    72a3:	21 d0                	and    %edx,%eax
}
    72a5:	5d                   	pop    %rbp
    72a6:	c3                   	ret
    72a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000072b0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    72b0:	f3 0f 1e fa          	endbr64
    72b4:	55                   	push   %rbp
    72b5:	48 89 e5             	mov    %rsp,%rbp
    72b8:	ff 15 2a 3d 00 00    	call   *0x3d2a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    72be:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    72c2:	48 8b 75 30          	mov    0x30(%rbp),%rsi
    72c6:	4c 8b 4d 20          	mov    0x20(%rbp),%r9
    72ca:	4c 8b 55 28          	mov    0x28(%rbp),%r10
    72ce:	4c 8b 45 40          	mov    0x40(%rbp),%r8
    72d2:	4c 8b 5d 48          	mov    0x48(%rbp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    72d6:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
    72da:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  return left.tv_sec > right.tv_sec &&
    72de:	48 39 fe             	cmp    %rdi,%rsi
    72e1:	7d 2d                	jge    7310 <overlap+0x60>
    72e3:	48 39 ca             	cmp    %rcx,%rdx
    72e6:	7d 60                	jge    7348 <overlap+0x98>
    72e8:	4d 39 da             	cmp    %r11,%r10
    72eb:	7d 0a                	jge    72f7 <overlap+0x47>
    return 1;
    72ed:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    72f2:	4d 39 c1             	cmp    %r8,%r9
    72f5:	7c 0f                	jl     7306 <overlap+0x56>
  return 0;
    72f7:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    72f9:	4d 39 c1             	cmp    %r8,%r9
    72fc:	7f 08                	jg     7306 <overlap+0x56>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    72fe:	31 c0                	xor    %eax,%eax
    7300:	4d 39 da             	cmp    %r11,%r10
    7303:	0f 9e c0             	setle  %al
}
    7306:	5d                   	pop    %rbp
    7307:	c3                   	ret
    7308:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7310:	7e 56                	jle    7368 <overlap+0xb8>
    7312:	48 39 ca             	cmp    %rcx,%rdx
    7315:	7f 39                	jg     7350 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7317:	75 31                	jne    734a <overlap+0x9a>
    7319:	4d 39 c1             	cmp    %r8,%r9
    731c:	7c 2c                	jl     734a <overlap+0x9a>
    return 1;
    731e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7323:	4d 39 da             	cmp    %r11,%r10
    7326:	7d de                	jge    7306 <overlap+0x56>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7328:	48 39 ca             	cmp    %rcx,%rdx
}
    732b:	5d                   	pop    %rbp
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    732c:	0f 94 c2             	sete   %dl
    732f:	48 39 fe             	cmp    %rdi,%rsi
    7332:	0f 94 c0             	sete   %al
    7335:	21 c2                	and    %eax,%edx
    7337:	31 c0                	xor    %eax,%eax
    7339:	4d 39 c1             	cmp    %r8,%r9
    733c:	0f 94 c0             	sete   %al
    733f:	21 d0                	and    %edx,%eax
}
    7341:	c3                   	ret
    7342:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7348:	74 ad                	je     72f7 <overlap+0x47>
  return 0;
    734a:	31 c0                	xor    %eax,%eax
}
    734c:	5d                   	pop    %rbp
    734d:	c3                   	ret
    734e:	66 90                	xchg   %ax,%ax
  return left.tv_sec > right.tv_sec &&
    7350:	4d 39 da             	cmp    %r11,%r10
    7353:	7e c4                	jle    7319 <overlap+0x69>
    return 1;
    7355:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    735a:	4d 39 c1             	cmp    %r8,%r9
    735d:	7e ba                	jle    7319 <overlap+0x69>
    735f:	eb a5                	jmp    7306 <overlap+0x56>
    7361:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7368:	48 39 ca             	cmp    %rcx,%rdx
    736b:	7c 8a                	jl     72f7 <overlap+0x47>
    736d:	4d 39 c1             	cmp    %r8,%r9
    7370:	7d ac                	jge    731e <overlap+0x6e>
    7372:	48 39 ca             	cmp    %rcx,%rdx
    7375:	74 87                	je     72fe <overlap+0x4e>
  return 0;
    7377:	31 c0                	xor    %eax,%eax
    7379:	eb d1                	jmp    734c <overlap+0x9c>
    737b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000007380 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    7380:	f3 0f 1e fa          	endbr64
    7384:	55                   	push   %rbp
    7385:	48 89 e5             	mov    %rsp,%rbp
    7388:	41 57                	push   %r15
    738a:	41 56                	push   %r14
    738c:	41 55                	push   %r13
    738e:	41 54                	push   %r12
    7390:	53                   	push   %rbx
    7391:	48 83 ec 58          	sub    $0x58,%rsp
    7395:	ff 15 4d 3c 00 00    	call   *0x3c4d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    739b:	41 89 f4             	mov    %esi,%r12d
  for (int x = 0 ; x < thread_count; x++) {
    739e:	85 f6                	test   %esi,%esi
    73a0:	0f 8e df 02 00 00    	jle    7685 <verify+0x305>
    73a6:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    73aa:	45 31 ff             	xor    %r15d,%r15d
    73ad:	48 89 5d b8          	mov    %rbx,-0x48(%rbp)
    for (int z = 0 ; z < thread_count; z++) {
    73b1:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    73b5:	45 31 ed             	xor    %r13d,%r13d
    73b8:	45 89 e6             	mov    %r12d,%r14d
      if (z != x)  {
    73bb:	45 39 ef             	cmp    %r13d,%r15d
    73be:	0f 84 27 02 00 00    	je     75eb <verify+0x26b>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    73c4:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    73c8:	8b 50 08             	mov    0x8(%rax),%edx
    73cb:	85 d2                	test   %edx,%edx
    73cd:	0f 8e 18 02 00 00    	jle    75eb <verify+0x26b>
    73d3:	48 89 5d 98          	mov    %rbx,-0x68(%rbp)
    73d7:	45 31 e4             	xor    %r12d,%r12d
    73da:	44 89 6d 94          	mov    %r13d,-0x6c(%rbp)
    73de:	44 89 75 90          	mov    %r14d,-0x70(%rbp)
    73e2:	4d 89 e6             	mov    %r12,%r14
    73e5:	44 89 fa             	mov    %r15d,%edx
    73e8:	48 8d 35 67 0e 00 00 	lea    0xe67(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    73ef:	bf 01 00 00 00       	mov    $0x1,%edi
    73f4:	31 c0                	xor    %eax,%eax
    73f6:	e8 e5 b0 ff ff       	call   24e0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    73fb:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    73ff:	8b 40 08             	mov    0x8(%rax),%eax
    7402:	85 c0                	test   %eax,%eax
    7404:	0f 8e c3 01 00 00    	jle    75cd <verify+0x24d>
    740a:	4c 89 f0             	mov    %r14,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    740d:	4c 89 75 88          	mov    %r14,-0x78(%rbp)
    7411:	31 db                	xor    %ebx,%ebx
    7413:	48 c1 e0 09          	shl    $0x9,%rax
    7417:	44 89 7d 84          	mov    %r15d,-0x7c(%rbp)
    741b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    741f:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    7423:	4c 8b 08             	mov    (%rax),%r9
    7426:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    7430:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    7434:	4c 8b 7d c8          	mov    -0x38(%rbp),%r15
    7438:	49 89 de             	mov    %rbx,%r14
    743b:	bf 01 00 00 00       	mov    $0x1,%edi
    7440:	49 c1 e6 09          	shl    $0x9,%r14
    7444:	48 8d 35 20 0e 00 00 	lea    0xe20(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    744b:	49 8b 04 24          	mov    (%r12),%rax
    744f:	4b 8b 8c 39 60 01 00 00 	mov    0x160(%r9,%r15,1),%rcx
    7457:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    745b:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    7463:	31 c0                	xor    %eax,%eax
    7465:	e8 76 b0 ff ff       	call   24e0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    746a:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    746e:	4c 8b 08             	mov    (%rax),%r9
    7471:	4b 83 bc 39 60 01 00 00 00 	cmpq   $0x0,0x160(%r9,%r15,1)
    747a:	0f 8e 34 01 00 00    	jle    75b4 <verify+0x234>
    7480:	4d 03 34 24          	add    (%r12),%r14
    7484:	48 89 5d a0          	mov    %rbx,-0x60(%rbp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7488:	ba 01 00 00 00       	mov    $0x1,%edx
    748d:	4d 89 f5             	mov    %r14,%r13
    7490:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7497:	4d 85 f6             	test   %r14,%r14
    749a:	0f 8e 10 01 00 00    	jle    75b0 <verify+0x230>
    74a0:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    74a4:	49 89 d4             	mov    %rdx,%r12
    74a7:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    74ab:	31 db                	xor    %ebx,%ebx
    74ad:	49 c1 e4 05          	shl    $0x5,%r12
    74b1:	49 83 ec 20          	sub    $0x20,%r12
    74b5:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
    74b9:	eb 32                	jmp    74ed <verify+0x16d>
    74bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    74c0:	4c 39 c1             	cmp    %r8,%rcx
    74c3:	0f 8d 47 01 00 00    	jge    7610 <verify+0x290>
    74c9:	4c 39 d7             	cmp    %r10,%rdi
    74cc:	7e 05                	jle    74d3 <verify+0x153>
    74ce:	49 39 c3             	cmp    %rax,%r11
    74d1:	7c 75                	jl     7548 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    74d3:	4c 39 d7             	cmp    %r10,%rdi
    74d6:	0f 8d 9b 01 00 00    	jge    7677 <verify+0x2f7>
    74dc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    74e0:	48 83 c3 01          	add    $0x1,%rbx
    74e4:	49 39 de             	cmp    %rbx,%r14
    74e7:	0f 8e a2 00 00 00    	jle    758f <verify+0x20f>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    74ed:	49 8b 8f 50 01 00 00 	mov    0x150(%r15),%rcx
    74f4:	48 89 d8             	mov    %rbx,%rax
    74f7:	48 c1 e0 05          	shl    $0x5,%rax
    74fb:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    7502:	4c 01 e1             	add    %r12,%rcx
    7505:	48 8b 30             	mov    (%rax),%rsi
    7508:	48 8b 78 10          	mov    0x10(%rax),%rdi
    750c:	48 8b 11             	mov    (%rcx),%rdx
    750f:	4c 8b 41 08          	mov    0x8(%rcx),%r8
    7513:	4c 8b 51 10          	mov    0x10(%rcx),%r10
    7517:	4c 8b 59 18          	mov    0x18(%rcx),%r11
    751b:	48 8b 48 08          	mov    0x8(%rax),%rcx
    751f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    7523:	48 39 d6             	cmp    %rdx,%rsi
    7526:	7c 98                	jl     74c0 <verify+0x140>
    7528:	0f 8e 32 01 00 00    	jle    7660 <verify+0x2e0>
    752e:	4c 39 c1             	cmp    %r8,%rcx
    7531:	0f 8f e9 00 00 00    	jg     7620 <verify+0x2a0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7537:	75 a7                	jne    74e0 <verify+0x160>
    7539:	4c 39 d7             	cmp    %r10,%rdi
    753c:	7f a2                	jg     74e0 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    753e:	49 39 c3             	cmp    %rax,%r11
    7541:	7c 9d                	jl     74e0 <verify+0x160>
    7543:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7548:	49 89 c1             	mov    %rax,%r9
    754b:	48 89 f9             	mov    %rdi,%rcx
    754e:	48 8d 35 e3 10 00 00 	lea    0x10e3(%rip),%rsi        # 8638 <_IO_stdin_used+0x638>
    7555:	31 c0                	xor    %eax,%eax
    7557:	bf 01 00 00 00       	mov    $0x1,%edi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    755c:	48 83 c3 01          	add    $0x1,%rbx
    7560:	e8 7b af ff ff       	call   24e0 <__printf_chk@plt>
    7565:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    7569:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    756d:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7570:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7574:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    757b:	4c 8b 08             	mov    (%rax),%r9
    757e:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    7582:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7586:	49 39 de             	cmp    %rbx,%r14
    7589:	0f 8f 5e ff ff ff    	jg     74ed <verify+0x16d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    758f:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    7593:	49 3b 97 60 01 00 00 	cmp    0x160(%r15),%rdx
    759a:	7d 14                	jge    75b0 <verify+0x230>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    759c:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    75a3:	48 83 c2 01          	add    $0x1,%rdx
    75a7:	4d 85 f6             	test   %r14,%r14
    75aa:	0f 8f f0 fe ff ff    	jg     74a0 <verify+0x120>
    75b0:	48 8b 5d a0          	mov    -0x60(%rbp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    75b4:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    75b8:	48 83 c3 01          	add    $0x1,%rbx
    75bc:	39 58 08             	cmp    %ebx,0x8(%rax)
    75bf:	0f 8f 6b fe ff ff    	jg     7430 <verify+0xb0>
    75c5:	4c 8b 75 88          	mov    -0x78(%rbp),%r14
    75c9:	44 8b 7d 84          	mov    -0x7c(%rbp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    75cd:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    75d1:	49 83 c6 01          	add    $0x1,%r14
    75d5:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    75d9:	0f 8f 06 fe ff ff    	jg     73e5 <verify+0x65>
    75df:	48 8b 5d 98          	mov    -0x68(%rbp),%rbx
    75e3:	44 8b 6d 94          	mov    -0x6c(%rbp),%r13d
    75e7:	44 8b 75 90          	mov    -0x70(%rbp),%r14d
    for (int z = 0 ; z < thread_count; z++) {
    75eb:	41 8d 45 01          	lea    0x1(%r13),%eax
    75ef:	48 81 45 c0 e0 00 00 00 	addq   $0xe0,-0x40(%rbp)
    75f7:	41 39 c6             	cmp    %eax,%r14d
    75fa:	0f 84 96 00 00 00    	je     7696 <verify+0x316>
    7600:	41 89 c5             	mov    %eax,%r13d
    7603:	e9 b3 fd ff ff       	jmp    73bb <verify+0x3b>
    7608:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7610:	0f 85 ca fe ff ff    	jne    74e0 <verify+0x160>
    7616:	e9 b8 fe ff ff       	jmp    74d3 <verify+0x153>
    761b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7620:	49 39 c3             	cmp    %rax,%r11
    7623:	7e 09                	jle    762e <verify+0x2ae>
    7625:	4c 39 d7             	cmp    %r10,%rdi
    7628:	0f 8c 1a ff ff ff    	jl     7548 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    762e:	4c 39 d7             	cmp    %r10,%rdi
    7631:	0f 8f a9 fe ff ff    	jg     74e0 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7637:	49 39 c3             	cmp    %rax,%r11
    763a:	0f 8d 08 ff ff ff    	jge    7548 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7640:	48 39 d6             	cmp    %rdx,%rsi
    7643:	0f 85 97 fe ff ff    	jne    74e0 <verify+0x160>
    7649:	4c 39 c1             	cmp    %r8,%rcx
    764c:	0f 85 8e fe ff ff    	jne    74e0 <verify+0x160>
    7652:	4c 39 d7             	cmp    %r10,%rdi
    7655:	0f 84 ed fe ff ff    	je     7548 <verify+0x1c8>
    765b:	e9 80 fe ff ff       	jmp    74e0 <verify+0x160>
    7660:	4c 39 c1             	cmp    %r8,%rcx
    7663:	0f 8c 6a fe ff ff    	jl     74d3 <verify+0x153>
    7669:	4c 39 d7             	cmp    %r10,%rdi
    766c:	7e c9                	jle    7637 <verify+0x2b7>
    766e:	4c 39 c1             	cmp    %r8,%rcx
    7671:	0f 85 69 fe ff ff    	jne    74e0 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7677:	49 39 c3             	cmp    %rax,%r11
    767a:	0f 8f 60 fe ff ff    	jg     74e0 <verify+0x160>
    7680:	e9 c3 fe ff ff       	jmp    7548 <verify+0x1c8>
}
    7685:	48 83 c4 58          	add    $0x58,%rsp
    7689:	31 c0                	xor    %eax,%eax
    768b:	5b                   	pop    %rbx
    768c:	41 5c                	pop    %r12
    768e:	41 5d                	pop    %r13
    7690:	41 5e                	pop    %r14
    7692:	41 5f                	pop    %r15
    7694:	5d                   	pop    %rbp
    7695:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
    7696:	48 81 45 b8 e0 00 00 00 	addq   $0xe0,-0x48(%rbp)
    769e:	45 89 f4             	mov    %r14d,%r12d
    76a1:	41 8d 57 01          	lea    0x1(%r15),%edx
    76a5:	45 39 ef             	cmp    %r13d,%r15d
    76a8:	74 db                	je     7685 <verify+0x305>
    76aa:	41 89 d7             	mov    %edx,%r15d
    76ad:	e9 ff fc ff ff       	jmp    73b1 <verify+0x31>
    76b2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    76bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000076c0 <atexit>:
    76c0:	f3 0f 1e fa          	endbr64
    76c4:	48 8b 15 3d 39 00 00 	mov    0x393d(%rip),%rdx        # b008 <__dso_handle>
    76cb:	31 f6                	xor    %esi,%esi
    76cd:	e9 6e ae ff ff       	jmp    2540 <__cxa_atexit@plt>
    76d2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    76dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000076e0 <__stack_chk_fail_local>:
    76e0:	f3 0f 1e fa          	endbr64
    76e4:	50                   	push   %rax
    76e5:	58                   	pop    %rax
    76e6:	48 83 ec 08          	sub    $0x8,%rsp
    76ea:	e8 b1 ac ff ff       	call   23a0 <__stack_chk_fail@plt>

Disassembly of section .fini:

00000000000076f0 <_fini>:
    76f0:	f3 0f 1e fa          	endbr64
    76f4:	48 83 ec 08          	sub    $0x8,%rsp
    76f8:	48 83 c4 08          	add    $0x8,%rsp
    76fc:	c3                   	ret
