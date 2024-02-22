
multibarrier-evented:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8d 05 d1 23 00 00 	lea    0x23d1(%rip),%rax        # 43e0 <__gmon_start__>
    200f:	48 85 c0             	test   %rax,%rax
    2012:	74 02                	je     2016 <_init+0x16>
    2014:	ff d0                	call   *%rax
    2016:	48 83 c4 08          	add    $0x8,%rsp
    201a:	c3                   	ret

Disassembly of section .plt:

0000000000002020 <.plt>:
    2020:	ff 35 1a 8e 00 00    	push   0x8e1a(%rip)        # ae40 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 1c 8e 00 00    	jmp    *0x8e1c(%rip)        # ae48 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    2310:	f3 0f 1e fa          	endbr64
    2314:	68 2e 00 00 00       	push   $0x2e
    2319:	e9 02 fd ff ff       	jmp    2020 <_init+0x20>
    231e:	66 90                	xchg   %ax,%ax
    2320:	f3 0f 1e fa          	endbr64
    2324:	68 2f 00 00 00       	push   $0x2f
    2329:	e9 f2 fc ff ff       	jmp    2020 <_init+0x20>
    232e:	66 90                	xchg   %ax,%ax

Disassembly of section .plt.got:

0000000000002330 <__cxa_finalize@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 be 8c 00 00    	jmp    *0x8cbe(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000002340 <free@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 06 8b 00 00    	jmp    *0x8b06(%rip)        # ae50 <free@GLIBC_2.2.5>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <putchar@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 fe 8a 00 00    	jmp    *0x8afe(%rip)        # ae58 <putchar@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <pthread_setaffinity_np@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 f6 8a 00 00    	jmp    *0x8af6(%rip)        # ae60 <pthread_setaffinity_np@GLIBC_2.34>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <puts@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 ee 8a 00 00    	jmp    *0x8aee(%rip)        # ae68 <puts@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <setsockopt@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 e6 8a 00 00    	jmp    *0x8ae6(%rip)        # ae70 <setsockopt@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <clock_gettime@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 de 8a 00 00    	jmp    *0x8ade(%rip)        # ae78 <clock_gettime@GLIBC_2.17>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <fclose@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 d6 8a 00 00    	jmp    *0x8ad6(%rip)        # ae80 <fclose@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <strlen@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 ce 8a 00 00    	jmp    *0x8ace(%rip)        # ae88 <strlen@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <__stack_chk_fail@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 c6 8a 00 00    	jmp    *0x8ac6(%rip)        # ae90 <__stack_chk_fail@GLIBC_2.4>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <io_uring_submit@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 be 8a 00 00    	jmp    *0x8abe(%rip)        # ae98 <io_uring_submit@LIBURING_2.0>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <nanosleep@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 b6 8a 00 00    	jmp    *0x8ab6(%rip)        # aea0 <nanosleep@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <strrchr@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 ae 8a 00 00    	jmp    *0x8aae(%rip)        # aea8 <strrchr@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <fputs@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 a6 8a 00 00    	jmp    *0x8aa6(%rip)        # aeb0 <fputs@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <close@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 9e 8a 00 00    	jmp    *0x8a9e(%rip)        # aeb8 <close@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <strtok_r@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 96 8a 00 00    	jmp    *0x8a96(%rip)        # aec0 <strtok_r@GLIBC_2.2.5>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <read@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 8e 8a 00 00    	jmp    *0x8a8e(%rip)        # aec8 <read@GLIBC_2.2.5>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <calloc@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 86 8a 00 00    	jmp    *0x8a86(%rip)        # aed0 <calloc@GLIBC_2.2.5>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <strcmp@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 7e 8a 00 00    	jmp    *0x8a7e(%rip)        # aed8 <strcmp@GLIBC_2.2.5>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <__monstartup@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 76 8a 00 00    	jmp    *0x8a76(%rip)        # aee0 <__monstartup@GLIBC_2.2.5>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <__memcpy_chk@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 6e 8a 00 00    	jmp    *0x8a6e(%rip)        # aee8 <__memcpy_chk@GLIBC_2.3.4>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <stat@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 66 8a 00 00    	jmp    *0x8a66(%rip)        # aef0 <stat@GLIBC_2.33>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <memcpy@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 5e 8a 00 00    	jmp    *0x8a5e(%rip)        # aef8 <memcpy@GLIBC_2.14>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <io_uring_queue_init@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 56 8a 00 00    	jmp    *0x8a56(%rip)        # af00 <io_uring_queue_init@LIBURING_2.0>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <eventfd_write@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 4e 8a 00 00    	jmp    *0x8a4e(%rip)        # af08 <eventfd_write@GLIBC_2.7>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <pthread_mutex_unlock@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 46 8a 00 00    	jmp    *0x8a46(%rip)        # af10 <pthread_mutex_unlock@GLIBC_2.2.5>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <malloc@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 3e 8a 00 00    	jmp    *0x8a3e(%rip)        # af18 <malloc@GLIBC_2.2.5>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <listen@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 36 8a 00 00    	jmp    *0x8a36(%rip)        # af20 <listen@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <__strcpy_chk@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 2e 8a 00 00    	jmp    *0x8a2e(%rip)        # af28 <__strcpy_chk@GLIBC_2.3.4>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <__io_uring_get_cqe@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 26 8a 00 00    	jmp    *0x8a26(%rip)        # af30 <__io_uring_get_cqe@LIBURING_2.0>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <__printf_chk@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 1e 8a 00 00    	jmp    *0x8a1e(%rip)        # af38 <__printf_chk@GLIBC_2.3.4>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <bind@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 16 8a 00 00    	jmp    *0x8a16(%rip)        # af40 <bind@GLIBC_2.2.5>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <pthread_create@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 0e 8a 00 00    	jmp    *0x8a0e(%rip)        # af48 <pthread_create@GLIBC_2.34>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <open@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 06 8a 00 00    	jmp    *0x8a06(%rip)        # af50 <open@GLIBC_2.2.5>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <fopen@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 fe 89 00 00    	jmp    *0x89fe(%rip)        # af58 <fopen@GLIBC_2.2.5>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <perror@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 f6 89 00 00    	jmp    *0x89f6(%rip)        # af60 <perror@GLIBC_2.2.5>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <__cxa_atexit@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 ee 89 00 00    	jmp    *0x89ee(%rip)        # af68 <__cxa_atexit@GLIBC_2.2.5>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <exit@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 e6 89 00 00    	jmp    *0x89e6(%rip)        # af70 <exit@GLIBC_2.2.5>
    258a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002590 <eventfd@plt>:
    2590:	f3 0f 1e fa          	endbr64
    2594:	ff 25 de 89 00 00    	jmp    *0x89de(%rip)        # af78 <eventfd@GLIBC_2.7>
    259a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025a0 <fwrite@plt>:
    25a0:	f3 0f 1e fa          	endbr64
    25a4:	ff 25 d6 89 00 00    	jmp    *0x89d6(%rip)        # af80 <fwrite@GLIBC_2.2.5>
    25aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025b0 <__fprintf_chk@plt>:
    25b0:	f3 0f 1e fa          	endbr64
    25b4:	ff 25 ce 89 00 00    	jmp    *0x89ce(%rip)        # af88 <__fprintf_chk@GLIBC_2.3.4>
    25ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025c0 <io_uring_register_eventfd@plt>:
    25c0:	f3 0f 1e fa          	endbr64
    25c4:	ff 25 c6 89 00 00    	jmp    *0x89c6(%rip)        # af90 <io_uring_register_eventfd@LIBURING_2.0>
    25ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025d0 <pthread_join@plt>:
    25d0:	f3 0f 1e fa          	endbr64
    25d4:	ff 25 be 89 00 00    	jmp    *0x89be(%rip)        # af98 <pthread_join@GLIBC_2.34>
    25da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025e0 <strerror@plt>:
    25e0:	f3 0f 1e fa          	endbr64
    25e4:	ff 25 b6 89 00 00    	jmp    *0x89b6(%rip)        # afa0 <strerror@GLIBC_2.2.5>
    25ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025f0 <pthread_mutex_init@plt>:
    25f0:	f3 0f 1e fa          	endbr64
    25f4:	ff 25 ae 89 00 00    	jmp    *0x89ae(%rip)        # afa8 <pthread_mutex_init@GLIBC_2.2.5>
    25fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002600 <pthread_mutex_lock@plt>:
    2600:	f3 0f 1e fa          	endbr64
    2604:	ff 25 a6 89 00 00    	jmp    *0x89a6(%rip)        # afb0 <pthread_mutex_lock@GLIBC_2.2.5>
    260a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002610 <__ctype_tolower_loc@plt>:
    2610:	f3 0f 1e fa          	endbr64
    2614:	ff 25 9e 89 00 00    	jmp    *0x899e(%rip)        # afb8 <__ctype_tolower_loc@GLIBC_2.3>
    261a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002620 <__sprintf_chk@plt>:
    2620:	f3 0f 1e fa          	endbr64
    2624:	ff 25 96 89 00 00    	jmp    *0x8996(%rip)        # afc0 <__sprintf_chk@GLIBC_2.3.4>
    262a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002630 <socket@plt>:
    2630:	f3 0f 1e fa          	endbr64
    2634:	ff 25 8e 89 00 00    	jmp    *0x898e(%rip)        # afc8 <socket@GLIBC_2.2.5>
    263a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000002640 <fatal_error>:
  if (a > b) { return a; }
  if (b > a) { return b; }
  return a;
}

void fatal_error(const char *syscall) {
    2640:	f3 0f 1e fa          	endbr64
    2644:	55                   	push   %rbp
    2645:	48 89 e5             	mov    %rsp,%rbp
    2648:	ff 15 9a 89 00 00    	call   *0x899a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    perror(syscall);
    264e:	e8 0d ff ff ff       	call   2560 <perror@plt>
    exit(1);
    2653:	bf 01 00 00 00       	mov    $0x1,%edi
    2658:	e8 23 ff ff ff       	call   2580 <exit@plt>

000000000000265d <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    265d:	48 8d 3d c2 5b 00 00 	lea    0x5bc2(%rip),%rdi        # 8226 <_IO_stdin_used+0x226>
    2664:	e8 d7 ff ff ff       	call   2640 <fatal_error>

0000000000002669 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    2669:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    266f:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2677:	0f 0b                	ud2

0000000000002679 <add_read_request.cold>:
    2679:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2681:	0f 0b                	ud2

0000000000002683 <_send_static_string_content.cold>:
    2683:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    2689:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2691:	0f 0b                	ud2

0000000000002693 <add_accept_request.cold>:
    2693:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    269b:	0f 0b                	ud2

000000000000269d <io_thread.cold>:
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    269d:	48 8d 3d 52 5b 00 00 	lea    0x5b52(%rip),%rdi        # 81f6 <_IO_stdin_used+0x1f6>
    26a4:	e8 97 ff ff ff       	call   2640 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    26a9:	48 8d 3d ca 5a 00 00 	lea    0x5aca(%rip),%rdi        # 817a <_IO_stdin_used+0x17a>
    26b0:	e8 8b ff ff ff       	call   2640 <fatal_error>
    fatal_error("listen()");
    26b5:	48 8d 3d de 5a 00 00 	lea    0x5ade(%rip),%rdi        # 819a <_IO_stdin_used+0x19a>
    26bc:	e8 7f ff ff ff       	call   2640 <fatal_error>
    26c1:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26c9:	0f 0b                	ud2
    26cb:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26d3:	0f 0b                	ud2
      fatal_error("socket()");
    26d5:	48 8d 3d 95 5a 00 00 	lea    0x5a95(%rip),%rdi        # 8171 <_IO_stdin_used+0x171>
    26dc:	e8 5f ff ff ff       	call   2640 <fatal_error>
      fatal_error("bind()");
    26e1:	48 8d 3d ab 5a 00 00 	lea    0x5aab(%rip),%rdi        # 8193 <_IO_stdin_used+0x193>
    26e8:	e8 53 ff ff ff       	call   2640 <fatal_error>
    26ed:	0f 1f 00             	nopl   (%rax)

00000000000026f0 <main>:
    }


  return 0;
}
int main() {
    26f0:	f3 0f 1e fa          	endbr64
    26f4:	55                   	push   %rbp
    26f5:	48 89 e5             	mov    %rsp,%rbp
    26f8:	41 57                	push   %r15
    26fa:	41 56                	push   %r14
    26fc:	41 55                	push   %r13
    26fe:	41 54                	push   %r12
    2700:	53                   	push   %rbx
    2701:	48 81 ec 08 01 00 00 	sub    $0x108,%rsp
    2708:	ff 15 da 88 00 00    	call   *0x88da(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    270e:	48 8d 3d 53 5f 00 00 	lea    0x5f53(%rip),%rdi        # 8668 <_IO_stdin_used+0x668>
    2715:	4c 8d 25 60 5c 00 00 	lea    0x5c60(%rip),%r12        # 837c <_IO_stdin_used+0x37c>
    271c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    2725:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    2729:	48 8d 05 20 1e 00 00 	lea    0x1e20(%rip),%rax        # 4550 <barriered_reset>
    2730:	66 48 0f 6e f0       	movq   %rax,%xmm6
    2735:	0f 16 35 f4 84 00 00 	movhps 0x84f4(%rip),%xmm6        # ac30 <__do_global_dtors_aux_fini_array_entry+0x8>
    273c:	0f 29 b5 00 ff ff ff 	movaps %xmm6,-0x100(%rbp)
    2743:	e8 28 fc ff ff       	call   2370 <puts@plt>
    2748:	bf 0a 00 00 00       	mov    $0xa,%edi
    274d:	e8 fe fb ff ff       	call   2350 <putchar@plt>
    2752:	ba 01 00 00 00       	mov    $0x1,%edx
    2757:	48 8d 35 16 5b 00 00 	lea    0x5b16(%rip),%rsi        # 8274 <_IO_stdin_used+0x274>
    275e:	31 c0                	xor    %eax,%eax
    2760:	bf 01 00 00 00       	mov    $0x1,%edi
    2765:	e8 a6 fd ff ff       	call   2510 <__printf_chk@plt>
    276a:	ba 06 00 00 00       	mov    $0x6,%edx
    276f:	48 8d 35 0e 5b 00 00 	lea    0x5b0e(%rip),%rsi        # 8284 <_IO_stdin_used+0x284>
    2776:	31 c0                	xor    %eax,%eax
    2778:	bf 01 00 00 00       	mov    $0x1,%edi
    277d:	e8 8e fd ff ff       	call   2510 <__printf_chk@plt>
    2782:	ba 03 00 00 00       	mov    $0x3,%edx
    2787:	48 8d 35 0b 5b 00 00 	lea    0x5b0b(%rip),%rsi        # 8299 <_IO_stdin_used+0x299>
    278e:	31 c0                	xor    %eax,%eax
    2790:	bf 01 00 00 00       	mov    $0x1,%edi
    2795:	e8 76 fd ff ff       	call   2510 <__printf_chk@plt>
    279a:	ba 02 00 00 00       	mov    $0x2,%edx
    279f:	48 8d 35 03 5b 00 00 	lea    0x5b03(%rip),%rsi        # 82a9 <_IO_stdin_used+0x2a9>
    27a6:	31 c0                	xor    %eax,%eax
    27a8:	bf 01 00 00 00       	mov    $0x1,%edi
    27ad:	e8 5e fd ff ff       	call   2510 <__printf_chk@plt>
    27b2:	48 8d 3d 06 5b 00 00 	lea    0x5b06(%rip),%rdi        # 82bf <_IO_stdin_used+0x2bf>
    27b9:	e8 b2 fb ff ff       	call   2370 <puts@plt>
    27be:	ba 02 00 00 00       	mov    $0x2,%edx
    27c3:	48 8d 35 11 5b 00 00 	lea    0x5b11(%rip),%rsi        # 82db <_IO_stdin_used+0x2db>
    27ca:	31 c0                	xor    %eax,%eax
    27cc:	bf 01 00 00 00       	mov    $0x1,%edi
    27d1:	e8 3a fd ff ff       	call   2510 <__printf_chk@plt>
    27d6:	ba 0a 00 00 00       	mov    $0xa,%edx
    27db:	48 8d 35 13 5b 00 00 	lea    0x5b13(%rip),%rsi        # 82f5 <_IO_stdin_used+0x2f5>
    27e2:	31 c0                	xor    %eax,%eax
    27e4:	bf 01 00 00 00       	mov    $0x1,%edi
    27e9:	e8 22 fd ff ff       	call   2510 <__printf_chk@plt>
    27ee:	ba 01 00 00 00       	mov    $0x1,%edx
    27f3:	48 8d 35 0f 5b 00 00 	lea    0x5b0f(%rip),%rsi        # 8309 <_IO_stdin_used+0x309>
    27fa:	31 c0                	xor    %eax,%eax
    27fc:	bf 01 00 00 00       	mov    $0x1,%edi
    2801:	e8 0a fd ff ff       	call   2510 <__printf_chk@plt>
    2806:	ba 01 00 00 00       	mov    $0x1,%edx
    280b:	48 8d 35 08 5b 00 00 	lea    0x5b08(%rip),%rsi        # 831a <_IO_stdin_used+0x31a>
    2812:	31 c0                	xor    %eax,%eax
    2814:	bf 01 00 00 00       	mov    $0x1,%edi
    2819:	e8 f2 fc ff ff       	call   2510 <__printf_chk@plt>
    281e:	ba 02 00 00 00       	mov    $0x2,%edx
    2823:	48 8d 35 08 5b 00 00 	lea    0x5b08(%rip),%rsi        # 8332 <_IO_stdin_used+0x332>
    282a:	31 c0                	xor    %eax,%eax
    282c:	bf 01 00 00 00       	mov    $0x1,%edi
    2831:	e8 da fc ff ff       	call   2510 <__printf_chk@plt>
    2836:	ba 01 00 00 00       	mov    $0x1,%edx
    283b:	48 8d 35 8e 5e 00 00 	lea    0x5e8e(%rip),%rsi        # 86d0 <_IO_stdin_used+0x6d0>
    2842:	31 c0                	xor    %eax,%eax
    2844:	bf 01 00 00 00       	mov    $0x1,%edi
    2849:	e8 c2 fc ff ff       	call   2510 <__printf_chk@plt>
    284e:	ba 01 00 00 00       	mov    $0x1,%edx
    2853:	48 8d 35 a6 5e 00 00 	lea    0x5ea6(%rip),%rsi        # 8700 <_IO_stdin_used+0x700>
    285a:	31 c0                	xor    %eax,%eax
    285c:	bf 01 00 00 00       	mov    $0x1,%edi
    2861:	e8 aa fc ff ff       	call   2510 <__printf_chk@plt>
    2866:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    286b:	48 8d 35 dc 5a 00 00 	lea    0x5adc(%rip),%rsi        # 834e <_IO_stdin_used+0x34e>
    2872:	31 c0                	xor    %eax,%eax
    2874:	bf 01 00 00 00       	mov    $0x1,%edi
    2879:	e8 92 fc ff ff       	call   2510 <__printf_chk@plt>
    287e:	ba 05 00 00 00       	mov    $0x5,%edx
    2883:	48 8d 35 de 5a 00 00 	lea    0x5ade(%rip),%rsi        # 8368 <_IO_stdin_used+0x368>
    288a:	31 c0                	xor    %eax,%eax
    288c:	bf 01 00 00 00       	mov    $0x1,%edi
    2891:	e8 7a fc ff ff       	call   2510 <__printf_chk@plt>
    2896:	48 8d 3d 58 58 00 00 	lea    0x5858(%rip),%rdi        # 80f5 <_IO_stdin_used+0xf5>
    289d:	e8 ce fa ff ff       	call   2370 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    28a2:	be 18 00 00 00       	mov    $0x18,%esi
    28a7:	bf 03 00 00 00       	mov    $0x3,%edi
    28ac:	e8 8f fb ff ff       	call   2440 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28b1:	be d8 00 00 00       	mov    $0xd8,%esi
    28b6:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    28bb:	48 89 85 20 ff ff ff 	mov    %rax,-0xe0(%rbp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28c2:	e8 79 fb ff ff       	call   2440 <calloc@plt>
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28c7:	be 28 00 00 00       	mov    $0x28,%esi
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
    28cc:	45 31 ff             	xor    %r15d,%r15d
  int cc = 0; 
    28cf:	45 31 f6             	xor    %r14d,%r14d
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28d2:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28d7:	48 89 45 88          	mov    %rax,-0x78(%rbp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28db:	e8 60 fb ff ff       	call   2440 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28e0:	be 28 00 00 00       	mov    $0x28,%esi
    28e5:	bf 64 00 00 00       	mov    $0x64,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28ea:	48 89 85 f0 fe ff ff 	mov    %rax,-0x110(%rbp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28f1:	e8 4a fb ff ff       	call   2440 <calloc@plt>
    28f6:	48 89 85 e8 fe ff ff 	mov    %rax,-0x118(%rbp)
    for (int y = 0 ; y < total_threads; y++) {
    28fd:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
int main() {
    2901:	49 89 c5             	mov    %rax,%r13
    for (int y = 0 ; y < total_threads; y++) {
    2904:	31 db                	xor    %ebx,%ebx
    2906:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    2910:	41 8d 14 1e          	lea    (%r14,%rbx,1),%edx
    2914:	41 89 d8             	mov    %ebx,%r8d
    2917:	44 89 f9             	mov    %r15d,%ecx
    291a:	4c 89 e6             	mov    %r12,%rsi
    291d:	bf 01 00 00 00       	mov    $0x1,%edi
    2922:	31 c0                	xor    %eax,%eax
    2924:	83 c3 01             	add    $0x1,%ebx
    2927:	e8 e4 fb ff ff       	call   2510 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    292c:	4c 89 ef             	mov    %r13,%rdi
    292f:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    2931:	49 83 c5 28          	add    $0x28,%r13
      pthread_mutex_init(&swapmutex[cc++], NULL);
    2935:	e8 b6 fc ff ff       	call   25f0 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    293a:	83 fb 0a             	cmp    $0xa,%ebx
    293d:	75 d1                	jne    2910 <main+0x220>
    293f:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    2943:	41 83 c6 0a          	add    $0xa,%r14d
  for (int x = 0 ; x < total_threads; x++) {
    2947:	41 83 c7 01          	add    $0x1,%r15d
    294b:	48 05 90 01 00 00    	add    $0x190,%rax
    2951:	41 83 fe 64          	cmp    $0x64,%r14d
    2955:	75 a6                	jne    28fd <main+0x20d>
    2957:	ba 06 00 00 00       	mov    $0x6,%edx
    295c:	48 8d 35 29 5a 00 00 	lea    0x5a29(%rip),%rsi        # 838c <_IO_stdin_used+0x38c>
    2963:	bf 01 00 00 00       	mov    $0x1,%edi
    2968:	31 c0                	xor    %eax,%eax
    296a:	e8 a1 fb ff ff       	call   2510 <__printf_chk@plt>
    296f:	ba 0c 00 00 00       	mov    $0xc,%edx
    2974:	48 8d 35 27 5a 00 00 	lea    0x5a27(%rip),%rsi        # 83a2 <_IO_stdin_used+0x3a2>
    297b:	31 c0                	xor    %eax,%eax
    297d:	bf 01 00 00 00       	mov    $0x1,%edi
    2982:	e8 89 fb ff ff       	call   2510 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2987:	be 10 00 00 00       	mov    $0x10,%esi
    298c:	bf 0c 00 00 00       	mov    $0xc,%edi
    2991:	e8 aa fa ff ff       	call   2440 <calloc@plt>
    2996:	48 89 85 10 ff ff ff 	mov    %rax,-0xf0(%rbp)
    299d:	49 89 c7             	mov    %rax,%r15
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    29a0:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    29a7:	49 89 c6             	mov    %rax,%r14
    buffers[x].count = buffer_size;
    29aa:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29b1:	be 00 01 00 00       	mov    $0x100,%esi
    29b6:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    29bb:	49 83 c6 10          	add    $0x10,%r14
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29bf:	e8 7c fa ff ff       	call   2440 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29c4:	be 20 00 00 00       	mov    $0x20,%esi
    29c9:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29ce:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    29d2:	49 89 c4             	mov    %rax,%r12
      buffers[x].buffer[y].available = 0;
    29d5:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    29df:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29e9:	e8 52 fa ff ff       	call   2440 <calloc@plt>
    29ee:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
  for (int x = 0 ; x < buffers_required; x++) {
    29f6:	4c 39 f3             	cmp    %r14,%rbx
    29f9:	75 af                	jne    29aa <main+0x2ba>
    29fb:	48 8b b5 20 ff ff ff 	mov    -0xe0(%rbp),%rsi
    2a02:	4c 89 f8             	mov    %r15,%rax
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  int swap = 0;
  for (int k = 0 ; k < group_count ; k++) {
    2a05:	45 31 ed             	xor    %r13d,%r13d
  int dataid = 0;
    2a08:	45 31 e4             	xor    %r12d,%r12d
    2a0b:	48 8b 5d 88          	mov    -0x78(%rbp),%rbx
  int swap = 0;
    2a0f:	c7 45 90 00 00 00 00 	movl   $0x0,-0x70(%rbp)
    2a16:	48 89 b5 28 ff ff ff 	mov    %rsi,-0xd8(%rbp)
  int cur_buffer = 0;
    2a1d:	c7 85 40 ff ff ff 00 00 00 00 	movl   $0x0,-0xc0(%rbp)
    2a27:	49 89 df             	mov    %rbx,%r15
  int curcpu = 0;
    2a2a:	c7 85 44 ff ff ff 00 00 00 00 	movl   $0x0,-0xbc(%rbp)
    2a34:	48 89 9d 18 ff ff ff 	mov    %rbx,-0xe8(%rbp)
    2a3b:	48 89 c3             	mov    %rax,%rbx
    for (int d = 0 ; d < threads_per_group ; d++) {
    2a3e:	48 63 85 40 ff ff ff 	movslq -0xc0(%rbp),%rax
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2a45:	4d 89 f9             	mov    %r15,%r9
    2a48:	45 89 ee             	mov    %r13d,%r14d
    2a4b:	4c 89 bd e0 fe ff ff 	mov    %r15,-0x120(%rbp)
    2a52:	48 89 b5 f8 fe ff ff 	mov    %rsi,-0x108(%rbp)
    2a59:	48 c1 e0 04          	shl    $0x4,%rax
    2a5d:	48 89 9d d8 fe ff ff 	mov    %rbx,-0x128(%rbp)
    2a64:	48 01 d8             	add    %rbx,%rax
    2a67:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
    2a6e:	43 8d 44 2d 00       	lea    0x0(%r13,%r13,1),%eax
    2a73:	8d 78 01             	lea    0x1(%rax),%edi
    2a76:	83 c0 03             	add    $0x3,%eax
    2a79:	89 7d 98             	mov    %edi,-0x68(%rbp)
    2a7c:	89 85 38 ff ff ff    	mov    %eax,-0xc8(%rbp)
    2a82:	8b 7d 98             	mov    -0x68(%rbp),%edi
    2a85:	44 89 f2             	mov    %r14d,%edx
    2a88:	48 8d 35 99 5c 00 00 	lea    0x5c99(%rip),%rsi        # 8728 <_IO_stdin_used+0x728>
    2a8f:	31 c0                	xor    %eax,%eax
    2a91:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
      int x = (k * threads_per_group) + d;
    2a95:	44 8d 7f ff          	lea    -0x1(%rdi),%r15d
    2a99:	bf 01 00 00 00       	mov    $0x1,%edi
    2a9e:	44 89 f9             	mov    %r15d,%ecx
    2aa1:	44 89 7d a0          	mov    %r15d,-0x60(%rbp)
    2aa5:	e8 66 fa ff ff       	call   2510 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2aaa:	be 08 00 00 00       	mov    $0x8,%esi
    2aaf:	bf 02 00 00 00       	mov    $0x2,%edi
    2ab4:	e8 87 f9 ff ff       	call   2440 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2ab9:	be 80 00 00 00       	mov    $0x80,%esi
    2abe:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2ac3:	48 89 c3             	mov    %rax,%rbx
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2ac6:	e8 75 f9 ff ff       	call   2440 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2acb:	41 83 e7 01          	and    $0x1,%r15d
    2acf:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
    2ad3:	44 89 bd 60 ff ff ff 	mov    %r15d,-0xa0(%rbp)
    2ada:	45 89 f8             	mov    %r15d,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2add:	49 89 c5             	mov    %rax,%r13
        other = abs(x - 1) % total_threads;
    2ae0:	44 8b 7d 98          	mov    -0x68(%rbp),%r15d
      if (x % 2 == 1) {
    2ae4:	0f 84 19 11 00 00    	je     3c03 <main+0x1513>
        other = abs(x - 1) % total_threads;
    2aea:	41 8d 47 fe          	lea    -0x2(%r15),%eax
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    2aee:	48 8b 75 88          	mov    -0x78(%rbp),%rsi
        my_thread_data[1] = &thread_data[x]; 
    2af2:	4c 89 ca             	mov    %r9,%rdx
        other = abs(x - 1) % total_threads;
    2af5:	48 89 c1             	mov    %rax,%rcx
        my_thread_data[0] = &thread_data[other]; 
    2af8:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2afc:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    2b00:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2b04:	48 8d 73 08          	lea    0x8(%rbx),%rsi
    2b08:	48 89 b5 70 ff ff ff 	mov    %rsi,-0x90(%rbp)
        thread_data[x].protected_state = &protected_state[k];
    2b0f:	48 8b bd f8 fe ff ff 	mov    -0x108(%rbp),%rdi
        thread_data[x].thread_index = 1;
    2b16:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2b1a:	48 8d 35 37 5c 00 00 	lea    0x5c37(%rip),%rsi        # 8758 <_IO_stdin_used+0x758>
    2b21:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    2b25:	8b 55 a0             	mov    -0x60(%rbp),%edx
        thread_data[x].protected_state = &protected_state[k];
    2b28:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2b2c:	bf 01 00 00 00       	mov    $0x1,%edi
    2b31:	48 89 03             	mov    %rax,(%rbx)
    2b34:	31 c0                	xor    %eax,%eax
    2b36:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    2b3a:	89 4d b8             	mov    %ecx,-0x48(%rbp)
    2b3d:	e8 ce f9 ff ff       	call   2510 <__printf_chk@plt>
      thread_data[x].other = other;
    2b42:	8b 4d b8             	mov    -0x48(%rbp),%ecx
    2b45:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    2b49:	31 c0                	xor    %eax,%eax
    2b4b:	8b 55 a0             	mov    -0x60(%rbp),%edx
    2b4e:	48 8d 35 33 5c 00 00 	lea    0x5c33(%rip),%rsi        # 8788 <_IO_stdin_used+0x788>
    2b55:	bf 01 00 00 00       	mov    $0x1,%edi
    2b5a:	41 89 89 b8 00 00 00 	mov    %ecx,0xb8(%r9)
    2b61:	8b 8d 44 ff ff ff    	mov    -0xbc(%rbp),%ecx
    2b67:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
    2b6b:	e8 a0 f9 ff ff       	call   2510 <__printf_chk@plt>
        if (x < thread_count) {
    2b70:	83 7d a0 01          	cmpl   $0x1,-0x60(%rbp)
    2b74:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
    2b78:	0f 87 aa 10 00 00    	ja     3c28 <main+0x1538>
          CPU_SET(curcpu, sendercpu);
    2b7e:	48 63 85 44 ff ff ff 	movslq -0xbc(%rbp),%rax
    2b85:	48 89 c7             	mov    %rax,%rdi
    2b88:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2b8e:	77 13                	ja     2ba3 <main+0x4b3>
    2b90:	48 c1 e8 06          	shr    $0x6,%rax
    2b94:	ba 01 00 00 00       	mov    $0x1,%edx
    2b99:	89 f9                	mov    %edi,%ecx
    2b9b:	48 d3 e2             	shl    %cl,%rdx
    2b9e:	49 09 54 c5 00       	or     %rdx,0x0(%r13,%rax,8)
          curcpu += 2;
    2ba3:	83 85 44 ff ff ff 02 	addl   $0x2,-0xbc(%rbp)
      thread_data[x].swapmutex = swapmutex;
    2baa:	48 8b 85 e8 fe ff ff 	mov    -0x118(%rbp),%rax
      thread_data[x].threads = my_thread_data;
    2bb1:	49 89 59 18          	mov    %rbx,0x18(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2bb5:	be 10 00 00 00       	mov    $0x10,%esi
    2bba:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].kind = KERNEL_THREAD;
    2bbf:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
            data[0].messages_count = 0;
    2bc6:	44 89 e3             	mov    %r12d,%ebx
      thread_data[x].swapmutex = swapmutex;
    2bc9:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2bd0:	48 8b 85 f0 fe ff ff 	mov    -0x110(%rbp),%rax
      thread_data[x].cpu_set = sendercpu;
    2bd7:	4d 89 a9 b0 00 00 00 	mov    %r13,0xb0(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2bde:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].real_thread_index = x;
    2be5:	8b 45 a0             	mov    -0x60(%rbp),%eax
      thread_data[x].task_count = total_barrier_count;
    2be8:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].real_thread_index = x;
    2bf0:	41 89 41 08          	mov    %eax,0x8(%r9)
      thread_data[x].all_threads = thread_data;
    2bf4:	48 8b 45 88          	mov    -0x78(%rbp),%rax
      thread_data[x].task_count = total_barrier_count;
    2bf8:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
      thread_data[x].all_threads = thread_data;
    2bfc:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2c00:	48 8b 05 a9 60 00 00 	mov    0x60a9(%rip),%rax        # 8cb0 <_IO_stdin_used+0xcb0>
    2c07:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2c0e:	48 8b 05 a3 60 00 00 	mov    0x60a3(%rip),%rax        # 8cb8 <_IO_stdin_used+0xcb8>
    2c15:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2c19:	e8 22 f8 ff ff       	call   2440 <calloc@plt>
    2c1e:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2c22:	be 10 00 00 00       	mov    $0x10,%esi
    2c27:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2c2c:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2c30:	e8 0b f8 ff ff       	call   2440 <calloc@plt>
    2c35:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c39:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2c3e:	66 0f 6f 3d 3a 60 00 00 	movdqa 0x603a(%rip),%xmm7        # 8c80 <_IO_stdin_used+0xc80>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c46:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2c4b:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2c4f:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c57:	e8 e4 f7 ff ff       	call   2440 <calloc@plt>
    2c5c:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c60:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2c65:	66 0f 6f 35 13 60 00 00 	movdqa 0x6013(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c6d:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c72:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2c79:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c81:	e8 ba f7 ff ff       	call   2440 <calloc@plt>
        thread_data[x].tasks = barriers;
    2c86:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c8a:	4c 89 ff             	mov    %r15,%rdi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2c8d:	45 31 ff             	xor    %r15d,%r15d
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c90:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2c93:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c97:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
    2c9c:	48 0f af f8          	imul   %rax,%rdi
            data[0].messages_count = 0;
    2ca0:	4c 89 8d 68 ff ff ff 	mov    %r9,-0x98(%rbp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2ca7:	48 c1 ef 22          	shr    $0x22,%rdi
    2cab:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2cae:	8b 7d 98             	mov    -0x68(%rbp),%edi
    2cb1:	01 c0                	add    %eax,%eax
    2cb3:	29 c7                	sub    %eax,%edi
            data[0].messages_count = 0;
    2cb5:	89 bd 3c ff ff ff    	mov    %edi,-0xc4(%rbp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2cbb:	49 63 c7             	movslq %r15d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2cbe:	be 38 00 00 00       	mov    $0x38,%esi
    2cc3:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cc8:	45 31 e4             	xor    %r12d,%r12d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2ccb:	48 89 85 78 ff ff ff 	mov    %rax,-0x88(%rbp)
    2cd2:	48 c1 e0 09          	shl    $0x9,%rax
    2cd6:	4c 8d 2c 02          	lea    (%rdx,%rax,1),%r13
    2cda:	48 89 45 80          	mov    %rax,-0x80(%rbp)
    2cde:	48 8d 05 1b 18 00 00 	lea    0x181b(%rip),%rax        # 4500 <do_protected_write>
    2ce5:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2cec:	e8 4f f7 ff ff       	call   2440 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2cf1:	49 89 85 70 01 00 00 	mov    %rax,0x170(%r13)
    2cf8:	44 8b ad 60 ff ff ff 	mov    -0xa0(%rbp),%r13d
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2cff:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d02:	45 85 ed             	test   %r13d,%r13d
    2d05:	0f 84 7c 06 00 00    	je     3387 <main+0xc97>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2d0b:	8b 45 98             	mov    -0x68(%rbp),%eax
    2d0e:	44 89 7d b8          	mov    %r15d,-0x48(%rbp)
    2d12:	49 89 cd             	mov    %rcx,%r13
    2d15:	48 89 8d 30 ff ff ff 	mov    %rcx,-0xd0(%rbp)
    2d1c:	83 e8 02             	sub    $0x2,%eax
    2d1f:	89 85 48 ff ff ff    	mov    %eax,-0xb8(%rbp)
    2d25:	eb 1b                	jmp    2d42 <main+0x652>
    2d27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d30:	41 83 c4 01          	add    $0x1,%r12d
    2d34:	49 83 c5 38          	add    $0x38,%r13
    2d38:	41 83 fc 06          	cmp    $0x6,%r12d
    2d3c:	0f 84 54 01 00 00    	je     2e96 <main+0x7a6>
            int group_of = b / threads_per_group;
    2d42:	45 89 e7             	mov    %r12d,%r15d
    2d45:	31 c0                	xor    %eax,%eax
    2d47:	44 89 e2             	mov    %r12d,%edx
    2d4a:	bf 01 00 00 00       	mov    $0x1,%edi
    2d4f:	41 d1 ff             	sar    %r15d
    2d52:	48 8d 35 63 56 00 00 	lea    0x5663(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2d59:	44 89 f9             	mov    %r15d,%ecx
    2d5c:	e8 af f7 ff ff       	call   2510 <__printf_chk@plt>
            if (k == group_of) {
    2d61:	45 39 fe             	cmp    %r15d,%r14d
    2d64:	75 ca                	jne    2d30 <main+0x640>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d66:	be 08 00 00 00       	mov    $0x8,%esi
    2d6b:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d70:	49 83 c5 38          	add    $0x38,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d74:	e8 c7 f6 ff ff       	call   2440 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d79:	be 08 00 00 00       	mov    $0x8,%esi
    2d7e:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d83:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d8a:	e8 b1 f6 ff ff       	call   2440 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2d8f:	be 80 03 00 00       	mov    $0x380,%esi
    2d94:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d99:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2d9d:	e8 9e f6 ff ff       	call   2440 <calloc@plt>
              data[0].a = x;
    2da2:	8b 7d a0             	mov    -0x60(%rbp),%edi
              data[0].b = y;
    2da5:	8b 75 b8             	mov    -0x48(%rbp),%esi
    2da8:	44 89 e2             	mov    %r12d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    2dab:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    2dae:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
              data[0].a = x;
    2db5:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].b = y;
    2dbb:	89 b0 20 03 00 00    	mov    %esi,0x320(%rax)
              data[0].kind = MAILBOX_LOWER;
    2dc1:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].id = dataid++;
    2dcb:	8d 43 01             	lea    0x1(%rbx),%eax
              data[1].id = dataid++;
    2dce:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2dd5:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2ddc:	49 89 45 d0          	mov    %rax,-0x30(%r13)
    2de0:	8b 85 48 ff ff ff    	mov    -0xb8(%rbp),%eax
              data[0].id = dataid++;
    2de6:	41 89 99 28 03 00 00 	mov    %ebx,0x328(%r9)
              data[1].id = dataid++;
    2ded:	83 c3 02             	add    $0x2,%ebx
              data[1].a = x;
    2df0:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    2df7:	89 c1                	mov    %eax,%ecx
    2df9:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].b = y;
    2dfe:	41 89 b1 a0 06 00 00 	mov    %esi,0x6a0(%r9)
    2e05:	48 8d 35 9c 59 00 00 	lea    0x599c(%rip),%rsi        # 87a8 <_IO_stdin_used+0x7a8>
              data[1].c = b;
    2e0c:	45 89 a1 a4 06 00 00 	mov    %r12d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e13:	41 83 c4 01          	add    $0x1,%r12d
              mailboxes[b].lower = &data[0];
    2e17:	4d 89 4d c8          	mov    %r9,-0x38(%r13)
    2e1b:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    2e1f:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    2e21:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[0].finished_reading = 1;
    2e2c:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    2e37:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].pending = NULL;
    2e42:	49 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%r13)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2e4a:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    2e52:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    2e56:	e8 b5 f6 ff ff       	call   2510 <__printf_chk@plt>
              data[0].messages = messages;
    2e5b:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    2e5f:	4c 8b 9d 58 ff ff ff 	mov    -0xa8(%rbp),%r11
              data[0].messages_count = 0;
    2e66:	66 0f 6f 35 22 5e 00 00 	movdqa 0x5e22(%rip),%xmm6        # 8c90 <_IO_stdin_used+0xc90>
              data[1].messages = messages2;
    2e6e:	4c 8b 55 a8          	mov    -0x58(%rbp),%r10
              data[0].messages = messages;
    2e72:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2e75:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2e7c:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2e84:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e8c:	41 83 fc 06          	cmp    $0x6,%r12d
    2e90:	0f 85 ac fe ff ff    	jne    2d42 <main+0x652>
    2e96:	44 8b 7d b8          	mov    -0x48(%rbp),%r15d
    2e9a:	48 8b 8d 30 ff ff ff 	mov    -0xd0(%rbp),%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ea1:	45 31 ed             	xor    %r13d,%r13d
    2ea4:	44 89 75 b8          	mov    %r14d,-0x48(%rbp)
    2ea8:	41 89 de             	mov    %ebx,%r14d
    2eab:	44 89 eb             	mov    %r13d,%ebx
    2eae:	49 89 cd             	mov    %rcx,%r13
    2eb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            int group_of = b / threads_per_group;
    2eb8:	89 d8                	mov    %ebx,%eax
    2eba:	d1 f8                	sar    %eax
            if (k == group_of) {
    2ebc:	39 45 b8             	cmp    %eax,-0x48(%rbp)
    2ebf:	0f 84 68 01 00 00    	je     302d <main+0x93d>
    2ec5:	89 da                	mov    %ebx,%edx
    2ec7:	48 8d 35 fe 54 00 00 	lea    0x54fe(%rip),%rsi        # 83cc <_IO_stdin_used+0x3cc>
    2ece:	bf 01 00 00 00       	mov    $0x1,%edi
    2ed3:	31 c0                	xor    %eax,%eax
    2ed5:	e8 36 f6 ff ff       	call   2510 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2eda:	be 08 00 00 00       	mov    $0x8,%esi
    2edf:	bf 01 00 00 00       	mov    $0x1,%edi
    2ee4:	e8 57 f5 ff ff       	call   2440 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ee9:	be 08 00 00 00       	mov    $0x8,%esi
    2eee:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ef3:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ef7:	e8 44 f5 ff ff       	call   2440 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2efc:	be 80 03 00 00       	mov    $0x380,%esi
    2f01:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f06:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
            struct Data *data = calloc(3, sizeof(struct Data));
    2f0a:	e8 31 f5 ff ff       	call   2440 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2f0f:	be 80 03 00 00       	mov    $0x380,%esi
    2f14:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2f19:	49 89 c4             	mov    %rax,%r12
            struct Data **stack = calloc(3, sizeof(struct Data));
    2f1c:	e8 1f f5 ff ff       	call   2440 <calloc@plt>
            data[0].a = x;
    2f21:	8b 7d a0             	mov    -0x60(%rbp),%edi
            data[0].id = dataid++;
    2f24:	41 8d 76 01          	lea    0x1(%r14),%esi
            data[0].messages = messages;
    2f28:	4c 8b 4d a8          	mov    -0x58(%rbp),%r9
            data[1].messages = messages2;
    2f2c:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
            data[0].messages_count = 0;
    2f30:	66 0f 6f 35 58 5d 00 00 	movdqa 0x5d58(%rip),%xmm6        # 8c90 <_IO_stdin_used+0xc90>
            data[1].id = dataid++;
    2f38:	41 89 b4 24 a8 06 00 00 	mov    %esi,0x6a8(%r12)
            mailboxes[b].higher = &data[1];
    2f40:	49 8d b4 24 80 03 00 00 	lea    0x380(%r12),%rsi
            data[0].id = dataid++;
    2f48:	45 89 b4 24 28 03 00 00 	mov    %r14d,0x328(%r12)
            data[1].id = dataid++;
    2f50:	41 83 c6 02          	add    $0x2,%r14d
            data[0].kind = MAILBOX_LOWER;
    2f54:	41 c7 84 24 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r12)
            data[0].a = x;
    2f60:	41 89 bc 24 1c 03 00 00 	mov    %edi,0x31c(%r12)
            data[0].b = y;
    2f68:	45 89 bc 24 20 03 00 00 	mov    %r15d,0x320(%r12)
            data[0].c = b;
    2f70:	41 89 9c 24 24 03 00 00 	mov    %ebx,0x324(%r12)
            data[1].kind = MAILBOX_HIGHER;
    2f78:	41 c7 84 24 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r12)
            data[1].a = x;
    2f84:	41 89 bc 24 9c 06 00 00 	mov    %edi,0x69c(%r12)
            data[1].b = y;
    2f8c:	45 89 bc 24 a0 06 00 00 	mov    %r15d,0x6a0(%r12)
            data[1].c = b;
    2f94:	41 89 9c 24 a4 06 00 00 	mov    %ebx,0x6a4(%r12)
            mailboxes[b].lower = &data[0];
    2f9c:	4d 89 65 00          	mov    %r12,0x0(%r13)
            mailboxes[b].my_lower = &data[0];
    2fa0:	4d 89 65 20          	mov    %r12,0x20(%r13)
            mailboxes[b].higher = &data[1];
    2fa4:	49 89 75 08          	mov    %rsi,0x8(%r13)
            mailboxes[b].pending = NULL;
    2fa8:	49 c7 45 10 00 00 00 00 	movq   $0x0,0x10(%r13)
            data[0].finished_reading = 1;
    2fb0:	41 c7 84 24 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r12)
            data[1].finished_reading = 1;
    2fbc:	41 c7 84 24 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r12)
            mailboxes[b].my_higher = &data[1];
    2fc8:	49 89 75 28          	mov    %rsi,0x28(%r13)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2fcc:	41 c7 45 30 02 00 00 00 	movl   $0x2,0x30(%r13)
            stack[0] = mailboxes[b].lower;
    2fd4:	4c 89 20             	mov    %r12,(%rax)
            stack[1] = mailboxes[b].higher;
    2fd7:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2fdb:	49 89 45 18          	mov    %rax,0x18(%r13)
            data[0].available_sending = 0;
    2fdf:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
            data[0].available_receiving = 0;
    2feb:	41 c7 84 24 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r12)
            data[0].messages = messages;
    2ff7:	4d 89 0c 24          	mov    %r9,(%r12)
            data[1].messages = messages2;
    2ffb:	49 89 94 24 80 03 00 00 	mov    %rdx,0x380(%r12)
            data[1].available_sending = 1;
    3003:	41 c7 84 24 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r12)
            data[1].available_receiving = 0;
    300f:	41 c7 84 24 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r12)
            data[0].messages_count = 0;
    301b:	41 0f 29 b4 24 80 00 00 00 	movaps %xmm6,0x80(%r12)
            data[1].messages_count = 0;
    3024:	41 0f 29 b4 24 00 04 00 00 	movaps %xmm6,0x400(%r12)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    302d:	83 c3 01             	add    $0x1,%ebx
    3030:	49 83 c5 38          	add    $0x38,%r13
    3034:	83 fb 06             	cmp    $0x6,%ebx
    3037:	0f 85 7b fe ff ff    	jne    2eb8 <main+0x7c8>
          char *message = malloc(sizeof(char) * 256);
    303d:	be 01 00 00 00       	mov    $0x1,%esi
    3042:	bf 00 01 00 00       	mov    $0x100,%edi
    3047:	44 89 f3             	mov    %r14d,%ebx
    304a:	44 8b 75 b8          	mov    -0x48(%rbp),%r14d
    304e:	e8 ed f3 ff ff       	call   2440 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    3053:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    3058:	49 89 c5             	mov    %rax,%r13
          struct Message *messaged = malloc(sizeof(struct Message));
    305b:	e8 70 f4 ff ff       	call   24d0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3060:	48 83 ec 08          	sub    $0x8,%rsp
    3064:	44 8b 45 a0          	mov    -0x60(%rbp),%r8d
    3068:	4c 89 ef             	mov    %r13,%rdi
    306b:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    306f:	45 89 f9             	mov    %r15d,%r9d
    3072:	ba 00 01 00 00       	mov    $0x100,%edx
    3077:	31 c0                	xor    %eax,%eax
    3079:	41 56                	push   %r14
    307b:	48 8d 0d 4e 57 00 00 	lea    0x574e(%rip),%rcx        # 87d0 <_IO_stdin_used+0x7d0>
    3082:	be 01 00 00 00       	mov    $0x1,%esi
    3087:	e8 94 f5 ff ff       	call   2620 <__sprintf_chk@plt>
          messaged->message = message;
    308c:	4c 8b 5d b8          	mov    -0x48(%rbp),%r11
          thread_data[x].tasks[y].swap = swap;
    3090:	48 8b 4d 80          	mov    -0x80(%rbp),%rcx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3094:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->task_index = y;
    3099:	48 8b 85 78 ff ff ff 	mov    -0x88(%rbp),%rax
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    30a0:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->message = message;
    30a5:	4d 89 2b             	mov    %r13,(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    30a8:	4c 8b ad 68 ff ff ff 	mov    -0x98(%rbp),%r13
          messaged->task_index = y;
    30af:	49 89 43 10          	mov    %rax,0x10(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    30b3:	49 63 45 08          	movslq 0x8(%r13),%rax
          thread_data[x].tasks[y].swap = swap;
    30b7:	49 8b 55 38          	mov    0x38(%r13),%rdx
          messaged->group = k;
    30bb:	45 89 73 18          	mov    %r14d,0x18(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    30bf:	49 89 43 08          	mov    %rax,0x8(%r11)
          thread_data[x].tasks[y].swap = swap;
    30c3:	8b 45 90             	mov    -0x70(%rbp),%eax
    30c6:	48 01 d1             	add    %rdx,%rcx
          thread_data[x].tasks[y].message = messaged;
    30c9:	4c 89 99 88 01 00 00 	mov    %r11,0x188(%rcx)
          thread_data[x].tasks[y].swap = swap;
    30d0:	89 81 98 01 00 00    	mov    %eax,0x198(%rcx)
          swap += 1;
    30d6:	83 c0 01             	add    $0x1,%eax
    30d9:	89 45 90             	mov    %eax,-0x70(%rbp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    30dc:	41 8d 47 01          	lea    0x1(%r15),%eax
    30e0:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    30e3:	c7 01 41 00 00 00    	movl   $0x41,(%rcx)
          thread_data[x].tasks[y].group = k;
    30e9:	44 89 b1 94 01 00 00 	mov    %r14d,0x194(%rcx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    30f0:	89 81 90 01 00 00    	mov    %eax,0x190(%rcx)
          thread_data[x].tasks[y].sending = 1;
    30f6:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
          thread_data[x].tasks[y].snapshot_count = 99;
    3100:	48 c7 81 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rcx)
          thread_data[x].tasks[y].swap = swap;
    310b:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
          thread_data[x].tasks[y].snapshot_count = 99;
    310f:	48 89 4d b8          	mov    %rcx,-0x48(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3113:	e8 28 f3 ff ff       	call   2440 <calloc@plt>
    3118:	48 8b 4d b8          	mov    -0x48(%rbp),%rcx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    311c:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3120:	48 89 81 50 01 00 00 	mov    %rax,0x150(%rcx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3127:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    312e:	48 c7 81 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rcx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3139:	48 8b 00             	mov    (%rax),%rax
    313c:	8b 70 04             	mov    0x4(%rax),%esi
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    313f:	4c 39 e8             	cmp    %r13,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    3142:	48 89 81 28 01 00 00 	mov    %rax,0x128(%rcx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3149:	89 b1 30 01 00 00    	mov    %esi,0x130(%rcx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    314f:	41 5b                	pop    %r11
    3151:	41 5c                	pop    %r12
    3153:	0f 85 45 12 00 00    	jne    439e <main+0x1cae>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    3159:	66 0f 6f 05 3f 5b 00 00 	movdqa 0x5b3f(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    3161:	44 89 79 04          	mov    %r15d,0x4(%rcx)
          thread_data[x].tasks[y].available = 1;
    3165:	4c 8b 2d 54 5b 00 00 	mov    0x5b54(%rip),%r13        # 8cc0 <_IO_stdin_used+0xcc0>
          thread_data[x].tasks[y].arrived = 0;
    316c:	c7 81 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rcx)
          thread_data[x].tasks[y].worker_count = thread_count;
    3176:	c7 81 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rcx)
          thread_data[x].tasks[y].available = 1;
    3180:	4c 89 a9 44 01 00 00 	mov    %r13,0x144(%rcx)
          thread_data[x].tasks[y].thread_count = 2;
    3187:	0f 11 81 34 01 00 00 	movups %xmm0,0x134(%rcx)
          if (y == barrier_count - 1) {
    318e:	41 83 ff 01          	cmp    $0x1,%r15d
    3192:	0f 84 97 03 00 00    	je     352f <main+0xe3f>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    3198:	45 85 ff             	test   %r15d,%r15d
    319b:	0f 84 75 03 00 00    	je     3516 <main+0xe26>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    31a1:	4c 8b 8d 68 ff ff ff 	mov    -0x98(%rbp),%r9
    31a8:	48 8d 05 31 38 00 00 	lea    0x3831(%rip),%rax        # 69e0 <barriered_work>
    31af:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    31b3:	41 89 dc             	mov    %ebx,%r12d
    31b6:	48 89 81 18 01 00 00 	mov    %rax,0x118(%rcx)
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    31bd:	bf 01 00 00 00       	mov    $0x1,%edi
    31c2:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers_count = buffers_per_thread;
    31c7:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    31d2:	4c 89 4d b8          	mov    %r9,-0x48(%rbp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    31d6:	e8 65 f2 ff ff       	call   2440 <calloc@plt>
    31db:	4c 8b 4d b8          	mov    -0x48(%rbp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    31df:	48 8b bd 50 ff ff ff 	mov    -0xb0(%rbp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    31e6:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    31ea:	66 0f 6f bd 00 ff ff ff 	movdqa -0x100(%rbp),%xmm7
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    31f2:	48 89 38             	mov    %rdi,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    31f5:	48 83 c7 10          	add    $0x10,%rdi
    31f9:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3200:	49 89 81 78 ff ff ff 	mov    %rax,-0x88(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3207:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    320e:	83 45 98 01          	addl   $0x1,-0x68(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3212:	48 8b 00             	mov    (%rax),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3215:	83 85 40 ff ff ff 01 	addl   $0x1,-0xc0(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    321c:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3226:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    322d:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    3237:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    3241:	41 8b 81 2c ff ff ff 	mov    -0xd4(%r9),%eax
    for (int d = 0 ; d < threads_per_group ; d++) {
    3248:	48 89 bd 50 ff ff ff 	mov    %rdi,-0xb0(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    324f:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3255:	8b 45 98             	mov    -0x68(%rbp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    3258:	c7 82 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
    3262:	4c 89 aa 44 05 00 00 	mov    %r13,0x544(%rdx)
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3269:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3270:	39 85 38 ff ff ff    	cmp    %eax,-0xc8(%rbp)
    3276:	0f 85 06 f8 ff ff    	jne    2a82 <main+0x392>
    327c:	4c 8b bd e0 fe ff ff 	mov    -0x120(%rbp),%r15
    3283:	48 8b b5 f8 fe ff ff 	mov    -0x108(%rbp),%rsi
    328a:	45 89 f5             	mov    %r14d,%r13d
  for (int k = 0 ; k < group_count ; k++) {
    328d:	41 83 c5 01          	add    $0x1,%r13d
    3291:	48 8b 9d d8 fe ff ff 	mov    -0x128(%rbp),%rbx
    3298:	48 83 c6 18          	add    $0x18,%rsi
    329c:	49 81 c7 b0 01 00 00 	add    $0x1b0,%r15
    32a3:	41 83 fd 03          	cmp    $0x3,%r13d
    32a7:	0f 85 91 f7 ff ff    	jne    2a3e <main+0x34e>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    32ad:	be 08 00 00 00       	mov    $0x8,%esi
    32b2:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    32b7:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    32ba:	e8 81 f1 ff ff       	call   2440 <calloc@plt>
    32bf:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    32c3:	49 89 c7             	mov    %rax,%r15
    32c6:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    32c8:	49 89 d1             	mov    %rdx,%r9
    32cb:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    32cd:	45 8b 51 40          	mov    0x40(%r9),%r10d
    32d1:	45 85 d2             	test   %r10d,%r10d
    32d4:	0f 8e 94 00 00 00    	jle    336e <main+0xc7e>
    32da:	49 8b 79 38          	mov    0x38(%r9),%rdi
    32de:	4d 63 c2             	movslq %r10d,%r8
    32e1:	49 63 cc             	movslq %r12d,%rcx
    32e4:	49 c1 e0 09          	shl    $0x9,%r8
    32e8:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    32ec:	49 01 f8             	add    %rdi,%r8
    32ef:	90                   	nop
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32f0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    32f7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    32fe:	48 83 c6 60          	add    $0x60,%rsi
    3302:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    3307:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    330c:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3314:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3318:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3320:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3324:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    3328:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    3330:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3337:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    333b:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    333f:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3346:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    334d:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3351:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3355:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3359:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    335d:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3361:	49 39 f8             	cmp    %rdi,%r8
    3364:	75 8a                	jne    32f0 <main+0xc00>
    3366:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    336a:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    336e:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    3375:	85 db                	test   %ebx,%ebx
    3377:	0f 85 c1 01 00 00    	jne    353e <main+0xe4e>
    337d:	bb 01 00 00 00       	mov    $0x1,%ebx
    3382:	e9 46 ff ff ff       	jmp    32cd <main+0xbdd>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3387:	44 89 7d b8          	mov    %r15d,-0x48(%rbp)
    338b:	49 89 c5             	mov    %rax,%r13
    338e:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
    3395:	eb 1b                	jmp    33b2 <main+0xcc2>
    3397:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    33a0:	41 83 c4 01          	add    $0x1,%r12d
    33a4:	49 83 c5 38          	add    $0x38,%r13
    33a8:	41 83 fc 06          	cmp    $0x6,%r12d
    33ac:	0f 84 54 01 00 00    	je     3506 <main+0xe16>
            int group_of = b / threads_per_group;
    33b2:	45 89 e7             	mov    %r12d,%r15d
    33b5:	31 c0                	xor    %eax,%eax
    33b7:	44 89 e2             	mov    %r12d,%edx
    33ba:	bf 01 00 00 00       	mov    $0x1,%edi
    33bf:	41 d1 ff             	sar    %r15d
    33c2:	48 8d 35 f3 4f 00 00 	lea    0x4ff3(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    33c9:	44 89 f9             	mov    %r15d,%ecx
    33cc:	e8 3f f1 ff ff       	call   2510 <__printf_chk@plt>
            if (k == group_of) {
    33d1:	45 39 fe             	cmp    %r15d,%r14d
    33d4:	75 ca                	jne    33a0 <main+0xcb0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    33d6:	be 08 00 00 00       	mov    $0x8,%esi
    33db:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    33e0:	49 83 c5 38          	add    $0x38,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    33e4:	e8 57 f0 ff ff       	call   2440 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    33e9:	be 08 00 00 00       	mov    $0x8,%esi
    33ee:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    33f3:	48 89 85 58 ff ff ff 	mov    %rax,-0xa8(%rbp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    33fa:	e8 41 f0 ff ff       	call   2440 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    33ff:	be 80 03 00 00       	mov    $0x380,%esi
    3404:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3409:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
              struct Data *data = calloc(3, sizeof(struct Data));
    340d:	e8 2e f0 ff ff       	call   2440 <calloc@plt>
              data[0].a = x;
    3412:	8b 7d a0             	mov    -0x60(%rbp),%edi
              data[0].b = y;
    3415:	8b 75 b8             	mov    -0x48(%rbp),%esi
    3418:	44 89 e2             	mov    %r12d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    341b:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    341e:	44 89 a0 24 03 00 00 	mov    %r12d,0x324(%rax)
              data[0].a = x;
    3425:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].b = y;
    342b:	89 b0 20 03 00 00    	mov    %esi,0x320(%rax)
              data[0].kind = MAILBOX_LOWER;
    3431:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].id = dataid++;
    343b:	8d 43 01             	lea    0x1(%rbx),%eax
              data[1].id = dataid++;
    343e:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    3445:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    344c:	49 89 45 d0          	mov    %rax,-0x30(%r13)
    3450:	8b 85 3c ff ff ff    	mov    -0xc4(%rbp),%eax
              data[0].id = dataid++;
    3456:	41 89 99 28 03 00 00 	mov    %ebx,0x328(%r9)
              data[1].id = dataid++;
    345d:	83 c3 02             	add    $0x2,%ebx
              data[1].a = x;
    3460:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    3467:	89 c1                	mov    %eax,%ecx
    3469:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].b = y;
    346e:	41 89 b1 a0 06 00 00 	mov    %esi,0x6a0(%r9)
    3475:	48 8d 35 2c 53 00 00 	lea    0x532c(%rip),%rsi        # 87a8 <_IO_stdin_used+0x7a8>
              data[1].c = b;
    347c:	45 89 a1 a4 06 00 00 	mov    %r12d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3483:	41 83 c4 01          	add    $0x1,%r12d
              mailboxes[b].lower = &data[0];
    3487:	4d 89 4d c8          	mov    %r9,-0x38(%r13)
    348b:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    348f:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    3491:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[0].finished_reading = 1;
    349c:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    34a7:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].pending = NULL;
    34b2:	49 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%r13)
              mailboxes[b].kind = MAILBOX_FRIEND;
    34ba:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    34c2:	4c 89 4d b0          	mov    %r9,-0x50(%rbp)
    34c6:	e8 45 f0 ff ff       	call   2510 <__printf_chk@plt>
              data[0].messages = messages;
    34cb:	4c 8b 4d b0          	mov    -0x50(%rbp),%r9
    34cf:	4c 8b 9d 58 ff ff ff 	mov    -0xa8(%rbp),%r11
              data[0].messages_count = 0;
    34d6:	66 0f 6f 35 b2 57 00 00 	movdqa 0x57b2(%rip),%xmm6        # 8c90 <_IO_stdin_used+0xc90>
              data[1].messages = messages2;
    34de:	4c 8b 55 a8          	mov    -0x58(%rbp),%r10
              data[0].messages = messages;
    34e2:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    34e5:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    34ec:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    34f4:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    34fc:	41 83 fc 06          	cmp    $0x6,%r12d
    3500:	0f 85 ac fe ff ff    	jne    33b2 <main+0xcc2>
    3506:	44 8b 7d b8          	mov    -0x48(%rbp),%r15d
    350a:	48 8b 8d 48 ff ff ff 	mov    -0xb8(%rbp),%rcx
    3511:	e9 8b f9 ff ff       	jmp    2ea1 <main+0x7b1>
    3516:	48 8d 05 c3 3a 00 00 	lea    0x3ac3(%rip),%rax        # 6fe0 <barriered_work_ingest_andwork>
    351d:	41 bf 01 00 00 00    	mov    $0x1,%r15d
            thread_data[x].tasks[y].run = barriered_work; 
    3523:	48 89 81 18 01 00 00 	mov    %rax,0x118(%rcx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    352a:	e9 8c f7 ff ff       	jmp    2cbb <main+0x5cb>
    352f:	48 8d 05 aa 34 00 00 	lea    0x34aa(%rip),%rax        # 69e0 <barriered_work>
    3536:	41 bf 02 00 00 00    	mov    $0x2,%r15d
    353c:	eb e5                	jmp    3523 <main+0xe33>
  for (int k = 0 ; k < group_count ; k++) {
    353e:	83 c0 02             	add    $0x2,%eax
    3541:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3548:	83 f8 06             	cmp    $0x6,%eax
    354b:	0f 85 77 fd ff ff    	jne    32c8 <main+0xbd8>
    3551:	48 8d 3d 92 4e 00 00 	lea    0x4e92(%rip),%rdi        # 83ea <_IO_stdin_used+0x3ea>
    3558:	e8 13 ee ff ff       	call   2370 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    355d:	48 8d 3d 9d 4e 00 00 	lea    0x4e9d(%rip),%rdi        # 8401 <_IO_stdin_used+0x401>
    3564:	48 8d 35 94 4e 00 00 	lea    0x4e94(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    356b:	e8 e0 ef ff ff       	call   2550 <fopen@plt>
    3570:	48 89 c7             	mov    %rax,%rdi
  for (int x = 0 ; x < datas_size; x++) {
    3573:	45 85 e4             	test   %r12d,%r12d
    3576:	0f 8e 80 00 00 00    	jle    35fc <main+0xf0c>
    357c:	4d 63 e4             	movslq %r12d,%r12
    357f:	89 5d b0             	mov    %ebx,-0x50(%rbp)
    3582:	4c 8d 35 55 4e 00 00 	lea    0x4e55(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    3589:	4c 8d 2d 92 4e 00 00 	lea    0x4e92(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    3590:	4b 8d 04 e7          	lea    (%r15,%r12,8),%rax
    3594:	48 89 fb             	mov    %rdi,%rbx
    3597:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    char * c = calloc(250, sizeof(char));
    359b:	be 01 00 00 00       	mov    $0x1,%esi
    35a0:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    35a5:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    35a9:	e8 92 ee ff ff       	call   2440 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    35ae:	4c 89 f1             	mov    %r14,%rcx
    35b1:	ba fa 00 00 00       	mov    $0xfa,%edx
    35b6:	be 01 00 00 00       	mov    $0x1,%esi
    35bb:	49 89 c4             	mov    %rax,%r12
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    35be:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    35c2:	4c 89 e7             	mov    %r12,%rdi
    35c5:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    35cc:	31 c0                	xor    %eax,%eax
    35ce:	e8 4d f0 ff ff       	call   2620 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    35d3:	4c 89 e2             	mov    %r12,%rdx
    35d6:	4c 89 ee             	mov    %r13,%rsi
    35d9:	bf 01 00 00 00       	mov    $0x1,%edi
    35de:	31 c0                	xor    %eax,%eax
    35e0:	e8 2b ef ff ff       	call   2510 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    35e5:	48 89 de             	mov    %rbx,%rsi
    35e8:	4c 89 e7             	mov    %r12,%rdi
    35eb:	e8 10 ee ff ff       	call   2400 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    35f0:	4c 39 7d b8          	cmp    %r15,-0x48(%rbp)
    35f4:	75 a5                	jne    359b <main+0xeab>
    35f6:	48 89 df             	mov    %rbx,%rdi
    35f9:	8b 5d b0             	mov    -0x50(%rbp),%ebx
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    35fc:	e8 9f ed ff ff       	call   23a0 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3601:	48 8d 3d 02 4e 00 00 	lea    0x4e02(%rip),%rdi        # 840a <_IO_stdin_used+0x40a>
    3608:	45 31 ed             	xor    %r13d,%r13d
    360b:	e8 60 ed ff ff       	call   2370 <puts@plt>
    3610:	48 8b 45 88          	mov    -0x78(%rbp),%rax
    3614:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    3618:	44 89 ea             	mov    %r13d,%edx
    361b:	48 8d 35 03 4e 00 00 	lea    0x4e03(%rip),%rsi        # 8425 <_IO_stdin_used+0x425>
    3622:	31 c0                	xor    %eax,%eax

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    3624:	45 31 f6             	xor    %r14d,%r14d
    3627:	bf 01 00 00 00       	mov    $0x1,%edi
    362c:	47 8d 7c 2d 00       	lea    0x0(%r13,%r13,1),%r15d
    3631:	e8 da ee ff ff       	call   2510 <__printf_chk@plt>
    3636:	4c 8b 65 b8          	mov    -0x48(%rbp),%r12
    363a:	44 89 7d b0          	mov    %r15d,-0x50(%rbp)
    363e:	4c 89 e0             	mov    %r12,%rax
    3641:	41 89 dc             	mov    %ebx,%r12d
    3644:	44 89 f3             	mov    %r14d,%ebx
    3647:	49 89 c6             	mov    %rax,%r14
      int x = (k * threads_per_group) + d;
    364a:	8b 45 b0             	mov    -0x50(%rbp),%eax
    364d:	89 da                	mov    %ebx,%edx
    364f:	48 8d 35 d9 4d 00 00 	lea    0x4dd9(%rip),%rsi        # 842f <_IO_stdin_used+0x42f>
    3656:	45 31 ff             	xor    %r15d,%r15d
    3659:	bf 01 00 00 00       	mov    $0x1,%edi
    365e:	8d 0c 03             	lea    (%rbx,%rax,1),%ecx
    3661:	31 c0                	xor    %eax,%eax
    3663:	e8 a8 ee ff ff       	call   2510 <__printf_chk@plt>
    3668:	89 5d a8             	mov    %ebx,-0x58(%rbp)
    366b:	44 89 65 a0          	mov    %r12d,-0x60(%rbp)
    366f:	44 89 6d 98          	mov    %r13d,-0x68(%rbp)
    3673:	44 89 fa             	mov    %r15d,%edx
    3676:	48 8d 35 c4 4d 00 00 	lea    0x4dc4(%rip),%rsi        # 8441 <_IO_stdin_used+0x441>
    367d:	31 c0                	xor    %eax,%eax
    367f:	4d 89 fd             	mov    %r15,%r13
    3682:	bf 01 00 00 00       	mov    $0x1,%edi
    3687:	49 c1 e5 09          	shl    $0x9,%r13
    368b:	45 31 e4             	xor    %r12d,%r12d
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    368e:	31 db                	xor    %ebx,%ebx
    3690:	e8 7b ee ff ff       	call   2510 <__printf_chk@plt>
    3695:	eb 37                	jmp    36ce <main+0xfde>
    3697:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    36a0:	83 fa 01             	cmp    $0x1,%edx
    36a3:	0f 84 94 00 00 00    	je     373d <main+0x104d>
    36a9:	44 8b 40 34          	mov    0x34(%rax),%r8d
    36ad:	89 da                	mov    %ebx,%edx
    36af:	48 8d 35 96 4d 00 00 	lea    0x4d96(%rip),%rsi        # 844c <_IO_stdin_used+0x44c>
    36b6:	31 c0                	xor    %eax,%eax
    36b8:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    36bd:	83 c3 01             	add    $0x1,%ebx
    36c0:	49 83 c4 38          	add    $0x38,%r12
    36c4:	e8 47 ee ff ff       	call   2510 <__printf_chk@plt>
    36c9:	83 fb 06             	cmp    $0x6,%ebx
    36cc:	74 43                	je     3711 <main+0x1021>
          char * mailbox_kind = calloc(100, sizeof(char));
    36ce:	be 01 00 00 00       	mov    $0x1,%esi
    36d3:	bf 64 00 00 00       	mov    $0x64,%edi
    36d8:	e8 63 ed ff ff       	call   2440 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    36dd:	49 8b 76 38          	mov    0x38(%r14),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    36e1:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    36e4:	4a 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%r13,1),%rax
    36ec:	4c 01 e0             	add    %r12,%rax
    36ef:	8b 50 30             	mov    0x30(%rax),%edx
    36f2:	83 fa 02             	cmp    $0x2,%edx
    36f5:	75 a9                	jne    36a0 <main+0xfb0>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    36f7:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    3701:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3704:	4a 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%r13,1),%rax
    370c:	4c 01 e0             	add    %r12,%rax
    370f:	eb 98                	jmp    36a9 <main+0xfb9>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3711:	49 83 c7 01          	add    $0x1,%r15
    3715:	49 83 ff 03          	cmp    $0x3,%r15
    3719:	0f 85 54 ff ff ff    	jne    3673 <main+0xf83>
    for (int d = 0 ; d < threads_per_group ; d++) {
    371f:	8b 5d a8             	mov    -0x58(%rbp),%ebx
    3722:	44 8b 65 a0          	mov    -0x60(%rbp),%r12d
    3726:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    372d:	44 8b 6d 98          	mov    -0x68(%rbp),%r13d
    3731:	85 db                	test   %ebx,%ebx
    3733:	75 25                	jne    375a <main+0x106a>
    3735:	44 89 e3             	mov    %r12d,%ebx
    3738:	e9 0d ff ff ff       	jmp    364a <main+0xf5a>
    373d:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3743:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    374a:	4a 8b 84 2e 70 01 00 00 	mov    0x170(%rsi,%r13,1),%rax
    3752:	4c 01 e0             	add    %r12,%rax
    3755:	e9 4f ff ff ff       	jmp    36a9 <main+0xfb9>
  for (int k = 0 ; k < group_count ; k++) {
    375a:	41 83 c5 01          	add    $0x1,%r13d
    375e:	41 89 de             	mov    %ebx,%r14d
    3761:	48 81 45 b8 b0 01 00 00 	addq   $0x1b0,-0x48(%rbp)
    3769:	44 89 e3             	mov    %r12d,%ebx
    376c:	41 83 fd 03          	cmp    $0x3,%r13d
    3770:	0f 85 a2 fe ff ff    	jne    3618 <main+0xf28>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3776:	ba 07 00 00 00       	mov    $0x7,%edx
    377b:	bf 01 00 00 00       	mov    $0x1,%edi
    3780:	31 c0                	xor    %eax,%eax
    3782:	45 89 f5             	mov    %r14d,%r13d
    3785:	48 8d 35 db 4c 00 00 	lea    0x4cdb(%rip),%rsi        # 8467 <_IO_stdin_used+0x467>
    378c:	e8 7f ed ff ff       	call   2510 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    3791:	be 08 00 00 00       	mov    $0x8,%esi
    3796:	bf 02 00 00 00       	mov    $0x2,%edi
    379b:	e8 a0 ec ff ff       	call   2440 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    37a0:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37a4:	be 38 00 00 00       	mov    $0x38,%esi
    my_thread_data[0] = &thread_data[x]; 
    37a9:	4c 8d bf e8 05 00 00 	lea    0x5e8(%rdi),%r15
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    37b0:	48 89 78 08          	mov    %rdi,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    37b4:	4c 8d b7 d8 00 00 00 	lea    0xd8(%rdi),%r14
    thread_data[x].threads = my_thread_data;
    37bb:	48 89 87 00 06 00 00 	mov    %rax,0x600(%rdi)
    my_thread_data[0] = &thread_data[x]; 
    37c2:	4c 89 38             	mov    %r15,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    37c5:	48 8b 47 38          	mov    0x38(%rdi),%rax
    thread_data[x].thread_count = 2;
    37c9:	c7 87 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%rdi)
    thread_data[x].thread_index = 0;
    37d3:	c7 87 ec 05 00 00 00 00 00 00 	movl   $0x0,0x5ec(%rdi)
    thread_data[x].task_count = total_barrier_count;
    37dd:	c7 87 28 06 00 00 03 00 00 00 	movl   $0x3,0x628(%rdi)
    thread_data[n].tasks[0].scheduled = 1;
    37e7:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    37f1:	48 8b 87 10 01 00 00 	mov    0x110(%rdi),%rax
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37f8:	bf 0a 00 00 00       	mov    $0xa,%edi
    thread_data[n].tasks[0].scheduled = 1;
    37fd:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3807:	e8 34 ec ff ff       	call   2440 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    380c:	be 38 00 00 00       	mov    $0x38,%esi
    3811:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3816:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    381a:	e8 21 ec ff ff       	call   2440 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    381f:	be 38 00 00 00       	mov    $0x38,%esi
    3824:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3829:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    382c:	e8 0f ec ff ff       	call   2440 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3831:	be 38 00 00 00       	mov    $0x38,%esi
    3836:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    383b:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    383f:	e8 fc eb ff ff       	call   2440 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3844:	be 08 00 00 00       	mov    $0x8,%esi
    3849:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    384e:	48 89 45 a8          	mov    %rax,-0x58(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3852:	e8 e9 eb ff ff       	call   2440 <calloc@plt>


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
    3857:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    385b:	be 08 00 00 00       	mov    $0x8,%esi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3860:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    3863:	48 8b 05 5e 54 00 00 	mov    0x545e(%rip),%rax        # 8cc8 <_IO_stdin_used+0xcc8>
  thread_data[timer_threadi].type = TIMER;
    386a:	c7 87 1c 05 00 00 00 00 00 00 	movl   $0x0,0x51c(%rdi)
  thread_data[timer_threadi].task_count = total_barrier_count;
    3874:	48 89 87 50 05 00 00 	mov    %rax,0x550(%rdi)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    387b:	bf 0a 00 00 00       	mov    $0xa,%edi
    3880:	e8 bb eb ff ff       	call   2440 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3885:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
    3889:	4c 89 78 38          	mov    %r15,0x38(%rax)
    388d:	48 8d 97 b0 01 00 00 	lea    0x1b0(%rdi),%rdx
    3894:	48 8d 8f 10 05 00 00 	lea    0x510(%rdi),%rcx
    389b:	48 89 38             	mov    %rdi,(%rax)
    389e:	48 89 50 10          	mov    %rdx,0x10(%rax)
    38a2:	48 8d 97 88 02 00 00 	lea    0x288(%rdi),%rdx
    38a9:	48 8d b7 c0 06 00 00 	lea    0x6c0(%rdi),%rsi
    38b0:	48 89 50 18          	mov    %rdx,0x18(%rax)
    38b4:	48 8d 97 60 03 00 00 	lea    0x360(%rdi),%rdx
    38bb:	48 89 50 20          	mov    %rdx,0x20(%rax)
    38bf:	48 8d 97 38 04 00 00 	lea    0x438(%rdi),%rdx
    38c6:	48 89 50 28          	mov    %rdx,0x28(%rax)
    38ca:	48 8d 97 98 07 00 00 	lea    0x798(%rdi),%rdx
    38d1:	48 89 48 30          	mov    %rcx,0x30(%rax)
    38d5:	48 89 70 40          	mov    %rsi,0x40(%rax)
    38d9:	48 89 50 48          	mov    %rdx,0x48(%rax)
    38dd:	ba 06 00 00 00       	mov    $0x6,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    38e2:	48 89 87 28 05 00 00 	mov    %rax,0x528(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    38e9:	4c 89 70 08          	mov    %r14,0x8(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    38ed:	48 8b 05 dc 53 00 00 	mov    0x53dc(%rip),%rax        # 8cd0 <_IO_stdin_used+0xcd0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    38f4:	c7 87 40 05 00 00 06 00 00 00 	movl   $0x6,0x540(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    38fe:	48 89 87 38 05 00 00 	mov    %rax,0x538(%rdi)
    3905:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3907:	c7 87 14 05 00 00 00 00 00 00 	movl   $0x0,0x514(%rdi)
    3911:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    3916:	48 89 75 a0          	mov    %rsi,-0x60(%rbp)
    391a:	48 8d 35 55 4b 00 00 	lea    0x4b55(%rip),%rsi        # 8476 <_IO_stdin_used+0x476>
    3921:	48 89 4d 98          	mov    %rcx,-0x68(%rbp)
    3925:	e8 e6 eb ff ff       	call   2510 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    392a:	48 8b 4d 98          	mov    -0x68(%rbp),%rcx
    392e:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    3932:	48 8d 15 a7 0d 00 00 	lea    0xda7(%rip),%rdx        # 46e0 <timer_thread>
    3939:	49 8d b4 24 50 01 00 00 	lea    0x150(%r12),%rsi
    3941:	e8 ea eb ff ff       	call   2530 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    3946:	44 89 6d 98          	mov    %r13d,-0x68(%rbp)
    394a:	45 31 c0             	xor    %r8d,%r8d
    394d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    3951:	4c 89 b5 78 ff ff ff 	mov    %r14,-0x88(%rbp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3958:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    395e:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    3962:	48 89 d9             	mov    %rbx,%rcx
    3965:	4c 89 7d 90          	mov    %r15,-0x70(%rbp)
    3969:	45 89 d7             	mov    %r10d,%r15d
    396c:	48 89 5d 80          	mov    %rbx,-0x80(%rbp)
    3970:	44 89 c3             	mov    %r8d,%ebx
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3973:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    3977:	44 8d 34 1b          	lea    (%rbx,%rbx,1),%r14d
    397b:	49 89 cd             	mov    %rcx,%r13
    397e:	49 89 d4             	mov    %rdx,%r12
    3981:	48 89 85 70 ff ff ff 	mov    %rax,-0x90(%rbp)
    3988:	48 89 8d 68 ff ff ff 	mov    %rcx,-0x98(%rbp)
    398f:	48 89 95 60 ff ff ff 	mov    %rdx,-0xa0(%rbp)
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3996:	41 c7 44 24 0c 01 00 00 00 	movl   $0x1,0xc(%r12)
    399f:	44 89 f2             	mov    %r14d,%edx
    39a2:	89 d9                	mov    %ebx,%ecx
    39a4:	31 c0                	xor    %eax,%eax
    39a6:	48 8d 35 53 4e 00 00 	lea    0x4e53(%rip),%rsi        # 8800 <_IO_stdin_used+0x800>
    39ad:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    39b2:	41 83 c6 01          	add    $0x1,%r14d
      thread_data[x].running = 1;
    39b6:	41 c7 44 24 44 01 00 00 00 	movl   $0x1,0x44(%r12)
    39bf:	e8 4c eb ff ff       	call   2510 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    39c4:	48 8b 75 b8          	mov    -0x48(%rbp),%rsi
    39c8:	4c 89 e1             	mov    %r12,%rcx
    39cb:	4c 89 ef             	mov    %r13,%rdi
    39ce:	48 8d 15 4b 29 00 00 	lea    0x294b(%rip),%rdx        # 6320 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    39d5:	49 81 c4 d8 00 00 00 	add    $0xd8,%r12
    39dc:	49 83 c5 08          	add    $0x8,%r13
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    39e0:	e8 4b eb ff ff       	call   2530 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    39e5:	49 8b 54 24 d8       	mov    -0x28(%r12),%rdx
    39ea:	49 8b 7d f8          	mov    -0x8(%r13),%rdi
    39ee:	be 08 00 00 00       	mov    $0x8,%esi
    39f3:	e8 68 e9 ff ff       	call   2360 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    39f8:	48 83 45 b8 38       	addq   $0x38,-0x48(%rbp)
    39fd:	45 39 f7             	cmp    %r14d,%r15d
    3a00:	75 94                	jne    3996 <main+0x12a6>
  for (int k = 0 ; k < group_count ; k++) {
    3a02:	48 8b 85 70 ff ff ff 	mov    -0x90(%rbp),%rax
    3a09:	48 8b 8d 68 ff ff ff 	mov    -0x98(%rbp),%rcx
    3a10:	83 c3 01             	add    $0x1,%ebx
    3a13:	41 83 c7 02          	add    $0x2,%r15d
    3a17:	48 8b 95 60 ff ff ff 	mov    -0xa0(%rbp),%rdx
    3a1e:	48 83 c1 10          	add    $0x10,%rcx
    3a22:	48 83 c0 70          	add    $0x70,%rax
    3a26:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3a2d:	83 fb 03             	cmp    $0x3,%ebx
    3a30:	0f 85 3d ff ff ff    	jne    3973 <main+0x1283>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    3a36:	4c 8b 65 88          	mov    -0x78(%rbp),%r12
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a3a:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].task_count = 0;
    3a3f:	48 8b 05 92 52 00 00 	mov    0x5292(%rip),%rax        # 8cd8 <_IO_stdin_used+0xcd8>
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a46:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = IO;
    3a4b:	4c 8b 7d 90          	mov    -0x70(%rbp),%r15
    3a4f:	48 8b 5d 80          	mov    -0x80(%rbp),%rbx
    3a53:	41 c7 84 24 f4 05 00 00 02 00 00 00 	movl   $0x2,0x5f4(%r12)
    3a5f:	4c 8b b5 78 ff ff ff 	mov    -0x88(%rbp),%r14
    thread_data[x].task_count = 0;
    3a66:	49 89 84 24 28 06 00 00 	mov    %rax,0x628(%r12)
    thread_data[x].type = IO;
    3a6e:	44 8b 6d 98          	mov    -0x68(%rbp),%r13d
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a72:	e8 c9 e9 ff ff       	call   2440 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a77:	be 00 08 00 00       	mov    $0x800,%esi
    3a7c:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a7e:	49 89 84 24 40 06 00 00 	mov    %rax,0x640(%r12)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a86:	e8 05 eb ff ff       	call   2590 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a8b:	be 08 00 00 00       	mov    $0x8,%esi
    3a90:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a95:	41 89 84 24 48 06 00 00 	mov    %eax,0x648(%r12)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a9d:	e8 9e e9 ff ff       	call   2440 <calloc@plt>
    3aa2:	ba 07 00 00 00       	mov    $0x7,%edx
    3aa7:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3aac:	41 c7 84 24 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r12)
      my_thread_data[n] = &thread_data[n]; 
    3ab8:	4c 89 20             	mov    %r12,(%rax)
    3abb:	48 8d 35 d2 49 00 00 	lea    0x49d2(%rip),%rsi        # 8494 <_IO_stdin_used+0x494>
    thread_data[x].threads = my_thread_data;
    3ac2:	49 89 84 24 00 06 00 00 	mov    %rax,0x600(%r12)
      my_thread_data[n] = &thread_data[n]; 
    3aca:	4c 89 70 08          	mov    %r14,0x8(%rax)
    3ace:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3ad0:	41 c7 84 24 ec 05 00 00 07 00 00 00 	movl   $0x7,0x5ec(%r12)
    3adc:	e8 2f ea ff ff       	call   2510 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3ae1:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
    3ae5:	4c 89 f9             	mov    %r15,%rcx
    3ae8:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3aec:	48 8d 15 dd 1f 00 00 	lea    0x1fdd(%rip),%rdx        # 5ad0 <io_thread>
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3af3:	41 bf 08 00 00 00    	mov    $0x8,%r15d
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3af9:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3b00:	e8 2b ea ff ff       	call   2530 <pthread_create@plt>
    3b05:	ba 08 00 00 00       	mov    $0x8,%edx
    3b0a:	48 8d 35 9a 49 00 00 	lea    0x499a(%rip),%rsi        # 84ab <_IO_stdin_used+0x4ab>
    3b11:	31 c0                	xor    %eax,%eax
    3b13:	bf 01 00 00 00       	mov    $0x1,%edi
    3b18:	e8 f3 e9 ff ff       	call   2510 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b1d:	48 8d 43 40          	lea    0x40(%rbx),%rax
    3b21:	4c 8b 65 a0          	mov    -0x60(%rbp),%r12
    3b25:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    3b29:	48 8b 45 a8          	mov    -0x58(%rbp),%rax
    3b2d:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    3b33:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    3b37:	44 89 fa             	mov    %r15d,%edx
    3b3a:	48 8d 35 80 49 00 00 	lea    0x4980(%rip),%rsi        # 84c1 <_IO_stdin_used+0x4c1>
    3b41:	bf 01 00 00 00       	mov    $0x1,%edi
    3b46:	31 c0                	xor    %eax,%eax
    3b48:	e8 c3 e9 ff ff       	call   2510 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3b4d:	be 08 00 00 00       	mov    $0x8,%esi
    3b52:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3b57:	48 8b 05 7a 51 00 00 	mov    0x517a(%rip),%rax        # 8cd8 <_IO_stdin_used+0xcd8>
    thread_data[x].type = EXTERNAL;
    3b5e:	41 c7 44 24 0c 03 00 00 00 	movl   $0x3,0xc(%r12)
    thread_data[x].task_count = 0;
    3b67:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3b6c:	e8 cf e8 ff ff       	call   2440 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3b71:	48 8b bd 10 ff ff ff 	mov    -0xf0(%rbp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3b78:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3b7d:	41 c7 84 24 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3b89:	49 89 44 24 50       	mov    %rax,0x50(%r12)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3b8e:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3b91:	bf 02 00 00 00       	mov    $0x2,%edi
    3b96:	e8 a5 e8 ff ff       	call   2440 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3b9b:	48 8b 75 88          	mov    -0x78(%rbp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b9f:	48 8b 7d b8          	mov    -0x48(%rbp),%rdi
    3ba3:	4c 89 e1             	mov    %r12,%rcx
    thread_data[x].threads = my_thread_data;
    3ba6:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3bab:	48 8d 15 0e 0a 00 00 	lea    0xa0e(%rip),%rdx        # 45c0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3bb2:	49 81 c4 d8 00 00 00 	add    $0xd8,%r12
      my_thread_data[n] = &thread_data[n]; 
    3bb9:	48 89 30             	mov    %rsi,(%rax)
    thread_data[x].thread_count = thread_count;
    3bbc:	48 8b 35 f5 50 00 00 	mov    0x50f5(%rip),%rsi        # 8cb8 <_IO_stdin_used+0xcb8>
    thread_data[x].thread_index = x;
    3bc3:	45 89 bc 24 2c ff ff ff 	mov    %r15d,-0xd4(%r12)
    thread_data[x].thread_count = thread_count;
    3bcb:	49 89 b4 24 50 ff ff ff 	mov    %rsi,-0xb0(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3bd3:	48 8b 75 b0          	mov    -0x50(%rbp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3bd7:	4c 89 70 08          	mov    %r14,0x8(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3bdb:	e8 50 e9 ff ff       	call   2530 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3be0:	48 83 85 10 ff ff ff 10 	addq   $0x10,-0xf0(%rbp)
    3be8:	48 83 45 b8 08       	addq   $0x8,-0x48(%rbp)
    3bed:	48 83 45 b0 38       	addq   $0x38,-0x50(%rbp)
    3bf2:	41 83 ff 08          	cmp    $0x8,%r15d
    3bf6:	75 3d                	jne    3c35 <main+0x1545>
    3bf8:	41 bf 09 00 00 00    	mov    $0x9,%r15d
    3bfe:	e9 34 ff ff ff       	jmp    3b37 <main+0x1447>
        my_thread_data[1] = &thread_data[other]; 
    3c03:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
    3c07:	4b 8d 04 7f          	lea    (%r15,%r15,2),%rax
        other = (x + 1) % total_threads;
    3c0b:	44 89 f9             	mov    %r15d,%ecx
        my_thread_data[1] = &thread_data[other]; 
    3c0e:	45 31 c0             	xor    %r8d,%r8d
    3c11:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3c15:	48 89 9d 70 ff ff ff 	mov    %rbx,-0x90(%rbp)
    3c1c:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        my_thread_data[0] = &thread_data[x]; 
    3c20:	4c 89 c8             	mov    %r9,%rax
    3c23:	e9 e7 ee ff ff       	jmp    2b0f <main+0x41f>
            CPU_SET(j, sendercpu);
    3c28:	49 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%r13)
          for (int j = 0 ; j < cores ; j++) {
    3c30:	e9 75 ef ff ff       	jmp    2baa <main+0x4ba>
    3c35:	48 8b 45 88          	mov    -0x78(%rbp),%rax
    3c39:	4c 8d 25 9e 48 00 00 	lea    0x489e(%rip),%r12        # 84de <_IO_stdin_used+0x4de>
    3c40:	4c 8d 78 04          	lea    0x4(%rax),%r15
    3c44:	4c 8d b0 74 08 00 00 	lea    0x874(%rax),%r14
    3c4b:	41 8b 4f 04          	mov    0x4(%r15),%ecx
    3c4f:	41 8b 17             	mov    (%r15),%edx
    3c52:	4c 89 e6             	mov    %r12,%rsi
    3c55:	bf 01 00 00 00       	mov    $0x1,%edi
    3c5a:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3c5c:	49 81 c7 d8 00 00 00 	add    $0xd8,%r15
    3c63:	e8 a8 e8 ff ff       	call   2510 <__printf_chk@plt>
    3c68:	4d 39 fe             	cmp    %r15,%r14
    3c6b:	75 de                	jne    3c4b <main+0x155b>
    3c6d:	48 8d 3d 7d 48 00 00 	lea    0x487d(%rip),%rdi        # 84f1 <_IO_stdin_used+0x4f1>
    3c74:	45 31 ff             	xor    %r15d,%r15d
    3c77:	4c 8d 75 c0          	lea    -0x40(%rbp),%r14
    3c7b:	e8 f0 e6 ff ff       	call   2370 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3c80:	4c 8d 25 88 48 00 00 	lea    0x4888(%rip),%r12        # 850f <_IO_stdin_used+0x50f>
    void * result; 
    pthread_join(thread[x], &result);
    3c87:	4a 8b 3c fb          	mov    (%rbx,%r15,8),%rdi
    3c8b:	4c 89 f6             	mov    %r14,%rsi
    3c8e:	e8 3d e9 ff ff       	call   25d0 <pthread_join@plt>
    3c93:	44 89 fa             	mov    %r15d,%edx
    3c96:	4c 89 e6             	mov    %r12,%rsi
    3c99:	bf 01 00 00 00       	mov    $0x1,%edi
    3c9e:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3ca0:	49 83 c7 01          	add    $0x1,%r15
    3ca4:	e8 67 e8 ff ff       	call   2510 <__printf_chk@plt>
    3ca9:	49 83 ff 0a          	cmp    $0xa,%r15
    3cad:	75 d8                	jne    3c87 <main+0x1597>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3caf:	be 08 00 00 00       	mov    $0x8,%esi
    3cb4:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3cb9:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3cbb:	e8 80 e7 ff ff       	call   2440 <calloc@plt>
    3cc0:	48 8b 55 88          	mov    -0x78(%rbp),%rdx
    3cc4:	49 89 c4             	mov    %rax,%r12
    3cc7:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3cc9:	49 89 d1             	mov    %rdx,%r9
    3ccc:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3ccf:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3cd3:	45 85 d2             	test   %r10d,%r10d
    3cd6:	0f 8e 99 00 00 00    	jle    3d75 <main+0x1685>
    3cdc:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3ce0:	4d 63 c2             	movslq %r10d,%r8
    3ce3:	48 63 cb             	movslq %ebx,%rcx
    3ce6:	49 c1 e0 09          	shl    $0x9,%r8
    3cea:	49 8d 34 cc          	lea    (%r12,%rcx,8),%rsi
    3cee:	49 01 f8             	add    %rdi,%r8
    3cf1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3cf8:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3cff:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3d06:	48 83 c6 60          	add    $0x60,%rsi
    3d0a:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    3d0f:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    3d14:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3d1c:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3d20:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3d28:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3d2c:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    3d30:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    3d38:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3d3f:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    3d43:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3d47:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3d4e:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3d55:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3d59:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3d5d:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3d61:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3d65:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3d69:	4c 39 c7             	cmp    %r8,%rdi
    3d6c:	75 8a                	jne    3cf8 <main+0x1608>
    3d6e:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3d72:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3d75:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    3d7c:	45 85 db             	test   %r11d,%r11d
    3d7f:	75 08                	jne    3d89 <main+0x1699>
    3d81:	45 89 eb             	mov    %r13d,%r11d
    3d84:	e9 46 ff ff ff       	jmp    3ccf <main+0x15df>
  for (int k = 0 ; k < group_count ; k++) {
    3d89:	83 c0 02             	add    $0x2,%eax
    3d8c:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3d93:	83 f8 06             	cmp    $0x6,%eax
    3d96:	0f 85 2d ff ff ff    	jne    3cc9 <main+0x15d9>
    3d9c:	48 8d 3d 80 47 00 00 	lea    0x4780(%rip),%rdi        # 8523 <_IO_stdin_used+0x523>
    3da3:	e8 c8 e5 ff ff       	call   2370 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3da8:	48 8d 35 50 46 00 00 	lea    0x4650(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3daf:	48 8d 3d 85 47 00 00 	lea    0x4785(%rip),%rdi        # 853b <_IO_stdin_used+0x53b>
    3db6:	e8 95 e7 ff ff       	call   2550 <fopen@plt>
    3dbb:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas2_size; x++) {
    3dbe:	85 db                	test   %ebx,%ebx
    3dc0:	7e 78                	jle    3e3a <main+0x174a>
    3dc2:	48 63 db             	movslq %ebx,%rbx
    3dc5:	4c 8d 35 12 46 00 00 	lea    0x4612(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    3dcc:	4c 8d 2d 4f 46 00 00 	lea    0x464f(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    3dd3:	49 8d 04 dc          	lea    (%r12,%rbx,8),%rax
    3dd7:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    char * c = calloc(250, sizeof(char));
    3ddb:	be 01 00 00 00       	mov    $0x1,%esi
    3de0:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3de5:	49 83 c4 08          	add    $0x8,%r12
    char * c = calloc(250, sizeof(char));
    3de9:	e8 52 e6 ff ff       	call   2440 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3dee:	4c 89 f1             	mov    %r14,%rcx
    3df1:	ba fa 00 00 00       	mov    $0xfa,%edx
    3df6:	be 01 00 00 00       	mov    $0x1,%esi
    3dfb:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3dfe:	49 8b 44 24 f8       	mov    -0x8(%r12),%rax
    3e03:	48 89 df             	mov    %rbx,%rdi
    3e06:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3e0d:	31 c0                	xor    %eax,%eax
    3e0f:	e8 0c e8 ff ff       	call   2620 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3e14:	48 89 da             	mov    %rbx,%rdx
    3e17:	4c 89 ee             	mov    %r13,%rsi
    3e1a:	bf 01 00 00 00       	mov    $0x1,%edi
    3e1f:	31 c0                	xor    %eax,%eax
    3e21:	e8 ea e6 ff ff       	call   2510 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3e26:	4c 89 fe             	mov    %r15,%rsi
    3e29:	48 89 df             	mov    %rbx,%rdi
    3e2c:	e8 cf e5 ff ff       	call   2400 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3e31:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    3e35:	49 39 c4             	cmp    %rax,%r12
    3e38:	75 a1                	jne    3ddb <main+0x16eb>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    3e3a:	4c 89 ff             	mov    %r15,%rdi
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    3e3d:	45 31 f6             	xor    %r14d,%r14d
  long sents = 0;
    3e40:	45 31 ed             	xor    %r13d,%r13d
  fclose(m2);
    3e43:	e8 58 e5 ff ff       	call   23a0 <fclose@plt>
  long sends = 0;
    3e48:	48 c7 45 98 00 00 00 00 	movq   $0x0,-0x68(%rbp)
  fclose(m2);
    3e50:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  long ingests = 0;
    3e55:	48 c7 45 a0 00 00 00 00 	movq   $0x0,-0x60(%rbp)
  long total = 0;
    3e5d:	48 c7 45 90 00 00 00 00 	movq   $0x0,-0x70(%rbp)
  int datas2_size = 0; 
    3e65:	48 8b bd 28 ff ff ff 	mov    -0xd8(%rbp),%rdi
    3e6c:	8d 48 02             	lea    0x2(%rax),%ecx
    3e6f:	89 45 b0             	mov    %eax,-0x50(%rbp)
    3e72:	89 8d 78 ff ff ff    	mov    %ecx,-0x88(%rbp)
    3e78:	4c 8b bd 18 ff ff ff 	mov    -0xe8(%rbp),%r15
    3e7f:	48 89 7d 80          	mov    %rdi,-0x80(%rbp)
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
    3e83:	8b 7d b0             	mov    -0x50(%rbp),%edi
    3e86:	89 f8                	mov    %edi,%eax
    3e88:	83 c7 01             	add    $0x1,%edi
      long v = 0;
      
      int other = -1;
      int me = x;
      if (x % 2 == 1) {
        other = abs(x - 1) % total_threads;
    3e8b:	8d 50 02             	lea    0x2(%rax),%edx
    3e8e:	89 7d b0             	mov    %edi,-0x50(%rbp)
    3e91:	83 e7 01             	and    $0x1,%edi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3e94:	bf 0a 00 00 00       	mov    $0xa,%edi
    3e99:	0f 44 c2             	cmove  %edx,%eax
    3e9c:	48 63 d8             	movslq %eax,%rbx
    3e9f:	e8 ac e4 ff ff       	call   2350 <putchar@plt>
    3ea4:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    3ea8:	bf 01 00 00 00       	mov    $0x1,%edi
    3ead:	48 8d 35 90 46 00 00 	lea    0x4690(%rip),%rsi        # 8544 <_IO_stdin_used+0x544>
    3eb4:	48 8b 10             	mov    (%rax),%rdx
    3eb7:	31 c0                	xor    %eax,%eax
    3eb9:	e8 52 e6 ff ff       	call   2510 <__printf_chk@plt>
        other = (x + 1) % total_threads;
      }
      printf("\n");
      printf("Total Protected %ld\n", protected_state[me].protected);

      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3ebe:	41 8b 57 40          	mov    0x40(%r15),%edx
    3ec2:	85 d2                	test   %edx,%edx
    3ec4:	0f 8e cd 04 00 00    	jle    4397 <main+0x1ca7>
    3eca:	48 63 ca             	movslq %edx,%rcx
    3ecd:	49 8b 47 38          	mov    0x38(%r15),%rax
      long v = 0;
    3ed1:	31 d2                	xor    %edx,%edx
    3ed3:	48 c1 e1 09          	shl    $0x9,%rcx
    3ed7:	48 01 c1             	add    %rax,%rcx
    3eda:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3ee0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3ee7:	48 05 00 02 00 00    	add    $0x200,%rax
    3eed:	48 39 c8             	cmp    %rcx,%rax
    3ef0:	75 ee                	jne    3ee0 <main+0x17f0>
      }
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3ef2:	48 8b 7d 88          	mov    -0x78(%rbp),%rdi
    3ef6:	48 8d 04 5b          	lea    (%rbx,%rbx,2),%rax
    3efa:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3efe:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3f02:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3f06:	85 c9                	test   %ecx,%ecx
    3f08:	7e 20                	jle    3f2a <main+0x183a>
    3f0a:	48 8b 40 38          	mov    0x38(%rax),%rax
    3f0e:	48 c1 e1 09          	shl    $0x9,%rcx
    3f12:	48 01 c1             	add    %rax,%rcx
    3f15:	0f 1f 00             	nopl   (%rax)
        v += thread_data[other].tasks[n].v;
    3f18:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3f1f:	48 05 00 02 00 00    	add    $0x200,%rax
    3f25:	48 39 c8             	cmp    %rcx,%rax
    3f28:	75 ee                	jne    3f18 <main+0x1828>
    3f2a:	48 8d 35 28 46 00 00 	lea    0x4628(%rip),%rsi        # 8559 <_IO_stdin_used+0x559>
    3f31:	bf 01 00 00 00       	mov    $0x1,%edi
    3f36:	31 c0                	xor    %eax,%eax
    3f38:	e8 d3 e5 ff ff       	call   2510 <__printf_chk@plt>
      }
      printf("Total V %ld\n", v);
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3f3d:	48 8b 45 80          	mov    -0x80(%rbp),%rax
    3f41:	bf 01 00 00 00       	mov    $0x1,%edi
    3f46:	48 8d 35 e3 48 00 00 	lea    0x48e3(%rip),%rsi        # 8830 <_IO_stdin_used+0x830>
    3f4d:	48 8b 08             	mov    (%rax),%rcx
    3f50:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3f5a:	48 f7 e9             	imul   %rcx
    3f5d:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3f61:	31 c0                	xor    %eax,%eax
    3f63:	48 d1 fa             	sar    %rdx
    3f66:	48 29 ca             	sub    %rcx,%rdx
    3f69:	e8 a2 e5 ff ff       	call   2510 <__printf_chk@plt>
    3f6e:	bf 0a 00 00 00       	mov    $0xa,%edi
    3f73:	e8 d8 e3 ff ff       	call   2350 <putchar@plt>
      printf("\n");
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3f78:	45 8b 57 40          	mov    0x40(%r15),%r10d
    3f7c:	45 85 d2             	test   %r10d,%r10d
    3f7f:	0f 8e f3 00 00 00    	jle    4078 <main+0x1988>
        total += thread_data[x].tasks[n].n;
    3f85:	49 8b 4f 38          	mov    0x38(%r15),%rcx
    3f89:	4c 8b 45 90          	mov    -0x70(%rbp),%r8
    3f8d:	31 d2                	xor    %edx,%edx
    3f8f:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
    3f93:	48 8b 7d 98          	mov    -0x68(%rbp),%rdi
    3f97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3fa0:	49 89 d4             	mov    %rdx,%r12
    3fa3:	89 55 b8             	mov    %edx,-0x48(%rbp)
        ingests += thread_data[x].tasks[n].ingest_count;
        sends += thread_data[x].tasks[n].sends;
    3fa6:	31 db                	xor    %ebx,%ebx
    3fa8:	49 c1 e4 09          	shl    $0x9,%r12
    3fac:	48 89 55 90          	mov    %rdx,-0x70(%rbp)
        total += thread_data[x].tasks[n].n;
    3fb0:	4c 01 e1             	add    %r12,%rcx
        sends += thread_data[x].tasks[n].sends;
    3fb3:	4c 89 e0             	mov    %r12,%rax
    3fb6:	4d 89 ec             	mov    %r13,%r12
    3fb9:	4d 89 f5             	mov    %r14,%r13
        total += thread_data[x].tasks[n].n;
    3fbc:	4c 03 81 08 01 00 00 	add    0x108(%rcx),%r8
        ingests += thread_data[x].tasks[n].ingest_count;
    3fc3:	48 03 b1 68 01 00 00 	add    0x168(%rcx),%rsi
        sends += thread_data[x].tasks[n].sends;
    3fca:	49 89 c6             	mov    %rax,%r14
    3fcd:	48 03 b9 78 01 00 00 	add    0x178(%rcx),%rdi
    3fd4:	4c 89 45 a8          	mov    %r8,-0x58(%rbp)
    3fd8:	48 89 75 a0          	mov    %rsi,-0x60(%rbp)
    3fdc:	48 89 7d 98          	mov    %rdi,-0x68(%rbp)
    3fe0:	8b 4d b8             	mov    -0x48(%rbp),%ecx
    3fe3:	8b 55 b0             	mov    -0x50(%rbp),%edx
    3fe6:	41 89 d8             	mov    %ebx,%r8d
    3fe9:	48 8d 35 76 45 00 00 	lea    0x4576(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    3ff0:	bf 01 00 00 00       	mov    $0x1,%edi
    3ff5:	31 c0                	xor    %eax,%eax
    3ff7:	e8 14 e5 ff ff       	call   2510 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          printf("combo %d %d %d\n", x, n, kk);
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3ffc:	49 8b 4f 38          	mov    0x38(%r15),%rcx
    4000:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    4008:	48 29 d8             	sub    %rbx,%rax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    400b:	48 83 c3 01          	add    $0x1,%rbx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    400f:	4a 8b 94 31 70 01 00 00 	mov    0x170(%rcx,%r14,1),%rdx
    4017:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    401b:	48 8b 10             	mov    (%rax),%rdx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    401e:	48 8b 40 08          	mov    0x8(%rax),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4022:	4c 8b 8a 08 03 00 00 	mov    0x308(%rdx),%r9

          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    4029:	4c 8b 92 10 03 00 00 	mov    0x310(%rdx),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4030:	4d 01 e1             	add    %r12,%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    4033:	4d 01 ea             	add    %r13,%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4036:	4c 03 88 08 03 00 00 	add    0x308(%rax),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    403d:	4c 03 90 10 03 00 00 	add    0x310(%rax),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4044:	4d 89 cc             	mov    %r9,%r12
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4047:	4d 89 d5             	mov    %r10,%r13
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    404a:	48 83 fb 06          	cmp    $0x6,%rbx
    404e:	75 90                	jne    3fe0 <main+0x18f0>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    4050:	48 8b 55 90          	mov    -0x70(%rbp),%rdx
    4054:	4c 8b 45 a8          	mov    -0x58(%rbp),%r8
    4058:	4d 89 d6             	mov    %r10,%r14
    405b:	4d 89 cd             	mov    %r9,%r13
    405e:	48 8b 75 a0          	mov    -0x60(%rbp),%rsi
    4062:	48 8b 7d 98          	mov    -0x68(%rbp),%rdi
    4066:	48 83 c2 01          	add    $0x1,%rdx
    406a:	41 39 57 40          	cmp    %edx,0x40(%r15)
    406e:	0f 8f 2c ff ff ff    	jg     3fa0 <main+0x18b0>
    4074:	4c 89 45 90          	mov    %r8,-0x70(%rbp)
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        // printf("elapsed %ld seconds (%ld ms)\n", seconds, seconds2 / 1000000);
        // printf("%ld iterations\n", thread_data[x].iteration_count);
      }
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    4078:	45 31 e4             	xor    %r12d,%r12d
    407b:	49 83 bf a0 00 00 00 00 	cmpq   $0x0,0xa0(%r15)
    4083:	48 8d 1d c6 47 00 00 	lea    0x47c6(%rip),%rbx        # 8850 <_IO_stdin_used+0x850>
    408a:	7e 63                	jle    40ef <main+0x19ff>
    408c:	0f 1f 40 00          	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4090:	49 8b 87 90 00 00 00 	mov    0x90(%r15),%rax
    4097:	4b 8d 14 a4          	lea    (%r12,%r12,4),%rdx
    409b:	48 83 ec 08          	sub    $0x8,%rsp
    409f:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    40a4:	49 83 c4 01          	add    $0x1,%r12
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    40a8:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    40ac:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    40b6:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    40ba:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    40be:	48 f7 e6             	mul    %rsi
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    40c1:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    40c5:	4c 2b 01             	sub    (%rcx),%r8
    40c8:	31 c0                	xor    %eax,%eax
    40ca:	8b 49 20             	mov    0x20(%rcx),%ecx
    40cd:	56                   	push   %rsi
    40ce:	48 89 de             	mov    %rbx,%rsi
    40d1:	48 c1 ea 12          	shr    $0x12,%rdx
    40d5:	49 89 d1             	mov    %rdx,%r9
    40d8:	ba 02 00 00 00       	mov    $0x2,%edx
    40dd:	e8 2e e4 ff ff       	call   2510 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    40e2:	41 58                	pop    %r8
    40e4:	41 59                	pop    %r9
    40e6:	4d 39 a7 a0 00 00 00 	cmp    %r12,0xa0(%r15)
    40ed:	7f a1                	jg     4090 <main+0x19a0>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    40ef:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    40f6:	85 c9                	test   %ecx,%ecx
    40f8:	0f 8e 09 01 00 00    	jle    4207 <main+0x1b17>
    40fe:	4c 89 ad 70 ff ff ff 	mov    %r13,-0x90(%rbp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4105:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    4109:	31 db                	xor    %ebx,%ebx
    410b:	4c 89 b5 68 ff ff ff 	mov    %r14,-0x98(%rbp)
    4112:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4118:	49 8b 04 d9          	mov    (%r9,%rbx,8),%rax
    411c:	41 89 dd             	mov    %ebx,%r13d
    411f:	4c 8d 34 dd 00 00 00 00 	lea    0x0(,%rbx,8),%r14
    4127:	8b 30                	mov    (%rax),%esi
    4129:	85 f6                	test   %esi,%esi
    412b:	0f 8e bc 00 00 00    	jle    41ed <main+0x1afd>
    4131:	48 89 5d a8          	mov    %rbx,-0x58(%rbp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    4135:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4139:	31 ff                	xor    %edi,%edi
    413b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4140:	48 89 fb             	mov    %rdi,%rbx
    4143:	45 31 e4             	xor    %r12d,%r12d
    4146:	48 c1 e3 08          	shl    $0x8,%rbx
    414a:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    414e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4154:	85 d2                	test   %edx,%edx
    4156:	7e 7e                	jle    41d6 <main+0x1ae6>
    4158:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)
    415c:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4160:	4c 89 e1             	mov    %r12,%rcx
    4163:	48 83 ec 08          	sub    $0x8,%rsp
    4167:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    416c:	49 83 c4 01          	add    $0x1,%r12
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4170:	48 c1 e1 05          	shl    $0x5,%rcx
    4174:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    417b:	48 b8 db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rax
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    4185:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    4189:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    418d:	48 f7 e6             	mul    %rsi
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4190:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    4194:	4c 2b 01             	sub    (%rcx),%r8
    4197:	56                   	push   %rsi
    4198:	44 89 e9             	mov    %r13d,%ecx
    419b:	48 8d 35 fe 46 00 00 	lea    0x46fe(%rip),%rsi        # 88a0 <_IO_stdin_used+0x8a0>
    41a2:	31 c0                	xor    %eax,%eax
    41a4:	48 c1 ea 12          	shr    $0x12,%rdx
    41a8:	49 89 d1             	mov    %rdx,%r9
    41ab:	ba 02 00 00 00       	mov    $0x2,%edx
    41b0:	e8 5b e3 ff ff       	call   2510 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    41b5:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    41b9:	5e                   	pop    %rsi
    41ba:	5f                   	pop    %rdi
    41bb:	4b 8b 14 31          	mov    (%r9,%r14,1),%rdx
    41bf:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    41c3:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    41c7:	44 39 a0 94 00 00 00 	cmp    %r12d,0x94(%rax)
    41ce:	7f 90                	jg     4160 <main+0x1a70>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    41d0:	48 8b 7d b8          	mov    -0x48(%rbp),%rdi
    41d4:	8b 32                	mov    (%rdx),%esi
    41d6:	48 83 c7 01          	add    $0x1,%rdi
    41da:	39 fe                	cmp    %edi,%esi
    41dc:	0f 8f 5e ff ff ff    	jg     4140 <main+0x1a50>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    41e2:	48 8b 5d a8          	mov    -0x58(%rbp),%rbx
    41e6:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    41ed:	48 83 c3 01          	add    $0x1,%rbx
    41f1:	39 d9                	cmp    %ebx,%ecx
    41f3:	0f 8f 1f ff ff ff    	jg     4118 <main+0x1a28>
    41f9:	4c 8b ad 70 ff ff ff 	mov    -0x90(%rbp),%r13
    4200:	4c 8b b5 68 ff ff ff 	mov    -0x98(%rbp),%r14
    for (int d = 0 ; d < threads_per_group ; d++) {
    4207:	48 83 45 80 18       	addq   $0x18,-0x80(%rbp)
    420c:	8b 7d b0             	mov    -0x50(%rbp),%edi
    420f:	49 81 c7 d8 00 00 00 	add    $0xd8,%r15
    4216:	39 bd 78 ff ff ff    	cmp    %edi,-0x88(%rbp)
    421c:	0f 85 61 fc ff ff    	jne    3e83 <main+0x1793>
  for (int k = 0 ; k < group_count ; k++) {
    4222:	8b 8d 78 ff ff ff    	mov    -0x88(%rbp),%ecx
    4228:	48 83 85 28 ff ff ff 30 	addq   $0x30,-0xd8(%rbp)
    4230:	48 81 85 18 ff ff ff b0 01 00 00 	addq   $0x1b0,-0xe8(%rbp)
    423b:	83 f9 05             	cmp    $0x5,%ecx
    423e:	74 07                	je     4247 <main+0x1b57>
    4240:	89 c8                	mov    %ecx,%eax
    4242:	e9 1e fc ff ff       	jmp    3e65 <main+0x1775>
    4247:	4c 8b 7d 90          	mov    -0x70(%rbp),%r15
    424b:	48 8d 35 24 43 00 00 	lea    0x4324(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    4252:	bf 01 00 00 00       	mov    $0x1,%edi
    4257:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    4259:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4263:	4c 89 fa             	mov    %r15,%rdx
    4266:	e8 a5 e2 ff ff       	call   2510 <__printf_chk@plt>
    426b:	bf 0a 00 00 00       	mov    $0xa,%edi
    4270:	e8 db e0 ff ff       	call   2350 <putchar@plt>
    4275:	48 8b bd 20 ff ff ff 	mov    -0xe0(%rbp),%rdi
    427c:	48 8d 35 75 46 00 00 	lea    0x4675(%rip),%rsi        # 88f8 <_IO_stdin_used+0x8f8>
    4283:	31 c0                	xor    %eax,%eax
    4285:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    4289:	bf 01 00 00 00       	mov    $0x1,%edi
    428e:	e8 7d e2 ff ff       	call   2510 <__printf_chk@plt>
    4293:	48 8b 45 a0          	mov    -0x60(%rbp),%rax
    4297:	48 8b 7d a0          	mov    -0x60(%rbp),%rdi
    429b:	48 8d 35 7e 46 00 00 	lea    0x467e(%rip),%rsi        # 8920 <_IO_stdin_used+0x920>
    42a2:	48 f7 eb             	imul   %rbx
    42a5:	48 c1 ff 3f          	sar    $0x3f,%rdi
    42a9:	31 c0                	xor    %eax,%eax
    42ab:	48 d1 fa             	sar    %rdx
    42ae:	48 29 fa             	sub    %rdi,%rdx
    42b1:	bf 01 00 00 00       	mov    $0x1,%edi
    42b6:	e8 55 e2 ff ff       	call   2510 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    42bb:	48 8b 45 98          	mov    -0x68(%rbp),%rax
    42bf:	48 8b 7d 98          	mov    -0x68(%rbp),%rdi
    42c3:	48 8d 35 86 46 00 00 	lea    0x4686(%rip),%rsi        # 8950 <_IO_stdin_used+0x950>
    42ca:	48 f7 eb             	imul   %rbx
    42cd:	48 c1 ff 3f          	sar    $0x3f,%rdi
    42d1:	31 c0                	xor    %eax,%eax
    42d3:	48 d1 fa             	sar    %rdx
    42d6:	48 29 fa             	sub    %rdi,%rdx
    42d9:	bf 01 00 00 00       	mov    $0x1,%edi
    42de:	e8 2d e2 ff ff       	call   2510 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    42e3:	4c 89 f8             	mov    %r15,%rax
    42e6:	4c 89 ff             	mov    %r15,%rdi
    42e9:	48 8d 35 90 46 00 00 	lea    0x4690(%rip),%rsi        # 8980 <_IO_stdin_used+0x980>
    42f0:	48 f7 eb             	imul   %rbx
    42f3:	48 c1 ff 3f          	sar    $0x3f,%rdi
    42f7:	31 c0                	xor    %eax,%eax
    42f9:	48 d1 fa             	sar    %rdx
    42fc:	48 29 fa             	sub    %rdi,%rdx
    42ff:	bf 01 00 00 00       	mov    $0x1,%edi
    4304:	e8 07 e2 ff ff       	call   2510 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    4309:	4c 89 e8             	mov    %r13,%rax
    430c:	bf 01 00 00 00       	mov    $0x1,%edi
    4311:	48 8d 35 72 42 00 00 	lea    0x4272(%rip),%rsi        # 858a <_IO_stdin_used+0x58a>
    4318:	48 f7 eb             	imul   %rbx
    431b:	4c 89 e8             	mov    %r13,%rax
    431e:	48 c1 f8 3f          	sar    $0x3f,%rax
    4322:	48 d1 fa             	sar    %rdx
    4325:	48 29 c2             	sub    %rax,%rdx
    4328:	31 c0                	xor    %eax,%eax
    432a:	49 89 d4             	mov    %rdx,%r12
    432d:	e8 de e1 ff ff       	call   2510 <__printf_chk@plt>
  printf("Total sents %ld\n", sentdur);
  long recdur = received / DURATION;
    4332:	4c 89 f0             	mov    %r14,%rax
    4335:	bf 01 00 00 00       	mov    $0x1,%edi
    433a:	48 8d 35 5a 42 00 00 	lea    0x425a(%rip),%rsi        # 859b <_IO_stdin_used+0x59b>
    4341:	48 f7 eb             	imul   %rbx
    4344:	4c 89 f0             	mov    %r14,%rax
    4347:	48 c1 f8 3f          	sar    $0x3f,%rax
    434b:	48 89 d3             	mov    %rdx,%rbx
    434e:	48 d1 fb             	sar    %rbx
    4351:	48 29 c3             	sub    %rax,%rbx
    4354:	31 c0                	xor    %eax,%eax
    4356:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    4359:	4c 29 e3             	sub    %r12,%rbx
    435c:	e8 af e1 ff ff       	call   2510 <__printf_chk@plt>
    4361:	31 c0                	xor    %eax,%eax
    4363:	48 89 da             	mov    %rbx,%rdx
    4366:	bf 01 00 00 00       	mov    $0x1,%edi
    436b:	48 8d 35 3d 42 00 00 	lea    0x423d(%rip),%rsi        # 85af <_IO_stdin_used+0x5af>
    4372:	e8 99 e1 ff ff       	call   2510 <__printf_chk@plt>
  return 0;

}
    4377:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    437b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4384:	75 22                	jne    43a8 <main+0x1cb8>
    4386:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    438a:	31 c0                	xor    %eax,%eax
    438c:	5b                   	pop    %rbx
    438d:	41 5c                	pop    %r12
    438f:	41 5d                	pop    %r13
    4391:	41 5e                	pop    %r14
    4393:	41 5f                	pop    %r15
    4395:	5d                   	pop    %rbp
    4396:	c3                   	ret
      long v = 0;
    4397:	31 d2                	xor    %edx,%edx
    4399:	e9 54 fb ff ff       	jmp    3ef2 <main+0x1802>
            exit(1);
    439e:	bf 01 00 00 00       	mov    $0x1,%edi
    43a3:	e8 d8 e1 ff ff       	call   2580 <exit@plt>
}
    43a8:	e8 13 e0 ff ff       	call   23c0 <__stack_chk_fail@plt>
    43ad:	0f 1f 00             	nopl   (%rax)

00000000000043b0 <_start>:
    43b0:	f3 0f 1e fa          	endbr64
    43b4:	31 ed                	xor    %ebp,%ebp
    43b6:	49 89 d1             	mov    %rdx,%r9
    43b9:	5e                   	pop    %rsi
    43ba:	48 89 e2             	mov    %rsp,%rdx
    43bd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    43c1:	50                   	push   %rax
    43c2:	54                   	push   %rsp
    43c3:	45 31 c0             	xor    %r8d,%r8d
    43c6:	31 c9                	xor    %ecx,%ecx
    43c8:	48 8d 3d 21 e3 ff ff 	lea    -0x1cdf(%rip),%rdi        # 26f0 <main>
    43cf:	ff 15 fb 6b 00 00    	call   *0x6bfb(%rip)        # afd0 <__libc_start_main@GLIBC_2.34>
    43d5:	f4                   	hlt
    43d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000043e0 <__gmon_start__>:
    43e0:	f3 0f 1e fa          	endbr64
    43e4:	8b 05 3e 6c 00 00    	mov    0x6c3e(%rip),%eax        # b028 <called.0>
    43ea:	85 c0                	test   %eax,%eax
    43ec:	74 02                	je     43f0 <__gmon_start__+0x10>
    43ee:	c3                   	ret
    43ef:	90                   	nop
    43f0:	48 83 ec 08          	sub    $0x8,%rsp
    43f4:	48 8d 35 82 31 00 00 	lea    0x3182(%rip),%rsi        # 757d <etext>
    43fb:	48 8d 3d fe bb ff ff 	lea    -0x4402(%rip),%rdi        # 0 <__executable_start>
    4402:	c7 05 1c 6c 00 00 01 00 00 00 	movl   $0x1,0x6c1c(%rip)        # b028 <called.0>
    440c:	e8 4f e0 ff ff       	call   2460 <__monstartup@plt>
    4411:	48 8b 3d c8 6b 00 00 	mov    0x6bc8(%rip),%rdi        # afe0 <_mcleanup@GLIBC_2.2.5>
    4418:	48 83 c4 08          	add    $0x8,%rsp
    441c:	e9 1f 31 00 00       	jmp    7540 <atexit>
    4421:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    442b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004430 <_dl_relocate_static_pie>:
    4430:	f3 0f 1e fa          	endbr64
    4434:	c3                   	ret
    4435:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    443f:	90                   	nop

0000000000004440 <deregister_tm_clones>:
    4440:	48 8d 3d d9 6b 00 00 	lea    0x6bd9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4447:	48 8d 05 d2 6b 00 00 	lea    0x6bd2(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    444e:	48 39 f8             	cmp    %rdi,%rax
    4451:	74 15                	je     4468 <deregister_tm_clones+0x28>
    4453:	48 8b 05 7e 6b 00 00 	mov    0x6b7e(%rip),%rax        # afd8 <_ITM_deregisterTMCloneTable@Base>
    445a:	48 85 c0             	test   %rax,%rax
    445d:	74 09                	je     4468 <deregister_tm_clones+0x28>
    445f:	ff e0                	jmp    *%rax
    4461:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4468:	c3                   	ret
    4469:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004470 <register_tm_clones>:
    4470:	48 8d 3d a9 6b 00 00 	lea    0x6ba9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4477:	48 8d 35 a2 6b 00 00 	lea    0x6ba2(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    447e:	48 29 fe             	sub    %rdi,%rsi
    4481:	48 89 f0             	mov    %rsi,%rax
    4484:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4488:	48 c1 f8 03          	sar    $0x3,%rax
    448c:	48 01 c6             	add    %rax,%rsi
    448f:	48 d1 fe             	sar    %rsi
    4492:	74 14                	je     44a8 <register_tm_clones+0x38>
    4494:	48 8b 05 55 6b 00 00 	mov    0x6b55(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    449b:	48 85 c0             	test   %rax,%rax
    449e:	74 08                	je     44a8 <register_tm_clones+0x38>
    44a0:	ff e0                	jmp    *%rax
    44a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    44a8:	c3                   	ret
    44a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044b0 <__do_global_dtors_aux>:
    44b0:	f3 0f 1e fa          	endbr64
    44b4:	80 3d 71 6b 00 00 00 	cmpb   $0x0,0x6b71(%rip)        # b02c <completed.0>
    44bb:	75 2b                	jne    44e8 <__do_global_dtors_aux+0x38>
    44bd:	55                   	push   %rbp
    44be:	48 83 3d 32 6b 00 00 00 	cmpq   $0x0,0x6b32(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    44c6:	48 89 e5             	mov    %rsp,%rbp
    44c9:	74 0c                	je     44d7 <__do_global_dtors_aux+0x27>
    44cb:	48 8b 3d 36 6b 00 00 	mov    0x6b36(%rip),%rdi        # b008 <__dso_handle>
    44d2:	e8 59 de ff ff       	call   2330 <__cxa_finalize@plt>
    44d7:	e8 64 ff ff ff       	call   4440 <deregister_tm_clones>
    44dc:	c6 05 49 6b 00 00 01 	movb   $0x1,0x6b49(%rip)        # b02c <completed.0>
    44e3:	5d                   	pop    %rbp
    44e4:	c3                   	ret
    44e5:	0f 1f 00             	nopl   (%rax)
    44e8:	c3                   	ret
    44e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000044f0 <frame_dummy>:
    44f0:	f3 0f 1e fa          	endbr64
    44f4:	e9 77 ff ff ff       	jmp    4470 <register_tm_clones>
    44f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004500 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4500:	f3 0f 1e fa          	endbr64
    4504:	55                   	push   %rbp
    4505:	48 89 e5             	mov    %rsp,%rbp
    4508:	ff 15 da 6a 00 00    	call   *0x6ada(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  struct ProtectedState *protected = data->thread->protected_state;
    450e:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4515:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    4519:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4521:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    4525:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    4529:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4530:	48 85 c9             	test   %rcx,%rcx
    4533:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    453a:	48 0f 4f d6          	cmovg  %rsi,%rdx
    453e:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4542:	31 c0                	xor    %eax,%eax
    4544:	5d                   	pop    %rbp
    4545:	c3                   	ret
    4546:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004550 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4550:	f3 0f 1e fa          	endbr64
    4554:	55                   	push   %rbp
    4555:	48 89 e5             	mov    %rsp,%rbp
    4558:	ff 15 8a 6a 00 00    	call   *0x6a8a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    for (int x = 0 ; x < data->task_count ; x++) {
    455e:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    4565:	85 c9                	test   %ecx,%ecx
    4567:	7e 4d                	jle    45b6 <barriered_reset+0x66>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4569:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4570:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    4577:	48 c1 e1 09          	shl    $0x9,%rcx
    457b:	48 8b 50 18          	mov    0x18(%rax),%rdx
    457f:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    4583:	48 8b 70 38          	mov    0x38(%rax),%rsi
    4587:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4589:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    458d:	0f 1f 00             	nopl   (%rax)
    4590:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4598:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    45a0:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    45ab:	48 05 00 02 00 00    	add    $0x200,%rax
    45b1:	48 39 c1             	cmp    %rax,%rcx
    45b4:	75 da                	jne    4590 <barriered_reset+0x40>
  asm volatile ("sfence" ::: "memory");
    45b6:	0f ae f8             	sfence
}
    45b9:	31 c0                	xor    %eax,%eax
    45bb:	5d                   	pop    %rbp
    45bc:	c3                   	ret
    45bd:	0f 1f 00             	nopl   (%rax)

00000000000045c0 <external_thread>:
void * external_thread(void *arg) {
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	55                   	push   %rbp
    45c5:	48 89 e5             	mov    %rsp,%rbp
    45c8:	41 57                	push   %r15
    45ca:	41 56                	push   %r14
    45cc:	41 55                	push   %r13
    45ce:	41 54                	push   %r12
    45d0:	53                   	push   %rbx
    45d1:	48 83 ec 08          	sub    $0x8,%rsp
    45d5:	ff 15 0d 6a 00 00    	call   *0x6a0d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  while (data->running == 1) {
    45db:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
void * external_thread(void *arg) {
    45df:	49 89 fe             	mov    %rdi,%r14
  while (data->running == 1) {
    45e2:	75 6b                	jne    464f <external_thread+0x8f>
    for (int b = 0; b < data->buffers_count; b++) {
    45e4:	8b b7 bc 00 00 00    	mov    0xbc(%rdi),%esi
    45ea:	4c 8b 47 50          	mov    0x50(%rdi),%r8
    45ee:	66 90                	xchg   %ax,%ax
    45f0:	85 f6                	test   %esi,%esi
    45f2:	7e 6c                	jle    4660 <external_thread+0xa0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    45f4:	45 31 ed             	xor    %r13d,%r13d
    45f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4600:	4e 8d 3c ed 00 00 00 00 	lea    0x0(,%r13,8),%r15
    4608:	31 db                	xor    %ebx,%ebx
    460a:	4b 8d 3c 38          	lea    (%r8,%r15,1),%rdi
    460e:	48 8b 07             	mov    (%rdi),%rax
    4611:	8b 10                	mov    (%rax),%edx
    4613:	85 d2                	test   %edx,%edx
    4615:	7e 28                	jle    463f <external_thread+0x7f>
    4617:	48 8b 70 08          	mov    0x8(%rax),%rsi
				if (data->buffers[b]->buffer[x].available == 0) {
    461b:	49 89 dc             	mov    %rbx,%r12
    461e:	49 c1 e4 08          	shl    $0x8,%r12
    4622:	4a 8d 04 26          	lea    (%rsi,%r12,1),%rax
    4626:	8b 88 80 00 00 00    	mov    0x80(%rax),%ecx
    462c:	85 c9                	test   %ecx,%ecx
    462e:	74 38                	je     4668 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4630:	48 83 c3 01          	add    $0x1,%rbx
    4634:	39 da                	cmp    %ebx,%edx
    4636:	7f e3                	jg     461b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    4638:	41 8b b6 bc 00 00 00 	mov    0xbc(%r14),%esi
    463f:	49 83 c5 01          	add    $0x1,%r13
    4643:	44 39 ee             	cmp    %r13d,%esi
    4646:	7f b8                	jg     4600 <external_thread+0x40>
  while (data->running == 1) {
    4648:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    464d:	74 a1                	je     45f0 <external_thread+0x30>
}
    464f:	48 83 c4 08          	add    $0x8,%rsp
    4653:	31 c0                	xor    %eax,%eax
    4655:	5b                   	pop    %rbx
    4656:	41 5c                	pop    %r12
    4658:	41 5d                	pop    %r13
    465a:	41 5e                	pop    %r14
    465c:	41 5f                	pop    %r15
    465e:	5d                   	pop    %rbp
    465f:	c3                   	ret
  while (data->running == 1) {
    4660:	eb fe                	jmp    4660 <external_thread+0xa0>
    4662:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    4668:	48 8d 0d 95 39 00 00 	lea    0x3995(%rip),%rcx        # 8004 <_IO_stdin_used+0x4>
    466f:	48 89 08             	mov    %rcx,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    4672:	48 8b 07             	mov    (%rdi),%rax
    4675:	bf 04 00 00 00       	mov    $0x4,%edi
    467a:	48 8b 48 08          	mov    0x8(%rax),%rcx
    467e:	4c 01 e1             	add    %r12,%rcx
    4681:	48 63 b1 94 00 00 00 	movslq 0x94(%rcx),%rsi
    4688:	48 c1 e6 05          	shl    $0x5,%rsi
    468c:	48 03 b1 88 00 00 00 	add    0x88(%rcx),%rsi
    4693:	e8 f8 dc ff ff       	call   2390 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4698:	49 8b 46 50          	mov    0x50(%r14),%rax
    469c:	4a 8b 04 38          	mov    (%rax,%r15,1),%rax
    46a0:	48 8b 40 08          	mov    0x8(%rax),%rax
    46a4:	42 c7 84 20 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%r12,1)
          asm volatile ("sfence" ::: "memory");
    46b0:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    46b3:	4d 8b 46 50          	mov    0x50(%r14),%r8
    46b7:	48 83 c3 01          	add    $0x1,%rbx
    46bb:	4b 8d 3c 38          	lea    (%r8,%r15,1),%rdi
    46bf:	48 8b 07             	mov    (%rdi),%rax
    46c2:	8b 10                	mov    (%rax),%edx
    46c4:	39 da                	cmp    %ebx,%edx
    46c6:	0f 8f 4b ff ff ff    	jg     4617 <external_thread+0x57>
    46cc:	e9 67 ff ff ff       	jmp    4638 <external_thread+0x78>
    46d1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    46dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000046e0 <timer_thread>:
void* timer_thread(void *arg) {
    46e0:	f3 0f 1e fa          	endbr64
    46e4:	55                   	push   %rbp
    46e5:	48 89 e5             	mov    %rsp,%rbp
    46e8:	41 57                	push   %r15
    46ea:	41 56                	push   %r14
    46ec:	41 55                	push   %r13
    46ee:	41 54                	push   %r12
    46f0:	53                   	push   %rbx
    46f1:	48 83 ec 68          	sub    $0x68,%rsp
    46f5:	ff 15 ed 68 00 00    	call   *0x68ed(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    46fb:	48 8d 35 0e 39 00 00 	lea    0x390e(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    4702:	8b 57 04             	mov    0x4(%rdi),%edx
    4705:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    470e:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    4712:	31 c0                	xor    %eax,%eax
    4714:	48 89 fb             	mov    %rdi,%rbx
    4717:	bf 01 00 00 00       	mov    $0x1,%edi
    471c:	e8 ef dd ff ff       	call   2510 <__printf_chk@plt>
  struct timespec preempt = {
    4721:	66 0f 6f 05 77 44 00 00 	movdqa 0x4477(%rip),%xmm0        # 8ba0 <_IO_stdin_used+0xba0>
    4729:	ba 88 13 00 00       	mov    $0x1388,%edx
    472e:	31 c0                	xor    %eax,%eax
    4730:	48 8d 35 eb 38 00 00 	lea    0x38eb(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    4737:	bf 01 00 00 00       	mov    $0x1,%edi
    473c:	0f 29 45 90          	movaps %xmm0,-0x70(%rbp)
    4740:	e8 cb dd ff ff       	call   2510 <__printf_chk@plt>
  while (data->running && n < times) {
    4745:	44 8b 63 44          	mov    0x44(%rbx),%r12d
    4749:	45 85 e4             	test   %r12d,%r12d
    474c:	0f 84 9b 00 00 00    	je     47ed <timer_thread+0x10d>
  int n = 0;
    4752:	45 31 ed             	xor    %r13d,%r13d
    4755:	4c 8d 7d 80          	lea    -0x80(%rbp),%r15
    4759:	4c 8d 75 90          	lea    -0x70(%rbp),%r14
  int y = 0;
    475d:	45 31 e4             	xor    %r12d,%r12d
    nanosleep(&preempt , &rem2);
    4760:	4c 89 f7             	mov    %r14,%rdi
    4763:	4c 89 fe             	mov    %r15,%rsi
    n++;
    4766:	41 83 c5 01          	add    $0x1,%r13d
    nanosleep(&preempt , &rem2);
    476a:	e8 71 dc ff ff       	call   23e0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    476f:	48 63 43 30          	movslq 0x30(%rbx),%rax
    y++;
    4773:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4778:	85 c0                	test   %eax,%eax
    477a:	7e 49                	jle    47c5 <timer_thread+0xe5>
    477c:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4780:	4d 63 c4             	movslq %r12d,%r8
    4783:	49 c1 e0 09          	shl    $0x9,%r8
    4787:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    478b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    4790:	4c 8b 19             	mov    (%rcx),%r11
    4793:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4795:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4799:	99                   	cltd
    479a:	41 f7 7b 40          	idivl  0x40(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    479e:	49 8b 73 38          	mov    0x38(%r11),%rsi
    47a2:	48 63 d2             	movslq %edx,%rdx
    47a5:	48 c1 e2 09          	shl    $0x9,%rdx
    47a9:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    47b4:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    47c0:	49 39 c9             	cmp    %rcx,%r9
    47c3:	75 cb                	jne    4790 <timer_thread+0xb0>
    asm volatile ("mfence" ::: "memory");
    47c5:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    47c8:	48 8b 43 18          	mov    0x18(%rbx),%rax
  while (data->running && n < times) {
    47cc:	8b 4b 44             	mov    0x44(%rbx),%ecx
    y++;
    47cf:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    47d2:	48 8b 00             	mov    (%rax),%rax
    y++;
    47d5:	39 78 40             	cmp    %edi,0x40(%rax)
    47d8:	44 0f 4f e7          	cmovg  %edi,%r12d
  while (data->running && n < times) {
    47dc:	85 c9                	test   %ecx,%ecx
    47de:	74 0d                	je     47ed <timer_thread+0x10d>
    47e0:	41 81 fd 88 13 00 00 	cmp    $0x1388,%r13d
    47e7:	0f 85 73 ff ff ff    	jne    4760 <timer_thread+0x80>
    47ed:	48 8d 3d 44 38 00 00 	lea    0x3844(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    47f4:	e8 77 db ff ff       	call   2370 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    47f9:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    47fd:	85 d2                	test   %edx,%edx
    47ff:	7e 74                	jle    4875 <timer_thread+0x195>
    for (int y = 0 ; y < data->task_count ; y++) {
    4801:	48 63 43 40          	movslq 0x40(%rbx),%rax
    4805:	85 c0                	test   %eax,%eax
    4807:	7e 6c                	jle    4875 <timer_thread+0x195>
    4809:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    480d:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    4811:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4819:	31 c9                	xor    %ecx,%ecx
    481b:	48 89 c6             	mov    %rax,%rsi
    481e:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4822:	48 8b 40 38          	mov    0x38(%rax),%rax
    4826:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    482a:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4830:	74 1e                	je     4850 <timer_thread+0x170>
    4832:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    483c:	48 05 00 02 00 00    	add    $0x200,%rax
    4842:	48 39 c2             	cmp    %rax,%rdx
    4845:	74 25                	je     486c <timer_thread+0x18c>
    4847:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      data->threads[x]->tasks[y].sending = 0;
    4850:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    485a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4860:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4867:	48 39 c2             	cmp    %rax,%rdx
    486a:	75 e4                	jne    4850 <timer_thread+0x170>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    486c:	48 83 c1 08          	add    $0x8,%rcx
    4870:	48 39 cf             	cmp    %rcx,%rdi
    4873:	75 a9                	jne    481e <timer_thread+0x13e>
  asm volatile ("mfence" ::: "memory");
    4875:	0f ae f0             	mfence
  struct timespec drain = {
    4878:	66 0f 6f 05 30 43 00 00 	movdqa 0x4330(%rip),%xmm0        # 8bb0 <_IO_stdin_used+0xbb0>
    4880:	0f 29 45 b0          	movaps %xmm0,-0x50(%rbp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4884:	48 63 43 28          	movslq 0x28(%rbx),%rax
    y++;
    4888:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    488d:	85 c0                	test   %eax,%eax
    488f:	7e 44                	jle    48d5 <timer_thread+0x1f5>
    4891:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4895:	4d 63 c4             	movslq %r12d,%r8
    4898:	49 c1 e0 09          	shl    $0x9,%r8
    489c:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
        int next = (y + 1) % data->threads[x]->task_count;
    48a0:	4c 8b 31             	mov    (%rcx),%r14
    48a3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    48a5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    48a9:	99                   	cltd
    48aa:	41 f7 7e 40          	idivl  0x40(%r14)
        data->threads[x]->tasks[next].scheduled = 1;
    48ae:	49 8b 76 38          	mov    0x38(%r14),%rsi
    48b2:	48 63 d2             	movslq %edx,%rdx
    48b5:	48 c1 e2 09          	shl    $0x9,%rdx
    48b9:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    48c4:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    48d0:	4c 39 c9             	cmp    %r9,%rcx
    48d3:	75 cb                	jne    48a0 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    48d5:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    48d8:	48 8b 43 18          	mov    0x18(%rbx),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48dc:	44 8b 53 30          	mov    0x30(%rbx),%r10d
    if (y >= data->threads[0]->task_count) {
    48e0:	48 8b 00             	mov    (%rax),%rax
    y++;
    48e3:	39 78 40             	cmp    %edi,0x40(%rax)
    48e6:	b8 00 00 00 00       	mov    $0x0,%eax
    48eb:	0f 4f c7             	cmovg  %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48ee:	45 85 d2             	test   %r10d,%r10d
    48f1:	0f 8e 57 01 00 00    	jle    4a4e <timer_thread+0x36e>
    int all_empty = 1;
    48f7:	89 85 78 ff ff ff    	mov    %eax,-0x88(%rbp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48fd:	45 31 ff             	xor    %r15d,%r15d
    int all_empty = 1;
    4900:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    4906:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int y = 0 ; y < 2 ; y++) {
    4910:	45 31 f6             	xor    %r14d,%r14d
    4913:	45 89 fc             	mov    %r15d,%r12d
    4916:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    491e:	44 89 f7             	mov    %r14d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4921:	45 85 d2             	test   %r10d,%r10d
    4924:	0f 8e c2 00 00 00    	jle    49ec <timer_thread+0x30c>
    492a:	44 89 9d 7c ff ff ff 	mov    %r11d,-0x84(%rbp)
    4931:	4d 89 f3             	mov    %r14,%r11
      y = 0;
    4934:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4936:	45 31 c0             	xor    %r8d,%r8d
    4939:	49 c1 e3 09          	shl    $0x9,%r11
    493d:	0f 1f 00             	nopl   (%rax)
          if (x == k) { continue; }
    4940:	45 39 f8             	cmp    %r15d,%r8d
    4943:	74 36                	je     497b <timer_thread+0x29b>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4945:	48 8b 53 18          	mov    0x18(%rbx),%rdx
    4949:	4a 8b 14 2a          	mov    (%rdx,%r13,1),%rdx
    494d:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4951:	4a 8b 8c 1a 70 01 00 00 	mov    0x170(%rdx,%r11,1),%rcx
    4959:	48 01 c1             	add    %rax,%rcx
    495c:	48 8b 11             	mov    (%rcx),%rdx
    495f:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    4963:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    496a:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    4971:	4d 85 c9             	test   %r9,%r9
    4974:	7f 2a                	jg     49a0 <timer_thread+0x2c0>
    4976:	48 85 f6             	test   %rsi,%rsi
    4979:	7f 25                	jg     49a0 <timer_thread+0x2c0>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    497b:	41 83 c0 01          	add    $0x1,%r8d
    497f:	48 83 c0 38          	add    $0x38,%rax
    4983:	45 39 d0             	cmp    %r10d,%r8d
    4986:	75 b8                	jne    4940 <timer_thread+0x260>
      for (int y = 0 ; y < 2 ; y++) {
    4988:	49 83 fe 01          	cmp    $0x1,%r14
    498c:	0f 84 a6 00 00 00    	je     4a38 <timer_thread+0x358>
    4992:	49 83 c6 01          	add    $0x1,%r14
    4996:	44 89 f7             	mov    %r14d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4999:	eb 96                	jmp    4931 <timer_thread+0x251>
    499b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    49a0:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    49a6:	48 83 ec 08          	sub    $0x8,%rsp
    49aa:	89 f9                	mov    %edi,%ecx
    49ac:	bf 01 00 00 00       	mov    $0x1,%edi
    49b1:	50                   	push   %rax
    49b2:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    49b8:	44 89 e2             	mov    %r12d,%edx
    49bb:	50                   	push   %rax
    49bc:	31 c0                	xor    %eax,%eax
    49be:	56                   	push   %rsi
    49bf:	48 8d 35 97 36 00 00 	lea    0x3697(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    49c6:	e8 45 db ff ff       	call   2510 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    49cb:	44 8b 53 30          	mov    0x30(%rbx),%r10d
      for (int y = 0 ; y < 2 ; y++) {
    49cf:	48 83 c4 20          	add    $0x20,%rsp
    49d3:	49 83 fe 01          	cmp    $0x1,%r14
    49d7:	74 47                	je     4a20 <timer_thread+0x340>
    49d9:	49 83 c6 01          	add    $0x1,%r14
    49dd:	45 31 db             	xor    %r11d,%r11d
    49e0:	44 89 f7             	mov    %r14d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    49e3:	45 85 d2             	test   %r10d,%r10d
    49e6:	0f 8f 3e ff ff ff    	jg     492a <timer_thread+0x24a>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    49ec:	49 83 c7 01          	add    $0x1,%r15
    49f0:	45 39 fa             	cmp    %r15d,%r10d
    49f3:	0f 8f 17 ff ff ff    	jg     4910 <timer_thread+0x230>
    49f9:	44 8b a5 78 ff ff ff 	mov    -0x88(%rbp),%r12d
    if (all_empty == 1) {
    4a00:	41 83 fb 01          	cmp    $0x1,%r11d
    4a04:	74 48                	je     4a4e <timer_thread+0x36e>
      nanosleep(&drain , &drainrem);
    4a06:	48 8d 75 a0          	lea    -0x60(%rbp),%rsi
    4a0a:	48 8d 7d b0          	lea    -0x50(%rbp),%rdi
    4a0e:	e8 cd d9 ff ff       	call   23e0 <nanosleep@plt>
    4a13:	e9 6c fe ff ff       	jmp    4884 <timer_thread+0x1a4>
    4a18:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4a20:	49 83 c7 01          	add    $0x1,%r15
    4a24:	45 31 db             	xor    %r11d,%r11d
    4a27:	45 39 fa             	cmp    %r15d,%r10d
    4a2a:	0f 8f e0 fe ff ff    	jg     4910 <timer_thread+0x230>
    4a30:	eb c7                	jmp    49f9 <timer_thread+0x319>
    4a32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a38:	49 83 c7 01          	add    $0x1,%r15
    4a3c:	44 8b 9d 7c ff ff ff 	mov    -0x84(%rbp),%r11d
    4a43:	45 39 fa             	cmp    %r15d,%r10d
    4a46:	0f 8f c4 fe ff ff    	jg     4910 <timer_thread+0x230>
    4a4c:	eb ab                	jmp    49f9 <timer_thread+0x319>
    4a4e:	48 8d 3d ff 35 00 00 	lea    0x35ff(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4a55:	e8 16 d9 ff ff       	call   2370 <puts@plt>
  while (data->running) {
    4a5a:	8b 53 44             	mov    0x44(%rbx),%edx
    4a5d:	85 d2                	test   %edx,%edx
    4a5f:	0f 84 e9 00 00 00    	je     4b4e <timer_thread+0x46e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4a65:	8b 43 2c             	mov    0x2c(%rbx),%eax
    4a68:	45 31 e4             	xor    %r12d,%r12d
    4a6b:	4c 8d 2d 08 36 00 00 	lea    0x3608(%rip),%r13        # 807a <_IO_stdin_used+0x7a>
    4a72:	4c 8d 35 1c 36 00 00 	lea    0x361c(%rip),%r14        # 8095 <_IO_stdin_used+0x95>
    4a79:	85 c0                	test   %eax,%eax
    4a7b:	7e 38                	jle    4ab5 <timer_thread+0x3d5>
    4a7d:	0f 1f 00             	nopl   (%rax)
    4a80:	31 c0                	xor    %eax,%eax
    4a82:	44 89 e2             	mov    %r12d,%edx
    4a85:	4c 89 ee             	mov    %r13,%rsi
    4a88:	bf 01 00 00 00       	mov    $0x1,%edi
    4a8d:	e8 7e da ff ff       	call   2510 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4a92:	48 8b 43 18          	mov    0x18(%rbx),%rax
    4a96:	4a 8b 04 e0          	mov    (%rax,%r12,8),%rax
      if (data->threads[x]->type == IO) {
    4a9a:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4a9e:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4aa5:	0f 84 cf 00 00 00    	je     4b7a <timer_thread+0x49a>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4aab:	49 83 c4 01          	add    $0x1,%r12
    4aaf:	44 39 63 2c          	cmp    %r12d,0x2c(%rbx)
    4ab3:	7f cb                	jg     4a80 <timer_thread+0x3a0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4ab5:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    4ab9:	85 d2                	test   %edx,%edx
    4abb:	7e 7b                	jle    4b38 <timer_thread+0x458>
      for (int y = 0 ; y < data->task_count ; y++) {
    4abd:	8b 43 40             	mov    0x40(%rbx),%eax
    4ac0:	85 c0                	test   %eax,%eax
    4ac2:	7e 74                	jle    4b38 <timer_thread+0x458>
    4ac4:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4ac7:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    4acb:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4ad3:	31 c9                	xor    %ecx,%ecx
    4ad5:	48 c1 e6 09          	shl    $0x9,%rsi
    4ad9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ae0:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4ae4:	48 8b 40 38          	mov    0x38(%rax),%rax
    4ae8:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4aec:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4af2:	74 1c                	je     4b10 <timer_thread+0x430>
    4af4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4afe:	48 05 00 02 00 00    	add    $0x200,%rax
    4b04:	48 39 d0             	cmp    %rdx,%rax
    4b07:	74 26                	je     4b2f <timer_thread+0x44f>
    4b09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4b10:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4b1a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4b20:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4b2a:	48 39 d0             	cmp    %rdx,%rax
    4b2d:	75 e1                	jne    4b10 <timer_thread+0x430>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4b2f:	48 83 c1 08          	add    $0x8,%rcx
    4b33:	48 39 f9             	cmp    %rdi,%rcx
    4b36:	75 a8                	jne    4ae0 <timer_thread+0x400>
    asm volatile ("mfence" ::: "memory");
    4b38:	0f ae f0             	mfence
    4b3b:	48 8d 3d 65 35 00 00 	lea    0x3565(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4b42:	e8 29 d8 ff ff       	call   2370 <puts@plt>
    data->running = 0;
    4b47:	c7 43 44 00 00 00 00 	movl   $0x0,0x44(%rbx)
    4b4e:	48 8d 3d 59 35 00 00 	lea    0x3559(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4b55:	e8 16 d8 ff ff       	call   2370 <puts@plt>
}
    4b5a:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    4b5e:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b67:	75 41                	jne    4baa <timer_thread+0x4ca>
    4b69:	48 8d 65 d8          	lea    -0x28(%rbp),%rsp
    4b6d:	31 c0                	xor    %eax,%eax
    4b6f:	5b                   	pop    %rbx
    4b70:	41 5c                	pop    %r12
    4b72:	41 5d                	pop    %r13
    4b74:	41 5e                	pop    %r14
    4b76:	41 5f                	pop    %r15
    4b78:	5d                   	pop    %rbp
    4b79:	c3                   	ret
    4b7a:	4c 89 f7             	mov    %r14,%rdi
    4b7d:	e8 ee d7 ff ff       	call   2370 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4b82:	48 8b 43 18          	mov    0x18(%rbx),%rax
    4b86:	be 01 00 00 00       	mov    $0x1,%esi
    4b8b:	4a 8b 04 e0          	mov    (%rax,%r12,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4b8f:	49 83 c4 01          	add    $0x1,%r12
        eventfd_write(data->threads[x]->_eventfd, 1);
    4b93:	8b 78 60             	mov    0x60(%rax),%edi
    4b96:	e8 15 d9 ff ff       	call   24b0 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4b9b:	44 39 63 2c          	cmp    %r12d,0x2c(%rbx)
    4b9f:	0f 8f db fe ff ff    	jg     4a80 <timer_thread+0x3a0>
    4ba5:	e9 0b ff ff ff       	jmp    4ab5 <timer_thread+0x3d5>
}
    4baa:	e8 11 d8 ff ff       	call   23c0 <__stack_chk_fail@plt>
    4baf:	90                   	nop

0000000000004bb0 <minf>:
int minf(int a, int b) {
    4bb0:	f3 0f 1e fa          	endbr64
    4bb4:	55                   	push   %rbp
    4bb5:	48 89 e5             	mov    %rsp,%rbp
    4bb8:	ff 15 2a 64 00 00    	call   *0x642a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    4bbe:	5d                   	pop    %rbp
  if (b < a) { return b; }
    4bbf:	39 f7                	cmp    %esi,%edi
    4bc1:	89 f0                	mov    %esi,%eax
    4bc3:	0f 4e c7             	cmovle %edi,%eax
}
    4bc6:	c3                   	ret
    4bc7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004bd0 <maxf>:
int maxf(int a, int b) {
    4bd0:	f3 0f 1e fa          	endbr64
    4bd4:	55                   	push   %rbp
    4bd5:	48 89 e5             	mov    %rsp,%rbp
    4bd8:	ff 15 0a 64 00 00    	call   *0x640a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    4bde:	5d                   	pop    %rbp
  if (b > a) { return b; }
    4bdf:	39 f7                	cmp    %esi,%edi
    4be1:	89 f0                	mov    %esi,%eax
    4be3:	0f 4d c7             	cmovge %edi,%eax
}
    4be6:	c3                   	ret
    4be7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004bf0 <strtolower>:
void strtolower(char *str) {
    4bf0:	f3 0f 1e fa          	endbr64
    4bf4:	55                   	push   %rbp
    4bf5:	48 89 e5             	mov    %rsp,%rbp
    4bf8:	41 54                	push   %r12
    4bfa:	53                   	push   %rbx
    4bfb:	ff 15 e7 63 00 00    	call   *0x63e7(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    for (; *str; ++str)
    4c01:	48 0f be 1f          	movsbq (%rdi),%rbx
void strtolower(char *str) {
    4c05:	49 89 fc             	mov    %rdi,%r12
    for (; *str; ++str)
    4c08:	84 db                	test   %bl,%bl
    4c0a:	74 24                	je     4c30 <strtolower+0x40>
        *str = (char)tolower(*str);
    4c0c:	e8 ff d9 ff ff       	call   2610 <__ctype_tolower_loc@plt>
    4c11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c18:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4c1b:	49 83 c4 01          	add    $0x1,%r12
        *str = (char)tolower(*str);
    4c1f:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4c22:	41 88 54 24 ff       	mov    %dl,-0x1(%r12)
    for (; *str; ++str)
    4c27:	49 0f be 1c 24       	movsbq (%r12),%rbx
    4c2c:	84 db                	test   %bl,%bl
    4c2e:	75 e8                	jne    4c18 <strtolower+0x28>
}
    4c30:	5b                   	pop    %rbx
    4c31:	41 5c                	pop    %r12
    4c33:	5d                   	pop    %rbp
    4c34:	c3                   	ret
    4c35:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004c40 <zh_malloc>:
void *zh_malloc(size_t size) {
    4c40:	f3 0f 1e fa          	endbr64
    4c44:	55                   	push   %rbp
    4c45:	48 89 e5             	mov    %rsp,%rbp
    4c48:	ff 15 9a 63 00 00    	call   *0x639a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    void *buf = malloc(size);
    4c4e:	e8 7d d8 ff ff       	call   24d0 <malloc@plt>
    if (!buf) {
    4c53:	48 85 c0             	test   %rax,%rax
    4c56:	74 02                	je     4c5a <zh_malloc+0x1a>
}
    4c58:	5d                   	pop    %rbp
    4c59:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4c5a:	48 8b 0d bf 63 00 00 	mov    0x63bf(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4c61:	ba 28 00 00 00       	mov    $0x28,%edx
    4c66:	be 01 00 00 00       	mov    $0x1,%esi
    4c6b:	48 8d 3d 4e 39 00 00 	lea    0x394e(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    4c72:	e8 29 d9 ff ff       	call   25a0 <fwrite@plt>
        exit(1);
    4c77:	bf 01 00 00 00       	mov    $0x1,%edi
    4c7c:	e8 ff d8 ff ff       	call   2580 <exit@plt>
    4c81:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4c8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c90 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4c90:	f3 0f 1e fa          	endbr64
    4c94:	55                   	push   %rbp
    4c95:	48 89 e5             	mov    %rsp,%rbp
    4c98:	53                   	push   %rbx
    4c99:	48 83 ec 08          	sub    $0x8,%rsp
    4c9d:	ff 15 45 63 00 00    	call   *0x6345(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    const char *dot = strrchr(filename, '.');
    4ca3:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4ca8:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4cab:	e8 40 d7 ff ff       	call   23f0 <strrchr@plt>
    if (!dot || dot == filename)
    4cb0:	48 85 c0             	test   %rax,%rax
    4cb3:	74 13                	je     4cc8 <get_filename_ext+0x38>
    4cb5:	48 39 c3             	cmp    %rax,%rbx
    4cb8:	74 0e                	je     4cc8 <get_filename_ext+0x38>
}
    4cba:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    return dot + 1;
    4cbe:	48 83 c0 01          	add    $0x1,%rax
}
    4cc2:	c9                   	leave
    4cc3:	c3                   	ret
    4cc4:	0f 1f 40 00          	nopl   0x0(%rax)
    4cc8:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
        return "";
    4ccc:	48 8d 05 23 34 00 00 	lea    0x3423(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4cd3:	c9                   	leave
    4cd4:	c3                   	ret
    4cd5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000004ce0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4ce0:	f3 0f 1e fa          	endbr64
    4ce4:	55                   	push   %rbp
    4ce5:	48 89 e5             	mov    %rsp,%rbp
    4ce8:	41 56                	push   %r14
    4cea:	41 55                	push   %r13
    4cec:	41 54                	push   %r12
    4cee:	53                   	push   %rbx
    4cef:	48 81 ec 10 08 00 00 	sub    $0x810,%rsp
    4cf6:	ff 15 ec 62 00 00    	call   *0x62ec(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    4cfc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4d05:	48 89 45 d8          	mov    %rax,-0x28(%rbp)
    4d09:	31 c0                	xor    %eax,%eax
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d0b:	4c 8d ad d0 f7 ff ff 	lea    -0x830(%rbp),%r13
    4d12:	49 89 f6             	mov    %rsi,%r14
    4d15:	49 89 d4             	mov    %rdx,%r12
    4d18:	48 89 fe             	mov    %rdi,%rsi
    4d1b:	ba 00 04 00 00       	mov    $0x400,%edx
    4d20:	4c 89 ef             	mov    %r13,%rdi
    4d23:	e8 c8 d7 ff ff       	call   24f0 <__strcpy_chk@plt>
    for (; *str; ++str)
    4d28:	48 0f be 9d d0 f7 ff ff 	movsbq -0x830(%rbp),%rbx
    4d30:	84 db                	test   %bl,%bl
    4d32:	74 1e                	je     4d52 <send_headers+0x72>
        *str = (char)tolower(*str);
    4d34:	e8 d7 d8 ff ff       	call   2610 <__ctype_tolower_loc@plt>
    4d39:	48 8b 08             	mov    (%rax),%rcx
    4d3c:	4c 89 e8             	mov    %r13,%rax
    4d3f:	90                   	nop
    4d40:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4d43:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4d47:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4d4a:	48 0f be 18          	movsbq (%rax),%rbx
    4d4e:	84 db                	test   %bl,%bl
    4d50:	75 ee                	jne    4d40 <send_headers+0x60>
    void *buf = malloc(size);
    4d52:	bf 11 00 00 00       	mov    $0x11,%edi
    4d57:	e8 74 d7 ff ff       	call   24d0 <malloc@plt>
    if (!buf) {
    4d5c:	48 85 c0             	test   %rax,%rax
    4d5f:	0f 84 72 04 00 00    	je     51d7 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4d65:	66 0f 6f 05 53 3e 00 00 	movdqa 0x3e53(%rip),%xmm0        # 8bc0 <_IO_stdin_used+0xbc0>
    iov[0].iov_base = zh_malloc(slen);
    4d6d:	49 89 04 24          	mov    %rax,(%r12)
    void *buf = malloc(size);
    4d71:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4d76:	49 c7 44 24 08 11 00 00 00 	movq   $0x11,0x8(%r12)
    4d7f:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4d83:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4d86:	e8 45 d7 ff ff       	call   24d0 <malloc@plt>
    if (!buf) {
    4d8b:	48 85 c0             	test   %rax,%rax
    4d8e:	0f 84 43 04 00 00    	je     51d7 <send_headers+0x4f7>
    4d94:	66 0f 6f 05 34 3e 00 00 	movdqa 0x3e34(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    iov[1].iov_base = zh_malloc(slen);
    4d9c:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    const char *dot = strrchr(filename, '.');
    4da1:	4c 89 ef             	mov    %r13,%rdi
    4da4:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4dae:	49 c7 44 24 18 17 00 00 00 	movq   $0x17,0x18(%r12)
    4db7:	0f 11 00             	movups %xmm0,(%rax)
    4dba:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4dbe:	be 2e 00 00 00       	mov    $0x2e,%esi
    4dc3:	e8 28 d6 ff ff       	call   23f0 <strrchr@plt>
    if (!dot || dot == filename)
    4dc8:	48 85 c0             	test   %rax,%rax
    4dcb:	0f 84 df 02 00 00    	je     50b0 <send_headers+0x3d0>
    4dd1:	4c 39 e8             	cmp    %r13,%rax
    4dd4:	0f 84 d6 02 00 00    	je     50b0 <send_headers+0x3d0>
    return dot + 1;
    4dda:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4dde:	48 8d 3d df 32 00 00 	lea    0x32df(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4de5:	48 89 de             	mov    %rbx,%rsi
    4de8:	e8 63 d6 ff ff       	call   2450 <strcmp@plt>
    4ded:	85 c0                	test   %eax,%eax
    4def:	75 1e                	jne    4e0f <send_headers+0x12f>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4df1:	66 0f 6f 05 e7 3d 00 00 	movdqa 0x3de7(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4df9:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4e00:	66 0f 6f 05 e8 3d 00 00 	movdqa 0x3de8(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4e08:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("jpeg", file_ext) == 0)
    4e0f:	48 89 de             	mov    %rbx,%rsi
    4e12:	48 8d 3d af 32 00 00 	lea    0x32af(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4e19:	e8 32 d6 ff ff       	call   2450 <strcmp@plt>
    4e1e:	85 c0                	test   %eax,%eax
    4e20:	75 1e                	jne    4e40 <send_headers+0x160>
    4e22:	66 0f 6f 05 b6 3d 00 00 	movdqa 0x3db6(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4e2a:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    4e31:	66 0f 6f 05 b7 3d 00 00 	movdqa 0x3db7(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4e39:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    if (strcmp("png", file_ext) == 0)
    4e40:	48 89 de             	mov    %rbx,%rsi
    4e43:	48 8d 3d 83 32 00 00 	lea    0x3283(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4e4a:	e8 01 d6 ff ff       	call   2450 <strcmp@plt>
    4e4f:	85 c0                	test   %eax,%eax
    4e51:	0f 84 09 02 00 00    	je     5060 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4e57:	48 89 de             	mov    %rbx,%rsi
    4e5a:	48 8d 3d 70 32 00 00 	lea    0x3270(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4e61:	e8 ea d5 ff ff       	call   2450 <strcmp@plt>
    4e66:	85 c0                	test   %eax,%eax
    4e68:	0f 84 a2 02 00 00    	je     5110 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4e6e:	48 89 de             	mov    %rbx,%rsi
    4e71:	48 8d 3d 5d 32 00 00 	lea    0x325d(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4e78:	e8 d3 d5 ff ff       	call   2450 <strcmp@plt>
    4e7d:	85 c0                	test   %eax,%eax
    4e7f:	0f 84 63 02 00 00    	je     50e8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4e85:	48 89 de             	mov    %rbx,%rsi
    4e88:	48 8d 3d 89 32 00 00 	lea    0x3289(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4e8f:	e8 bc d5 ff ff       	call   2450 <strcmp@plt>
    4e94:	85 c0                	test   %eax,%eax
    4e96:	0f 84 24 02 00 00    	je     50c0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4e9c:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4e9f:	0f 84 53 01 00 00    	je     4ff8 <send_headers+0x318>
    if (strcmp("css", file_ext) == 0)
    4ea5:	48 89 de             	mov    %rbx,%rsi
    4ea8:	48 8d 3d 2a 32 00 00 	lea    0x322a(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4eaf:	e8 9c d5 ff ff       	call   2450 <strcmp@plt>
    4eb4:	85 c0                	test   %eax,%eax
    4eb6:	0f 84 a4 02 00 00    	je     5160 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4ebc:	48 89 de             	mov    %rbx,%rsi
    4ebf:	48 8d 3d 17 32 00 00 	lea    0x3217(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4ec6:	e8 85 d5 ff ff       	call   2450 <strcmp@plt>
    4ecb:	85 c0                	test   %eax,%eax
    4ecd:	0f 84 65 02 00 00    	je     5138 <send_headers+0x458>
    slen = strlen(send_buffer);
    4ed3:	4c 8d ad d0 fb ff ff 	lea    -0x430(%rbp),%r13
    4eda:	4c 89 ef             	mov    %r13,%rdi
    4edd:	e8 ce d4 ff ff       	call   23b0 <strlen@plt>
    void *buf = malloc(size);
    4ee2:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4ee5:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4ee8:	e8 e3 d5 ff ff       	call   24d0 <malloc@plt>
    if (!buf) {
    4eed:	48 85 c0             	test   %rax,%rax
    4ef0:	0f 84 e1 02 00 00    	je     51d7 <send_headers+0x4f7>
    iov[2].iov_base = zh_malloc(slen);
    4ef6:	49 89 44 24 20       	mov    %rax,0x20(%r12)
    iov[2].iov_len = slen;
    4efb:	49 89 5c 24 28       	mov    %rbx,0x28(%r12)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f00:	83 fb 08             	cmp    $0x8,%ebx
    4f03:	0f 83 37 01 00 00    	jae    5040 <send_headers+0x360>
    4f09:	f6 c3 04             	test   $0x4,%bl
    4f0c:	0f 85 71 02 00 00    	jne    5183 <send_headers+0x4a3>
    4f12:	85 db                	test   %ebx,%ebx
    4f14:	74 12                	je     4f28 <send_headers+0x248>
    4f16:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    4f1d:	88 10                	mov    %dl,(%rax)
    4f1f:	f6 c3 02             	test   $0x2,%bl
    4f22:	0f 85 8b 02 00 00    	jne    51b3 <send_headers+0x4d3>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4f28:	4d 89 f0             	mov    %r14,%r8
    4f2b:	48 8d 0d af 31 00 00 	lea    0x31af(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4f32:	4c 89 ef             	mov    %r13,%rdi
    4f35:	31 c0                	xor    %eax,%eax
    4f37:	ba 00 04 00 00       	mov    $0x400,%edx
    4f3c:	be 01 00 00 00       	mov    $0x1,%esi
    4f41:	e8 da d6 ff ff       	call   2620 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4f46:	4c 89 ef             	mov    %r13,%rdi
    4f49:	e8 62 d4 ff ff       	call   23b0 <strlen@plt>
    void *buf = malloc(size);
    4f4e:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4f51:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4f54:	e8 77 d5 ff ff       	call   24d0 <malloc@plt>
    if (!buf) {
    4f59:	48 85 c0             	test   %rax,%rax
    4f5c:	0f 84 75 02 00 00    	je     51d7 <send_headers+0x4f7>
    iov[3].iov_base = zh_malloc(slen);
    4f62:	49 89 44 24 30       	mov    %rax,0x30(%r12)
    iov[3].iov_len = slen;
    4f67:	49 89 5c 24 38       	mov    %rbx,0x38(%r12)
    4f6c:	83 fb 08             	cmp    $0x8,%ebx
    4f6f:	0f 83 13 01 00 00    	jae    5088 <send_headers+0x3a8>
    4f75:	f6 c3 04             	test   $0x4,%bl
    4f78:	0f 85 1d 02 00 00    	jne    519b <send_headers+0x4bb>
    4f7e:	85 db                	test   %ebx,%ebx
    4f80:	74 12                	je     4f94 <send_headers+0x2b4>
    4f82:	0f b6 95 d0 fb ff ff 	movzbl -0x430(%rbp),%edx
    4f89:	88 10                	mov    %dl,(%rax)
    4f8b:	f6 c3 02             	test   $0x2,%bl
    4f8e:	0f 85 31 02 00 00    	jne    51c5 <send_headers+0x4e5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f94:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4f99:	bf 02 00 00 00       	mov    $0x2,%edi
    4f9e:	c6 85 d2 fb ff ff 00 	movb   $0x0,-0x42e(%rbp)
    4fa5:	66 89 85 d0 fb ff ff 	mov    %ax,-0x430(%rbp)
    4fac:	e8 1f d5 ff ff       	call   24d0 <malloc@plt>
    if (!buf) {
    4fb1:	48 85 c0             	test   %rax,%rax
    4fb4:	0f 84 1d 02 00 00    	je     51d7 <send_headers+0x4f7>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4fba:	0f b7 95 d0 fb ff ff 	movzwl -0x430(%rbp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4fc1:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    iov[4].iov_len = slen;
    4fc6:	49 c7 44 24 48 02 00 00 00 	movq   $0x2,0x48(%r12)
    4fcf:	66 89 10             	mov    %dx,(%rax)
}
    4fd2:	48 8b 45 d8          	mov    -0x28(%rbp),%rax
    4fd6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4fdf:	0f 85 19 02 00 00    	jne    51fe <send_headers+0x51e>
    4fe5:	48 81 c4 10 08 00 00 	add    $0x810,%rsp
    4fec:	5b                   	pop    %rbx
    4fed:	41 5c                	pop    %r12
    4fef:	41 5d                	pop    %r13
    4ff1:	41 5e                	pop    %r14
    4ff3:	5d                   	pop    %rbp
    4ff4:	c3                   	ret
    4ff5:	0f 1f 00             	nopl   (%rax)
    if (strcmp("js", file_ext) == 0)
    4ff8:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4ffc:	0f 85 a3 fe ff ff    	jne    4ea5 <send_headers+0x1c5>
    5002:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    5006:	0f 85 99 fe ff ff    	jne    4ea5 <send_headers+0x1c5>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    500c:	66 0f 6f 05 2c 3c 00 00 	movdqa 0x3c2c(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    5014:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    501e:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    5025:	66 0f 6f 05 23 3c 00 00 	movdqa 0x3c23(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    502d:	0f 29 85 e0 fb ff ff 	movaps %xmm0,-0x420(%rbp)
    5034:	48 89 85 ef fb ff ff 	mov    %rax,-0x411(%rbp)
    503b:	e9 65 fe ff ff       	jmp    4ea5 <send_headers+0x1c5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5040:	89 da                	mov    %ebx,%edx
    5042:	48 89 c7             	mov    %rax,%rdi
    5045:	4c 89 ee             	mov    %r13,%rsi
    5048:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    504d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5052:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5055:	c1 e9 03             	shr    $0x3,%ecx
    5058:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    505b:	e9 c8 fe ff ff       	jmp    4f28 <send_headers+0x248>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5060:	66 0f 6f 05 78 3b 00 00 	movdqa 0x3b78(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    5068:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    506f:	66 0f 6f 05 89 3b 00 00 	movdqa 0x3b89(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    5077:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    507e:	e9 d4 fd ff ff       	jmp    4e57 <send_headers+0x177>
    5083:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5088:	89 da                	mov    %ebx,%edx
    508a:	48 89 c7             	mov    %rax,%rdi
    508d:	4c 89 ee             	mov    %r13,%rsi
    5090:	49 8b 4c 15 f8       	mov    -0x8(%r13,%rdx,1),%rcx
    5095:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    509a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    509d:	c1 e9 03             	shr    $0x3,%ecx
    50a0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    50a3:	e9 ec fe ff ff       	jmp    4f94 <send_headers+0x2b4>
    50a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    50b0:	48 8d 1d 3f 30 00 00 	lea    0x303f(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    50b7:	e9 9b fd ff ff       	jmp    4e57 <send_headers+0x177>
    50bc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    50c0:	66 0f 6f 05 58 3b 00 00 	movdqa 0x3b58(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    50c8:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    50cf:	66 0f 6f 05 59 3b 00 00 	movdqa 0x3b59(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    50d7:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    50de:	e9 b9 fd ff ff       	jmp    4e9c <send_headers+0x1bc>
    50e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    50e8:	66 0f 6f 05 30 3b 00 00 	movdqa 0x3b30(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    50f0:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    50f7:	66 0f 6f 05 31 3b 00 00 	movdqa 0x3b31(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    50ff:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    5106:	e9 7a fd ff ff       	jmp    4e85 <send_headers+0x1a5>
    510b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5110:	66 0f 6f 05 c8 3a 00 00 	movdqa 0x3ac8(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    5118:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    511f:	66 0f 6f 05 e9 3a 00 00 	movdqa 0x3ae9(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    5127:	0f 11 85 da fb ff ff 	movups %xmm0,-0x426(%rbp)
    512e:	e9 3b fd ff ff       	jmp    4e6e <send_headers+0x18e>
    5133:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5138:	66 0f 6f 05 e0 3a 00 00 	movdqa 0x3ae0(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    5140:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    5147:	66 0f 6f 05 21 3b 00 00 	movdqa 0x3b21(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    514f:	0f 11 85 db fb ff ff 	movups %xmm0,-0x425(%rbp)
    5156:	e9 78 fd ff ff       	jmp    4ed3 <send_headers+0x1f3>
    515b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5160:	66 0f 6f 05 b8 3a 00 00 	movdqa 0x3ab8(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    5168:	0f 29 85 d0 fb ff ff 	movaps %xmm0,-0x430(%rbp)
    516f:	66 0f 6f 05 e9 3a 00 00 	movdqa 0x3ae9(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5177:	0f 11 85 d9 fb ff ff 	movups %xmm0,-0x427(%rbp)
    517e:	e9 39 fd ff ff       	jmp    4ebc <send_headers+0x1dc>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5183:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    5189:	89 db                	mov    %ebx,%ebx
    518b:	89 10                	mov    %edx,(%rax)
    518d:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    5192:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5196:	e9 8d fd ff ff       	jmp    4f28 <send_headers+0x248>
    519b:	8b 95 d0 fb ff ff    	mov    -0x430(%rbp),%edx
    51a1:	89 db                	mov    %ebx,%ebx
    51a3:	89 10                	mov    %edx,(%rax)
    51a5:	41 8b 54 1d fc       	mov    -0x4(%r13,%rbx,1),%edx
    51aa:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    51ae:	e9 e1 fd ff ff       	jmp    4f94 <send_headers+0x2b4>
    51b3:	89 db                	mov    %ebx,%ebx
    51b5:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    51bb:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    51c0:	e9 63 fd ff ff       	jmp    4f28 <send_headers+0x248>
    51c5:	89 db                	mov    %ebx,%ebx
    51c7:	41 0f b7 54 1d fe    	movzwl -0x2(%r13,%rbx,1),%edx
    51cd:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    51d2:	e9 bd fd ff ff       	jmp    4f94 <send_headers+0x2b4>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    51d7:	48 8b 0d 42 5e 00 00 	mov    0x5e42(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    51de:	ba 28 00 00 00       	mov    $0x28,%edx
    51e3:	be 01 00 00 00       	mov    $0x1,%esi
    51e8:	48 8d 3d d1 33 00 00 	lea    0x33d1(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    51ef:	e8 ac d3 ff ff       	call   25a0 <fwrite@plt>
        exit(1);
    51f4:	bf 01 00 00 00       	mov    $0x1,%edi
    51f9:	e8 82 d3 ff ff       	call   2580 <exit@plt>
}
    51fe:	e8 bd d1 ff ff       	call   23c0 <__stack_chk_fail@plt>
    5203:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    520e:	66 90                	xchg   %ax,%ax

0000000000005210 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5210:	f3 0f 1e fa          	endbr64
    5214:	55                   	push   %rbp
    5215:	48 89 e5             	mov    %rsp,%rbp
    5218:	41 56                	push   %r14
    521a:	41 55                	push   %r13
    521c:	41 54                	push   %r12
    521e:	53                   	push   %rbx
    521f:	ff 15 c3 5d 00 00    	call   *0x5dc3(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    5225:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    5228:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    522b:	48 89 f3             	mov    %rsi,%rbx
    522e:	49 89 d6             	mov    %rdx,%r14
    void *buf = malloc(size);
    5231:	e8 9a d2 ff ff       	call   24d0 <malloc@plt>
    5236:	49 89 c4             	mov    %rax,%r12
    if (!buf) {
    5239:	48 85 c0             	test   %rax,%rax
    523c:	74 69                	je     52a7 <copy_file_contents+0x97>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    523e:	4c 89 ef             	mov    %r13,%rdi
    5241:	31 f6                	xor    %esi,%esi
    5243:	31 c0                	xor    %eax,%eax
    5245:	e8 f6 d2 ff ff       	call   2540 <open@plt>
    524a:	41 89 c5             	mov    %eax,%r13d
    if (fd < 0)
    524d:	85 c0                	test   %eax,%eax
    524f:	0f 88 08 d4 ff ff    	js     265d <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    5255:	48 89 da             	mov    %rbx,%rdx
    5258:	4c 89 e6             	mov    %r12,%rsi
    525b:	89 c7                	mov    %eax,%edi
    525d:	e8 ce d1 ff ff       	call   2430 <read@plt>
    if (ret < file_size) {
    5262:	48 98                	cltq
    5264:	48 39 d8             	cmp    %rbx,%rax
    5267:	7c 1f                	jl     5288 <copy_file_contents+0x78>
    close(fd);
    5269:	44 89 ef             	mov    %r13d,%edi
    526c:	e8 9f d1 ff ff       	call   2410 <close@plt>
    iov->iov_base = buf;
    5271:	4d 89 26             	mov    %r12,(%r14)
    iov->iov_len = file_size;
    5274:	49 89 5e 08          	mov    %rbx,0x8(%r14)
}
    5278:	5b                   	pop    %rbx
    5279:	41 5c                	pop    %r12
    527b:	41 5d                	pop    %r13
    527d:	41 5e                	pop    %r14
    527f:	5d                   	pop    %rbp
    5280:	c3                   	ret
    5281:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5288:	48 8b 0d 91 5d 00 00 	mov    0x5d91(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    528f:	ba 1a 00 00 00       	mov    $0x1a,%edx
    5294:	be 01 00 00 00       	mov    $0x1,%esi
    5299:	48 8d 3d 57 2e 00 00 	lea    0x2e57(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    52a0:	e8 fb d2 ff ff       	call   25a0 <fwrite@plt>
    52a5:	eb c2                	jmp    5269 <copy_file_contents+0x59>
    52a7:	48 8b 0d 72 5d 00 00 	mov    0x5d72(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    52ae:	ba 28 00 00 00       	mov    $0x28,%edx
    52b3:	be 01 00 00 00       	mov    $0x1,%esi
    52b8:	48 8d 3d 01 33 00 00 	lea    0x3301(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    52bf:	e8 dc d2 ff ff       	call   25a0 <fwrite@plt>
        exit(1);
    52c4:	bf 01 00 00 00       	mov    $0x1,%edi
    52c9:	e8 b2 d2 ff ff       	call   2580 <exit@plt>
    52ce:	66 90                	xchg   %ax,%ax

00000000000052d0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    52d0:	f3 0f 1e fa          	endbr64
    52d4:	55                   	push   %rbp
    52d5:	48 89 e5             	mov    %rsp,%rbp
    52d8:	ff 15 0a 5d 00 00    	call   *0x5d0a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    52de:	8b 46 44             	mov    0x44(%rsi),%eax
    52e1:	48 89 fa             	mov    %rdi,%rdx
    52e4:	48 89 f7             	mov    %rsi,%rdi
    52e7:	8d 70 01             	lea    0x1(%rax),%esi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    52ea:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    52f0:	48 8b 07             	mov    (%rdi),%rax
    52f3:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    52f6:	f6 c1 02             	test   $0x2,%cl
    52f9:	74 00                	je     52fb <add_write_request+0x2b>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    52fb:	89 f0                	mov    %esi,%eax
    52fd:	44 29 c0             	sub    %r8d,%eax
    5300:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5303:	0f 82 60 d3 ff ff    	jb     2669 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5309:	c1 e9 0a             	shr    $0xa,%ecx
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    530c:	8b 47 44             	mov    0x44(%rdi),%eax
    530f:	23 47 58             	and    0x58(%rdi),%eax
		sq->sqe_tail = next;
    5312:	89 77 44             	mov    %esi,0x44(%rdi)
	if (ring->flags & IORING_SETUP_SQE128)
    5315:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5318:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    531b:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    531f:	d3 e0                	shl    %cl,%eax
    5321:	8b 4a 04             	mov    0x4(%rdx),%ecx
    5324:	48 c1 e0 06          	shl    $0x6,%rax
    5328:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    532c:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    5332:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5335:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    5339:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    533f:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5347:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    534b:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    534e:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    5355:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    535d:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    5361:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    5365:	e8 66 d0 ff ff       	call   23d0 <io_uring_submit@plt>
}
    536a:	31 c0                	xor    %eax,%eax
    536c:	5d                   	pop    %rbp
    536d:	c3                   	ret
    536e:	66 90                	xchg   %ax,%ax

0000000000005370 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    5370:	f3 0f 1e fa          	endbr64
    5374:	55                   	push   %rbp
    5375:	48 89 e5             	mov    %rsp,%rbp
    5378:	41 56                	push   %r14
    537a:	41 55                	push   %r13
    537c:	41 54                	push   %r12
    537e:	53                   	push   %rbx
    537f:	ff 15 63 5c 00 00    	call   *0x5c63(%rip)        # afe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    5385:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5388:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    538e:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    5391:	83 c0 01             	add    $0x1,%eax
    5394:	48 89 f3             	mov    %rsi,%rbx
    5397:	41 89 fe             	mov    %edi,%r14d
		head = IO_URING_READ_ONCE(*sq->khead);
    539a:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    539c:	f6 c1 02             	test   $0x2,%cl
    539f:	74 00                	je     53a1 <add_read_request+0x31>
	if (next - head <= sq->ring_entries) {
    53a1:	89 c2                	mov    %eax,%edx
    53a3:	29 f2                	sub    %esi,%edx
    53a5:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    53a8:	0f 82 cb d2 ff ff    	jb     2679 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53ae:	44 8b 63 44          	mov    0x44(%rbx),%r12d
	if (ring->flags & IORING_SETUP_SQE128)
    53b2:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    53b5:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    53b8:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    53bd:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53c0:	44 23 63 58          	and    0x58(%rbx),%r12d
    53c4:	41 d3 e4             	shl    %cl,%r12d
    53c7:	49 c1 e4 06          	shl    $0x6,%r12
    53cb:	4c 03 63 38          	add    0x38(%rbx),%r12
    53cf:	e8 fc d0 ff ff       	call   24d0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    53d4:	be 01 00 00 00       	mov    $0x1,%esi
    53d9:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    53de:	49 89 c5             	mov    %rax,%r13
    req->iov[0].iov_base = malloc(READ_SZ);
    53e1:	e8 5a d0 ff ff       	call   2440 <calloc@plt>
    req->client_socket = client_socket;
    53e6:	45 89 75 08          	mov    %r14d,0x8(%r13)
	sqe->addr3 = 0;
    53ea:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    53ee:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    53f1:	49 89 45 10          	mov    %rax,0x10(%r13)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    53f5:	49 8d 45 10          	lea    0x10(%r13),%rax
    req->iov[0].iov_len = READ_SZ;
    53f9:	49 c7 45 18 00 20 00 00 	movq   $0x2000,0x18(%r13)
    req->event_type = EVENT_TYPE_READ;
    5401:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
	sqe->fd = fd;
    5409:	45 89 74 24 04       	mov    %r14d,0x4(%r12)
	sqe->user_data = (unsigned long) data;
    540e:	4d 89 6c 24 20       	mov    %r13,0x20(%r12)
	sqe->opcode = (__u8) op;
    5413:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->off = offset;
    541b:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    5424:	49 89 44 24 10       	mov    %rax,0x10(%r12)
	sqe->len = len;
    5429:	49 c7 44 24 18 01 00 00 00 	movq   $0x1,0x18(%r12)
	sqe->buf_index = 0;
    5432:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->addr3 = 0;
    543b:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    io_uring_submit(ring);
    5441:	e8 8a cf ff ff       	call   23d0 <io_uring_submit@plt>
}
    5446:	5b                   	pop    %rbx
    5447:	31 c0                	xor    %eax,%eax
    5449:	41 5c                	pop    %r12
    544b:	41 5d                	pop    %r13
    544d:	41 5e                	pop    %r14
    544f:	5d                   	pop    %rbp
    5450:	c3                   	ret
    5451:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    545c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005460 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5460:	f3 0f 1e fa          	endbr64
    5464:	55                   	push   %rbp
    5465:	48 89 e5             	mov    %rsp,%rbp
    5468:	41 57                	push   %r15
    546a:	41 56                	push   %r14
    546c:	41 55                	push   %r13
    546e:	41 54                	push   %r12
    5470:	53                   	push   %rbx
    5471:	48 83 ec 08          	sub    $0x8,%rsp
    5475:	ff 15 6d 5b 00 00    	call   *0x5b6d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    547b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    547e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5483:	41 89 f7             	mov    %esi,%r15d
    5486:	49 89 d4             	mov    %rdx,%r12
    void *buf = malloc(size);
    5489:	e8 42 d0 ff ff       	call   24d0 <malloc@plt>
    548e:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5491:	48 85 c0             	test   %rax,%rax
    5494:	0f 84 eb 00 00 00    	je     5585 <_send_static_string_content+0x125>
    unsigned long slen = strlen(str);
    549a:	4c 89 ef             	mov    %r13,%rdi
    549d:	e8 0e cf ff ff       	call   23b0 <strlen@plt>
    req->iovec_count = 1;
    54a2:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    54a9:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
    void *buf = malloc(size);
    54ad:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    54b0:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    54b3:	e8 18 d0 ff ff       	call   24d0 <malloc@plt>
    54b8:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    54bb:	48 85 c0             	test   %rax,%rax
    54be:	0f 84 c1 00 00 00    	je     5585 <_send_static_string_content+0x125>
    req->iov[0].iov_base = zh_malloc(slen);
    54c4:	48 89 43 10          	mov    %rax,0x10(%rbx)
    54c8:	4c 89 f2             	mov    %r14,%rdx
    54cb:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    54ce:	4c 89 73 18          	mov    %r14,0x18(%rbx)
    54d2:	e8 b9 cf ff ff       	call   2490 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    54d7:	41 8b 44 24 44       	mov    0x44(%r12),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    54dc:	41 8b 8c 24 c0 00 00 00 	mov    0xc0(%r12),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    54e4:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    54e7:	49 8b 04 24          	mov    (%r12),%rax
    54eb:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    54ed:	f6 c1 02             	test   $0x2,%cl
    54f0:	0f 85 8a 00 00 00    	jne    5580 <_send_static_string_content+0x120>
	if (next - head <= sq->ring_entries) {
    54f6:	89 d0                	mov    %edx,%eax
    54f8:	29 f0                	sub    %esi,%eax
    54fa:	41 39 44 24 5c       	cmp    %eax,0x5c(%r12)
    54ff:	0f 82 7e d1 ff ff    	jb     2683 <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5505:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5508:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    550d:	41 23 44 24 58       	and    0x58(%r12),%eax
    io_uring_submit(ring);
    5512:	4c 89 e7             	mov    %r12,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    5515:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5518:	41 89 54 24 44       	mov    %edx,0x44(%r12)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    551d:	8b 53 04             	mov    0x4(%rbx),%edx
	sqe->addr3 = 0;
    5520:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5524:	d3 e0                	shl    %cl,%eax
    5526:	8b 4b 08             	mov    0x8(%rbx),%ecx
    req->event_type = EVENT_TYPE_WRITE;
    5529:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    552f:	48 c1 e0 06          	shl    $0x6,%rax
    5533:	49 03 44 24 38       	add    0x38(%r12),%rax
	sqe->fd = fd;
    5538:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    553b:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    553f:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5545:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    554d:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5551:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5554:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    555b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5563:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    5567:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    556b:	48 83 c4 08          	add    $0x8,%rsp
    556f:	5b                   	pop    %rbx
    5570:	41 5c                	pop    %r12
    5572:	41 5d                	pop    %r13
    5574:	41 5e                	pop    %r14
    5576:	41 5f                	pop    %r15
    5578:	5d                   	pop    %rbp
    io_uring_submit(ring);
    5579:	e9 52 ce ff ff       	jmp    23d0 <io_uring_submit@plt>
    557e:	66 90                	xchg   %ax,%ax
		head = io_uring_smp_load_acquire(sq->khead);
    5580:	e9 71 ff ff ff       	jmp    54f6 <_send_static_string_content+0x96>
    5585:	48 8b 0d 94 5a 00 00 	mov    0x5a94(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    558c:	ba 28 00 00 00       	mov    $0x28,%edx
    5591:	be 01 00 00 00       	mov    $0x1,%esi
    5596:	48 8d 3d 23 30 00 00 	lea    0x3023(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    559d:	e8 fe cf ff ff       	call   25a0 <fwrite@plt>
        exit(1);
    55a2:	bf 01 00 00 00       	mov    $0x1,%edi
    55a7:	e8 d4 cf ff ff       	call   2580 <exit@plt>
    55ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000055b0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    55b0:	f3 0f 1e fa          	endbr64
    55b4:	55                   	push   %rbp
    55b5:	48 89 e5             	mov    %rsp,%rbp
    55b8:	ff 15 2a 5a 00 00    	call   *0x5a2a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    55be:	5d                   	pop    %rbp
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    55bf:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    55c2:	89 fe                	mov    %edi,%esi
    55c4:	48 8b 3d 4d 5a 00 00 	mov    0x5a4d(%rip),%rdi        # b018 <unimplemented_content>
    55cb:	e9 90 fe ff ff       	jmp    5460 <_send_static_string_content>

00000000000055d0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    55d0:	f3 0f 1e fa          	endbr64
    55d4:	55                   	push   %rbp
    55d5:	48 89 e5             	mov    %rsp,%rbp
    55d8:	ff 15 0a 5a 00 00    	call   *0x5a0a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    55de:	5d                   	pop    %rbp
void handle_http_404(int client_socket, struct io_uring *ring) {
    55df:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    55e2:	89 fe                	mov    %edi,%esi
    55e4:	48 8b 3d 25 5a 00 00 	mov    0x5a25(%rip),%rdi        # b010 <http_404_content>
    55eb:	e9 70 fe ff ff       	jmp    5460 <_send_static_string_content>

00000000000055f0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    55f0:	f3 0f 1e fa          	endbr64
    55f4:	55                   	push   %rbp
    55f5:	48 89 e5             	mov    %rsp,%rbp
    55f8:	41 57                	push   %r15
    55fa:	41 56                	push   %r14
    55fc:	41 55                	push   %r13
    55fe:	41 54                	push   %r12
    5600:	53                   	push   %rbx
    5601:	48 81 ec a8 04 00 00 	sub    $0x4a8,%rsp
    5608:	ff 15 da 59 00 00    	call   *0x59da(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    560e:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5617:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    561b:	31 c0                	xor    %eax,%eax
    561d:	49 89 fc             	mov    %rdi,%r12
    5620:	41 89 f5             	mov    %esi,%r13d
    5623:	49 89 d6             	mov    %rdx,%r14
    if (path[strlen(path) - 1] == '/') {
    5626:	e8 85 cd ff ff       	call   23b0 <strlen@plt>
    562b:	41 80 7c 04 ff 2f    	cmpb   $0x2f,-0x1(%r12,%rax,1)
    5631:	48 89 c3             	mov    %rax,%rbx
    5634:	0f 84 b6 00 00 00    	je     56f0 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    563a:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    563f:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    5643:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5648:	4c 89 e6             	mov    %r12,%rsi
    564b:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5652:	66 89 85 c4 fb ff ff 	mov    %ax,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5659:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5660:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    566a:	e8 01 ce ff ff       	call   2470 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    566f:	48 8d b5 30 fb ff ff 	lea    -0x4d0(%rbp),%rsi
    5676:	4c 89 ff             	mov    %r15,%rdi
    5679:	e8 02 ce ff ff       	call   2480 <stat@plt>
    567e:	83 f8 ff             	cmp    $0xffffffff,%eax
    5681:	0f 84 41 01 00 00    	je     57c8 <handle_get_method+0x1d8>
        if (S_ISREG(path_stat.st_mode)) {
    5687:	8b 85 48 fb ff ff    	mov    -0x4b8(%rbp),%eax
    568d:	25 00 f0 00 00       	and    $0xf000,%eax
    5692:	3d 00 80 00 00       	cmp    $0x8000,%eax
    5697:	0f 84 b3 00 00 00    	je     5750 <handle_get_method+0x160>
    _send_static_string_content(http_404_content, client_socket, ring);
    569d:	48 8b 3d 6c 59 00 00 	mov    0x596c(%rip),%rdi        # b010 <http_404_content>
    56a4:	4c 89 f2             	mov    %r14,%rdx
    56a7:	44 89 ee             	mov    %r13d,%esi
    56aa:	e8 b1 fd ff ff       	call   5460 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    56af:	4c 89 fa             	mov    %r15,%rdx
    56b2:	bf 01 00 00 00       	mov    $0x1,%edi
    56b7:	31 c0                	xor    %eax,%eax
    56b9:	48 8d 35 87 2a 00 00 	lea    0x2a87(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    56c0:	e8 4b ce ff ff       	call   2510 <__printf_chk@plt>
}
    56c5:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    56c9:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    56d2:	0f 85 20 01 00 00    	jne    57f8 <handle_get_method+0x208>
    56d8:	48 81 c4 a8 04 00 00 	add    $0x4a8,%rsp
    56df:	5b                   	pop    %rbx
    56e0:	41 5c                	pop    %r12
    56e2:	41 5d                	pop    %r13
    56e4:	41 5e                	pop    %r14
    56e6:	41 5f                	pop    %r15
    56e8:	5d                   	pop    %rbp
    56e9:	c3                   	ret
    56ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    56f0:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    56f5:	48 8d bd c6 fb ff ff 	lea    -0x43a(%rbp),%rdi
    56fc:	4c 89 e6             	mov    %r12,%rsi
    56ff:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5704:	66 89 95 c4 fb ff ff 	mov    %dx,-0x43c(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    570b:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    570e:	4c 8d bd c0 fb ff ff 	lea    -0x440(%rbp),%r15
    5715:	c7 85 c0 fb ff ff 70 75 62 6c 	movl   $0x6c627570,-0x440(%rbp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    571f:	e8 4c cd ff ff       	call   2470 <__memcpy_chk@plt>
    5724:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5729:	49 8d 7c 1f 06       	lea    0x6(%r15,%rbx,1),%rdi
    572e:	ba 0b 00 00 00       	mov    $0xb,%edx
    5733:	48 29 d9             	sub    %rbx,%rcx
    5736:	48 8d 35 d5 29 00 00 	lea    0x29d5(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    573d:	e8 2e cd ff ff       	call   2470 <__memcpy_chk@plt>
    5742:	e9 28 ff ff ff       	jmp    566f <handle_get_method+0x7f>
    5747:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5750:	bf 70 00 00 00       	mov    $0x70,%edi
    5755:	e8 76 cd ff ff       	call   24d0 <malloc@plt>
    575a:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    575d:	48 85 c0             	test   %rax,%rax
    5760:	0f 84 97 00 00 00    	je     57fd <handle_get_method+0x20d>
            req->client_socket = client_socket;
    5766:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    576a:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    5771:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5775:	4c 89 ff             	mov    %r15,%rdi
            req->iovec_count = 6;
    5778:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    577f:	e8 5c f5 ff ff       	call   4ce0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5784:	48 8b b5 60 fb ff ff 	mov    -0x4a0(%rbp),%rsi
    578b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    578f:	4c 89 ff             	mov    %r15,%rdi
    5792:	e8 79 fa ff ff       	call   5210 <copy_file_contents>
    5797:	4c 89 fa             	mov    %r15,%rdx
    579a:	bf 01 00 00 00       	mov    $0x1,%edi
    579f:	31 c0                	xor    %eax,%eax
    57a1:	48 8b 8d 60 fb ff ff 	mov    -0x4a0(%rbp),%rcx
    57a8:	48 8d 35 86 29 00 00 	lea    0x2986(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    57af:	e8 5c cd ff ff       	call   2510 <__printf_chk@plt>
            add_write_request(req, ring);
    57b4:	4c 89 f6             	mov    %r14,%rsi
    57b7:	48 89 df             	mov    %rbx,%rdi
    57ba:	e8 11 fb ff ff       	call   52d0 <add_write_request>
    57bf:	e9 01 ff ff ff       	jmp    56c5 <handle_get_method+0xd5>
    57c4:	0f 1f 40 00          	nopl   0x0(%rax)
    57c8:	4c 89 fa             	mov    %r15,%rdx
    57cb:	4c 89 e1             	mov    %r12,%rcx
    57ce:	48 8d 35 48 29 00 00 	lea    0x2948(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    57d5:	31 c0                	xor    %eax,%eax
    57d7:	bf 01 00 00 00       	mov    $0x1,%edi
    57dc:	e8 2f cd ff ff       	call   2510 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    57e1:	48 8b 3d 28 58 00 00 	mov    0x5828(%rip),%rdi        # b010 <http_404_content>
    57e8:	4c 89 f2             	mov    %r14,%rdx
    57eb:	44 89 ee             	mov    %r13d,%esi
    57ee:	e8 6d fc ff ff       	call   5460 <_send_static_string_content>
}
    57f3:	e9 cd fe ff ff       	jmp    56c5 <handle_get_method+0xd5>
}
    57f8:	e8 c3 cb ff ff       	call   23c0 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    57fd:	48 8b 0d 1c 58 00 00 	mov    0x581c(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5804:	ba 28 00 00 00       	mov    $0x28,%edx
    5809:	be 01 00 00 00       	mov    $0x1,%esi
    580e:	48 8d 3d ab 2d 00 00 	lea    0x2dab(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    5815:	e8 86 cd ff ff       	call   25a0 <fwrite@plt>
        exit(1);
    581a:	bf 01 00 00 00       	mov    $0x1,%edi
    581f:	e8 5c cd ff ff       	call   2580 <exit@plt>
    5824:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    582f:	90                   	nop

0000000000005830 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5830:	f3 0f 1e fa          	endbr64
    5834:	55                   	push   %rbp
    5835:	48 89 e5             	mov    %rsp,%rbp
    5838:	41 57                	push   %r15
    583a:	41 56                	push   %r14
    583c:	41 55                	push   %r13
    583e:	41 54                	push   %r12
    5840:	53                   	push   %rbx
    5841:	48 83 ec 28          	sub    $0x28,%rsp
    5845:	ff 15 9d 57 00 00    	call   *0x579d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    method = strtok_r(method_buffer, " ", &saveptr);
    584b:	4c 8d 35 5a 28 00 00 	lea    0x285a(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5852:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    585b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    585f:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5861:	4c 8d 7d c0          	lea    -0x40(%rbp),%r15
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5865:	41 89 f4             	mov    %esi,%r12d
    5868:	49 89 d5             	mov    %rdx,%r13
    method = strtok_r(method_buffer, " ", &saveptr);
    586b:	4c 89 f6             	mov    %r14,%rsi
    586e:	4c 89 fa             	mov    %r15,%rdx
    5871:	e8 aa cb ff ff       	call   2420 <strtok_r@plt>
    for (; *str; ++str)
    5876:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    5879:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    587c:	84 d2                	test   %dl,%dl
    587e:	88 55 bf             	mov    %dl,-0x41(%rbp)
    5881:	74 22                	je     58a5 <handle_http_method+0x75>
        *str = (char)tolower(*str);
    5883:	e8 88 cd ff ff       	call   2610 <__ctype_tolower_loc@plt>
    5888:	48 0f be 55 bf       	movsbq -0x41(%rbp),%rdx
    588d:	48 89 d9             	mov    %rbx,%rcx
    5890:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    5893:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    5897:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    589a:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    589d:	48 0f be 11          	movsbq (%rcx),%rdx
    58a1:	84 d2                	test   %dl,%dl
    58a3:	75 eb                	jne    5890 <handle_http_method+0x60>
    path = strtok_r(NULL, " ", &saveptr);
    58a5:	4c 89 fa             	mov    %r15,%rdx
    58a8:	4c 89 f6             	mov    %r14,%rsi
    58ab:	31 ff                	xor    %edi,%edi
    58ad:	e8 6e cb ff ff       	call   2420 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    58b2:	48 8d 35 a1 28 00 00 	lea    0x28a1(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    58b9:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    58bc:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    58bf:	e8 8c cb ff ff       	call   2450 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    58c4:	4c 89 ea             	mov    %r13,%rdx
    58c7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    58ca:	85 c0                	test   %eax,%eax
    58cc:	75 2a                	jne    58f8 <handle_http_method+0xc8>
        handle_get_method(path, client_socket, ring);
    58ce:	4c 89 f7             	mov    %r14,%rdi
    58d1:	e8 1a fd ff ff       	call   55f0 <handle_get_method>
}
    58d6:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    58da:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    58e3:	75 21                	jne    5906 <handle_http_method+0xd6>
    58e5:	48 83 c4 28          	add    $0x28,%rsp
    58e9:	5b                   	pop    %rbx
    58ea:	41 5c                	pop    %r12
    58ec:	41 5d                	pop    %r13
    58ee:	41 5e                	pop    %r14
    58f0:	41 5f                	pop    %r15
    58f2:	5d                   	pop    %rbp
    58f3:	c3                   	ret
    58f4:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    58f8:	48 8b 3d 19 57 00 00 	mov    0x5719(%rip),%rdi        # b018 <unimplemented_content>
    58ff:	e8 5c fb ff ff       	call   5460 <_send_static_string_content>
}
    5904:	eb d0                	jmp    58d6 <handle_http_method+0xa6>
    5906:	e8 b5 ca ff ff       	call   23c0 <__stack_chk_fail@plt>
    590b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005910 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5910:	f3 0f 1e fa          	endbr64
    5914:	55                   	push   %rbp
    5915:	48 89 e5             	mov    %rsp,%rbp
    5918:	ff 15 ca 56 00 00    	call   *0x56ca(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    for (int i = 0; i < dest_sz; i++) {
    591e:	85 d2                	test   %edx,%edx
    5920:	7e 36                	jle    5958 <get_line+0x48>
    5922:	48 63 d2             	movslq %edx,%rdx
    5925:	48 83 c7 01          	add    $0x1,%rdi
    5929:	48 01 f2             	add    %rsi,%rdx
    592c:	eb 0f                	jmp    593d <get_line+0x2d>
    592e:	66 90                	xchg   %ax,%ax
    5930:	48 83 c6 01          	add    $0x1,%rsi
    5934:	48 83 c7 01          	add    $0x1,%rdi
    5938:	48 39 d6             	cmp    %rdx,%rsi
    593b:	74 1b                	je     5958 <get_line+0x48>
        dest[i] = src[i];
    593d:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5941:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5943:	3c 0d                	cmp    $0xd,%al
    5945:	75 e9                	jne    5930 <get_line+0x20>
    5947:	80 3f 0a             	cmpb   $0xa,(%rdi)
    594a:	75 e4                	jne    5930 <get_line+0x20>
            return 0;
    594c:	31 c0                	xor    %eax,%eax
            dest[i] = '\0';
    594e:	c6 06 00             	movb   $0x0,(%rsi)
}
    5951:	5d                   	pop    %rbp
    5952:	c3                   	ret
    5953:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return 1;
    5958:	b8 01 00 00 00       	mov    $0x1,%eax
}
    595d:	5d                   	pop    %rbp
    595e:	c3                   	ret
    595f:	90                   	nop

0000000000005960 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5960:	f3 0f 1e fa          	endbr64
    5964:	55                   	push   %rbp
    5965:	48 89 e5             	mov    %rsp,%rbp
    5968:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    596f:	ff 15 73 56 00 00    	call   *0x5673(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    5975:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    5979:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5982:	48 89 45 f8          	mov    %rax,-0x8(%rbp)
    5986:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5988:	4c 8d 95 f0 fb ff ff 	lea    -0x410(%rbp),%r10
    598f:	4c 8d 4d f0          	lea    -0x10(%rbp),%r9
    5993:	4c 89 d0             	mov    %r10,%rax
    5996:	eb 15                	jmp    59ad <handle_client_request+0x4d>
    5998:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    59a0:	48 83 c0 01          	add    $0x1,%rax
    59a4:	48 83 c1 01          	add    $0x1,%rcx
    59a8:	4c 39 c8             	cmp    %r9,%rax
    59ab:	74 43                	je     59f0 <handle_client_request+0x90>
        dest[i] = src[i];
    59ad:	44 0f b6 01          	movzbl (%rcx),%r8d
    59b1:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    59b4:	41 80 f8 0d          	cmp    $0xd,%r8b
    59b8:	75 e6                	jne    59a0 <handle_client_request+0x40>
    59ba:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    59be:	75 e0                	jne    59a0 <handle_client_request+0x40>
            dest[i] = '\0';
    59c0:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    59c3:	8b 47 08             	mov    0x8(%rdi),%eax
    59c6:	48 89 f2             	mov    %rsi,%rdx
    59c9:	4c 89 d7             	mov    %r10,%rdi
    59cc:	89 c6                	mov    %eax,%esi
    59ce:	e8 5d fe ff ff       	call   5830 <handle_http_method>
}
    59d3:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    59d7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    59e0:	75 35                	jne    5a17 <handle_client_request+0xb7>
    59e2:	c9                   	leave
    59e3:	31 c0                	xor    %eax,%eax
    59e5:	c3                   	ret
    59e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    59f0:	48 8b 0d 29 56 00 00 	mov    0x5629(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    59f7:	ba 12 00 00 00       	mov    $0x12,%edx
    59fc:	be 01 00 00 00       	mov    $0x1,%esi
    5a01:	48 8d 3d 56 27 00 00 	lea    0x2756(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5a08:	e8 93 cb ff ff       	call   25a0 <fwrite@plt>
        exit(1);
    5a0d:	bf 01 00 00 00       	mov    $0x1,%edi
    5a12:	e8 69 cb ff ff       	call   2580 <exit@plt>
}
    5a17:	e8 a4 c9 ff ff       	call   23c0 <__stack_chk_fail@plt>
    5a1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005a20 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5a20:	f3 0f 1e fa          	endbr64
    5a24:	55                   	push   %rbp
    5a25:	48 89 e5             	mov    %rsp,%rbp
    5a28:	41 54                	push   %r12
    5a2a:	53                   	push   %rbx
    5a2b:	ff 15 b7 55 00 00    	call   *0x55b7(%rip)        # afe8 <mcount@GLIBC_2.2.5>
	unsigned int head, next = sq->sqe_tail + 1;
    5a31:	8b 41 44             	mov    0x44(%rcx),%eax
    5a34:	83 c0 01             	add    $0x1,%eax
    5a37:	48 89 cb             	mov    %rcx,%rbx
	if (ring->flags & IORING_SETUP_SQE128)
    5a3a:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    5a40:	4c 8b 03             	mov    (%rbx),%r8
    5a43:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5a46:	f6 c1 02             	test   $0x2,%cl
    5a49:	74 00                	je     5a4b <add_accept_request+0x2b>
	if (next - head <= sq->ring_entries) {
    5a4b:	41 89 c0             	mov    %eax,%r8d
    5a4e:	45 29 c8             	sub    %r9d,%r8d
    5a51:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    5a55:	0f 82 38 cc ff ff    	jb     2693 <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5a5b:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a5e:	44 8b 63 44          	mov    0x44(%rbx),%r12d
    5a62:	44 23 63 58          	and    0x58(%rbx),%r12d
		sq->sqe_tail = next;
    5a66:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5a69:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5a6c:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5a70:	41 d3 e4             	shl    %cl,%r12d
    5a73:	49 c1 e4 06          	shl    $0x6,%r12
    5a77:	4c 03 63 38          	add    0x38(%rbx),%r12
	sqe->fd = fd;
    5a7b:	41 89 7c 24 04       	mov    %edi,0x4(%r12)
  struct Request *req = malloc(sizeof(*req));
    5a80:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5a85:	41 c7 04 24 0d 00 00 00 	movl   $0xd,(%r12)
	sqe->off = offset;
    5a8d:	49 89 54 24 08       	mov    %rdx,0x8(%r12)
	sqe->addr = (unsigned long) addr;
    5a92:	49 89 74 24 10       	mov    %rsi,0x10(%r12)
	sqe->buf_index = 0;
    5a97:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->len = len;
    5aa0:	49 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%r12)
	sqe->addr3 = 0;
    5aa9:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
    5aaf:	e8 1c ca ff ff       	call   24d0 <malloc@plt>
  io_uring_submit(ring);
    5ab4:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5ab7:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    5abd:	49 89 44 24 20       	mov    %rax,0x20(%r12)
}
    5ac2:	5b                   	pop    %rbx
    5ac3:	41 5c                	pop    %r12
    5ac5:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5ac6:	e9 05 c9 ff ff       	jmp    23d0 <io_uring_submit@plt>
    5acb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005ad0 <io_thread>:
void* io_thread(void *arg) {
    5ad0:	f3 0f 1e fa          	endbr64
    5ad4:	55                   	push   %rbp
    5ad5:	48 89 e5             	mov    %rsp,%rbp
    5ad8:	41 57                	push   %r15
    5ada:	41 56                	push   %r14
    5adc:	41 55                	push   %r13
    5ade:	41 54                	push   %r12
    5ae0:	53                   	push   %rbx
    5ae1:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    5ae8:	ff 15 fa 54 00 00    	call   *0x54fa(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5aee:	31 d2                	xor    %edx,%edx
  struct io_uring ring = *data->ring;
    5af0:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5af9:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    5afd:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5b01:	48 8d 9d e0 fa ff ff 	lea    -0x520(%rbp),%rbx
void* io_thread(void *arg) {
    5b08:	49 89 fc             	mov    %rdi,%r12
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5b0b:	bf 00 01 00 00       	mov    $0x100,%edi
    5b10:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    5b13:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5b17:	0f 29 8d e0 fa ff ff 	movaps %xmm1,-0x520(%rbp)
    5b1e:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5b23:	0f 29 95 f0 fa ff ff 	movaps %xmm2,-0x510(%rbp)
    5b2a:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5b2f:	0f 29 9d 00 fb ff ff 	movaps %xmm3,-0x500(%rbp)
    5b36:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5b3b:	0f 29 a5 10 fb ff ff 	movaps %xmm4,-0x4f0(%rbp)
    5b42:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5b47:	0f 29 ad 20 fb ff ff 	movaps %xmm5,-0x4e0(%rbp)
    5b4e:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5b53:	0f 29 b5 30 fb ff ff 	movaps %xmm6,-0x4d0(%rbp)
    5b5a:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5b5f:	0f 29 bd 40 fb ff ff 	movaps %xmm7,-0x4c0(%rbp)
    5b66:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5b6b:	0f 29 8d 50 fb ff ff 	movaps %xmm1,-0x4b0(%rbp)
    5b72:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5b7a:	0f 29 95 60 fb ff ff 	movaps %xmm2,-0x4a0(%rbp)
    5b81:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5b89:	0f 29 9d 70 fb ff ff 	movaps %xmm3,-0x490(%rbp)
    5b90:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5b98:	0f 29 a5 80 fb ff ff 	movaps %xmm4,-0x480(%rbp)
    5b9f:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5ba7:	0f 29 ad 90 fb ff ff 	movaps %xmm5,-0x470(%rbp)
    5bae:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5bb6:	0f 29 b5 a0 fb ff ff 	movaps %xmm6,-0x460(%rbp)
    5bbd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5bc4:	48 89 85 b0 fb ff ff 	mov    %rax,-0x450(%rbp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5bcb:	e8 d0 c8 ff ff       	call   24a0 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5bd0:	49 8b 7c 24 58       	mov    0x58(%r12),%rdi
    5bd5:	31 f6                	xor    %esi,%esi
    5bd7:	e8 e4 c9 ff ff       	call   25c0 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5bdc:	31 d2                	xor    %edx,%edx
    5bde:	be 01 00 00 00       	mov    $0x1,%esi
    5be3:	bf 02 00 00 00       	mov    $0x2,%edi
    5be8:	e8 43 ca ff ff       	call   2630 <socket@plt>
    5bed:	89 85 ac fa ff ff    	mov    %eax,-0x554(%rbp)
  if (sock == -1)
    5bf3:	83 f8 ff             	cmp    $0xffffffff,%eax
    5bf6:	0f 84 d9 ca ff ff    	je     26d5 <io_thread.cold+0x38>
    5bfc:	89 c7                	mov    %eax,%edi
  if (setsockopt(sock,
    5bfe:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5c04:	ba 02 00 00 00       	mov    $0x2,%edx
    5c09:	be 01 00 00 00       	mov    $0x1,%esi
    5c0e:	48 8d 8d b0 fa ff ff 	lea    -0x550(%rbp),%rcx
  int enable = 1;
    5c15:	c7 85 b0 fa ff ff 01 00 00 00 	movl   $0x1,-0x550(%rbp)
  if (setsockopt(sock,
    5c1f:	e8 5c c7 ff ff       	call   2380 <setsockopt@plt>
    5c24:	85 c0                	test   %eax,%eax
    5c26:	0f 88 7d ca ff ff    	js     26a9 <io_thread.cold+0xc>
  if (bind(sock,
    5c2c:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5c32:	ba 10 00 00 00       	mov    $0x10,%edx
  return __builtin___memset_chk (__dest, __ch, __len,
    5c37:	48 8d b5 c0 fa ff ff 	lea    -0x540(%rbp),%rsi
    5c3e:	48 c7 85 c4 fa ff ff 00 00 00 00 	movq   $0x0,-0x53c(%rbp)
    5c49:	c7 85 cc fa ff ff 00 00 00 00 	movl   $0x0,-0x534(%rbp)
  srv_addr.sin_family = AF_INET;
    5c53:	c7 85 c0 fa ff ff 02 00 18 db 	movl   $0xdb180002,-0x540(%rbp)
  if (bind(sock,
    5c5d:	e8 be c8 ff ff       	call   2520 <bind@plt>
    5c62:	85 c0                	test   %eax,%eax
    5c64:	0f 88 77 ca ff ff    	js     26e1 <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5c6a:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5c70:	be 0a 00 00 00       	mov    $0xa,%esi
    5c75:	e8 66 c8 ff ff       	call   24e0 <listen@plt>
    5c7a:	85 c0                	test   %eax,%eax
    5c7c:	0f 88 33 ca ff ff    	js     26b5 <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5c82:	ba db 18 00 00       	mov    $0x18db,%edx
    5c87:	48 8d 35 15 25 00 00 	lea    0x2515(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5c8e:	bf 01 00 00 00       	mov    $0x1,%edi
    5c93:	31 c0                	xor    %eax,%eax
    5c95:	e8 76 c8 ff ff       	call   2510 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5c9a:	48 8d 85 d0 fa ff ff 	lea    -0x530(%rbp),%rax
    5ca1:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5ca7:	48 89 d9             	mov    %rbx,%rcx
    5caa:	48 8d 95 b4 fa ff ff 	lea    -0x54c(%rbp),%rdx
    5cb1:	48 89 c6             	mov    %rax,%rsi
  socklen_t client_addr_len = sizeof(client_addr);
    5cb4:	c7 85 b4 fa ff ff 10 00 00 00 	movl   $0x10,-0x54c(%rbp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5cbe:	48 89 95 88 fa ff ff 	mov    %rdx,-0x578(%rbp)
    5cc5:	48 89 85 90 fa ff ff 	mov    %rax,-0x570(%rbp)
    5ccc:	e8 4f fd ff ff       	call   5a20 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5cd1:	bf 01 00 00 00       	mov    $0x1,%edi
    5cd6:	be 10 00 00 00       	mov    $0x10,%esi
    5cdb:	e8 60 c7 ff ff       	call   2440 <calloc@plt>
    void *buf = malloc(size);
    5ce0:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5ce5:	49 89 c6             	mov    %rax,%r14
    void *buf = malloc(size);
    5ce8:	e8 e3 c7 ff ff       	call   24d0 <malloc@plt>
    if (!buf) {
    5ced:	48 85 c0             	test   %rax,%rax
    5cf0:	0f 84 cf 04 00 00    	je     61c5 <io_thread+0x6f5>
  iov->iov_base = zh_malloc(10);
    5cf6:	49 89 06             	mov    %rax,(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    5cf9:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5cff:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
  iov->iov_len = 10;
    5d05:	49 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    5d0d:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5d10:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    5d17:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5d19:	f6 c1 02             	test   $0x2,%cl
    5d1c:	0f 85 2e 04 00 00    	jne    6150 <io_thread+0x680>
	if (next - head <= sq->ring_entries) {
    5d22:	89 d0                	mov    %edx,%eax
    5d24:	29 f0                	sub    %esi,%eax
    5d26:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    5d2c:	0f 82 99 c9 ff ff    	jb     26cb <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5d32:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d35:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    5d3b:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5d3f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d42:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5d48:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5d4b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5d51:	49 8d 74 24 60       	lea    0x60(%r12),%rsi
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5d56:	41 8b 54 24 60       	mov    0x60(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d5b:	d3 e0                	shl    %cl,%eax
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5d5d:	48 89 b5 98 fa ff ff 	mov    %rsi,-0x568(%rbp)
    5d64:	48 c1 e0 06          	shl    $0x6,%rax
    5d68:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    5d6f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5d75:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5d78:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5d80:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    5d84:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5d8c:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5d94:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5d98:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5d9c:	e8 2f c6 ff ff       	call   23d0 <io_uring_submit@plt>
  while (data->running == 1) {
    5da1:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5da7:	4c 8d 8d b8 fa ff ff 	lea    -0x548(%rbp),%r9
    5dae:	4c 8d 95 c0 fb ff ff 	lea    -0x440(%rbp),%r10
    5db5:	0f 85 ed 01 00 00    	jne    5fa8 <io_thread+0x4d8>
    5dbb:	4c 89 8d a0 fa ff ff 	mov    %r9,-0x560(%rbp)
    5dc2:	4c 89 95 80 fa ff ff 	mov    %r10,-0x580(%rbp)
    5dc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5dd0:	48 8d 3d e2 23 00 00 	lea    0x23e2(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5dd7:	e8 94 c5 ff ff       	call   2370 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5ddc:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5de2:	8b bd 90 fb ff ff    	mov    -0x470(%rbp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5de8:	c1 e9 0b             	shr    $0xb,%ecx
    5deb:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5dee:	48 8b 85 50 fb ff ff 	mov    -0x4b0(%rbp),%rax
    5df5:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5df7:	48 8b b5 48 fb ff ff 	mov    -0x4b8(%rbp),%rsi
    5dfe:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5e00:	39 d0                	cmp    %edx,%eax
    5e02:	74 34                	je     5e38 <io_thread+0x368>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5e04:	89 f8                	mov    %edi,%eax
    5e06:	21 d0                	and    %edx,%eax
    5e08:	d3 e0                	shl    %cl,%eax
    5e0a:	48 c1 e0 04          	shl    $0x4,%rax
    5e0e:	48 03 85 78 fb ff ff 	add    -0x488(%rbp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5e15:	f6 85 a9 fb ff ff 01 	testb  $0x1,-0x457(%rbp)
    5e1c:	0f 85 be 01 00 00    	jne    5fe0 <io_thread+0x510>
    5e22:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5e26:	0f 85 2c 03 00 00    	jne    6158 <io_thread+0x688>
			if (cqe->res < 0)
    5e2c:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5e2f:	83 c2 01             	add    $0x1,%edx
    5e32:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5e34:	85 c0                	test   %eax,%eax
    5e36:	79 b6                	jns    5dee <io_thread+0x31e>
	*cqe_ptr = cqe;
    5e38:	48 c7 85 b8 fa ff ff 00 00 00 00 	movq   $0x0,-0x548(%rbp)
	return err;
    5e43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5e48:	48 8b b5 a0 fa ff ff 	mov    -0x560(%rbp),%rsi
    5e4f:	45 31 c0             	xor    %r8d,%r8d
    5e52:	31 d2                	xor    %edx,%edx
    5e54:	48 89 df             	mov    %rbx,%rdi
    5e57:	b9 01 00 00 00       	mov    $0x1,%ecx
    5e5c:	e8 9f c6 ff ff       	call   2500 <__io_uring_get_cqe@plt>
    5e61:	41 89 c5             	mov    %eax,%r13d
      if (cqe->user_data == 1) {
    5e64:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    5e6b:	48 83 38 01          	cmpq   $0x1,(%rax)
    5e6f:	0f 84 f3 02 00 00    	je     6168 <io_thread+0x698>
    5e75:	48 8d 3d 63 23 00 00 	lea    0x2363(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5e7c:	e8 ef c4 ff ff       	call   2370 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5e81:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    5e88:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    5e8b:	45 85 ed             	test   %r13d,%r13d
    5e8e:	0f 88 09 c8 ff ff    	js     269d <io_thread.cold>
      if (cqe->res < 0) {
    5e94:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5e97:	45 8b 07             	mov    (%r15),%r8d
      if (cqe->res < 0) {
    5e9a:	85 c0                	test   %eax,%eax
    5e9c:	0f 88 e5 02 00 00    	js     6187 <io_thread+0x6b7>
      switch (req->event_type) {
    5ea2:	41 83 f8 01          	cmp    $0x1,%r8d
    5ea6:	0f 84 84 01 00 00    	je     6030 <io_thread+0x560>
    5eac:	41 83 f8 02          	cmp    $0x2,%r8d
    5eb0:	0f 84 aa 01 00 00    	je     6060 <io_thread+0x590>
    5eb6:	45 85 c0             	test   %r8d,%r8d
    5eb9:	0f 85 59 01 00 00    	jne    6018 <io_thread+0x548>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5ebf:	48 8b 95 88 fa ff ff 	mov    -0x578(%rbp),%rdx
    5ec6:	48 8b b5 90 fa ff ff 	mov    -0x570(%rbp),%rsi
    5ecd:	48 89 d9             	mov    %rbx,%rcx
    5ed0:	8b bd ac fa ff ff    	mov    -0x554(%rbp),%edi
    5ed6:	e8 45 fb ff ff       	call   5a20 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5edb:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    5ee2:	48 89 de             	mov    %rbx,%rsi
    5ee5:	8b 78 08             	mov    0x8(%rax),%edi
    5ee8:	e8 83 f4 ff ff       	call   5370 <add_read_request>
              free(req);
    5eed:	4c 89 ff             	mov    %r15,%rdi
    5ef0:	e8 4b c4 ff ff       	call   2340 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5ef5:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
	if (cqe)
    5efc:	48 85 c0             	test   %rax,%rax
    5eff:	0f 85 13 01 00 00    	jne    6018 <io_thread+0x548>
	unsigned int head, next = sq->sqe_tail + 1;
    5f05:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5f0b:	8b 8d a0 fb ff ff    	mov    -0x460(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5f11:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5f14:	48 8b 85 e0 fa ff ff 	mov    -0x520(%rbp),%rax
    5f1b:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5f1d:	f6 c1 02             	test   $0x2,%cl
    5f20:	74 00                	je     5f22 <io_thread+0x452>
	if (next - head <= sq->ring_entries) {
    5f22:	89 d0                	mov    %edx,%eax
    5f24:	29 f0                	sub    %esi,%eax
    5f26:	39 85 3c fb ff ff    	cmp    %eax,-0x4c4(%rbp)
    5f2c:	0f 82 8f c7 ff ff    	jb     26c1 <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5f32:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f35:	8b 85 24 fb ff ff    	mov    -0x4dc(%rbp),%eax
	sqe->addr3 = 0;
    5f3b:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5f3f:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f42:	23 85 38 fb ff ff    	and    -0x4c8(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5f48:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    5f4b:	89 95 24 fb ff ff    	mov    %edx,-0x4dc(%rbp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f51:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5f53:	41 8b 54 24 60       	mov    0x60(%r12),%edx
	sqe->user_data = (unsigned long) data;
    5f58:	48 8b b5 98 fa ff ff 	mov    -0x568(%rbp),%rsi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f5f:	48 c1 e0 06          	shl    $0x6,%rax
    5f63:	48 03 85 18 fb ff ff 	add    -0x4e8(%rbp),%rax
	sqe->opcode = (__u8) op;
    5f6a:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5f70:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5f73:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5f7b:	4c 89 70 10          	mov    %r14,0x10(%rax)
	sqe->len = len;
    5f7f:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5f87:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5f8f:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5f93:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5f97:	e8 34 c4 ff ff       	call   23d0 <io_uring_submit@plt>
  while (data->running == 1) {
    5f9c:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5fa2:	0f 84 28 fe ff ff    	je     5dd0 <io_thread+0x300>
    5fa8:	48 8d 3d 69 22 00 00 	lea    0x2269(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5faf:	e8 bc c3 ff ff       	call   2370 <puts@plt>
}
    5fb4:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    5fb8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5fc1:	0f 85 25 02 00 00    	jne    61ec <io_thread+0x71c>
    5fc7:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5fce:	31 c0                	xor    %eax,%eax
    5fd0:	5b                   	pop    %rbx
    5fd1:	41 5c                	pop    %r12
    5fd3:	41 5d                	pop    %r13
    5fd5:	41 5e                	pop    %r14
    5fd7:	41 5f                	pop    %r15
    5fd9:	5d                   	pop    %rbp
    5fda:	c3                   	ret
    5fdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    5fe0:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5fe7:	48 85 c0             	test   %rax,%rax
    5fea:	0f 84 58 fe ff ff    	je     5e48 <io_thread+0x378>
      if (cqe->user_data == 1) {
    5ff0:	48 83 38 01          	cmpq   $0x1,(%rax)
    5ff4:	0f 84 6e 01 00 00    	je     6168 <io_thread+0x698>
    5ffa:	48 8d 3d de 21 00 00 	lea    0x21de(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    6001:	e8 6a c3 ff ff       	call   2370 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    6006:	48 8b 95 b8 fa ff ff 	mov    -0x548(%rbp),%rdx
    600d:	4c 8b 3a             	mov    (%rdx),%r15
      if (ret < 0)
    6010:	e9 7f fe ff ff       	jmp    5e94 <io_thread+0x3c4>
    6015:	0f 1f 00             	nopl   (%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6018:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
    601f:	8b 02                	mov    (%rdx),%eax
    6021:	83 c0 01             	add    $0x1,%eax
    6024:	89 02                	mov    %eax,(%rdx)
}
    6026:	e9 da fe ff ff       	jmp    5f05 <io_thread+0x435>
    602b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              if (!cqe->res) {
    6030:	85 c0                	test   %eax,%eax
    6032:	75 7c                	jne    60b0 <io_thread+0x5e0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6034:	48 8b 0d e5 4f 00 00 	mov    0x4fe5(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    603b:	ba 0f 00 00 00       	mov    $0xf,%edx
    6040:	be 01 00 00 00       	mov    $0x1,%esi
    6045:	48 8d 3d bc 21 00 00 	lea    0x21bc(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    604c:	e8 4f c5 ff ff       	call   25a0 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    6051:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
    6058:	e9 9f fe ff ff       	jmp    5efc <io_thread+0x42c>
    605d:	0f 1f 00             	nopl   (%rax)
              for (int i = 0; i < req->iovec_count; i++) {
    6060:	41 8b 47 04          	mov    0x4(%r15),%eax
    6064:	45 31 ed             	xor    %r13d,%r13d
    6067:	85 c0                	test   %eax,%eax
    6069:	7e 20                	jle    608b <io_thread+0x5bb>
    606b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                  free(req->iov[i].iov_base);
    6070:	4c 89 e8             	mov    %r13,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    6073:	49 83 c5 01          	add    $0x1,%r13
                  free(req->iov[i].iov_base);
    6077:	48 c1 e0 04          	shl    $0x4,%rax
    607b:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    6080:	e8 bb c2 ff ff       	call   2340 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    6085:	45 39 6f 04          	cmp    %r13d,0x4(%r15)
    6089:	7f e5                	jg     6070 <io_thread+0x5a0>
              close(req->client_socket);
    608b:	41 8b 7f 08          	mov    0x8(%r15),%edi
    608f:	e8 7c c3 ff ff       	call   2410 <close@plt>
              free(req);
    6094:	4c 89 ff             	mov    %r15,%rdi
    6097:	e8 a4 c2 ff ff       	call   2340 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    609c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    60a3:	e9 54 fe ff ff       	jmp    5efc <io_thread+0x42c>
    60a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    60b0:	49 8b 57 10          	mov    0x10(%r15),%rdx
    60b4:	48 8b 85 80 fa ff ff 	mov    -0x580(%rbp),%rax
    60bb:	48 8d 75 c0          	lea    -0x40(%rbp),%rsi
    60bf:	eb 14                	jmp    60d5 <io_thread+0x605>
    60c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    60c8:	48 83 c0 01          	add    $0x1,%rax
    60cc:	48 83 c2 01          	add    $0x1,%rdx
    60d0:	48 39 c6             	cmp    %rax,%rsi
    60d3:	74 4b                	je     6120 <io_thread+0x650>
        dest[i] = src[i];
    60d5:	0f b6 0a             	movzbl (%rdx),%ecx
    60d8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    60da:	80 f9 0d             	cmp    $0xd,%cl
    60dd:	75 e9                	jne    60c8 <io_thread+0x5f8>
    60df:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    60e3:	75 e3                	jne    60c8 <io_thread+0x5f8>
            dest[i] = '\0';
    60e5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    60e8:	48 8b bd 80 fa ff ff 	mov    -0x580(%rbp),%rdi
    60ef:	48 89 da             	mov    %rbx,%rdx
    60f2:	41 8b 77 08          	mov    0x8(%r15),%esi
    60f6:	e8 35 f7 ff ff       	call   5830 <handle_http_method>
              free(req->iov[0].iov_base);
    60fb:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    60ff:	e8 3c c2 ff ff       	call   2340 <free@plt>
              free(req);
    6104:	4c 89 ff             	mov    %r15,%rdi
    6107:	e8 34 c2 ff ff       	call   2340 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    610c:	48 8b 85 b8 fa ff ff 	mov    -0x548(%rbp),%rax
              break;
    6113:	e9 e4 fd ff ff       	jmp    5efc <io_thread+0x42c>
    6118:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6120:	48 8b 0d f9 4e 00 00 	mov    0x4ef9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6127:	ba 12 00 00 00       	mov    $0x12,%edx
    612c:	be 01 00 00 00       	mov    $0x1,%esi
    6131:	48 8d 3d 26 20 00 00 	lea    0x2026(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6138:	e8 63 c4 ff ff       	call   25a0 <fwrite@plt>
        exit(1);
    613d:	bf 01 00 00 00       	mov    $0x1,%edi
    6142:	e8 39 c4 ff ff       	call   2580 <exit@plt>
    6147:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    6150:	e9 cd fb ff ff       	jmp    5d22 <io_thread+0x252>
    6155:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    6158:	48 89 85 b8 fa ff ff 	mov    %rax,-0x548(%rbp)
	return err;
    615f:	e9 8c fe ff ff       	jmp    5ff0 <io_thread+0x520>
    6164:	0f 1f 40 00          	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6168:	48 8b 95 48 fb ff ff 	mov    -0x4b8(%rbp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    616f:	48 8d 3d 55 20 00 00 	lea    0x2055(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    6176:	8b 02                	mov    (%rdx),%eax
    6178:	83 c0 01             	add    $0x1,%eax
    617b:	89 02                	mov    %eax,(%rdx)
    617d:	e8 ee c1 ff ff       	call   2370 <puts@plt>
    6182:	e9 21 fe ff ff       	jmp    5fa8 <io_thread+0x4d8>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    6187:	f7 d8                	neg    %eax
    6189:	44 89 85 ac fa ff ff 	mov    %r8d,-0x554(%rbp)
    6190:	89 c7                	mov    %eax,%edi
    6192:	e8 49 c4 ff ff       	call   25e0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6197:	48 8b 3d 82 4e 00 00 	mov    0x4e82(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    619e:	be 01 00 00 00       	mov    $0x1,%esi
    61a3:	44 8b 85 ac fa ff ff 	mov    -0x554(%rbp),%r8d
    61aa:	48 89 c1             	mov    %rax,%rcx
    61ad:	48 8d 15 3c 24 00 00 	lea    0x243c(%rip),%rdx        # 85f0 <_IO_stdin_used+0x5f0>
    61b4:	31 c0                	xor    %eax,%eax
    61b6:	e8 f5 c3 ff ff       	call   25b0 <__fprintf_chk@plt>
          exit(1);
    61bb:	bf 01 00 00 00       	mov    $0x1,%edi
    61c0:	e8 bb c3 ff ff       	call   2580 <exit@plt>
    61c5:	48 8b 0d 54 4e 00 00 	mov    0x4e54(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    61cc:	ba 28 00 00 00       	mov    $0x28,%edx
    61d1:	be 01 00 00 00       	mov    $0x1,%esi
    61d6:	48 8d 3d e3 23 00 00 	lea    0x23e3(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    61dd:	e8 be c3 ff ff       	call   25a0 <fwrite@plt>
        exit(1);
    61e2:	bf 01 00 00 00       	mov    $0x1,%edi
    61e7:	e8 94 c3 ff ff       	call   2580 <exit@plt>
}
    61ec:	e8 cf c1 ff ff       	call   23c0 <__stack_chk_fail@plt>
    61f1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    61fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006200 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    6200:	f3 0f 1e fa          	endbr64
    6204:	55                   	push   %rbp
    6205:	48 89 e5             	mov    %rsp,%rbp
    6208:	41 57                	push   %r15
    620a:	41 56                	push   %r14
    620c:	41 55                	push   %r13
    620e:	41 54                	push   %r12
    6210:	53                   	push   %rbx
    6211:	48 83 ec 08          	sub    $0x8,%rsp
    6215:	ff 15 cd 4d 00 00    	call   *0x4dcd(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    621b:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    6222:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
int barriered_work_ingest(struct BarrierTask *data) {
    6228:	49 89 fd             	mov    %rdi,%r13
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    622b:	85 c9                	test   %ecx,%ecx
    622d:	7e 54                	jle    6283 <barriered_work_ingest+0x83>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    622f:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6233:	45 31 f6             	xor    %r14d,%r14d
    6236:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6240:	4a 8b 04 f7          	mov    (%rdi,%r14,8),%rax
    6244:	4e 8d 3c f5 00 00 00 00 	lea    0x0(,%r14,8),%r15
    624c:	31 db                	xor    %ebx,%ebx
    624e:	8b 10                	mov    (%rax),%edx
    6250:	85 d2                	test   %edx,%edx
    6252:	7e 26                	jle    627a <barriered_work_ingest+0x7a>
    6254:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    6258:	49 89 dc             	mov    %rbx,%r12
    625b:	49 c1 e4 08          	shl    $0x8,%r12
    625f:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    6263:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    626a:	74 2c                	je     6298 <barriered_work_ingest+0x98>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    626c:	48 83 c3 01          	add    $0x1,%rbx
    6270:	39 da                	cmp    %ebx,%edx
    6272:	7f e4                	jg     6258 <barriered_work_ingest+0x58>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6274:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    627a:	49 83 c6 01          	add    $0x1,%r14
    627e:	44 39 f1             	cmp    %r14d,%ecx
    6281:	7f bd                	jg     6240 <barriered_work_ingest+0x40>
}
    6283:	48 83 c4 08          	add    $0x8,%rsp
    6287:	31 c0                	xor    %eax,%eax
    6289:	5b                   	pop    %rbx
    628a:	41 5c                	pop    %r12
    628c:	41 5d                	pop    %r13
    628e:	41 5e                	pop    %r14
    6290:	41 5f                	pop    %r15
    6292:	5d                   	pop    %rbp
    6293:	c3                   	ret
    6294:	0f 1f 40 00          	nopl   0x0(%rax)
        data->ingest_count++;
    6298:	49 83 85 68 01 00 00 01 	addq   $0x1,0x168(%r13)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    62a0:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    62a7:	bf 04 00 00 00       	mov    $0x4,%edi
    62ac:	48 c1 e6 05          	shl    $0x5,%rsi
    62b0:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    62b7:	48 83 c6 10          	add    $0x10,%rsi
    62bb:	e8 d0 c0 ff ff       	call   2390 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    62c0:	49 8b 85 28 01 00 00 	mov    0x128(%r13),%rax
    62c7:	48 8b 40 50          	mov    0x50(%rax),%rax
    62cb:	4a 8b 04 38          	mov    (%rax,%r15,1),%rax
    62cf:	4c 03 60 08          	add    0x8(%rax),%r12
    62d3:	41 8b 84 24 94 00 00 00 	mov    0x94(%r12),%eax
        data->thread->buffers[b]->buffer[x].available = 0;
    62db:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    62e7:	83 c0 01             	add    $0x1,%eax
    62ea:	99                   	cltd
    62eb:	41 f7 bc 24 90 00 00 00 	idivl  0x90(%r12)
    62f3:	41 89 94 24 94 00 00 00 	mov    %edx,0x94(%r12)
        asm volatile ("sfence" ::: "memory");
    62fb:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    62fe:	49 8b b5 28 01 00 00 	mov    0x128(%r13),%rsi
    6305:	48 83 c3 01          	add    $0x1,%rbx
    6309:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    630d:	4a 8b 04 3f          	mov    (%rdi,%r15,1),%rax
    6311:	8b 10                	mov    (%rax),%edx
    6313:	39 da                	cmp    %ebx,%edx
    6315:	0f 8f 39 ff ff ff    	jg     6254 <barriered_work_ingest+0x54>
    631b:	e9 54 ff ff ff       	jmp    6274 <barriered_work_ingest+0x74>

0000000000006320 <barriered_thread>:
void* barriered_thread(void *arg) {
    6320:	f3 0f 1e fa          	endbr64
    6324:	55                   	push   %rbp
    6325:	48 89 e5             	mov    %rsp,%rbp
    6328:	41 57                	push   %r15
    632a:	41 56                	push   %r14
    632c:	41 55                	push   %r13
    632e:	41 54                	push   %r12
    6330:	53                   	push   %rbx
    6331:	48 83 ec 08          	sub    $0x8,%rsp
    6335:	ff 15 ad 4c 00 00    	call   *0x4cad(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  int waiting = 0;
    633b:	45 31 e4             	xor    %r12d,%r12d
  int t = 0;
    633e:	45 31 ed             	xor    %r13d,%r13d
void* barriered_thread(void *arg) {
    6341:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    6344:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6348:	0f 85 1c 02 00 00    	jne    656a <barriered_thread+0x24a>
    if (t >= data->task_count) {
    634e:	8b 43 40             	mov    0x40(%rbx),%eax
    6351:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6358:	41 39 c5             	cmp    %eax,%r13d
    635b:	0f 8d 6f 01 00 00    	jge    64d0 <barriered_thread+0x1b0>
    6361:	49 63 fd             	movslq %r13d,%rdi
    6364:	48 c1 e7 09          	shl    $0x9,%rdi
    6368:	49 89 fe             	mov    %rdi,%r14
    636b:	eb 32                	jmp    639f <barriered_thread+0x7f>
    636d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    6370:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6374:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6378:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    637c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6380:	4c 01 f7             	add    %r14,%rdi
    6383:	e8 78 fe ff ff       	call   6200 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    6388:	8b 43 40             	mov    0x40(%rbx),%eax
    638b:	41 83 c5 01          	add    $0x1,%r13d
    638f:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    6396:	44 39 e8             	cmp    %r13d,%eax
    6399:	0f 8e c1 01 00 00    	jle    6560 <barriered_thread+0x240>
      if (data->tasks[t].available == 1) {
    639f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    63a3:	4a 8d 34 32          	lea    (%rdx,%r14,1),%rsi
    63a7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    63ae:	75 c0                	jne    6370 <barriered_thread+0x50>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    63b0:	8b 7b 28             	mov    0x28(%rbx),%edi
          previous = t - 1;
    63b3:	83 e8 01             	sub    $0x1,%eax
    63b6:	41 8d 4d ff          	lea    -0x1(%r13),%ecx
    63ba:	45 85 ed             	test   %r13d,%r13d
    63bd:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    63c0:	85 ff                	test   %edi,%edi
    63c2:	0f 8e d8 01 00 00    	jle    65a0 <barriered_thread+0x280>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    63c8:	48 63 c8             	movslq %eax,%rcx
    63cb:	48 8b 43 18          	mov    0x18(%rbx),%rax
    63cf:	48 63 d7             	movslq %edi,%rdx
        int prearrive = 0; 
    63d2:	45 31 d2             	xor    %r10d,%r10d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    63d5:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    63dc:	44 8b 86 00 01 00 00 	mov    0x100(%rsi),%r8d
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    63e3:	48 c1 e1 09          	shl    $0x9,%rcx
        int arrived = 0; 
    63e7:	45 31 ff             	xor    %r15d,%r15d
    63ea:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    63ee:	66 90                	xchg   %ax,%ax
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    63f0:	48 8b 10             	mov    (%rax),%rdx
    63f3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    63f7:	49 01 cb             	add    %rcx,%r11
    63fa:	4c 89 da             	mov    %r11,%rdx
    63fd:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6404:	75 04                	jne    640a <barriered_thread+0xea>
            arrived++;
    6406:	41 83 c7 01          	add    $0x1,%r15d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    640a:	44 3b 82 00 01 00 00 	cmp    0x100(%rdx),%r8d
    6411:	75 04                	jne    6417 <barriered_thread+0xf7>
            prearrive++;
    6413:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6417:	48 83 c0 08          	add    $0x8,%rax
    641b:	48 39 c6             	cmp    %rax,%rsi
    641e:	75 d0                	jne    63f0 <barriered_thread+0xd0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    6420:	45 85 d2             	test   %r10d,%r10d
    6423:	0f 84 bf 00 00 00    	je     64e8 <barriered_thread+0x1c8>
    6429:	44 39 d7             	cmp    %r10d,%edi
    642c:	0f 84 b6 00 00 00    	je     64e8 <barriered_thread+0x1c8>
        if (arrived == 0 || arrived == data->thread_count) {
    6432:	45 85 ff             	test   %r15d,%r15d
    6435:	74 0a                	je     6441 <barriered_thread+0x121>
    6437:	44 39 7b 28          	cmp    %r15d,0x28(%rbx)
    643b:	0f 85 b0 01 00 00    	jne    65f1 <barriered_thread+0x2d1>
    6441:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    6445:	4c 01 f2             	add    %r14,%rdx
    6448:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    644f:	45 85 ed             	test   %r13d,%r13d
    6452:	75 14                	jne    6468 <barriered_thread+0x148>
    6454:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    645b:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6462:	0f 8c 18 01 00 00    	jl     6580 <barriered_thread+0x260>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6468:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    646c:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    6470:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    647a:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    647e:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6482:	4c 01 f7             	add    %r14,%rdi
    6485:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    648b:	48 8b 43 38          	mov    0x38(%rbx),%rax
    648f:	4c 01 f0             	add    %r14,%rax
    6492:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6499:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    649c:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    64a1:	83 e8 01             	sub    $0x1,%eax
    64a4:	44 39 e8             	cmp    %r13d,%eax
    64a7:	74 57                	je     6500 <barriered_thread+0x1e0>
          asm volatile ("sfence" ::: "memory");
    64a9:	0f ae f8             	sfence
          if (waiting == 0) {
    64ac:	45 85 e4             	test   %r12d,%r12d
    64af:	74 7f                	je     6530 <barriered_thread+0x210>
        int arrived = 0; 
    64b1:	41 bc 01 00 00 00    	mov    $0x1,%r12d
    64b7:	e9 cc fe ff ff       	jmp    6388 <barriered_thread+0x68>
  while (data->running == 1) {
    64bc:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    64c0:	0f 85 a4 00 00 00    	jne    656a <barriered_thread+0x24a>
    64c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->cycles++;
    64d0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    64d8:	85 c0                	test   %eax,%eax
    64da:	7e e0                	jle    64bc <barriered_thread+0x19c>
    64dc:	45 31 ed             	xor    %r13d,%r13d
    64df:	e9 7d fe ff ff       	jmp    6361 <barriered_thread+0x41>
    64e4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    64e8:	41 83 fc 01          	cmp    $0x1,%r12d
    64ec:	0f 84 be 00 00 00    	je     65b0 <barriered_thread+0x290>
        int arrived = 0; 
    64f2:	45 31 e4             	xor    %r12d,%r12d
    64f5:	e9 38 ff ff ff       	jmp    6432 <barriered_thread+0x112>
    64fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6500:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6507:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    650e:	7d 99                	jge    64a9 <barriered_thread+0x189>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    6510:	48 c1 e6 04          	shl    $0x4,%rsi
    6514:	bf 04 00 00 00       	mov    $0x4,%edi
    6519:	48 03 73 70          	add    0x70(%rbx),%rsi
    651d:	e8 6e be ff ff       	call   2390 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6522:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    652a:	e9 7a ff ff ff       	jmp    64a9 <barriered_thread+0x189>
    652f:	90                   	nop
            data->task_snapshot[data->task_timestamp_count].task = t;
    6530:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6537:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    653c:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6540:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6547:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    654b:	44 89 6e 20          	mov    %r13d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    654f:	e8 3c be ff ff       	call   2390 <clock_gettime@plt>
            waiting = 1;
    6554:	e9 58 ff ff ff       	jmp    64b1 <barriered_thread+0x191>
    6559:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    6560:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6564:	0f 84 ee fd ff ff    	je     6358 <barriered_thread+0x38>
}
    656a:	48 83 c4 08          	add    $0x8,%rsp
    656e:	31 c0                	xor    %eax,%eax
    6570:	5b                   	pop    %rbx
    6571:	41 5c                	pop    %r12
    6573:	41 5d                	pop    %r13
    6575:	41 5e                	pop    %r14
    6577:	41 5f                	pop    %r15
    6579:	5d                   	pop    %rbp
    657a:	c3                   	ret
    657b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    6580:	48 c1 e6 04          	shl    $0x4,%rsi
    6584:	bf 04 00 00 00       	mov    $0x4,%edi
    6589:	48 03 73 68          	add    0x68(%rbx),%rsi
    658d:	e8 fe bd ff ff       	call   2390 <clock_gettime@plt>
          data->tasks[t].available = 0;
    6592:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6596:	4c 01 f2             	add    %r14,%rdx
    6599:	e9 ca fe ff ff       	jmp    6468 <barriered_thread+0x148>
    659e:	66 90                	xchg   %ax,%ax
          if (waiting == 1) {
    65a0:	41 83 fc 01          	cmp    $0x1,%r12d
    65a4:	0f 85 9b fe ff ff    	jne    6445 <barriered_thread+0x125>
        int arrived = 0; 
    65aa:	45 31 ff             	xor    %r15d,%r15d
    65ad:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    65b0:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    65b7:	bf 04 00 00 00       	mov    $0x4,%edi
    65bc:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    65c0:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    65c7:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    65cc:	e8 bf bd ff ff       	call   2390 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    65d1:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    65d8:	48 83 c0 01          	add    $0x1,%rax
    65dc:	48 99                	cqto
    65de:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    65e5:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    65ec:	e9 01 ff ff ff       	jmp    64f2 <barriered_thread+0x1d2>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    65f1:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    65f5:	48 8b 43 18          	mov    0x18(%rbx),%rax
    65f9:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    65fd:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6601:	4c 01 f7             	add    %r14,%rdi
    6604:	e8 f7 fb ff ff       	call   6200 <barriered_work_ingest>
          break;
    6609:	e9 36 fd ff ff       	jmp    6344 <barriered_thread+0x24>
    660e:	66 90                	xchg   %ax,%ax

0000000000006610 <receive>:
int receive(struct BarrierTask *data) {
    6610:	f3 0f 1e fa          	endbr64
    6614:	55                   	push   %rbp
    6615:	48 89 e5             	mov    %rsp,%rbp
    6618:	41 57                	push   %r15
    661a:	41 56                	push   %r14
    661c:	41 55                	push   %r13
    661e:	41 54                	push   %r12
    6620:	53                   	push   %rbx
    6621:	48 83 ec 18          	sub    $0x18,%rsp
    6625:	ff 15 bd 49 00 00    	call   *0x49bd(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    662b:	44 8b bf 40 01 00 00 	mov    0x140(%rdi),%r15d
int receive(struct BarrierTask *data) {
    6632:	48 89 f9             	mov    %rdi,%rcx
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6635:	45 85 ff             	test   %r15d,%r15d
    6638:	0f 8e 3b 01 00 00    	jle    6779 <receive+0x169>
    if (n == data->thread->real_thread_index) { continue; }
    663e:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    6645:	45 31 ed             	xor    %r13d,%r13d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6648:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    664a:	4c 63 60 08          	movslq 0x8(%rax),%r12
    664e:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    6652:	4d 89 e6             	mov    %r12,%r14
    6655:	0f 1f 00             	nopl   (%rax)
    6658:	41 39 de             	cmp    %ebx,%r14d
    665b:	0f 84 08 01 00 00    	je     6769 <receive+0x159>
    struct Data *me = data->mailboxes[n].lower;
    6661:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    6668:	4a 8b 34 28          	mov    (%rax,%r13,1),%rsi
    if (me->available_reading == 1) {
    666c:	8b 86 00 02 00 00    	mov    0x200(%rsi),%eax
    6672:	83 f8 01             	cmp    $0x1,%eax
    6675:	74 11                	je     6688 <receive+0x78>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    6677:	83 be 18 03 00 00 02 	cmpl   $0x2,0x318(%rsi)
    667e:	75 08                	jne    6688 <receive+0x78>
    6680:	85 c0                	test   %eax,%eax
    6682:	0f 84 e1 00 00 00    	je     6769 <receive+0x159>
    for (int x = 0 ; x < me->messages_count ; x++) {
    6688:	48 8b be 80 00 00 00 	mov    0x80(%rsi),%rdi
    668f:	48 85 ff             	test   %rdi,%rdi
    6692:	0f 8e a8 00 00 00    	jle    6740 <receive+0x130>
      data->sends++;
    6698:	48 8b 91 78 01 00 00 	mov    0x178(%rcx),%rdx
    669f:	4c 8b 06             	mov    (%rsi),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    66a2:	4c 63 59 04          	movslq 0x4(%rcx),%r11
    66a6:	49 89 d1             	mov    %rdx,%r9
    66a9:	48 8d 42 01          	lea    0x1(%rdx),%rax
    66ad:	49 f7 d9             	neg    %r9
    66b0:	48 01 c7             	add    %rax,%rdi
    66b3:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    66b7:	4c 8b 89 08 01 00 00 	mov    0x108(%rcx),%r9
      me->received++;
    66be:	4c 8b 86 10 03 00 00 	mov    0x310(%rsi),%r8
      data->n++;
    66c5:	49 29 d1             	sub    %rdx,%r9
      me->received++;
    66c8:	49 29 d0             	sub    %rdx,%r8
    66cb:	eb 0c                	jmp    66d9 <receive+0xc9>
    66cd:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    66d0:	48 83 c0 01          	add    $0x1,%rax
    66d4:	48 39 c7             	cmp    %rax,%rdi
    66d7:	74 67                	je     6740 <receive+0x130>
      data->n++;
    66d9:	49 8d 14 01          	lea    (%r9,%rax,1),%rdx
      data->sends++;
    66dd:	48 89 81 78 01 00 00 	mov    %rax,0x178(%rcx)
      data->n++;
    66e4:	48 89 91 08 01 00 00 	mov    %rdx,0x108(%rcx)
      me->received++;
    66eb:	49 8d 14 00          	lea    (%r8,%rax,1),%rdx
    66ef:	48 89 96 10 03 00 00 	mov    %rdx,0x310(%rsi)
      if (me->messages[x]->group == data->group) {
    66f6:	49 8b 54 c2 f8       	mov    -0x8(%r10,%rax,8),%rdx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    66fb:	4c 39 5a 10          	cmp    %r11,0x10(%rdx)
    66ff:	75 cf                	jne    66d0 <receive+0xc0>
    6701:	4c 39 62 08          	cmp    %r12,0x8(%rdx)
    6705:	75 c9                	jne    66d0 <receive+0xc0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    6707:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    670b:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    670d:	bf 01 00 00 00       	mov    $0x1,%edi
    6712:	ba 01 00 00 00       	mov    $0x1,%edx
    6717:	48 8d 35 fa 1e 00 00 	lea    0x1efa(%rip),%rsi        # 8618 <_IO_stdin_used+0x618>
    671e:	48 63 40 04          	movslq 0x4(%rax),%rax
    6722:	4c 39 e0             	cmp    %r12,%rax
    6725:	0f 94 c1             	sete   %cl
    6728:	31 c0                	xor    %eax,%eax
    672a:	e8 e1 bd ff ff       	call   2510 <__printf_chk@plt>
        exit(1);
    672f:	bf 01 00 00 00       	mov    $0x1,%edi
    6734:	e8 47 be ff ff       	call   2580 <exit@plt>
    6739:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    me->messages_count = 0;
    6740:	48 c7 86 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rsi)
      me->available_reading = 0;
    674b:	c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi)
      me->finished_reading = 1;
    6755:	c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rsi)
      me->available_sending = 1;
    675f:	c7 86 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rsi)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6769:	83 c3 01             	add    $0x1,%ebx
    676c:	49 83 c5 38          	add    $0x38,%r13
    6770:	44 39 fb             	cmp    %r15d,%ebx
    6773:	0f 85 df fe ff ff    	jne    6658 <receive+0x48>
  asm volatile ("sfence" ::: "memory");
    6779:	0f ae f8             	sfence
}
    677c:	48 83 c4 18          	add    $0x18,%rsp
    6780:	31 c0                	xor    %eax,%eax
    6782:	5b                   	pop    %rbx
    6783:	41 5c                	pop    %r12
    6785:	41 5d                	pop    %r13
    6787:	41 5e                	pop    %r14
    6789:	41 5f                	pop    %r15
    678b:	5d                   	pop    %rbp
    678c:	c3                   	ret
    678d:	0f 1f 00             	nopl   (%rax)

0000000000006790 <sendm>:
int sendm(struct BarrierTask *data) {
    6790:	f3 0f 1e fa          	endbr64
    6794:	55                   	push   %rbp
    6795:	48 89 e5             	mov    %rsp,%rbp
    6798:	41 57                	push   %r15
    679a:	41 56                	push   %r14
    679c:	41 55                	push   %r13
    679e:	41 54                	push   %r12
    67a0:	53                   	push   %rbx
    67a1:	48 83 ec 28          	sub    $0x28,%rsp
    67a5:	ff 15 3d 48 00 00    	call   *0x483d(%rip)        # afe8 <mcount@GLIBC_2.2.5>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    67ab:	44 8b a7 40 01 00 00 	mov    0x140(%rdi),%r12d
int sendm(struct BarrierTask *data) {
    67b2:	48 89 fe             	mov    %rdi,%rsi
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    67b5:	45 85 e4             	test   %r12d,%r12d
    67b8:	0f 8e a6 00 00 00    	jle    6864 <sendm+0xd4>
        if (n == data->thread->real_thread_index) { continue; }
    67be:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    67c5:	31 d2                	xor    %edx,%edx
    67c7:	44 8b 68 08          	mov    0x8(%rax),%r13d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    67cb:	31 c0                	xor    %eax,%eax
    67cd:	eb 33                	jmp    6802 <sendm+0x72>
    67cf:	90                   	nop
          data->mailboxes[n].higher = them;
    67d0:	4c 89 47 08          	mov    %r8,0x8(%rdi)
          them = data->mailboxes[n].pending;
    67d4:	4c 89 c1             	mov    %r8,%rcx
          data->mailboxes[n].pending = NULL;
    67d7:	48 c7 47 10 00 00 00 00 	movq   $0x0,0x10(%rdi)
        if (them->messages_count > 0) {
    67df:	49 8b b8 80 00 00 00 	mov    0x80(%r8),%rdi
          them->available_sending = 1;
    67e6:	41 c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r8)
        if (them->messages_count > 0) {
    67f1:	48 85 ff             	test   %rdi,%rdi
    67f4:	7e 4f                	jle    6845 <sendm+0xb5>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    67f6:	83 c0 01             	add    $0x1,%eax
    67f9:	48 83 c2 38          	add    $0x38,%rdx
    67fd:	44 39 e0             	cmp    %r12d,%eax
    6800:	74 62                	je     6864 <sendm+0xd4>
        if (n == data->thread->real_thread_index) { continue; }
    6802:	41 39 c5             	cmp    %eax,%r13d
    6805:	74 ef                	je     67f6 <sendm+0x66>
        struct Data *them = data->mailboxes[n].higher;
    6807:	48 8b be 70 01 00 00 	mov    0x170(%rsi),%rdi
    680e:	48 01 d7             	add    %rdx,%rdi
        if (data->mailboxes[n].pending != NULL) {
    6811:	4c 8b 47 10          	mov    0x10(%rdi),%r8
        struct Data *them = data->mailboxes[n].higher;
    6815:	48 8b 4f 08          	mov    0x8(%rdi),%rcx
        if (data->mailboxes[n].pending != NULL) {
    6819:	4d 85 c0             	test   %r8,%r8
    681c:	75 b2                	jne    67d0 <sendm+0x40>
        if (them->messages_count > 0) {
    681e:	48 8b b9 80 00 00 00 	mov    0x80(%rcx),%rdi
    6825:	48 85 ff             	test   %rdi,%rdi
    6828:	7f cc                	jg     67f6 <sendm+0x66>
        if (them->available_sending == 1) {
    682a:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    6831:	41 83 f8 01          	cmp    $0x1,%r8d
    6835:	74 0e                	je     6845 <sendm+0xb5>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    6837:	83 b9 18 03 00 00 02 	cmpl   $0x2,0x318(%rcx)
    683e:	75 05                	jne    6845 <sendm+0xb5>
    6840:	45 85 c0             	test   %r8d,%r8d
    6843:	74 b1                	je     67f6 <sendm+0x66>
        if (data->sending == 1) {
    6845:	83 be 80 01 00 00 01 	cmpl   $0x1,0x180(%rsi)
    684c:	74 32                	je     6880 <sendm+0xf0>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    684e:	83 c0 01             	add    $0x1,%eax
    6851:	48 83 c2 38          	add    $0x38,%rdx
          them->available_receiving = 1;
    6855:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    685f:	44 39 e0             	cmp    %r12d,%eax
    6862:	75 9e                	jne    6802 <sendm+0x72>
      asm volatile ("sfence" ::: "memory");
    6864:	0f ae f8             	sfence
}
    6867:	48 83 c4 28          	add    $0x28,%rsp
    686b:	31 c0                	xor    %eax,%eax
    686d:	5b                   	pop    %rbx
    686e:	41 5c                	pop    %r12
    6870:	41 5d                	pop    %r13
    6872:	41 5e                	pop    %r14
    6874:	41 5f                	pop    %r15
    6876:	5d                   	pop    %rbp
    6877:	c3                   	ret
    6878:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
          for (; them->messages_count < min;) {
    6880:	48 63 99 88 00 00 00 	movslq 0x88(%rcx),%rbx
    6887:	48 39 df             	cmp    %rbx,%rdi
    688a:	0f 8d b0 00 00 00    	jge    6940 <sendm+0x1b0>
    6890:	4c 8b b6 08 01 00 00 	mov    0x108(%rsi),%r14
    6897:	49 89 db             	mov    %rbx,%r11
            them->messages[them->messages_count++] = data->message; 
    689a:	4c 8b 11             	mov    (%rcx),%r10
    689d:	49 29 fb             	sub    %rdi,%r11
    68a0:	4c 89 75 c0          	mov    %r14,-0x40(%rbp)
    68a4:	4c 8b b1 08 03 00 00 	mov    0x308(%rcx),%r14
    68ab:	4d 8d 43 ff          	lea    -0x1(%r11),%r8
    68af:	4c 89 75 b8          	mov    %r14,-0x48(%rbp)
    68b3:	49 83 f8 02          	cmp    $0x2,%r8
    68b7:	0f 86 03 01 00 00    	jbe    69c0 <sendm+0x230>
    68bd:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    68c5:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    68cd:	4f 8d 3c 02          	lea    (%r10,%r8,1),%r15
    68d1:	4f 8d 34 0a          	lea    (%r10,%r9,1),%r14
    68d5:	4c 89 7d c8          	mov    %r15,-0x38(%rbp)
    68d9:	4c 8d be 88 01 00 00 	lea    0x188(%rsi),%r15
    68e0:	4d 39 f7             	cmp    %r14,%r15
    68e3:	73 6b                	jae    6950 <sendm+0x1c0>
    68e5:	4c 8d b6 90 01 00 00 	lea    0x190(%rsi),%r14
    68ec:	4c 39 75 c8          	cmp    %r14,-0x38(%rbp)
    68f0:	73 5e                	jae    6950 <sendm+0x1c0>
    68f2:	4d 01 d0             	add    %r10,%r8
    68f5:	4b 8d 3c 0a          	lea    (%r10,%r9,1),%rdi
    68f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6900:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
          for (; them->messages_count < min;) {
    6907:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    690b:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    690f:	4c 39 c7             	cmp    %r8,%rdi
    6912:	75 ec                	jne    6900 <sendm+0x170>
    6914:	0f 1f 40 00          	nopl   0x0(%rax)
    6918:	48 8b 7d c0          	mov    -0x40(%rbp),%rdi
    691c:	4c 01 df             	add    %r11,%rdi
    691f:	48 89 be 08 01 00 00 	mov    %rdi,0x108(%rsi)
    6926:	48 8b 7d b8          	mov    -0x48(%rbp),%rdi
    692a:	48 89 99 80 00 00 00 	mov    %rbx,0x80(%rcx)
    6931:	4c 01 df             	add    %r11,%rdi
    6934:	48 89 b9 08 03 00 00 	mov    %rdi,0x308(%rcx)
    693b:	4d 89 4c da f8       	mov    %r9,-0x8(%r10,%rbx,8)
          them->available_sending = 0;
    6940:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
    694a:	e9 ff fe ff ff       	jmp    684e <sendm+0xbe>
    694f:	90                   	nop
    6950:	4d 89 de             	mov    %r11,%r14
    6953:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
    695a:	4c 8b 45 c8          	mov    -0x38(%rbp),%r8
    695e:	49 d1 ee             	shr    %r14
    6961:	49 c1 e6 04          	shl    $0x4,%r14
    6965:	66 49 0f 6e c1       	movq   %r9,%xmm0
    696a:	4f 8d 3c 30          	lea    (%r8,%r14,1),%r15
    696e:	41 83 e6 10          	and    $0x10,%r14d
    6972:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    6976:	74 10                	je     6988 <sendm+0x1f8>
            them->messages[them->messages_count++] = data->message; 
    6978:	41 0f 11 00          	movups %xmm0,(%r8)
          for (; them->messages_count < min;) {
    697c:	49 83 c0 10          	add    $0x10,%r8
    6980:	4d 39 f8             	cmp    %r15,%r8
    6983:	74 15                	je     699a <sendm+0x20a>
    6985:	0f 1f 00             	nopl   (%rax)
            them->messages[them->messages_count++] = data->message; 
    6988:	41 0f 11 00          	movups %xmm0,(%r8)
    698c:	49 83 c0 20          	add    $0x20,%r8
    6990:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    6995:	4d 39 f8             	cmp    %r15,%r8
    6998:	75 ee                	jne    6988 <sendm+0x1f8>
    699a:	4d 89 d8             	mov    %r11,%r8
    699d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    69a1:	4c 01 c7             	add    %r8,%rdi
    69a4:	41 f6 c3 01          	test   $0x1,%r11b
    69a8:	0f 84 6a ff ff ff    	je     6918 <sendm+0x188>
            them->messages[them->messages_count++] = data->message; 
    69ae:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
    69b5:	4d 89 0c fa          	mov    %r9,(%r10,%rdi,8)
          for (; them->messages_count < min;) {
    69b9:	e9 5a ff ff ff       	jmp    6918 <sendm+0x188>
    69be:	66 90                	xchg   %ax,%ax
    69c0:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    69c8:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    69d0:	e9 1d ff ff ff       	jmp    68f2 <sendm+0x162>
    69d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000069e0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    69e0:	f3 0f 1e fa          	endbr64
    69e4:	55                   	push   %rbp
    69e5:	48 89 e5             	mov    %rsp,%rbp
    69e8:	41 57                	push   %r15
    69ea:	41 56                	push   %r14
    69ec:	41 55                	push   %r13
    69ee:	41 54                	push   %r12
    69f0:	53                   	push   %rbx
    69f1:	48 83 ec 48          	sub    $0x48,%rsp
    69f5:	ff 15 ed 45 00 00    	call   *0x45ed(%rip)        # afe8 <mcount@GLIBC_2.2.5>
        int t = data->task_index;
    69fb:	4c 63 6f 04          	movslq 0x4(%rdi),%r13
int barriered_work(struct BarrierTask *data) {
    69ff:	48 89 7d c0          	mov    %rdi,-0x40(%rbp)
      receive(data);
    6a03:	48 89 fb             	mov    %rdi,%rbx
  if (data->thread_index == data->task_index) {
    6a06:	44 39 af 30 01 00 00 	cmp    %r13d,0x130(%rdi)
    6a0d:	74 51                	je     6a60 <barriered_work+0x80>
    receive(data);
    6a0f:	e8 fc fb ff ff       	call   6610 <receive>
    while (data->scheduled == 1) {
    6a14:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6a1b:	75 1f                	jne    6a3c <barriered_work+0x5c>
    6a1d:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    6a21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      data->n++;
    6a28:	48 83 80 08 01 00 00 01 	addq   $0x1,0x108(%rax)
      asm volatile ("sfence" ::: "memory");
    6a30:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6a33:	83 b8 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rax)
    6a3a:	74 ec                	je     6a28 <barriered_work+0x48>
    sendm(data);
    6a3c:	48 8b 7d c0          	mov    -0x40(%rbp),%rdi
    6a40:	e8 4b fd ff ff       	call   6790 <sendm>
  asm volatile ("sfence" ::: "memory");
    6a45:	0f ae f8             	sfence
}
    6a48:	48 83 c4 48          	add    $0x48,%rsp
    6a4c:	31 c0                	xor    %eax,%eax
    6a4e:	5b                   	pop    %rbx
    6a4f:	41 5c                	pop    %r12
    6a51:	41 5d                	pop    %r13
    6a53:	41 5e                	pop    %r14
    6a55:	41 5f                	pop    %r15
    6a57:	5d                   	pop    %rbp
    6a58:	c3                   	ret
    6a59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      receive(data);
    6a60:	e8 ab fb ff ff       	call   6610 <receive>
      data->swap++;
    6a65:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    6a6b:	89 45 c8             	mov    %eax,-0x38(%rbp)
    6a6e:	83 c0 01             	add    $0x1,%eax
    6a71:	89 83 98 01 00 00    	mov    %eax,0x198(%rbx)
        if (data->swap % 2 == 0) {
    6a77:	a8 01                	test   $0x1,%al
    6a79:	0f 84 79 02 00 00    	je     6cf8 <barriered_work+0x318>
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6a7f:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    6a83:	48 8b b8 28 01 00 00 	mov    0x128(%rax),%rdi
          int k = data->group;
    6a8a:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6a8e:	48 63 97 c4 00 00 00 	movslq 0xc4(%rdi),%rdx
          int k = data->group;
    6a95:	8b 80 94 01 00 00    	mov    0x194(%rax),%eax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6a9b:	85 d2                	test   %edx,%edx
    6a9d:	0f 8e 3c 01 00 00    	jle    6bdf <barriered_work+0x1ff>
            int y = (k * data->thread->threads_per_group) + d;
    6aa3:	0f af c2             	imul   %edx,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6aa6:	4d 89 ee             	mov    %r13,%r14
              int next_task = abs((t + 1) % (data->thread_count));
    6aa9:	48 8b 5d c0          	mov    -0x40(%rbp),%rbx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6aad:	49 c1 e6 09          	shl    $0x9,%r14
    6ab1:	4c 89 75 b0          	mov    %r14,-0x50(%rbp)
              int next_task = abs((t + 1) % (data->thread_count));
    6ab5:	44 8b 8b 34 01 00 00 	mov    0x134(%rbx),%r9d
    6abc:	48 98                	cltq
    6abe:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    6ac2:	48 8d 34 c9          	lea    (%rcx,%rcx,8),%rsi
    6ac6:	48 8b 4f 20          	mov    0x20(%rdi),%rcx
    6aca:	4c 8d 04 f1          	lea    (%rcx,%rsi,8),%r8
    6ace:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    6ad6:	48 29 c1             	sub    %rax,%rcx
    6ad9:	48 01 d0             	add    %rdx,%rax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6adc:	4d 89 c2             	mov    %r8,%r10
    6adf:	4c 8d 24 c5 00 00 00 00 	lea    0x0(,%rax,8),%r12
    6ae7:	4c 8d 3c cd 00 00 00 00 	lea    0x0(,%rcx,8),%r15
    6aef:	49 29 c4             	sub    %rax,%r12
    6af2:	4d 89 fb             	mov    %r15,%r11
    6af5:	49 c1 e4 03          	shl    $0x3,%r12
    6af9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6b00:	4d 8b 6a 38          	mov    0x38(%r10),%r13
    6b04:	48 8b 45 b0          	mov    -0x50(%rbp),%rax
    6b08:	4c 89 fe             	mov    %r15,%rsi
    6b0b:	4c 89 c7             	mov    %r8,%rdi
    6b0e:	4c 89 d3             	mov    %r10,%rbx
    6b11:	4d 8b b4 05 70 01 00 00 	mov    0x170(%r13,%rax,1),%r14
    6b19:	eb 19                	jmp    6b34 <barriered_work+0x154>
    6b1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6b20:	48 83 c6 38          	add    $0x38,%rsi
    6b24:	48 81 c7 d8 00 00 00 	add    $0xd8,%rdi
    6b2b:	4c 39 e6             	cmp    %r12,%rsi
    6b2e:	0f 84 94 00 00 00    	je     6bc8 <barriered_work+0x1e8>
              if (kind == MAILBOX_FRIEND) {
    6b34:	41 83 7c 36 30 01    	cmpl   $0x1,0x30(%r14,%rsi,1)
    6b3a:	75 e4                	jne    6b20 <barriered_work+0x140>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6b3c:	4c 8b 57 38          	mov    0x38(%rdi),%r10
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6b40:	45 85 c9             	test   %r9d,%r9d
    6b43:	7e db                	jle    6b20 <barriered_work+0x140>
    6b45:	4c 89 75 c8          	mov    %r14,-0x38(%rbp)
    6b49:	49 81 c2 70 01 00 00 	add    $0x170,%r10
    6b50:	31 c9                	xor    %ecx,%ecx
    6b52:	48 89 7d b8          	mov    %rdi,-0x48(%rbp)
    6b56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
                    int next_task = abs((nn + 1) % (data->thread_count));
    6b60:	83 c1 01             	add    $0x1,%ecx
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6b63:	49 8b 3a             	mov    (%r10),%rdi
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6b66:	49 81 c2 00 02 00 00 	add    $0x200,%r10
                    int next_task = abs((nn + 1) % (data->thread_count));
    6b6d:	89 c8                	mov    %ecx,%eax
    6b6f:	99                   	cltd
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6b70:	4c 01 df             	add    %r11,%rdi
                    int next_task = abs((nn + 1) % (data->thread_count));
    6b73:	41 f7 f9             	idiv   %r9d
    return mailbox->lower;
    6b76:	4c 8b 37             	mov    (%rdi),%r14
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6b79:	48 63 d2             	movslq %edx,%rdx
    6b7c:	48 c1 e2 09          	shl    $0x9,%rdx
    6b80:	49 8b 84 15 70 01 00 00 	mov    0x170(%r13,%rdx,1),%rax
    mailbox->lower = data;
    6b88:	48 8b 57 08          	mov    0x8(%rdi),%rdx
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6b8c:	48 01 f0             	add    %rsi,%rax
    return mailbox->higher;
    6b8f:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    6b93:	48 89 10             	mov    %rdx,(%rax)
    return mailbox->lower;
    6b96:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
    mailbox->lower = data;
    6b9b:	0f 11 07             	movups %xmm0,(%rdi)
    mailbox->higher = data;
    6b9e:	4c 89 70 08          	mov    %r14,0x8(%rax)
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6ba2:	41 39 c9             	cmp    %ecx,%r9d
    6ba5:	75 b9                	jne    6b60 <barriered_work+0x180>
    6ba7:	48 8b 7d b8          	mov    -0x48(%rbp),%rdi
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6bab:	48 83 c6 38          	add    $0x38,%rsi
    6baf:	4c 8b 75 c8          	mov    -0x38(%rbp),%r14
    6bb3:	48 81 c7 d8 00 00 00 	add    $0xd8,%rdi
    6bba:	4c 39 e6             	cmp    %r12,%rsi
    6bbd:	0f 85 71 ff ff ff    	jne    6b34 <barriered_work+0x154>
    6bc3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6bc8:	49 89 da             	mov    %rbx,%r10
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6bcb:	49 83 c3 38          	add    $0x38,%r11
    6bcf:	49 81 c2 d8 00 00 00 	add    $0xd8,%r10
    6bd6:	4d 39 e3             	cmp    %r12,%r11
    6bd9:	0f 85 21 ff ff ff    	jne    6b00 <barriered_work+0x120>
      receive(data);
    6bdf:	48 8b 5d c0          	mov    -0x40(%rbp),%rbx
    6be3:	48 89 df             	mov    %rbx,%rdi
    6be6:	e8 25 fa ff ff       	call   6610 <receive>
      asm volatile ("sfence" ::: "memory");
    6beb:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6bee:	48 89 d8             	mov    %rbx,%rax
    6bf1:	48 8b 9b 60 01 00 00 	mov    0x160(%rbx),%rbx
    6bf8:	31 ff                	xor    %edi,%edi
    6bfa:	48 89 de             	mov    %rbx,%rsi
    6bfd:	48 89 5d c8          	mov    %rbx,-0x38(%rbp)
    6c01:	48 89 c3             	mov    %rax,%rbx
    6c04:	48 c1 e6 05          	shl    $0x5,%rsi
    6c08:	48 03 b0 50 01 00 00 	add    0x150(%rax),%rsi
    6c0f:	e8 7c b7 ff ff       	call   2390 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6c14:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6c1b:	48 89 d9             	mov    %rbx,%rcx
    6c1e:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    6c22:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6c26:	8b 5a 10             	mov    0x10(%rdx),%ebx
    6c29:	83 c3 01             	add    $0x1,%ebx
    while (data->scheduled == 1) {
    6c2c:	83 b9 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rcx)
    int modcount = ++data->thread->protected_state->modcount;
    6c33:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6c36:	74 10                	je     6c48 <barriered_work+0x268>
    6c38:	eb 6a                	jmp    6ca4 <barriered_work+0x2c4>
    6c3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    if (modcount != data->thread->protected_state->modcount) {
    6c40:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6c48:	49 63 94 24 30 01 00 00 	movslq 0x130(%r12),%rdx
    6c50:	48 8b 40 18          	mov    0x18(%rax),%rax
      data->n++;
    6c54:	49 83 84 24 08 01 00 00 01 	addq   $0x1,0x108(%r12)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6c5d:	49 63 7c 24 04       	movslq 0x4(%r12),%rdi
    6c62:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6c66:	48 c1 e7 09          	shl    $0x9,%rdi
    6c6a:	48 03 78 38          	add    0x38(%rax),%rdi
    6c6e:	41 ff 94 24 20 01 00 00 	call   *0x120(%r12)
      asm volatile ("sfence" ::: "memory");
    6c76:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6c79:	41 83 bc 24 4c 01 00 00 01 	cmpl   $0x1,0x14c(%r12)
    6c82:	74 bc                	je     6c40 <barriered_work+0x260>
    if (modcount != data->thread->protected_state->modcount) {
    6c84:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    6c88:	48 8b 80 28 01 00 00 	mov    0x128(%rax),%rax
    6c8f:	48 8b 40 48          	mov    0x48(%rax),%rax
    6c93:	3b 58 10             	cmp    0x10(%rax),%ebx
    6c96:	74 0c                	je     6ca4 <barriered_work+0x2c4>
    6c98:	48 8d 3d a7 15 00 00 	lea    0x15a7(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6c9f:	e8 cc b6 ff ff       	call   2370 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6ca4:	48 8b 5d c0          	mov    -0x40(%rbp),%rbx
    6ca8:	31 ff                	xor    %edi,%edi
    6caa:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6cb1:	48 89 c6             	mov    %rax,%rsi
    6cb4:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    6cb8:	48 c1 e6 05          	shl    $0x5,%rsi
    6cbc:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6cc3:	48 83 c6 10          	add    $0x10,%rsi
    6cc7:	e8 c4 b6 ff ff       	call   2390 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6ccc:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    sendm(data);
    6cd3:	48 89 df             	mov    %rbx,%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6cd6:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    6cda:	48 83 c0 01          	add    $0x1,%rax
    6cde:	48 99                	cqto
    6ce0:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6ce7:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    sendm(data);
    6cee:	e8 9d fa ff ff       	call   6790 <sendm>
    6cf3:	e9 4d fd ff ff       	jmp    6a45 <barriered_work+0x65>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6cf8:	44 8b 8b 40 01 00 00 	mov    0x140(%rbx),%r9d
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6cff:	48 8b bb 28 01 00 00 	mov    0x128(%rbx),%rdi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6d06:	45 85 c9             	test   %r9d,%r9d
    6d09:	0f 8e 7b fd ff ff    	jle    6a8a <barriered_work+0xaa>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    6d0f:	49 63 c5             	movslq %r13d,%rax
    6d12:	31 d2                	xor    %edx,%edx
    6d14:	31 f6                	xor    %esi,%esi
    6d16:	44 89 6d 9c          	mov    %r13d,-0x64(%rbp)
    6d1a:	48 c1 e0 09          	shl    $0x9,%rax
    6d1e:	48 89 75 c8          	mov    %rsi,-0x38(%rbp)
    6d22:	49 89 d7             	mov    %rdx,%r15
    6d25:	48 89 45 b8          	mov    %rax,-0x48(%rbp)
    6d29:	eb 1e                	jmp    6d49 <barriered_work+0x369>
    6d2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6d30:	48 83 45 c8 01       	addq   $0x1,-0x38(%rbp)
    6d35:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    6d39:	49 81 c7 d8 00 00 00 	add    $0xd8,%r15
    6d40:	41 39 c1             	cmp    %eax,%r9d
    6d43:	0f 8e 53 02 00 00    	jle    6f9c <barriered_work+0x5bc>
              int b = data->thread->real_thread_index;
    6d49:	48 8b 5d c8          	mov    -0x38(%rbp),%rbx
    6d4d:	48 63 57 08          	movslq 0x8(%rdi),%rdx
              if (y == b) { continue; }
    6d51:	48 63 cb             	movslq %ebx,%rcx
    6d54:	39 da                	cmp    %ebx,%edx
    6d56:	74 d8                	je     6d30 <barriered_work+0x350>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    6d58:	4c 63 f2             	movslq %edx,%r14
    6d5b:	4c 8b 47 20          	mov    0x20(%rdi),%r8
    6d5f:	4b 8d 04 76          	lea    (%r14,%r14,2),%rax
    6d63:	4c 8d 2c c0          	lea    (%rax,%rax,8),%r13
    6d67:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    6d6f:	49 c1 e5 03          	shl    $0x3,%r13
    6d73:	48 29 d8             	sub    %rbx,%rax
    6d76:	48 8b 5d b8          	mov    -0x48(%rbp),%rbx
    6d7a:	4f 8b 44 28 38       	mov    0x38(%r8,%r13,1),%r8
    6d7f:	4c 8d 24 c5 00 00 00 00 	lea    0x0(,%rax,8),%r12
    6d87:	4d 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%r8
    6d8f:	41 83 7c c0 30 02    	cmpl   $0x2,0x30(%r8,%rax,8)
    6d95:	75 99                	jne    6d30 <barriered_work+0x350>
  if (a < b) { return a; }
    6d97:	39 ca                	cmp    %ecx,%edx
    6d99:	0f 8c ee 01 00 00    	jl     6f8d <barriered_work+0x5ad>
  if (b < a) { return b; }
    6d9f:	48 0f 4f d1          	cmovg  %rcx,%rdx
    6da3:	4c 89 f0             	mov    %r14,%rax
                    pthread_mutex_lock(&data->thread->swapmutex[max]);   
    6da6:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6daa:	48 89 55 a8          	mov    %rdx,-0x58(%rbp)
    6dae:	48 c1 e0 03          	shl    $0x3,%rax
    6db2:	48 89 45 b0          	mov    %rax,-0x50(%rbp)
    6db6:	48 03 87 c8 00 00 00 	add    0xc8(%rdi),%rax
    6dbd:	48 89 c7             	mov    %rax,%rdi
    6dc0:	e8 3b b8 ff ff       	call   2600 <pthread_mutex_lock@plt>
                    pthread_mutex_lock(&data->thread->swapmutex[min]);   
    6dc5:	48 8b 55 a8          	mov    -0x58(%rbp),%rdx
    6dc9:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    6dcd:	48 8d 1c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbx
    6dd5:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    6dd9:	48 8b 80 28 01 00 00 	mov    0x128(%rax),%rax
    6de0:	48 8b b8 c8 00 00 00 	mov    0xc8(%rax),%rdi
    6de7:	48 01 df             	add    %rbx,%rdi
    6dea:	e8 11 b8 ff ff       	call   2600 <pthread_mutex_lock@plt>
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6def:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    6df3:	44 8b 98 34 01 00 00 	mov    0x134(%rax),%r11d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6dfa:	4c 8b 90 28 01 00 00 	mov    0x128(%rax),%r10
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6e01:	45 85 db             	test   %r11d,%r11d
    6e04:	0f 8e e5 00 00 00    	jle    6eef <barriered_work+0x50f>
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6e0a:	49 8b 42 20          	mov    0x20(%r10),%rax
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6e0e:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6e12:	31 c9                	xor    %ecx,%ecx
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6e14:	bf 70 01 00 00       	mov    $0x170,%edi
    6e19:	4e 8d 04 f5 00 00 00 00 	lea    0x0(,%r14,8),%r8
    6e21:	4c 89 55 a0          	mov    %r10,-0x60(%rbp)
    6e25:	4d 29 f0             	sub    %r14,%r8
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6e28:	4a 8b 74 28 38       	mov    0x38(%rax,%r13,1),%rsi
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6e2d:	4e 8b 4c 38 38       	mov    0x38(%rax,%r15,1),%r9
    6e32:	49 c1 e0 03          	shl    $0x3,%r8
    6e36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
                      int next_task = abs((nn + 1) % data->thread_count);
    6e40:	83 c1 01             	add    $0x1,%ecx
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6e43:	4c 8b 14 3e          	mov    (%rsi,%rdi,1),%r10
                      int next_task = abs((nn + 1) % data->thread_count);
    6e47:	89 c8                	mov    %ecx,%eax
    6e49:	99                   	cltd
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6e4a:	4d 01 e2             	add    %r12,%r10
                      int next_task = abs((nn + 1) % data->thread_count);
    6e4d:	41 f7 fb             	idiv   %r11d
    return mailbox->lower;
    6e50:	4d 8b 32             	mov    (%r10),%r14
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6e53:	48 63 d2             	movslq %edx,%rdx
    6e56:	48 c1 e2 09          	shl    $0x9,%rdx
    6e5a:	49 8b 84 11 70 01 00 00 	mov    0x170(%r9,%rdx,1),%rax
    mailbox->lower = data;
    6e62:	49 8b 52 08          	mov    0x8(%r10),%rdx
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6e66:	4c 01 c0             	add    %r8,%rax
    return mailbox->higher;
    6e69:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    6e6d:	48 89 10             	mov    %rdx,(%rax)
    return mailbox->lower;
    6e70:	66 0f 6f c8          	movdqa %xmm0,%xmm1
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6e74:	0f 12 d0             	movhlps %xmm0,%xmm2
    return mailbox->lower;
    6e77:	66 0f c6 c8 01       	shufpd $0x1,%xmm0,%xmm1
    mailbox->lower = data;
    6e7c:	41 0f 11 0a          	movups %xmm1,(%r10)
    mailbox->higher = data;
    6e80:	4c 89 70 08          	mov    %r14,0x8(%rax)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6e84:	49 8b 14 39          	mov    (%r9,%rdi,1),%rdx
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6e88:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6e8f:	4d 8b 52 08          	mov    0x8(%r10),%r10
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6e93:	48 8b 00             	mov    (%rax),%rax
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6e96:	4a 8b 54 02 08       	mov    0x8(%rdx,%r8,1),%rdx
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6e9b:	41 c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%r10)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6ea6:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    6eb0:	41 c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r10)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6ebb:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6ec5:	66 48 0f 7e d2       	movq   %xmm2,%rdx
    6eca:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6ed4:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6ede:	44 39 d9             	cmp    %r11d,%ecx
    6ee1:	0f 85 59 ff ff ff    	jne    6e40 <barriered_work+0x460>
    6ee7:	4c 8b 75 a8          	mov    -0x58(%rbp),%r14
    6eeb:	4c 8b 55 a0          	mov    -0x60(%rbp),%r10
                    pthread_mutex_unlock(&data->thread->swapmutex[min]);
    6eef:	49 03 9a c8 00 00 00 	add    0xc8(%r10),%rbx
    6ef6:	48 89 df             	mov    %rbx,%rdi
    6ef9:	e8 c2 b5 ff ff       	call   24c0 <pthread_mutex_unlock@plt>
                    pthread_mutex_unlock(&data->thread->swapmutex[max]);
    6efe:	48 8b 5d c0          	mov    -0x40(%rbp),%rbx
    6f02:	48 8b 7d b0          	mov    -0x50(%rbp),%rdi
    6f06:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6f0d:	48 03 b8 c8 00 00 00 	add    0xc8(%rax),%rdi
    6f14:	e8 a7 b5 ff ff       	call   24c0 <pthread_mutex_unlock@plt>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6f19:	48 63 83 34 01 00 00 	movslq 0x134(%rbx),%rax
    6f20:	85 c0                	test   %eax,%eax
    6f22:	0f 8e 7d 00 00 00    	jle    6fa5 <barriered_work+0x5c5>
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6f28:	48 8b 5d c0          	mov    -0x40(%rbp),%rbx
    6f2c:	48 c1 e0 09          	shl    $0x9,%rax
    6f30:	4c 8d 80 70 01 00 00 	lea    0x170(%rax),%r8
    6f37:	b8 70 01 00 00       	mov    $0x170,%eax
    6f3c:	48 8b bb 28 01 00 00 	mov    0x128(%rbx),%rdi
    6f43:	48 8b 57 20          	mov    0x20(%rdi),%rdx
    6f47:	4e 8b 5c 2a 38       	mov    0x38(%rdx,%r13,1),%r11
    6f4c:	4e 8d 2c f5 00 00 00 00 	lea    0x0(,%r14,8),%r13
    6f54:	4e 8b 4c 3a 38       	mov    0x38(%rdx,%r15,1),%r9
    6f59:	4d 29 f5             	sub    %r14,%r13
    6f5c:	49 c1 e5 03          	shl    $0x3,%r13
    6f60:	49 8b 14 01          	mov    (%r9,%rax,1),%rdx
    6f64:	49 8b 0c 03          	mov    (%r11,%rax,1),%rcx
    6f68:	4a 8b 1c 2a          	mov    (%rdx,%r13,1),%rbx
    6f6c:	4a 39 1c 21          	cmp    %rbx,(%rcx,%r12,1)
    6f70:	74 4a                	je     6fbc <barriered_work+0x5dc>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6f72:	48 05 00 02 00 00    	add    $0x200,%rax
    6f78:	49 39 c0             	cmp    %rax,%r8
    6f7b:	75 e3                	jne    6f60 <barriered_work+0x580>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6f7d:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    6f81:	44 8b 88 40 01 00 00 	mov    0x140(%rax),%r9d
    6f88:	e9 a3 fd ff ff       	jmp    6d30 <barriered_work+0x350>
  if (b > a) { return b; }
    6f8d:	48 63 c1             	movslq %ecx,%rax
    6f90:	48 0f 4d c2          	cmovge %rdx,%rax
    6f94:	4c 89 f2             	mov    %r14,%rdx
    6f97:	e9 0a fe ff ff       	jmp    6da6 <barriered_work+0x3c6>
    6f9c:	4c 63 6d 9c          	movslq -0x64(%rbp),%r13
    6fa0:	e9 e5 fa ff ff       	jmp    6a8a <barriered_work+0xaa>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6fa5:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    6fa9:	44 8b 88 40 01 00 00 	mov    0x140(%rax),%r9d
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6fb0:	48 8b b8 28 01 00 00 	mov    0x128(%rax),%rdi
    6fb7:	e9 74 fd ff ff       	jmp    6d30 <barriered_work+0x350>
    6fbc:	bf 01 00 00 00       	mov    $0x1,%edi
    6fc1:	48 8d 35 63 12 00 00 	lea    0x1263(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6fc8:	31 c0                	xor    %eax,%eax
    6fca:	e8 41 b5 ff ff       	call   2510 <__printf_chk@plt>
                          exit(1);
    6fcf:	bf 01 00 00 00       	mov    $0x1,%edi
    6fd4:	e8 a7 b5 ff ff       	call   2580 <exit@plt>
    6fd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006fe0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6fe0:	f3 0f 1e fa          	endbr64
    6fe4:	55                   	push   %rbp
    6fe5:	48 89 e5             	mov    %rsp,%rbp
    6fe8:	53                   	push   %rbx
    6fe9:	48 83 ec 08          	sub    $0x8,%rsp
    6fed:	ff 15 f5 3f 00 00    	call   *0x3ff5(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    6ff3:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6ff6:	e8 05 f2 ff ff       	call   6200 <barriered_work_ingest>
  barriered_work(data);
    6ffb:	48 89 df             	mov    %rbx,%rdi
}
    6ffe:	48 8b 5d f8          	mov    -0x8(%rbp),%rbx
    7002:	c9                   	leave
  barriered_work(data);
    7003:	e9 d8 f9 ff ff       	jmp    69e0 <barriered_work>
    7008:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000007010 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    7010:	f3 0f 1e fa          	endbr64
    7014:	55                   	push   %rbp
    7015:	48 89 e5             	mov    %rsp,%rbp
    7018:	ff 15 ca 3f 00 00    	call   *0x3fca(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  if (kind == 0) {
    701e:	85 f6                	test   %esi,%esi
    7020:	74 1e                	je     7040 <mailboxkind+0x30>
  return NULL;
    7022:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    7024:	83 fe 01             	cmp    $0x1,%esi
    7027:	74 07                	je     7030 <mailboxkind+0x20>
}
    7029:	5d                   	pop    %rbp
    702a:	c3                   	ret
    702b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    return mailbox->higher;
    7030:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    7034:	5d                   	pop    %rbp
    7035:	c3                   	ret
    7036:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    return mailbox->lower;
    7040:	48 8b 07             	mov    (%rdi),%rax
}
    7043:	5d                   	pop    %rbp
    7044:	c3                   	ret
    7045:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000007050 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    7050:	f3 0f 1e fa          	endbr64
    7054:	55                   	push   %rbp
    7055:	48 89 e5             	mov    %rsp,%rbp
    7058:	ff 15 8a 3f 00 00    	call   *0x3f8a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  if (kind == 0) {
    705e:	85 d2                	test   %edx,%edx
    7060:	75 0e                	jne    7070 <setmailboxkind+0x20>
    mailbox->lower = data;
    7062:	48 89 37             	mov    %rsi,(%rdi)
}
    7065:	31 c0                	xor    %eax,%eax
    7067:	5d                   	pop    %rbp
    7068:	c3                   	ret
    7069:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (kind == 1) {
    7070:	83 fa 01             	cmp    $0x1,%edx
    7073:	74 13                	je     7088 <setmailboxkind+0x38>
  if (kind == 2) {
    7075:	83 fa 02             	cmp    $0x2,%edx
    7078:	75 eb                	jne    7065 <setmailboxkind+0x15>
}
    707a:	31 c0                	xor    %eax,%eax
    mailbox->pending = data;
    707c:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
    7080:	5d                   	pop    %rbp
    7081:	c3                   	ret
    7082:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    7088:	31 c0                	xor    %eax,%eax
    mailbox->higher = data;
    708a:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    708e:	5d                   	pop    %rbp
    708f:	c3                   	ret

0000000000007090 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    7090:	f3 0f 1e fa          	endbr64
    7094:	55                   	push   %rbp
    7095:	48 89 e5             	mov    %rsp,%rbp
    7098:	ff 15 4a 3f 00 00    	call   *0x3f4a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
}
    709e:	31 c0                	xor    %eax,%eax
    70a0:	5d                   	pop    %rbp
    70a1:	c3                   	ret
    70a2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    70ad:	0f 1f 00             	nopl   (%rax)

00000000000070b0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    70b0:	f3 0f 1e fa          	endbr64
    70b4:	55                   	push   %rbp
    70b5:	48 89 e5             	mov    %rsp,%rbp
    70b8:	ff 15 2a 3f 00 00    	call   *0x3f2a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    70be:	31 c0                	xor    %eax,%eax
    70c0:	5d                   	pop    %rbp
    70c1:	c3                   	ret
    70c2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    70cd:	0f 1f 00             	nopl   (%rax)

00000000000070d0 <after>:
int after(struct timespec left, struct timespec right) {
    70d0:	f3 0f 1e fa          	endbr64
    70d4:	55                   	push   %rbp
    70d5:	48 89 e5             	mov    %rsp,%rbp
    70d8:	ff 15 0a 3f 00 00    	call   *0x3f0a(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  return left.tv_sec > right.tv_sec &&
    70de:	31 c0                	xor    %eax,%eax
    70e0:	48 39 d7             	cmp    %rdx,%rdi
    70e3:	7e 08                	jle    70ed <after+0x1d>
    70e5:	31 c0                	xor    %eax,%eax
    70e7:	48 39 ce             	cmp    %rcx,%rsi
    70ea:	0f 9f c0             	setg   %al
}
    70ed:	5d                   	pop    %rbp
    70ee:	c3                   	ret
    70ef:	90                   	nop

00000000000070f0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    70f0:	f3 0f 1e fa          	endbr64
    70f4:	55                   	push   %rbp
    70f5:	48 89 e5             	mov    %rsp,%rbp
    70f8:	ff 15 ea 3e 00 00    	call   *0x3eea(%rip)        # afe8 <mcount@GLIBC_2.2.5>
  return 0;
    70fe:	31 c0                	xor    %eax,%eax
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    7100:	4c 8b 5d 10          	mov    0x10(%rbp),%r11
    7104:	4c 8b 55 18          	mov    0x18(%rbp),%r10
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7108:	48 39 d7             	cmp    %rdx,%rdi
    710b:	7f 18                	jg     7125 <within+0x35>
    710d:	4d 39 d8             	cmp    %r11,%r8
    7110:	0f 9e c2             	setle  %dl
    7113:	48 39 ce             	cmp    %rcx,%rsi
    7116:	0f 9e c0             	setle  %al
    7119:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    711b:	31 c0                	xor    %eax,%eax
    711d:	4d 39 d1             	cmp    %r10,%r9
    7120:	0f 9e c0             	setle  %al
    7123:	21 d0                	and    %edx,%eax
}
    7125:	5d                   	pop    %rbp
    7126:	c3                   	ret
    7127:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007130 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    7130:	f3 0f 1e fa          	endbr64
    7134:	55                   	push   %rbp
    7135:	48 89 e5             	mov    %rsp,%rbp
    7138:	ff 15 aa 3e 00 00    	call   *0x3eaa(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    713e:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    7142:	48 8b 75 30          	mov    0x30(%rbp),%rsi
    7146:	4c 8b 4d 20          	mov    0x20(%rbp),%r9
    714a:	4c 8b 55 28          	mov    0x28(%rbp),%r10
    714e:	4c 8b 45 40          	mov    0x40(%rbp),%r8
    7152:	4c 8b 5d 48          	mov    0x48(%rbp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    7156:	48 8b 4d 18          	mov    0x18(%rbp),%rcx
    715a:	48 8b 55 38          	mov    0x38(%rbp),%rdx
  return left.tv_sec > right.tv_sec &&
    715e:	48 39 fe             	cmp    %rdi,%rsi
    7161:	7d 2d                	jge    7190 <overlap+0x60>
    7163:	48 39 ca             	cmp    %rcx,%rdx
    7166:	7d 60                	jge    71c8 <overlap+0x98>
    7168:	4d 39 da             	cmp    %r11,%r10
    716b:	7d 0a                	jge    7177 <overlap+0x47>
    return 1;
    716d:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    7172:	4d 39 c1             	cmp    %r8,%r9
    7175:	7c 0f                	jl     7186 <overlap+0x56>
  return 0;
    7177:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7179:	4d 39 c1             	cmp    %r8,%r9
    717c:	7f 08                	jg     7186 <overlap+0x56>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    717e:	31 c0                	xor    %eax,%eax
    7180:	4d 39 da             	cmp    %r11,%r10
    7183:	0f 9e c0             	setle  %al
}
    7186:	5d                   	pop    %rbp
    7187:	c3                   	ret
    7188:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7190:	7e 56                	jle    71e8 <overlap+0xb8>
    7192:	48 39 ca             	cmp    %rcx,%rdx
    7195:	7f 39                	jg     71d0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7197:	75 31                	jne    71ca <overlap+0x9a>
    7199:	4d 39 c1             	cmp    %r8,%r9
    719c:	7c 2c                	jl     71ca <overlap+0x9a>
    return 1;
    719e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    71a3:	4d 39 da             	cmp    %r11,%r10
    71a6:	7d de                	jge    7186 <overlap+0x56>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71a8:	48 39 ca             	cmp    %rcx,%rdx
}
    71ab:	5d                   	pop    %rbp
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71ac:	0f 94 c2             	sete   %dl
    71af:	48 39 fe             	cmp    %rdi,%rsi
    71b2:	0f 94 c0             	sete   %al
    71b5:	21 c2                	and    %eax,%edx
    71b7:	31 c0                	xor    %eax,%eax
    71b9:	4d 39 c1             	cmp    %r8,%r9
    71bc:	0f 94 c0             	sete   %al
    71bf:	21 d0                	and    %edx,%eax
}
    71c1:	c3                   	ret
    71c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71c8:	74 ad                	je     7177 <overlap+0x47>
  return 0;
    71ca:	31 c0                	xor    %eax,%eax
}
    71cc:	5d                   	pop    %rbp
    71cd:	c3                   	ret
    71ce:	66 90                	xchg   %ax,%ax
  return left.tv_sec > right.tv_sec &&
    71d0:	4d 39 da             	cmp    %r11,%r10
    71d3:	7e c4                	jle    7199 <overlap+0x69>
    return 1;
    71d5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    71da:	4d 39 c1             	cmp    %r8,%r9
    71dd:	7e ba                	jle    7199 <overlap+0x69>
    71df:	eb a5                	jmp    7186 <overlap+0x56>
    71e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71e8:	48 39 ca             	cmp    %rcx,%rdx
    71eb:	7c 8a                	jl     7177 <overlap+0x47>
    71ed:	4d 39 c1             	cmp    %r8,%r9
    71f0:	7d ac                	jge    719e <overlap+0x6e>
    71f2:	48 39 ca             	cmp    %rcx,%rdx
    71f5:	74 87                	je     717e <overlap+0x4e>
  return 0;
    71f7:	31 c0                	xor    %eax,%eax
    71f9:	eb d1                	jmp    71cc <overlap+0x9c>
    71fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000007200 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    7200:	f3 0f 1e fa          	endbr64
    7204:	55                   	push   %rbp
    7205:	48 89 e5             	mov    %rsp,%rbp
    7208:	41 57                	push   %r15
    720a:	41 56                	push   %r14
    720c:	41 55                	push   %r13
    720e:	41 54                	push   %r12
    7210:	53                   	push   %rbx
    7211:	48 83 ec 58          	sub    $0x58,%rsp
    7215:	ff 15 cd 3d 00 00    	call   *0x3dcd(%rip)        # afe8 <mcount@GLIBC_2.2.5>
    721b:	41 89 f4             	mov    %esi,%r12d
  for (int x = 0 ; x < thread_count; x++) {
    721e:	85 f6                	test   %esi,%esi
    7220:	0f 8e df 02 00 00    	jle    7505 <verify+0x305>
    7226:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    722a:	45 31 ff             	xor    %r15d,%r15d
    722d:	48 89 5d b8          	mov    %rbx,-0x48(%rbp)
    for (int z = 0 ; z < thread_count; z++) {
    7231:	48 89 5d c0          	mov    %rbx,-0x40(%rbp)
    7235:	45 31 ed             	xor    %r13d,%r13d
    7238:	45 89 e6             	mov    %r12d,%r14d
      if (z != x)  {
    723b:	45 39 ef             	cmp    %r13d,%r15d
    723e:	0f 84 27 02 00 00    	je     746b <verify+0x26b>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    7244:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    7248:	8b 50 08             	mov    0x8(%rax),%edx
    724b:	85 d2                	test   %edx,%edx
    724d:	0f 8e 18 02 00 00    	jle    746b <verify+0x26b>
    7253:	48 89 5d 98          	mov    %rbx,-0x68(%rbp)
    7257:	45 31 e4             	xor    %r12d,%r12d
    725a:	44 89 6d 94          	mov    %r13d,-0x6c(%rbp)
    725e:	44 89 75 90          	mov    %r14d,-0x70(%rbp)
    7262:	4d 89 e6             	mov    %r12,%r14
    7265:	44 89 fa             	mov    %r15d,%edx
    7268:	48 8d 35 e7 0f 00 00 	lea    0xfe7(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    726f:	bf 01 00 00 00       	mov    $0x1,%edi
    7274:	31 c0                	xor    %eax,%eax
    7276:	e8 95 b2 ff ff       	call   2510 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    727b:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    727f:	8b 40 08             	mov    0x8(%rax),%eax
    7282:	85 c0                	test   %eax,%eax
    7284:	0f 8e c3 01 00 00    	jle    744d <verify+0x24d>
    728a:	4c 89 f0             	mov    %r14,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    728d:	4c 89 75 88          	mov    %r14,-0x78(%rbp)
    7291:	31 db                	xor    %ebx,%ebx
    7293:	48 c1 e0 09          	shl    $0x9,%rax
    7297:	44 89 7d 84          	mov    %r15d,-0x7c(%rbp)
    729b:	48 89 45 c8          	mov    %rax,-0x38(%rbp)
    729f:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    72a3:	4c 8b 08             	mov    (%rax),%r9
    72a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    72b0:	4c 8b 65 c0          	mov    -0x40(%rbp),%r12
    72b4:	4c 8b 7d c8          	mov    -0x38(%rbp),%r15
    72b8:	49 89 de             	mov    %rbx,%r14
    72bb:	bf 01 00 00 00       	mov    $0x1,%edi
    72c0:	49 c1 e6 09          	shl    $0x9,%r14
    72c4:	48 8d 35 a0 0f 00 00 	lea    0xfa0(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    72cb:	49 8b 04 24          	mov    (%r12),%rax
    72cf:	4b 8b 8c 39 60 01 00 00 	mov    0x160(%r9,%r15,1),%rcx
    72d7:	4c 89 75 a8          	mov    %r14,-0x58(%rbp)
    72db:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    72e3:	31 c0                	xor    %eax,%eax
    72e5:	e8 26 b2 ff ff       	call   2510 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    72ea:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    72ee:	4c 8b 08             	mov    (%rax),%r9
    72f1:	4b 83 bc 39 60 01 00 00 00 	cmpq   $0x0,0x160(%r9,%r15,1)
    72fa:	0f 8e 34 01 00 00    	jle    7434 <verify+0x234>
    7300:	4d 03 34 24          	add    (%r12),%r14
    7304:	48 89 5d a0          	mov    %rbx,-0x60(%rbp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7308:	ba 01 00 00 00       	mov    $0x1,%edx
    730d:	4d 89 f5             	mov    %r14,%r13
    7310:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7317:	4d 85 f6             	test   %r14,%r14
    731a:	0f 8e 10 01 00 00    	jle    7430 <verify+0x230>
    7320:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    7324:	49 89 d4             	mov    %rdx,%r12
    7327:	48 89 55 b0          	mov    %rdx,-0x50(%rbp)
    732b:	31 db                	xor    %ebx,%ebx
    732d:	49 c1 e4 05          	shl    $0x5,%r12
    7331:	49 83 ec 20          	sub    $0x20,%r12
    7335:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
    7339:	eb 32                	jmp    736d <verify+0x16d>
    733b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7340:	4c 39 c1             	cmp    %r8,%rcx
    7343:	0f 8d 47 01 00 00    	jge    7490 <verify+0x290>
    7349:	4c 39 d7             	cmp    %r10,%rdi
    734c:	7e 05                	jle    7353 <verify+0x153>
    734e:	49 39 c3             	cmp    %rax,%r11
    7351:	7c 75                	jl     73c8 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7353:	4c 39 d7             	cmp    %r10,%rdi
    7356:	0f 8d 9b 01 00 00    	jge    74f7 <verify+0x2f7>
    735c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7360:	48 83 c3 01          	add    $0x1,%rbx
    7364:	49 39 de             	cmp    %rbx,%r14
    7367:	0f 8e a2 00 00 00    	jle    740f <verify+0x20f>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    736d:	49 8b 8f 50 01 00 00 	mov    0x150(%r15),%rcx
    7374:	48 89 d8             	mov    %rbx,%rax
    7377:	48 c1 e0 05          	shl    $0x5,%rax
    737b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    7382:	4c 01 e1             	add    %r12,%rcx
    7385:	48 8b 30             	mov    (%rax),%rsi
    7388:	48 8b 78 10          	mov    0x10(%rax),%rdi
    738c:	48 8b 11             	mov    (%rcx),%rdx
    738f:	4c 8b 41 08          	mov    0x8(%rcx),%r8
    7393:	4c 8b 51 10          	mov    0x10(%rcx),%r10
    7397:	4c 8b 59 18          	mov    0x18(%rcx),%r11
    739b:	48 8b 48 08          	mov    0x8(%rax),%rcx
    739f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    73a3:	48 39 d6             	cmp    %rdx,%rsi
    73a6:	7c 98                	jl     7340 <verify+0x140>
    73a8:	0f 8e 32 01 00 00    	jle    74e0 <verify+0x2e0>
    73ae:	4c 39 c1             	cmp    %r8,%rcx
    73b1:	0f 8f e9 00 00 00    	jg     74a0 <verify+0x2a0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    73b7:	75 a7                	jne    7360 <verify+0x160>
    73b9:	4c 39 d7             	cmp    %r10,%rdi
    73bc:	7f a2                	jg     7360 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    73be:	49 39 c3             	cmp    %rax,%r11
    73c1:	7c 9d                	jl     7360 <verify+0x160>
    73c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    73c8:	49 89 c1             	mov    %rax,%r9
    73cb:	48 89 f9             	mov    %rdi,%rcx
    73ce:	48 8d 35 6b 12 00 00 	lea    0x126b(%rip),%rsi        # 8640 <_IO_stdin_used+0x640>
    73d5:	31 c0                	xor    %eax,%eax
    73d7:	bf 01 00 00 00       	mov    $0x1,%edi
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    73dc:	48 83 c3 01          	add    $0x1,%rbx
    73e0:	e8 2b b1 ff ff       	call   2510 <__printf_chk@plt>
    73e5:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    73e9:	4c 8b 6d a8          	mov    -0x58(%rbp),%r13
    73ed:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    73f0:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    73f4:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    73fb:	4c 8b 08             	mov    (%rax),%r9
    73fe:	48 8b 45 c8          	mov    -0x38(%rbp),%rax
    7402:	4d 8d 3c 01          	lea    (%r9,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7406:	49 39 de             	cmp    %rbx,%r14
    7409:	0f 8f 5e ff ff ff    	jg     736d <verify+0x16d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    740f:	48 8b 55 b0          	mov    -0x50(%rbp),%rdx
    7413:	49 3b 97 60 01 00 00 	cmp    0x160(%r15),%rdx
    741a:	7d 14                	jge    7430 <verify+0x230>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    741c:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7423:	48 83 c2 01          	add    $0x1,%rdx
    7427:	4d 85 f6             	test   %r14,%r14
    742a:	0f 8f f0 fe ff ff    	jg     7320 <verify+0x120>
    7430:	48 8b 5d a0          	mov    -0x60(%rbp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    7434:	48 8b 45 c0          	mov    -0x40(%rbp),%rax
    7438:	48 83 c3 01          	add    $0x1,%rbx
    743c:	39 58 08             	cmp    %ebx,0x8(%rax)
    743f:	0f 8f 6b fe ff ff    	jg     72b0 <verify+0xb0>
    7445:	4c 8b 75 88          	mov    -0x78(%rbp),%r14
    7449:	44 8b 7d 84          	mov    -0x7c(%rbp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    744d:	48 8b 45 b8          	mov    -0x48(%rbp),%rax
    7451:	49 83 c6 01          	add    $0x1,%r14
    7455:	44 39 70 08          	cmp    %r14d,0x8(%rax)
    7459:	0f 8f 06 fe ff ff    	jg     7265 <verify+0x65>
    745f:	48 8b 5d 98          	mov    -0x68(%rbp),%rbx
    7463:	44 8b 6d 94          	mov    -0x6c(%rbp),%r13d
    7467:	44 8b 75 90          	mov    -0x70(%rbp),%r14d
    for (int z = 0 ; z < thread_count; z++) {
    746b:	41 8d 45 01          	lea    0x1(%r13),%eax
    746f:	48 81 45 c0 d8 00 00 00 	addq   $0xd8,-0x40(%rbp)
    7477:	41 39 c6             	cmp    %eax,%r14d
    747a:	0f 84 96 00 00 00    	je     7516 <verify+0x316>
    7480:	41 89 c5             	mov    %eax,%r13d
    7483:	e9 b3 fd ff ff       	jmp    723b <verify+0x3b>
    7488:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7490:	0f 85 ca fe ff ff    	jne    7360 <verify+0x160>
    7496:	e9 b8 fe ff ff       	jmp    7353 <verify+0x153>
    749b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    74a0:	49 39 c3             	cmp    %rax,%r11
    74a3:	7e 09                	jle    74ae <verify+0x2ae>
    74a5:	4c 39 d7             	cmp    %r10,%rdi
    74a8:	0f 8c 1a ff ff ff    	jl     73c8 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    74ae:	4c 39 d7             	cmp    %r10,%rdi
    74b1:	0f 8f a9 fe ff ff    	jg     7360 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    74b7:	49 39 c3             	cmp    %rax,%r11
    74ba:	0f 8d 08 ff ff ff    	jge    73c8 <verify+0x1c8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    74c0:	48 39 d6             	cmp    %rdx,%rsi
    74c3:	0f 85 97 fe ff ff    	jne    7360 <verify+0x160>
    74c9:	4c 39 c1             	cmp    %r8,%rcx
    74cc:	0f 85 8e fe ff ff    	jne    7360 <verify+0x160>
    74d2:	4c 39 d7             	cmp    %r10,%rdi
    74d5:	0f 84 ed fe ff ff    	je     73c8 <verify+0x1c8>
    74db:	e9 80 fe ff ff       	jmp    7360 <verify+0x160>
    74e0:	4c 39 c1             	cmp    %r8,%rcx
    74e3:	0f 8c 6a fe ff ff    	jl     7353 <verify+0x153>
    74e9:	4c 39 d7             	cmp    %r10,%rdi
    74ec:	7e c9                	jle    74b7 <verify+0x2b7>
    74ee:	4c 39 c1             	cmp    %r8,%rcx
    74f1:	0f 85 69 fe ff ff    	jne    7360 <verify+0x160>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    74f7:	49 39 c3             	cmp    %rax,%r11
    74fa:	0f 8f 60 fe ff ff    	jg     7360 <verify+0x160>
    7500:	e9 c3 fe ff ff       	jmp    73c8 <verify+0x1c8>
}
    7505:	48 83 c4 58          	add    $0x58,%rsp
    7509:	31 c0                	xor    %eax,%eax
    750b:	5b                   	pop    %rbx
    750c:	41 5c                	pop    %r12
    750e:	41 5d                	pop    %r13
    7510:	41 5e                	pop    %r14
    7512:	41 5f                	pop    %r15
    7514:	5d                   	pop    %rbp
    7515:	c3                   	ret
  for (int x = 0 ; x < thread_count; x++) {
    7516:	48 81 45 b8 d8 00 00 00 	addq   $0xd8,-0x48(%rbp)
    751e:	45 89 f4             	mov    %r14d,%r12d
    7521:	41 8d 57 01          	lea    0x1(%r15),%edx
    7525:	45 39 ef             	cmp    %r13d,%r15d
    7528:	74 db                	je     7505 <verify+0x305>
    752a:	41 89 d7             	mov    %edx,%r15d
    752d:	e9 ff fc ff ff       	jmp    7231 <verify+0x31>
    7532:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    753c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000007540 <atexit>:
    7540:	f3 0f 1e fa          	endbr64
    7544:	48 8b 15 bd 3a 00 00 	mov    0x3abd(%rip),%rdx        # b008 <__dso_handle>
    754b:	31 f6                	xor    %esi,%esi
    754d:	e9 1e b0 ff ff       	jmp    2570 <__cxa_atexit@plt>
    7552:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    755c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000007560 <__stack_chk_fail_local>:
    7560:	f3 0f 1e fa          	endbr64
    7564:	50                   	push   %rax
    7565:	58                   	pop    %rax
    7566:	48 83 ec 08          	sub    $0x8,%rsp
    756a:	e8 51 ae ff ff       	call   23c0 <__stack_chk_fail@plt>

Disassembly of section .fini:

0000000000007570 <_fini>:
    7570:	f3 0f 1e fa          	endbr64
    7574:	48 83 ec 08          	sub    $0x8,%rsp
    7578:	48 83 c4 08          	add    $0x8,%rsp
    757c:	c3                   	ret
