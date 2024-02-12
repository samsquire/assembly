
multibarrier-evented2:     file format elf64-x86-64


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
    2676:	48 8d 3d eb 5f 00 00 	lea    0x5feb(%rip),%rdi        # 8668 <_IO_stdin_used+0x668>
    267d:	41 56                	push   %r14
    267f:	41 55                	push   %r13
    2681:	41 54                	push   %r12
    2683:	55                   	push   %rbp
    2684:	48 8d 2d f1 5c 00 00 	lea    0x5cf1(%rip),%rbp        # 837c <_IO_stdin_used+0x37c>
    268b:	53                   	push   %rbx
    268c:	48 81 ec 08 01 00 00 	sub    $0x108,%rsp
    2693:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    269c:	48 89 84 24 f8 00 00 00 	mov    %rax,0xf8(%rsp)
    26a4:	48 8d 05 05 1e 00 00 	lea    0x1e05(%rip),%rax        # 44b0 <barriered_reset>
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
    27b7:	48 8d 35 12 5f 00 00 	lea    0x5f12(%rip),%rsi        # 86d0 <_IO_stdin_used+0x6d0>
    27be:	31 c0                	xor    %eax,%eax
    27c0:	bf 01 00 00 00       	mov    $0x1,%edi
    27c5:	e8 e6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27ca:	ba 01 00 00 00       	mov    $0x1,%edx
    27cf:	48 8d 35 2a 5f 00 00 	lea    0x5f2a(%rip),%rsi        # 8700 <_IO_stdin_used+0x700>
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
    282d:	be d8 00 00 00       	mov    $0xd8,%esi
  
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
    283d:	48 89 84 24 a0 00 00 00 	mov    %rax,0xa0(%rsp)
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
    2868:	48 89 84 24 d0 00 00 00 	mov    %rax,0xd0(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    2870:	e8 8b fb ff ff       	call   2400 <calloc@plt>
    2875:	48 89 84 24 d8 00 00 00 	mov    %rax,0xd8(%rsp)
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
    290c:	48 89 84 24 c0 00 00 00 	mov    %rax,0xc0(%rsp)
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
    2972:	48 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%rsi
    297a:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  int swap = 0;
    297f:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    2987:	45 31 f6             	xor    %r14d,%r14d
  int curcpu = 0;
    298a:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
  int dataid = 0;
    2992:	45 31 e4             	xor    %r12d,%r12d
    2995:	45 89 f7             	mov    %r14d,%r15d
    2998:	48 89 b4 24 90 00 00 00 	mov    %rsi,0x90(%rsp)
    29a0:	48 89 9c 24 a8 00 00 00 	mov    %rbx,0xa8(%rsp)
  int cur_buffer = 0;
    29a8:	c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    29b3:	48 63 84 24 80 00 00 00 	movslq 0x80(%rsp),%rax
    29bb:	44 89 bc 24 84 00 00 00 	mov    %r15d,0x84(%rsp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
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
    2a0b:	48 8d 35 16 5d 00 00 	lea    0x5d16(%rip),%rsi        # 8728 <_IO_stdin_used+0x728>
    2a12:	31 c0                	xor    %eax,%eax
    2a14:	bf 01 00 00 00       	mov    $0x1,%edi
    2a19:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      int x = (k * threads_per_group) + d;
    2a1e:	45 8d 7e ff          	lea    -0x1(%r14),%r15d
    2a22:	44 89 f9             	mov    %r15d,%ecx
    2a25:	e8 86 fa ff ff       	call   24b0 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a2a:	be 08 00 00 00       	mov    $0x8,%esi
    2a2f:	bf 02 00 00 00       	mov    $0x2,%edi
    2a34:	e8 c7 f9 ff ff       	call   2400 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a39:	be 80 00 00 00       	mov    $0x80,%esi
    2a3e:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a43:	48 89 c3             	mov    %rax,%rbx
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a46:	e8 b5 f9 ff ff       	call   2400 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2a4b:	45 89 f8             	mov    %r15d,%r8d
    2a4e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2a53:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a57:	48 89 c5             	mov    %rax,%rbp
      if (x % 2 == 1) {
    2a5a:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2a5f:	0f 84 f0 10 00 00    	je     3b55 <main+0x14e5>
        other = abs(x - 1) % total_threads;
    2a65:	45 89 f5             	mov    %r14d,%r13d
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    2a68:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
        my_thread_data[1] = &thread_data[x]; 
    2a6d:	4c 89 ca             	mov    %r9,%rdx
        other = abs(x - 1) % total_threads;
    2a70:	41 8d 45 fe          	lea    -0x2(%r13),%eax
    2a74:	49 89 c6             	mov    %rax,%r14
        my_thread_data[0] = &thread_data[other]; 
    2a77:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2a7b:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    2a7f:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2a83:	48 8d 73 08          	lea    0x8(%rbx),%rsi
    2a87:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    2a8c:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
    2a94:	48 89 03             	mov    %rax,(%rbx)
    2a97:	44 89 f1             	mov    %r14d,%ecx
    2a9a:	48 8d 35 b7 5c 00 00 	lea    0x5cb7(%rip),%rsi        # 8758 <_IO_stdin_used+0x758>
        thread_data[x].thread_index = 1;
    2aa1:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2aa5:	31 c0                	xor    %eax,%eax
        thread_data[x].protected_state = &protected_state[k];
    2aa7:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2aab:	bf 01 00 00 00       	mov    $0x1,%edi
    2ab0:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    2ab4:	44 89 fa             	mov    %r15d,%edx
    2ab7:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2abc:	e8 ef f9 ff ff       	call   24b0 <__printf_chk@plt>
      thread_data[x].other = other;
    2ac1:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2ac6:	8b 4c 24 7c          	mov    0x7c(%rsp),%ecx
    2aca:	31 c0                	xor    %eax,%eax
    2acc:	44 89 fa             	mov    %r15d,%edx
    2acf:	48 8d 35 b2 5c 00 00 	lea    0x5cb2(%rip),%rsi        # 8788 <_IO_stdin_used+0x788>
    2ad6:	bf 01 00 00 00       	mov    $0x1,%edi
    2adb:	45 89 b1 b8 00 00 00 	mov    %r14d,0xb8(%r9)
    2ae2:	e8 c9 f9 ff ff       	call   24b0 <__printf_chk@plt>
        if (x < thread_count) {
    2ae7:	41 83 ff 01          	cmp    $0x1,%r15d
    2aeb:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2af0:	0f 87 89 10 00 00    	ja     3b7f <main+0x150f>
          CPU_SET(curcpu, sendercpu);
    2af6:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2afb:	48 89 c7             	mov    %rax,%rdi
    2afe:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2b04:	77 13                	ja     2b19 <main+0x4a9>
    2b06:	48 c1 e8 06          	shr    $0x6,%rax
    2b0a:	ba 01 00 00 00       	mov    $0x1,%edx
    2b0f:	89 f9                	mov    %edi,%ecx
    2b11:	48 d3 e2             	shl    %cl,%rdx
    2b14:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
          curcpu += 2;
    2b19:	83 44 24 7c 02       	addl   $0x2,0x7c(%rsp)
      thread_data[x].real_thread_index = x;
    2b1e:	45 89 79 08          	mov    %r15d,0x8(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b22:	be 10 00 00 00       	mov    $0x10,%esi
    2b27:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].swapmutex = swapmutex;
    2b2c:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    2b34:	49 89 a9 b0 00 00 00 	mov    %rbp,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2b3b:	31 ed                	xor    %ebp,%ebp
      thread_data[x].swapmutex = swapmutex;
    2b3d:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2b44:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2b4c:	49 89 59 18          	mov    %rbx,0x18(%r9)
            data[0].messages_count = 0;
    2b50:	44 89 fb             	mov    %r15d,%ebx
      thread_data[x].mswapmutex = mswapmutex;
    2b53:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].all_threads = thread_data;
    2b5a:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].kind = KERNEL_THREAD;
    2b5f:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].all_threads = thread_data;
    2b66:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2b6a:	48 8b 05 5f 61 00 00 	mov    0x615f(%rip),%rax        # 8cd0 <_IO_stdin_used+0xcd0>
      thread_data[x].task_count = total_barrier_count;
    2b71:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].group_count = group_count;
    2b79:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2b80:	48 8b 05 51 61 00 00 	mov    0x6151(%rip),%rax        # 8cd8 <_IO_stdin_used+0xcd8>
      thread_data[x].task_count = total_barrier_count;
    2b87:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].thread_count = 2;
    2b8c:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b90:	e8 6b f8 ff ff       	call   2400 <calloc@plt>
    2b95:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2b9a:	be 10 00 00 00       	mov    $0x10,%esi
    2b9f:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2ba4:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2ba8:	e8 53 f8 ff ff       	call   2400 <calloc@plt>
    2bad:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bb2:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2bb7:	66 0f 6f 3d e1 60 00 00 	movdqa 0x60e1(%rip),%xmm7        # 8ca0 <_IO_stdin_used+0xca0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bbf:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2bc4:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2bc8:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bd0:	e8 2b f8 ff ff       	call   2400 <calloc@plt>
    2bd5:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2bda:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2bdf:	66 0f 6f 35 b9 60 00 00 	movdqa 0x60b9(%rip),%xmm6        # 8ca0 <_IO_stdin_used+0xca0>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2be7:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bec:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2bf3:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2bfb:	e8 00 f8 ff ff       	call   2400 <calloc@plt>
        thread_data[x].tasks = barriers;
    2c00:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c05:	4c 89 ef             	mov    %r13,%rdi
            data[0].messages_count = 0;
    2c08:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c10:	49 89 c6             	mov    %rax,%r14
        thread_data[x].tasks = barriers;
    2c13:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c17:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
            data[0].messages_count = 0;
    2c1c:	4c 89 f1             	mov    %r14,%rcx
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c1f:	48 0f af f8          	imul   %rax,%rdi
            data[0].messages_count = 0;
    2c23:	4c 89 4c 24 50       	mov    %r9,0x50(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c28:	48 c1 ef 22          	shr    $0x22,%rdi
    2c2c:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2c2f:	8b 7c 24 20          	mov    0x20(%rsp),%edi
    2c33:	01 c0                	add    %eax,%eax
    2c35:	29 c7                	sub    %eax,%edi
            data[0].messages_count = 0;
    2c37:	89 bc 24 98 00 00 00 	mov    %edi,0x98(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c3e:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c41:	be 38 00 00 00       	mov    $0x38,%esi
    2c46:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c4b:	45 31 f6             	xor    %r14d,%r14d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c4e:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2c53:	48 c1 e0 09          	shl    $0x9,%rax
    2c57:	4c 8d 2c 01          	lea    (%rcx,%rax,1),%r13
    2c5b:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2c60:	48 8d 05 09 18 00 00 	lea    0x1809(%rip),%rax        # 4470 <do_protected_write>
    2c67:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c6e:	e8 8d f7 ff ff       	call   2400 <calloc@plt>
    2c73:	8b 74 24 58          	mov    0x58(%rsp),%esi
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2c77:	49 89 85 70 01 00 00 	mov    %rax,0x170(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c7e:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c81:	85 f6                	test   %esi,%esi
    2c83:	0f 84 6e 06 00 00    	je     32f7 <main+0xc87>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2c89:	8b 44 24 20          	mov    0x20(%rsp),%eax
    2c8d:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    2c91:	49 89 cd             	mov    %rcx,%r13
    2c94:	48 89 8c 24 88 00 00 00 	mov    %rcx,0x88(%rsp)
    2c9c:	83 e8 02             	sub    $0x2,%eax
    2c9f:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2ca3:	eb 15                	jmp    2cba <main+0x64a>
    2ca5:	0f 1f 00             	nopl   (%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ca8:	41 83 c6 01          	add    $0x1,%r14d
    2cac:	49 83 c5 38          	add    $0x38,%r13
    2cb0:	41 83 fe 06          	cmp    $0x6,%r14d
    2cb4:	0f 84 51 01 00 00    	je     2e0b <main+0x79b>
            int group_of = b / threads_per_group;
    2cba:	44 89 f3             	mov    %r14d,%ebx
    2cbd:	31 c0                	xor    %eax,%eax
    2cbf:	44 89 f2             	mov    %r14d,%edx
    2cc2:	bf 01 00 00 00       	mov    $0x1,%edi
    2cc7:	d1 fb                	sar    %ebx
    2cc9:	48 8d 35 ec 56 00 00 	lea    0x56ec(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2cd0:	89 d9                	mov    %ebx,%ecx
    2cd2:	e8 d9 f7 ff ff       	call   24b0 <__printf_chk@plt>
            if (k == group_of) {
    2cd7:	41 39 df             	cmp    %ebx,%r15d
    2cda:	75 cc                	jne    2ca8 <main+0x638>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2cdc:	be 08 00 00 00       	mov    $0x8,%esi
    2ce1:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ce6:	49 83 c5 38          	add    $0x38,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2cea:	e8 11 f7 ff ff       	call   2400 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cef:	be 08 00 00 00       	mov    $0x8,%esi
    2cf4:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2cf9:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cfe:	e8 fd f6 ff ff       	call   2400 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2d03:	be 80 03 00 00       	mov    $0x380,%esi
    2d08:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d0d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2d12:	e8 e9 f6 ff ff       	call   2400 <calloc@plt>
              data[0].a = x;
    2d17:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2d1b:	44 89 f2             	mov    %r14d,%edx
    2d1e:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Data *data = calloc(3, sizeof(struct Data));
    2d23:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    2d26:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
    2d2d:	48 8d 35 74 5a 00 00 	lea    0x5a74(%rip),%rsi        # 87a8 <_IO_stdin_used+0x7a8>
              data[0].kind = MAILBOX_LOWER;
    2d34:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].a = x;
    2d3e:	89 98 1c 03 00 00    	mov    %ebx,0x31c(%rax)
              data[0].b = y;
    2d44:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    2d4a:	41 8d 44 24 01       	lea    0x1(%r12),%eax
              data[1].id = dataid++;
    2d4f:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2d56:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2d5d:	49 89 45 d0          	mov    %rax,-0x30(%r13)
    2d61:	8b 44 24 70          	mov    0x70(%rsp),%eax
              data[0].id = dataid++;
    2d65:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
              data[1].id = dataid++;
    2d6c:	41 83 c4 02          	add    $0x2,%r12d
              data[1].c = b;
    2d70:	45 89 b1 a4 06 00 00 	mov    %r14d,0x6a4(%r9)
    2d77:	89 c1                	mov    %eax,%ecx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d79:	41 83 c6 01          	add    $0x1,%r14d
              mailboxes[b].lower = &data[0];
    2d7d:	4d 89 4d c8          	mov    %r9,-0x38(%r13)
    2d81:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    2d85:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    2d87:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].a = x;
    2d92:	41 89 99 9c 06 00 00 	mov    %ebx,0x69c(%r9)
              data[1].b = y;
    2d99:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    2da0:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    2dab:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].pending = NULL;
    2db6:	49 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%r13)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2dbe:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    2dc6:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2dcb:	e8 e0 f6 ff ff       	call   24b0 <__printf_chk@plt>
              data[0].messages = messages;
    2dd0:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2dd5:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
              data[0].messages_count = 0;
    2dda:	66 0f 6f 35 ce 5e 00 00 	movdqa 0x5ece(%rip),%xmm6        # 8cb0 <_IO_stdin_used+0xcb0>
              data[1].messages = messages2;
    2de2:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
              data[0].messages = messages;
    2de7:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2dea:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2df1:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2df9:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e01:	41 83 fe 06          	cmp    $0x6,%r14d
    2e05:	0f 85 af fe ff ff    	jne    2cba <main+0x64a>
    2e0b:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2e0f:	48 8b 8c 24 88 00 00 00 	mov    0x88(%rsp),%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e17:	45 31 ed             	xor    %r13d,%r13d
    2e1a:	44 89 7c 24 08       	mov    %r15d,0x8(%rsp)
    2e1f:	41 89 e8             	mov    %ebp,%r8d
    2e22:	41 89 df             	mov    %ebx,%r15d
    2e25:	44 89 eb             	mov    %r13d,%ebx
    2e28:	49 89 cd             	mov    %rcx,%r13
    2e2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            int group_of = b / threads_per_group;
    2e30:	89 d8                	mov    %ebx,%eax
    2e32:	d1 f8                	sar    %eax
            if (k == group_of) {
    2e34:	39 44 24 08          	cmp    %eax,0x8(%rsp)
    2e38:	0f 84 58 01 00 00    	je     2f96 <main+0x926>
    2e3e:	89 da                	mov    %ebx,%edx
    2e40:	48 8d 35 85 55 00 00 	lea    0x5585(%rip),%rsi        # 83cc <_IO_stdin_used+0x3cc>
    2e47:	bf 01 00 00 00       	mov    $0x1,%edi
    2e4c:	31 c0                	xor    %eax,%eax
    2e4e:	44 89 44 24 18       	mov    %r8d,0x18(%rsp)
    2e53:	e8 58 f6 ff ff       	call   24b0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e58:	be 08 00 00 00       	mov    $0x8,%esi
    2e5d:	bf 01 00 00 00       	mov    $0x1,%edi
    2e62:	e8 99 f5 ff ff       	call   2400 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e67:	be 08 00 00 00       	mov    $0x8,%esi
    2e6c:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e71:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e76:	e8 85 f5 ff ff       	call   2400 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2e7b:	be 80 03 00 00       	mov    $0x380,%esi
    2e80:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e85:	48 89 c5             	mov    %rax,%rbp
            struct Data *data = calloc(3, sizeof(struct Data));
    2e88:	e8 73 f5 ff ff       	call   2400 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2e8d:	be 80 03 00 00       	mov    $0x380,%esi
    2e92:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2e97:	49 89 c6             	mov    %rax,%r14
            struct Data **stack = calloc(3, sizeof(struct Data));
    2e9a:	e8 61 f5 ff ff       	call   2400 <calloc@plt>
            data[0].id = dataid++;
    2e9f:	41 8d 74 24 01       	lea    0x1(%r12),%esi
            data[0].b = y;
    2ea4:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
            data[0].messages = messages;
    2ea9:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
            data[1].id = dataid++;
    2eae:	41 89 b6 a8 06 00 00 	mov    %esi,0x6a8(%r14)
            mailboxes[b].higher = &data[1];
    2eb5:	49 8d b6 80 03 00 00 	lea    0x380(%r14),%rsi
            data[0].messages_count = 0;
    2ebc:	66 0f 6f 35 ec 5d 00 00 	movdqa 0x5dec(%rip),%xmm6        # 8cb0 <_IO_stdin_used+0xcb0>
            data[0].kind = MAILBOX_LOWER;
    2ec4:	41 c7 86 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r14)
            data[0].a = x;
    2ecf:	45 89 be 1c 03 00 00 	mov    %r15d,0x31c(%r14)
            data[0].b = y;
    2ed6:	45 89 86 20 03 00 00 	mov    %r8d,0x320(%r14)
            data[0].c = b;
    2edd:	41 89 9e 24 03 00 00 	mov    %ebx,0x324(%r14)
            data[1].kind = MAILBOX_HIGHER;
    2ee4:	41 c7 86 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r14)
            data[1].a = x;
    2eef:	45 89 be 9c 06 00 00 	mov    %r15d,0x69c(%r14)
            data[1].b = y;
    2ef6:	45 89 86 a0 06 00 00 	mov    %r8d,0x6a0(%r14)
            data[1].c = b;
    2efd:	41 89 9e a4 06 00 00 	mov    %ebx,0x6a4(%r14)
            mailboxes[b].lower = &data[0];
    2f04:	4d 89 75 00          	mov    %r14,0x0(%r13)
            mailboxes[b].my_lower = &data[0];
    2f08:	4d 89 75 20          	mov    %r14,0x20(%r13)
            mailboxes[b].higher = &data[1];
    2f0c:	49 89 75 08          	mov    %rsi,0x8(%r13)
            mailboxes[b].pending = NULL;
    2f10:	49 c7 45 10 00 00 00 00 	movq   $0x0,0x10(%r13)
            data[0].finished_reading = 1;
    2f18:	41 c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r14)
            data[1].finished_reading = 1;
    2f23:	41 c7 86 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r14)
            mailboxes[b].my_higher = &data[1];
    2f2e:	49 89 75 28          	mov    %rsi,0x28(%r13)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2f32:	41 c7 45 30 02 00 00 00 	movl   $0x2,0x30(%r13)
            stack[0] = mailboxes[b].lower;
    2f3a:	4c 89 30             	mov    %r14,(%rax)
            stack[1] = mailboxes[b].higher;
    2f3d:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2f41:	49 89 45 18          	mov    %rax,0x18(%r13)
            data[0].available_sending = 0;
    2f45:	41 c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r14)
            data[0].available_receiving = 0;
    2f50:	41 c7 86 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r14)
            data[0].messages = messages;
    2f5b:	49 89 16             	mov    %rdx,(%r14)
            data[1].messages = messages2;
    2f5e:	49 89 ae 80 03 00 00 	mov    %rbp,0x380(%r14)
            data[1].available_sending = 1;
    2f65:	41 c7 86 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r14)
            data[1].available_receiving = 0;
    2f70:	41 c7 86 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r14)
            data[0].id = dataid++;
    2f7b:	45 89 a6 28 03 00 00 	mov    %r12d,0x328(%r14)
            data[1].id = dataid++;
    2f82:	41 83 c4 02          	add    $0x2,%r12d
            data[0].messages_count = 0;
    2f86:	41 0f 29 b6 80 00 00 00 	movaps %xmm6,0x80(%r14)
            data[1].messages_count = 0;
    2f8e:	41 0f 29 b6 00 04 00 00 	movaps %xmm6,0x400(%r14)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2f96:	83 c3 01             	add    $0x1,%ebx
    2f99:	49 83 c5 38          	add    $0x38,%r13
    2f9d:	83 fb 06             	cmp    $0x6,%ebx
    2fa0:	0f 85 8a fe ff ff    	jne    2e30 <main+0x7c0>
          char *message = malloc(sizeof(char) * 256);
    2fa6:	be 01 00 00 00       	mov    $0x1,%esi
    2fab:	bf 00 01 00 00       	mov    $0x100,%edi
    2fb0:	44 89 c5             	mov    %r8d,%ebp
    2fb3:	44 89 fb             	mov    %r15d,%ebx
    2fb6:	44 8b 7c 24 08       	mov    0x8(%rsp),%r15d
    2fbb:	e8 40 f4 ff ff       	call   2400 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2fc0:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2fc5:	49 89 c5             	mov    %rax,%r13
          struct Message *messaged = malloc(sizeof(struct Message));
    2fc8:	e8 a3 f4 ff ff       	call   2470 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2fcd:	48 83 ec 08          	sub    $0x8,%rsp
    2fd1:	4c 89 ef             	mov    %r13,%rdi
    2fd4:	41 89 e9             	mov    %ebp,%r9d
    2fd7:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2fdc:	41 89 d8             	mov    %ebx,%r8d
    2fdf:	ba 00 01 00 00       	mov    $0x100,%edx
    2fe4:	31 c0                	xor    %eax,%eax
    2fe6:	41 57                	push   %r15
    2fe8:	48 8d 0d e1 57 00 00 	lea    0x57e1(%rip),%rcx        # 87d0 <_IO_stdin_used+0x7d0>
    2fef:	be 01 00 00 00       	mov    $0x1,%esi
    2ff4:	e8 a7 f5 ff ff       	call   25a0 <__sprintf_chk@plt>
          messaged->message = message;
    2ff9:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
          messaged->thread_index = thread_data[x].real_thread_index;
    2ffe:	4c 8b 74 24 60       	mov    0x60(%rsp),%r14
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3003:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->task_index = y;
    3008:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
          thread_data[x].tasks[y].swap = swap;
    300d:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3012:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].swap = swap;
    3017:	49 8b 4e 38          	mov    0x38(%r14),%rcx
          messaged->message = message;
    301b:	4d 89 2a             	mov    %r13,(%r10)
          messaged->task_index = y;
    301e:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    3022:	49 63 46 08          	movslq 0x8(%r14),%rax
          thread_data[x].tasks[y].swap = swap;
    3026:	48 01 ca             	add    %rcx,%rdx
          messaged->group = k;
    3029:	45 89 7a 18          	mov    %r15d,0x18(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    302d:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].swap = swap;
    3031:	8b 44 24 38          	mov    0x38(%rsp),%eax
          thread_data[x].tasks[y].group = k;
    3035:	44 89 ba 94 01 00 00 	mov    %r15d,0x194(%rdx)
          thread_data[x].tasks[y].swap = swap;
    303c:	89 82 98 01 00 00    	mov    %eax,0x198(%rdx)
          swap += 1;
    3042:	83 c0 01             	add    $0x1,%eax
    3045:	89 44 24 38          	mov    %eax,0x38(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3049:	8d 45 01             	lea    0x1(%rbp),%eax
    304c:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    304f:	c7 02 41 00 00 00    	movl   $0x41,(%rdx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3055:	89 82 90 01 00 00    	mov    %eax,0x190(%rdx)
          thread_data[x].tasks[y].message = messaged;
    305b:	4c 89 92 88 01 00 00 	mov    %r10,0x188(%rdx)
          thread_data[x].tasks[y].sending = 1;
    3062:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
          thread_data[x].tasks[y].snapshot_count = 99;
    306c:	48 c7 82 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rdx)
    3077:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
          thread_data[x].tasks[y].swap = swap;
    307c:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3081:	e8 7a f3 ff ff       	call   2400 <calloc@plt>
    3086:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    308b:	48 89 82 50 01 00 00 	mov    %rax,0x150(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3092:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    3097:	48 c7 82 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    30a2:	48 8b 00             	mov    (%rax),%rax
    30a5:	8b 70 04             	mov    0x4(%rax),%esi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    30a8:	4c 39 f0             	cmp    %r14,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    30ab:	48 89 82 28 01 00 00 	mov    %rax,0x128(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    30b2:	89 b2 30 01 00 00    	mov    %esi,0x130(%rdx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    30b8:	41 5d                	pop    %r13
    30ba:	59                   	pop    %rcx
    30bb:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    30c0:	0f 85 a6 12 00 00    	jne    436c <main+0x1cfc>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    30c6:	66 0f 6f 05 f2 5b 00 00 	movdqa 0x5bf2(%rip),%xmm0        # 8cc0 <_IO_stdin_used+0xcc0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    30ce:	89 6a 04             	mov    %ebp,0x4(%rdx)
          thread_data[x].tasks[y].available = 1;
    30d1:	4c 8b 2d 08 5c 00 00 	mov    0x5c08(%rip),%r13        # 8ce0 <_IO_stdin_used+0xce0>
          thread_data[x].tasks[y].arrived = 0;
    30d8:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
          thread_data[x].tasks[y].worker_count = thread_count;
    30e2:	c7 82 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rdx)
          thread_data[x].tasks[y].available = 1;
    30ec:	4c 89 aa 44 01 00 00 	mov    %r13,0x144(%rdx)
          thread_data[x].tasks[y].thread_count = 2;
    30f3:	0f 11 82 34 01 00 00 	movups %xmm0,0x134(%rdx)
          if (y == barrier_count - 1) {
    30fa:	83 fd 01             	cmp    $0x1,%ebp
    30fd:	0f 84 91 03 00 00    	je     3494 <main+0xe24>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    3103:	85 ed                	test   %ebp,%ebp
    3105:	0f 84 71 03 00 00    	je     347c <main+0xe0c>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    310b:	4c 8b 4c 24 50       	mov    0x50(%rsp),%r9
    3110:	48 8d 05 19 37 00 00 	lea    0x3719(%rip),%rax        # 6830 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3117:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    311c:	49 89 ce             	mov    %rcx,%r14
    311f:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3126:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
    312b:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    3136:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    313b:	e8 c0 f2 ff ff       	call   2400 <calloc@plt>
    3140:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3145:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    314a:	66 0f 6f bc 24 b0 00 00 00 	movdqa 0xb0(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    3153:	83 44 24 20 01       	addl   $0x1,0x20(%rsp)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3158:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    315b:	48 83 c3 10          	add    $0x10,%rbx
    315f:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3166:	49 89 81 78 ff ff ff 	mov    %rax,-0x88(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    316d:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3172:	83 84 24 80 00 00 00 01 	addl   $0x1,0x80(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    317a:	48 8b 00             	mov    (%rax),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    317d:	48 89 5c 24 68       	mov    %rbx,0x68(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    3182:	41 c7 86 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r14)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    318d:	49 89 86 28 05 00 00 	mov    %rax,0x528(%r14)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    3194:	41 c7 86 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r14)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    319f:	41 c7 86 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    31aa:	41 8b 81 2c ff ff ff 	mov    -0xd4(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    31b1:	41 0f 11 be 18 05 00 00 	movups %xmm7,0x518(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    31b9:	41 89 86 30 05 00 00 	mov    %eax,0x530(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    31c0:	8b 44 24 20          	mov    0x20(%rsp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    31c4:	41 c7 86 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r14)
        thread_data[x].tasks[barrier_count].available = 1; 
    31cf:	4d 89 ae 44 05 00 00 	mov    %r13,0x544(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    31d6:	39 84 24 9c 00 00 00 	cmp    %eax,0x9c(%rsp)
    31dd:	0f 85 1c f8 ff ff    	jne    29ff <main+0x38f>
    31e3:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
    31eb:	48 8b 9c 24 e0 00 00 00 	mov    0xe0(%rsp),%rbx
    31f3:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    31fb:	48 8b ac 24 e8 00 00 00 	mov    0xe8(%rsp),%rbp
  for (int k = 0 ; k < group_count ; k++) {
    3203:	41 83 c7 01          	add    $0x1,%r15d
    3207:	48 81 c3 b0 01 00 00 	add    $0x1b0,%rbx
    320e:	48 83 c6 18          	add    $0x18,%rsi
    3212:	41 83 ff 03          	cmp    $0x3,%r15d
    3216:	0f 85 97 f7 ff ff    	jne    29b3 <main+0x343>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    321c:	be 08 00 00 00       	mov    $0x8,%esi
    3221:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    3226:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3229:	e8 d2 f1 ff ff       	call   2400 <calloc@plt>
    322e:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3233:	48 89 c5             	mov    %rax,%rbp
    3236:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3238:	49 89 d1             	mov    %rdx,%r9
    323b:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    323d:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3241:	45 85 d2             	test   %r10d,%r10d
    3244:	0f 8e 94 00 00 00    	jle    32de <main+0xc6e>
    324a:	49 8b 79 38          	mov    0x38(%r9),%rdi
    324e:	4d 63 c2             	movslq %r10d,%r8
    3251:	49 63 cc             	movslq %r12d,%rcx
    3254:	49 c1 e0 09          	shl    $0x9,%r8
    3258:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    325d:	49 01 f8             	add    %rdi,%r8
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3260:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3267:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    326e:	48 83 c6 60          	add    $0x60,%rsi
    3272:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    3277:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    327c:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3284:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3288:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3290:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3294:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    3298:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    32a0:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32a7:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    32ab:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    32af:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    32b6:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32bd:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    32c1:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    32c5:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    32c9:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    32cd:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    32d1:	49 39 f8             	cmp    %rdi,%r8
    32d4:	75 8a                	jne    3260 <main+0xbf0>
    32d6:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    32da:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    32de:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    32e5:	85 db                	test   %ebx,%ebx
    32e7:	0f 85 b5 01 00 00    	jne    34a2 <main+0xe32>
    32ed:	bb 01 00 00 00       	mov    $0x1,%ebx
    32f2:	e9 46 ff ff ff       	jmp    323d <main+0xbcd>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    32f7:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    32fb:	49 89 c5             	mov    %rax,%r13
    32fe:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
    3303:	eb 15                	jmp    331a <main+0xcaa>
    3305:	0f 1f 00             	nopl   (%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3308:	41 83 c6 01          	add    $0x1,%r14d
    330c:	49 83 c5 38          	add    $0x38,%r13
    3310:	41 83 fe 06          	cmp    $0x6,%r14d
    3314:	0f 84 54 01 00 00    	je     346e <main+0xdfe>
            int group_of = b / threads_per_group;
    331a:	44 89 f3             	mov    %r14d,%ebx
    331d:	31 c0                	xor    %eax,%eax
    331f:	44 89 f2             	mov    %r14d,%edx
    3322:	bf 01 00 00 00       	mov    $0x1,%edi
    3327:	d1 fb                	sar    %ebx
    3329:	48 8d 35 8c 50 00 00 	lea    0x508c(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    3330:	89 d9                	mov    %ebx,%ecx
    3332:	e8 79 f1 ff ff       	call   24b0 <__printf_chk@plt>
            if (k == group_of) {
    3337:	41 39 df             	cmp    %ebx,%r15d
    333a:	75 cc                	jne    3308 <main+0xc98>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    333c:	be 08 00 00 00       	mov    $0x8,%esi
    3341:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3346:	49 83 c5 38          	add    $0x38,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    334a:	e8 b1 f0 ff ff       	call   2400 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    334f:	be 08 00 00 00       	mov    $0x8,%esi
    3354:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3359:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    335e:	e8 9d f0 ff ff       	call   2400 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    3363:	be 80 03 00 00       	mov    $0x380,%esi
    3368:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    336d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    3372:	e8 89 f0 ff ff       	call   2400 <calloc@plt>
              data[0].a = x;
    3377:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    337b:	44 89 f2             	mov    %r14d,%edx
    337e:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Data *data = calloc(3, sizeof(struct Data));
    3383:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    3386:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
    338d:	48 8d 35 14 54 00 00 	lea    0x5414(%rip),%rsi        # 87a8 <_IO_stdin_used+0x7a8>
              data[0].kind = MAILBOX_LOWER;
    3394:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].a = x;
    339e:	89 98 1c 03 00 00    	mov    %ebx,0x31c(%rax)
              data[0].b = y;
    33a4:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    33aa:	41 8d 44 24 01       	lea    0x1(%r12),%eax
              data[1].id = dataid++;
    33af:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    33b6:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    33bd:	49 89 45 d0          	mov    %rax,-0x30(%r13)
    33c1:	8b 84 24 98 00 00 00 	mov    0x98(%rsp),%eax
              data[0].id = dataid++;
    33c8:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
              data[1].id = dataid++;
    33cf:	41 83 c4 02          	add    $0x2,%r12d
              data[1].c = b;
    33d3:	45 89 b1 a4 06 00 00 	mov    %r14d,0x6a4(%r9)
    33da:	89 c1                	mov    %eax,%ecx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    33dc:	41 83 c6 01          	add    $0x1,%r14d
              mailboxes[b].lower = &data[0];
    33e0:	4d 89 4d c8          	mov    %r9,-0x38(%r13)
    33e4:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    33e8:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    33ea:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].a = x;
    33f5:	41 89 99 9c 06 00 00 	mov    %ebx,0x69c(%r9)
              data[1].b = y;
    33fc:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    3403:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    340e:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].pending = NULL;
    3419:	49 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%r13)
              mailboxes[b].kind = MAILBOX_FRIEND;
    3421:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    3429:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    342e:	e8 7d f0 ff ff       	call   24b0 <__printf_chk@plt>
              data[0].messages = messages;
    3433:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3438:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
              data[0].messages_count = 0;
    343d:	66 0f 6f 35 6b 58 00 00 	movdqa 0x586b(%rip),%xmm6        # 8cb0 <_IO_stdin_used+0xcb0>
              data[1].messages = messages2;
    3445:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
              data[0].messages = messages;
    344a:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    344d:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    3454:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    345c:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3464:	41 83 fe 06          	cmp    $0x6,%r14d
    3468:	0f 85 ac fe ff ff    	jne    331a <main+0xcaa>
    346e:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    3472:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    3477:	e9 9b f9 ff ff       	jmp    2e17 <main+0x7a7>
    347c:	48 8d 05 ad 39 00 00 	lea    0x39ad(%rip),%rax        # 6e30 <barriered_work_ingest_andwork>
    3483:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    3488:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    348f:	e9 aa f7 ff ff       	jmp    2c3e <main+0x5ce>
    3494:	48 8d 05 95 33 00 00 	lea    0x3395(%rip),%rax        # 6830 <barriered_work>
    349b:	bd 02 00 00 00       	mov    $0x2,%ebp
    34a0:	eb e6                	jmp    3488 <main+0xe18>
  for (int k = 0 ; k < group_count ; k++) {
    34a2:	83 c0 02             	add    $0x2,%eax
    34a5:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    34ac:	83 f8 06             	cmp    $0x6,%eax
    34af:	0f 85 83 fd ff ff    	jne    3238 <main+0xbc8>
    34b5:	48 8d 3d 2e 4f 00 00 	lea    0x4f2e(%rip),%rdi        # 83ea <_IO_stdin_used+0x3ea>
    34bc:	e8 6f ee ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    34c1:	48 8d 35 37 4f 00 00 	lea    0x4f37(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    34c8:	48 8d 3d 32 4f 00 00 	lea    0x4f32(%rip),%rdi        # 8401 <_IO_stdin_used+0x401>
    34cf:	e8 1c f0 ff ff       	call   24f0 <fopen@plt>
    34d4:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas_size; x++) {
    34d7:	45 85 e4             	test   %r12d,%r12d
    34da:	7e 77                	jle    3553 <main+0xee3>
    34dc:	4d 63 e4             	movslq %r12d,%r12
    34df:	4c 8d 35 f8 4e 00 00 	lea    0x4ef8(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    34e6:	4c 8d 2d 35 4f 00 00 	lea    0x4f35(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    34ed:	4a 8d 44 e5 00       	lea    0x0(%rbp,%r12,8),%rax
    34f2:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    char * c = calloc(250, sizeof(char));
    34f7:	be 01 00 00 00       	mov    $0x1,%esi
    34fc:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    3501:	48 83 c5 08          	add    $0x8,%rbp
    char * c = calloc(250, sizeof(char));
    3505:	e8 f6 ee ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    350a:	4c 89 f1             	mov    %r14,%rcx
    350d:	ba fa 00 00 00       	mov    $0xfa,%edx
    3512:	be 01 00 00 00       	mov    $0x1,%esi
    3517:	49 89 c4             	mov    %rax,%r12
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    351a:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    351e:	4c 89 e7             	mov    %r12,%rdi
    3521:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3528:	31 c0                	xor    %eax,%eax
    352a:	e8 71 f0 ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    352f:	4c 89 e2             	mov    %r12,%rdx
    3532:	4c 89 ee             	mov    %r13,%rsi
    3535:	bf 01 00 00 00       	mov    $0x1,%edi
    353a:	31 c0                	xor    %eax,%eax
    353c:	e8 6f ef ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3541:	4c 89 fe             	mov    %r15,%rsi
    3544:	4c 89 e7             	mov    %r12,%rdi
    3547:	e8 74 ee ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    354c:	48 39 6c 24 08       	cmp    %rbp,0x8(%rsp)
    3551:	75 a4                	jne    34f7 <main+0xe87>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    3553:	4c 89 ff             	mov    %r15,%rdi

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    3556:	31 ed                	xor    %ebp,%ebp
    3558:	4c 8d 35 ed 4e 00 00 	lea    0x4eed(%rip),%r14        # 844c <_IO_stdin_used+0x44c>
  fclose(m1);
    355f:	e8 fc ed ff ff       	call   2360 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3564:	48 8d 3d 9f 4e 00 00 	lea    0x4e9f(%rip),%rdi        # 840a <_IO_stdin_used+0x40a>
    356b:	41 89 ec             	mov    %ebp,%r12d
    356e:	e8 bd ed ff ff       	call   2330 <puts@plt>
    3573:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3578:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    357d:	44 89 e2             	mov    %r12d,%edx
    3580:	48 8d 35 9e 4e 00 00 	lea    0x4e9e(%rip),%rsi        # 8425 <_IO_stdin_used+0x425>
    3587:	31 c0                	xor    %eax,%eax
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    3589:	45 31 ed             	xor    %r13d,%r13d
    358c:	bf 01 00 00 00       	mov    $0x1,%edi
    3591:	47 8d 3c 24          	lea    (%r12,%r12,1),%r15d
    3595:	e8 16 ef ff ff       	call   24b0 <__printf_chk@plt>
    359a:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    359f:	44 89 7c 24 10       	mov    %r15d,0x10(%rsp)
    35a4:	48 89 e8             	mov    %rbp,%rax
    35a7:	89 dd                	mov    %ebx,%ebp
    35a9:	44 89 eb             	mov    %r13d,%ebx
    35ac:	49 89 c5             	mov    %rax,%r13
      int x = (k * threads_per_group) + d;
    35af:	8b 44 24 10          	mov    0x10(%rsp),%eax
    35b3:	89 da                	mov    %ebx,%edx
    35b5:	48 8d 35 73 4e 00 00 	lea    0x4e73(%rip),%rsi        # 842f <_IO_stdin_used+0x42f>
    35bc:	45 31 ff             	xor    %r15d,%r15d
    35bf:	bf 01 00 00 00       	mov    $0x1,%edi
    35c4:	8d 0c 03             	lea    (%rbx,%rax,1),%ecx
    35c7:	31 c0                	xor    %eax,%eax
    35c9:	e8 e2 ee ff ff       	call   24b0 <__printf_chk@plt>
    35ce:	89 5c 24 18          	mov    %ebx,0x18(%rsp)
    35d2:	89 6c 24 20          	mov    %ebp,0x20(%rsp)
    35d6:	44 89 64 24 28       	mov    %r12d,0x28(%rsp)
    35db:	44 89 fa             	mov    %r15d,%edx
    35de:	48 8d 35 5c 4e 00 00 	lea    0x4e5c(%rip),%rsi        # 8441 <_IO_stdin_used+0x441>
    35e5:	31 c0                	xor    %eax,%eax
    35e7:	4d 89 fc             	mov    %r15,%r12
    35ea:	bf 01 00 00 00       	mov    $0x1,%edi
    35ef:	49 c1 e4 09          	shl    $0x9,%r12
    35f3:	31 ed                	xor    %ebp,%ebp
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    35f5:	31 db                	xor    %ebx,%ebx
    35f7:	e8 b4 ee ff ff       	call   24b0 <__printf_chk@plt>
    35fc:	eb 2c                	jmp    362a <main+0xfba>
    35fe:	66 90                	xchg   %ax,%ax
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    3600:	83 fa 01             	cmp    $0x1,%edx
    3603:	0f 84 91 00 00 00    	je     369a <main+0x102a>
    3609:	44 8b 40 34          	mov    0x34(%rax),%r8d
    360d:	89 da                	mov    %ebx,%edx
    360f:	4c 89 f6             	mov    %r14,%rsi
    3612:	bf 01 00 00 00       	mov    $0x1,%edi
    3617:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3619:	83 c3 01             	add    $0x1,%ebx
    361c:	48 83 c5 38          	add    $0x38,%rbp
    3620:	e8 8b ee ff ff       	call   24b0 <__printf_chk@plt>
    3625:	83 fb 06             	cmp    $0x6,%ebx
    3628:	74 43                	je     366d <main+0xffd>
          char * mailbox_kind = calloc(100, sizeof(char));
    362a:	be 01 00 00 00       	mov    $0x1,%esi
    362f:	bf 64 00 00 00       	mov    $0x64,%edi
    3634:	e8 c7 ed ff ff       	call   2400 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3639:	49 8b 75 38          	mov    0x38(%r13),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    363d:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3640:	4a 8b 84 26 70 01 00 00 	mov    0x170(%rsi,%r12,1),%rax
    3648:	48 01 e8             	add    %rbp,%rax
    364b:	8b 50 30             	mov    0x30(%rax),%edx
    364e:	83 fa 02             	cmp    $0x2,%edx
    3651:	75 ad                	jne    3600 <main+0xf90>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3653:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    365d:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3660:	4a 8b 84 26 70 01 00 00 	mov    0x170(%rsi,%r12,1),%rax
    3668:	48 01 e8             	add    %rbp,%rax
    366b:	eb 9c                	jmp    3609 <main+0xf99>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    366d:	49 83 c7 01          	add    $0x1,%r15
    3671:	49 83 ff 03          	cmp    $0x3,%r15
    3675:	0f 85 60 ff ff ff    	jne    35db <main+0xf6b>
    for (int d = 0 ; d < threads_per_group ; d++) {
    367b:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    367f:	8b 6c 24 20          	mov    0x20(%rsp),%ebp
    3683:	49 81 c5 d8 00 00 00 	add    $0xd8,%r13
    368a:	44 8b 64 24 28       	mov    0x28(%rsp),%r12d
    368f:	85 db                	test   %ebx,%ebx
    3691:	75 24                	jne    36b7 <main+0x1047>
    3693:	89 eb                	mov    %ebp,%ebx
    3695:	e9 15 ff ff ff       	jmp    35af <main+0xf3f>
    369a:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    36a0:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    36a7:	4a 8b 84 26 70 01 00 00 	mov    0x170(%rsi,%r12,1),%rax
    36af:	48 01 e8             	add    %rbp,%rax
    36b2:	e9 52 ff ff ff       	jmp    3609 <main+0xf99>
  for (int k = 0 ; k < group_count ; k++) {
    36b7:	48 81 44 24 08 b0 01 00 00 	addq   $0x1b0,0x8(%rsp)
    36c0:	41 83 c4 01          	add    $0x1,%r12d
    36c4:	41 89 dd             	mov    %ebx,%r13d
    36c7:	89 eb                	mov    %ebp,%ebx
    36c9:	41 83 fc 03          	cmp    $0x3,%r12d
    36cd:	0f 85 aa fe ff ff    	jne    357d <main+0xf0d>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    36d3:	ba 07 00 00 00       	mov    $0x7,%edx
    36d8:	bf 01 00 00 00       	mov    $0x1,%edi
    36dd:	31 c0                	xor    %eax,%eax
    36df:	45 89 ec             	mov    %r13d,%r12d
    36e2:	48 8d 35 7e 4d 00 00 	lea    0x4d7e(%rip),%rsi        # 8467 <_IO_stdin_used+0x467>
    36e9:	e8 c2 ed ff ff       	call   24b0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    36ee:	be 08 00 00 00       	mov    $0x8,%esi
    36f3:	bf 02 00 00 00       	mov    $0x2,%edi
    36f8:	e8 03 ed ff ff       	call   2400 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    36fd:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3702:	be 38 00 00 00       	mov    $0x38,%esi
    3707:	bf 0a 00 00 00       	mov    $0xa,%edi
    my_thread_data[0] = &thread_data[x]; 
    370c:	4c 8d b5 e8 05 00 00 	lea    0x5e8(%rbp),%r14
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3713:	48 89 68 08          	mov    %rbp,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3717:	4c 8d ad d8 00 00 00 	lea    0xd8(%rbp),%r13
    thread_data[x].threads = my_thread_data;
    371e:	48 89 85 00 06 00 00 	mov    %rax,0x600(%rbp)
    my_thread_data[0] = &thread_data[x]; 
    3725:	4c 89 30             	mov    %r14,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3728:	48 8b 45 38          	mov    0x38(%rbp),%rax
    thread_data[x].thread_count = 2;
    372c:	c7 85 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%rbp)
    thread_data[x].thread_index = 0;
    3736:	c7 85 ec 05 00 00 00 00 00 00 	movl   $0x0,0x5ec(%rbp)
    thread_data[x].task_count = total_barrier_count;
    3740:	c7 85 28 06 00 00 03 00 00 00 	movl   $0x3,0x628(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    374a:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3754:	48 8b 85 10 01 00 00 	mov    0x110(%rbp),%rax
    375b:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3765:	e8 96 ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    376a:	be 38 00 00 00       	mov    $0x38,%esi
    376f:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3774:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3779:	e8 82 ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    377e:	be 38 00 00 00       	mov    $0x38,%esi
    3783:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3788:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    378b:	e8 70 ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3790:	be 38 00 00 00       	mov    $0x38,%esi
    3795:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    379a:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    379f:	e8 5c ec ff ff       	call   2400 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37a4:	be 08 00 00 00       	mov    $0x8,%esi
    37a9:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37ae:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37b3:	e8 48 ec ff ff       	call   2400 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    37b8:	be 08 00 00 00       	mov    $0x8,%esi
    37bd:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
    37c2:	c7 85 1c 05 00 00 00 00 00 00 	movl   $0x0,0x51c(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37cc:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    37cf:	48 8b 05 12 55 00 00 	mov    0x5512(%rip),%rax        # 8ce8 <_IO_stdin_used+0xce8>
    37d6:	48 89 85 50 05 00 00 	mov    %rax,0x550(%rbp)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    37dd:	e8 1e ec ff ff       	call   2400 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    37e2:	48 8d 95 b0 01 00 00 	lea    0x1b0(%rbp),%rdx
    37e9:	48 89 ef             	mov    %rbp,%rdi
    37ec:	48 8d 8d 10 05 00 00 	lea    0x510(%rbp),%rcx
    37f3:	48 89 50 10          	mov    %rdx,0x10(%rax)
    37f7:	48 8d 95 88 02 00 00 	lea    0x288(%rbp),%rdx
    37fe:	48 8d 35 71 4c 00 00 	lea    0x4c71(%rip),%rsi        # 8476 <_IO_stdin_used+0x476>
    3805:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3809:	48 8d 95 60 03 00 00 	lea    0x360(%rbp),%rdx
    3810:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3814:	48 8d 95 38 04 00 00 	lea    0x438(%rbp),%rdx
    381b:	48 89 28             	mov    %rbp,(%rax)
    381e:	48 8d ad c0 06 00 00 	lea    0x6c0(%rbp),%rbp
    3825:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3829:	48 8d 97 98 07 00 00 	lea    0x798(%rdi),%rdx
    3830:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3834:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3838:	4c 89 70 38          	mov    %r14,0x38(%rax)
    383c:	48 89 50 48          	mov    %rdx,0x48(%rax)
    3840:	ba 06 00 00 00       	mov    $0x6,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3845:	48 89 87 28 05 00 00 	mov    %rax,0x528(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    384c:	48 89 68 40          	mov    %rbp,0x40(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3850:	48 8b 05 99 54 00 00 	mov    0x5499(%rip),%rax        # 8cf0 <_IO_stdin_used+0xcf0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3857:	c7 87 40 05 00 00 06 00 00 00 	movl   $0x6,0x540(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3861:	48 89 87 38 05 00 00 	mov    %rax,0x538(%rdi)
    3868:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    386a:	c7 87 14 05 00 00 00 00 00 00 	movl   $0x0,0x514(%rdi)
    3874:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
    3879:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    387e:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    3883:	e8 28 ec ff ff       	call   24b0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3888:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    388d:	49 8d b7 50 01 00 00 	lea    0x150(%r15),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    3894:	45 31 ff             	xor    %r15d,%r15d
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3897:	48 8d 15 92 0d 00 00 	lea    0xd92(%rip),%rdx        # 4630 <timer_thread>
    389e:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    38a2:	e8 29 ec ff ff       	call   24d0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    38a7:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
    38ac:	4c 89 f6             	mov    %r14,%rsi
    38af:	48 89 d9             	mov    %rbx,%rcx
    38b2:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38b7:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    38bc:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    38c1:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    38c7:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    38cc:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    38d1:	49 89 c6             	mov    %rax,%r14
    38d4:	45 89 d5             	mov    %r10d,%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    38d7:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    38dc:	47 8d 24 3f          	lea    (%r15,%r15,1),%r12d
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    38e0:	48 89 cd             	mov    %rcx,%rbp
    38e3:	48 89 d3             	mov    %rdx,%rbx
    38e6:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
    38eb:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    38f0:	4c 89 74 24 48       	mov    %r14,0x48(%rsp)
    38f5:	49 89 f6             	mov    %rsi,%r14
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    38f8:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    38ff:	44 89 e2             	mov    %r12d,%edx
    3902:	44 89 f9             	mov    %r15d,%ecx
    3905:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    3907:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    390e:	48 8d 35 eb 4e 00 00 	lea    0x4eeb(%rip),%rsi        # 8800 <_IO_stdin_used+0x800>
    3915:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    391a:	41 83 c4 01          	add    $0x1,%r12d
    391e:	e8 8d eb ff ff       	call   24b0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3923:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3928:	48 89 d9             	mov    %rbx,%rcx
    392b:	48 89 ef             	mov    %rbp,%rdi
    392e:	48 8d 15 9b 28 00 00 	lea    0x289b(%rip),%rdx        # 61d0 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3935:	48 81 c3 d8 00 00 00 	add    $0xd8,%rbx
    393c:	48 83 c5 08          	add    $0x8,%rbp
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3940:	e8 8b eb ff ff       	call   24d0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3945:	48 8b 53 d8          	mov    -0x28(%rbx),%rdx
    3949:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
    394d:	be 08 00 00 00       	mov    $0x8,%esi
    3952:	e8 c9 e9 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3957:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    395d:	45 39 e5             	cmp    %r12d,%r13d
    3960:	75 96                	jne    38f8 <main+0x1288>
  for (int k = 0 ; k < group_count ; k++) {
    3962:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    3967:	4c 89 f6             	mov    %r14,%rsi
    396a:	41 83 c7 01          	add    $0x1,%r15d
    396e:	41 83 c5 02          	add    $0x2,%r13d
    3972:	4c 8b 74 24 48       	mov    0x48(%rsp),%r14
    3977:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    397c:	48 83 c1 10          	add    $0x10,%rcx
    3980:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3987:	49 83 c6 70          	add    $0x70,%r14
    398b:	41 83 ff 03          	cmp    $0x3,%r15d
    398f:	0f 85 42 ff ff ff    	jne    38d7 <main+0x1267>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    3995:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    399a:	48 8b 05 57 53 00 00 	mov    0x5357(%rip),%rax        # 8cf8 <_IO_stdin_used+0xcf8>
    thread_data[x].type = IO;
    39a1:	49 89 f6             	mov    %rsi,%r14

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39a4:	bf 01 00 00 00       	mov    $0x1,%edi
    39a9:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    39ae:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    39b3:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    39b8:	41 c7 87 f4 05 00 00 02 00 00 00 	movl   $0x2,0x5f4(%r15)
    39c3:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    thread_data[x].task_count = 0;
    39c8:	49 89 87 28 06 00 00 	mov    %rax,0x628(%r15)
    thread_data[x].type = IO;
    39cf:	48 8b 6c 24 40       	mov    0x40(%rsp),%rbp
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39d4:	e8 27 ea ff ff       	call   2400 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    39d9:	be 00 08 00 00       	mov    $0x800,%esi
    39de:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39e0:	49 89 87 40 06 00 00 	mov    %rax,0x640(%r15)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    39e7:	e8 34 eb ff ff       	call   2520 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39ec:	be 08 00 00 00       	mov    $0x8,%esi
    39f1:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    39f6:	41 89 87 48 06 00 00 	mov    %eax,0x648(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39fd:	e8 fe e9 ff ff       	call   2400 <calloc@plt>
    3a02:	ba 07 00 00 00       	mov    $0x7,%edx
    3a07:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3a0c:	41 c7 87 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r15)
      my_thread_data[n] = &thread_data[n]; 
    3a17:	4c 89 38             	mov    %r15,(%rax)
    3a1a:	48 8d 35 73 4a 00 00 	lea    0x4a73(%rip),%rsi        # 8494 <_IO_stdin_used+0x494>
    thread_data[x].threads = my_thread_data;
    3a21:	49 89 87 00 06 00 00 	mov    %rax,0x600(%r15)
      my_thread_data[n] = &thread_data[n]; 
    3a28:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3a2c:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3a2e:	41 c7 87 ec 05 00 00 07 00 00 00 	movl   $0x7,0x5ec(%r15)
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a39:	41 bf 08 00 00 00    	mov    $0x8,%r15d
    3a3f:	e8 6c ea ff ff       	call   24b0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3a44:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3a49:	4c 89 f1             	mov    %r14,%rcx
    3a4c:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3a50:	48 8d 15 89 1f 00 00 	lea    0x1f89(%rip),%rdx        # 59e0 <io_thread>
    3a57:	4c 8d 73 40          	lea    0x40(%rbx),%r14
    3a5b:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3a62:	e8 69 ea ff ff       	call   24d0 <pthread_create@plt>
    3a67:	ba 08 00 00 00       	mov    $0x8,%edx
    3a6c:	48 8d 35 38 4a 00 00 	lea    0x4a38(%rip),%rsi        # 84ab <_IO_stdin_used+0x4ab>
    3a73:	31 c0                	xor    %eax,%eax
    3a75:	bf 01 00 00 00       	mov    $0x1,%edi
    3a7a:	e8 31 ea ff ff       	call   24b0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a7f:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3a84:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    3a8a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3a8f:	44 89 fa             	mov    %r15d,%edx
    3a92:	48 8d 35 28 4a 00 00 	lea    0x4a28(%rip),%rsi        # 84c1 <_IO_stdin_used+0x4c1>
    3a99:	bf 01 00 00 00       	mov    $0x1,%edi
    3a9e:	31 c0                	xor    %eax,%eax
    3aa0:	e8 0b ea ff ff       	call   24b0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3aa5:	be 08 00 00 00       	mov    $0x8,%esi
    3aaa:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3aaf:	48 8b 05 42 52 00 00 	mov    0x5242(%rip),%rax        # 8cf8 <_IO_stdin_used+0xcf8>
    thread_data[x].type = EXTERNAL;
    3ab6:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    thread_data[x].task_count = 0;
    3abd:	48 89 45 40          	mov    %rax,0x40(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3ac1:	e8 3a e9 ff ff       	call   2400 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3ac6:	48 8b bc 24 c0 00 00 00 	mov    0xc0(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3ace:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3ad3:	c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3add:	48 89 45 50          	mov    %rax,0x50(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3ae1:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3ae4:	bf 02 00 00 00       	mov    $0x2,%edi
    3ae9:	e8 12 e9 ff ff       	call   2400 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3aee:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3af3:	48 89 e9             	mov    %rbp,%rcx
    3af6:	4c 89 f7             	mov    %r14,%rdi
    thread_data[x].threads = my_thread_data;
    3af9:	48 89 45 18          	mov    %rax,0x18(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3afd:	48 8d 15 1c 0a 00 00 	lea    0xa1c(%rip),%rdx        # 4520 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b04:	49 83 c6 08          	add    $0x8,%r14
    3b08:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
      my_thread_data[n] = &thread_data[n]; 
    3b0f:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b12:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3b17:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3b1b:	48 8b 05 b6 51 00 00 	mov    0x51b6(%rip),%rax        # 8cd8 <_IO_stdin_used+0xcd8>
    thread_data[x].thread_index = x;
    3b22:	44 89 bd 2c ff ff ff 	mov    %r15d,-0xd4(%rbp)
    thread_data[x].thread_count = thread_count;
    3b29:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b30:	e8 9b e9 ff ff       	call   24d0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b35:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3b3b:	48 83 84 24 c0 00 00 00 10 	addq   $0x10,0xc0(%rsp)
    3b44:	41 83 ff 08          	cmp    $0x8,%r15d
    3b48:	75 42                	jne    3b8c <main+0x151c>
    3b4a:	41 bf 09 00 00 00    	mov    $0x9,%r15d
    3b50:	e9 3a ff ff ff       	jmp    3a8f <main+0x141f>
        other = (x + 1) % total_threads;
    3b55:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
        my_thread_data[1] = &thread_data[other]; 
    3b5a:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3b5f:	48 89 5c 24 48       	mov    %rbx,0x48(%rsp)
    3b64:	45 31 c0             	xor    %r8d,%r8d
    3b67:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
        other = (x + 1) % total_threads;
    3b6c:	45 89 ee             	mov    %r13d,%r14d
        my_thread_data[1] = &thread_data[other]; 
    3b6f:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3b73:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        my_thread_data[0] = &thread_data[x]; 
    3b77:	4c 89 c8             	mov    %r9,%rax
    3b7a:	e9 0d ef ff ff       	jmp    2a8c <main+0x41c>
            CPU_SET(j, sendercpu);
    3b7f:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
    3b87:	e9 92 ef ff ff       	jmp    2b1e <main+0x4ae>
    3b8c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3b91:	48 8d 2d 46 49 00 00 	lea    0x4946(%rip),%rbp        # 84de <_IO_stdin_used+0x4de>
    3b98:	4c 8d 70 04          	lea    0x4(%rax),%r14
    3b9c:	4c 8d a8 74 08 00 00 	lea    0x874(%rax),%r13
    3ba3:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3ba7:	41 8b 16             	mov    (%r14),%edx
    3baa:	48 89 ee             	mov    %rbp,%rsi
    3bad:	bf 01 00 00 00       	mov    $0x1,%edi
    3bb2:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3bb4:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    3bbb:	e8 f0 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bc0:	4d 39 f5             	cmp    %r14,%r13
    3bc3:	75 de                	jne    3ba3 <main+0x1533>
    3bc5:	48 8d 3d 25 49 00 00 	lea    0x4925(%rip),%rdi        # 84f1 <_IO_stdin_used+0x4f1>
    3bcc:	45 31 f6             	xor    %r14d,%r14d
    3bcf:	4c 8d ac 24 f0 00 00 00 	lea    0xf0(%rsp),%r13
    3bd7:	e8 54 e7 ff ff       	call   2330 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3bdc:	48 8d 2d 2c 49 00 00 	lea    0x492c(%rip),%rbp        # 850f <_IO_stdin_used+0x50f>
    void * result; 
    pthread_join(thread[x], &result);
    3be3:	4a 8b 3c f3          	mov    (%rbx,%r14,8),%rdi
    3be7:	4c 89 ee             	mov    %r13,%rsi
    3bea:	e8 71 e9 ff ff       	call   2560 <pthread_join@plt>
    3bef:	44 89 f2             	mov    %r14d,%edx
    3bf2:	48 89 ee             	mov    %rbp,%rsi
    3bf5:	bf 01 00 00 00       	mov    $0x1,%edi
    3bfa:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3bfc:	49 83 c6 01          	add    $0x1,%r14
    3c00:	e8 ab e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c05:	49 83 fe 0a          	cmp    $0xa,%r14
    3c09:	75 d8                	jne    3be3 <main+0x1573>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c0b:	be 08 00 00 00       	mov    $0x8,%esi
    3c10:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3c15:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c17:	e8 e4 e7 ff ff       	call   2400 <calloc@plt>
    3c1c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3c21:	49 89 c7             	mov    %rax,%r15
    3c24:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c26:	49 89 d1             	mov    %rdx,%r9
    3c29:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c2c:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3c30:	45 85 d2             	test   %r10d,%r10d
    3c33:	0f 8e 94 00 00 00    	jle    3ccd <main+0x165d>
    3c39:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3c3d:	4d 63 c2             	movslq %r10d,%r8
    3c40:	48 63 cb             	movslq %ebx,%rcx
    3c43:	49 c1 e0 09          	shl    $0x9,%r8
    3c47:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    3c4b:	49 01 f8             	add    %rdi,%r8
    3c4e:	66 90                	xchg   %ax,%ax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c50:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c57:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3c5e:	48 83 c6 60          	add    $0x60,%rsi
    3c62:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    3c67:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    3c6c:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c74:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3c78:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3c80:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3c84:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    3c88:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    3c90:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c97:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    3c9b:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3c9f:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3ca6:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3cad:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3cb1:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3cb5:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3cb9:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3cbd:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3cc1:	4c 39 c7             	cmp    %r8,%rdi
    3cc4:	75 8a                	jne    3c50 <main+0x15e0>
    3cc6:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3cca:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3ccd:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    3cd4:	45 85 db             	test   %r11d,%r11d
    3cd7:	75 08                	jne    3ce1 <main+0x1671>
    3cd9:	45 89 e3             	mov    %r12d,%r11d
    3cdc:	e9 4b ff ff ff       	jmp    3c2c <main+0x15bc>
  for (int k = 0 ; k < group_count ; k++) {
    3ce1:	83 c0 02             	add    $0x2,%eax
    3ce4:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3ceb:	83 f8 06             	cmp    $0x6,%eax
    3cee:	0f 85 32 ff ff ff    	jne    3c26 <main+0x15b6>
    3cf4:	48 8d 3d 28 48 00 00 	lea    0x4828(%rip),%rdi        # 8523 <_IO_stdin_used+0x523>
    3cfb:	e8 30 e6 ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3d00:	48 8d 35 f8 46 00 00 	lea    0x46f8(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3d07:	48 8d 3d 2d 48 00 00 	lea    0x482d(%rip),%rdi        # 853b <_IO_stdin_used+0x53b>
    3d0e:	e8 dd e7 ff ff       	call   24f0 <fopen@plt>
    3d13:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas2_size; x++) {
    3d16:	85 db                	test   %ebx,%ebx
    3d18:	7e 6f                	jle    3d89 <main+0x1719>
    3d1a:	48 63 db             	movslq %ebx,%rbx
    3d1d:	4c 8d 35 ba 46 00 00 	lea    0x46ba(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    3d24:	4c 8d 2d f7 46 00 00 	lea    0x46f7(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    3d2b:	49 8d 2c df          	lea    (%r15,%rbx,8),%rbp
    char * c = calloc(250, sizeof(char));
    3d2f:	be 01 00 00 00       	mov    $0x1,%esi
    3d34:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3d39:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    3d3d:	e8 be e6 ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3d42:	4c 89 f1             	mov    %r14,%rcx
    3d45:	ba fa 00 00 00       	mov    $0xfa,%edx
    3d4a:	be 01 00 00 00       	mov    $0x1,%esi
    3d4f:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3d52:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3d56:	48 89 df             	mov    %rbx,%rdi
    3d59:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3d60:	31 c0                	xor    %eax,%eax
    3d62:	e8 39 e8 ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3d67:	48 89 da             	mov    %rbx,%rdx
    3d6a:	4c 89 ee             	mov    %r13,%rsi
    3d6d:	bf 01 00 00 00       	mov    $0x1,%edi
    3d72:	31 c0                	xor    %eax,%eax
    3d74:	e8 37 e7 ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3d79:	4c 89 e6             	mov    %r12,%rsi
    3d7c:	48 89 df             	mov    %rbx,%rdi
    3d7f:	e8 3c e6 ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3d84:	49 39 ef             	cmp    %rbp,%r15
    3d87:	75 a6                	jne    3d2f <main+0x16bf>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3d89:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    3d93:	4c 89 e7             	mov    %r12,%rdi
  long received = 0;
    3d96:	31 db                	xor    %ebx,%ebx
  fclose(m2);
    3d98:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
    3d9e:	e8 bd e5 ff ff       	call   2360 <fclose@plt>
  long sents = 0;
    3da3:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long sends = 0;
    3dac:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long ingests = 0;
    3db5:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long total = 0;
    3dbe:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  int datas2_size = 0; 
    3dc7:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
    3dcf:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    3dd4:	4c 8b b4 24 a8 00 00 00 	mov    0xa8(%rsp),%r14
    3ddc:	45 89 e5             	mov    %r12d,%r13d
    3ddf:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    3de4:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
      int x = (k * threads_per_group) + d;
    3de9:	44 89 e8             	mov    %r13d,%eax
    3dec:	41 83 c5 01          	add    $0x1,%r13d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3df0:	bf 0a 00 00 00       	mov    $0xa,%edi
        other = abs(x - 1) % total_threads;
    3df5:	41 f6 c5 01          	test   $0x1,%r13b
    3df9:	8d 50 02             	lea    0x2(%rax),%edx
    3dfc:	0f 44 c2             	cmove  %edx,%eax
    3dff:	4c 63 e0             	movslq %eax,%r12
    3e02:	e8 09 e5 ff ff       	call   2310 <putchar@plt>
    3e07:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3e0c:	bf 01 00 00 00       	mov    $0x1,%edi
    3e11:	48 8d 35 2c 47 00 00 	lea    0x472c(%rip),%rsi        # 8544 <_IO_stdin_used+0x544>
    3e18:	48 8b 10             	mov    (%rax),%rdx
    3e1b:	31 c0                	xor    %eax,%eax
    3e1d:	e8 8e e6 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e22:	41 8b 56 40          	mov    0x40(%r14),%edx
    3e26:	85 d2                	test   %edx,%edx
    3e28:	0f 8e 37 05 00 00    	jle    4365 <main+0x1cf5>
    3e2e:	48 63 ca             	movslq %edx,%rcx
    3e31:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    3e35:	31 d2                	xor    %edx,%edx
    3e37:	48 c1 e1 09          	shl    $0x9,%rcx
    3e3b:	48 01 c1             	add    %rax,%rcx
    3e3e:	66 90                	xchg   %ax,%ax
        v += thread_data[me].tasks[n].v;
    3e40:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e47:	48 05 00 02 00 00    	add    $0x200,%rax
    3e4d:	48 39 c8             	cmp    %rcx,%rax
    3e50:	75 ee                	jne    3e40 <main+0x17d0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3e52:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3e57:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
    3e5b:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3e5f:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3e63:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3e67:	85 c9                	test   %ecx,%ecx
    3e69:	7e 27                	jle    3e92 <main+0x1822>
    3e6b:	48 8b 40 38          	mov    0x38(%rax),%rax
    3e6f:	48 c1 e1 09          	shl    $0x9,%rcx
    3e73:	48 01 c1             	add    %rax,%rcx
    3e76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3e80:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3e87:	48 05 00 02 00 00    	add    $0x200,%rax
    3e8d:	48 39 c8             	cmp    %rcx,%rax
    3e90:	75 ee                	jne    3e80 <main+0x1810>
    3e92:	48 8d 35 c0 46 00 00 	lea    0x46c0(%rip),%rsi        # 8559 <_IO_stdin_used+0x559>
    3e99:	bf 01 00 00 00       	mov    $0x1,%edi
    3e9e:	31 c0                	xor    %eax,%eax
    3ea0:	e8 0b e6 ff ff       	call   24b0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3ea5:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3eaa:	bf 01 00 00 00       	mov    $0x1,%edi
    3eaf:	48 8d 35 7a 49 00 00 	lea    0x497a(%rip),%rsi        # 8830 <_IO_stdin_used+0x830>
    3eb6:	48 8b 08             	mov    (%rax),%rcx
    3eb9:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3ec3:	48 f7 e9             	imul   %rcx
    3ec6:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3eca:	31 c0                	xor    %eax,%eax
    3ecc:	48 d1 fa             	sar    %rdx
    3ecf:	48 29 ca             	sub    %rcx,%rdx
    3ed2:	e8 d9 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3ed7:	bf 0a 00 00 00       	mov    $0xa,%edi
    3edc:	e8 2f e4 ff ff       	call   2310 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3ee1:	45 8b 66 40          	mov    0x40(%r14),%r12d
    3ee5:	45 85 e4             	test   %r12d,%r12d
    3ee8:	0f 8e 4c 01 00 00    	jle    403a <main+0x19ca>
    3eee:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    3ef3:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    3ef8:	31 d2                	xor    %edx,%edx
    3efa:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3eff:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3f04:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    3f09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        total += thread_data[x].tasks[n].n;
    3f10:	49 8b 46 38          	mov    0x38(%r14),%rax
    3f14:	49 89 d1             	mov    %rdx,%r9
        sends += thread_data[x].tasks[n].sends;
    3f17:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    3f1c:	41 89 d5             	mov    %edx,%r13d
        total += thread_data[x].tasks[n].n;
    3f1f:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    3f23:	45 31 e4             	xor    %r12d,%r12d
        total += thread_data[x].tasks[n].n;
    3f26:	4c 01 c8             	add    %r9,%rax
        sends += thread_data[x].tasks[n].sends;
    3f29:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
        total += thread_data[x].tasks[n].n;
    3f2e:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
        ingests += thread_data[x].tasks[n].ingest_count;
    3f35:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
        sends += thread_data[x].tasks[n].sends;
    3f3c:	48 03 b8 78 01 00 00 	add    0x178(%rax),%rdi
    3f43:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    3f48:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3f4d:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3f52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3f58:	8b 54 24 08          	mov    0x8(%rsp),%edx
    3f5c:	45 89 e0             	mov    %r12d,%r8d
    3f5f:	44 89 e9             	mov    %r13d,%ecx
    3f62:	bf 01 00 00 00       	mov    $0x1,%edi
    3f67:	48 8d 35 f8 45 00 00 	lea    0x45f8(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    3f6e:	31 c0                	xor    %eax,%eax
    3f70:	e8 3b e5 ff ff       	call   24b0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f75:	49 8b 56 38          	mov    0x38(%r14),%rdx
    3f79:	48 83 ec 08          	sub    $0x8,%rsp
    3f7d:	45 89 e0             	mov    %r12d,%r8d
    3f80:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    3f85:	4a 8d 04 e5 00 00 00 00 	lea    0x0(,%r12,8),%rax
    3f8d:	4c 29 e0             	sub    %r12,%rax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3f90:	49 83 c4 01          	add    $0x1,%r12
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f94:	48 8b 94 3a 70 01 00 00 	mov    0x170(%rdx,%rdi,1),%rdx
    3f9c:	bf 01 00 00 00       	mov    $0x1,%edi
    3fa1:	48 8d 14 c2          	lea    (%rdx,%rax,8),%rdx
    3fa5:	48 8b 02             	mov    (%rdx),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3fa8:	48 8b 72 08          	mov    0x8(%rdx),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fac:	48 8b 88 08 03 00 00 	mov    0x308(%rax),%rcx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3fb3:	48 8b 96 08 03 00 00 	mov    0x308(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3fba:	48 8b 80 10 03 00 00 	mov    0x310(%rax),%rax
    3fc1:	48 8b b6 10 03 00 00 	mov    0x310(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fc8:	49 01 cf             	add    %rcx,%r15
    3fcb:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
    3fcf:	44 89 e9             	mov    %r13d,%ecx
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3fd2:	48 01 c3             	add    %rax,%rbx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3fd5:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3fd8:	49 01 d7             	add    %rdx,%r15
    3fdb:	50                   	push   %rax
    3fdc:	8b 54 24 18          	mov    0x18(%rsp),%edx
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3fe0:	48 01 f3             	add    %rsi,%rbx
    3fe3:	31 c0                	xor    %eax,%eax
    3fe5:	48 8d 35 64 48 00 00 	lea    0x4864(%rip),%rsi        # 8850 <_IO_stdin_used+0x850>
    3fec:	e8 bf e4 ff ff       	call   24b0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3ff1:	41 5a                	pop    %r10
    3ff3:	41 5b                	pop    %r11
    3ff5:	49 83 fc 06          	cmp    $0x6,%r12
    3ff9:	0f 85 59 ff ff ff    	jne    3f58 <main+0x18e8>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3fff:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    4004:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    4009:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    400e:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4013:	48 83 c2 01          	add    $0x1,%rdx
    4017:	41 39 56 40          	cmp    %edx,0x40(%r14)
    401b:	0f 8f ef fe ff ff    	jg     3f10 <main+0x18a0>
    4021:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    4026:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    402b:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    4030:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    4035:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    403a:	45 31 ff             	xor    %r15d,%r15d
    403d:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    4045:	4c 8d 25 24 48 00 00 	lea    0x4824(%rip),%r12        # 8870 <_IO_stdin_used+0x870>
    404c:	7e 5a                	jle    40a8 <main+0x1a38>
    404e:	66 90                	xchg   %ax,%ax
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4050:	49 8b 86 90 00 00 00 	mov    0x90(%r14),%rax
    4057:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    405b:	48 83 ec 08          	sub    $0x8,%rsp
    405f:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    4064:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4068:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    406c:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    4070:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    4074:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4077:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    407b:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    407e:	48 f7 e5             	mul    %rbp
    4081:	8b 49 20             	mov    0x20(%rcx),%ecx
    4084:	56                   	push   %rsi
    4085:	31 c0                	xor    %eax,%eax
    4087:	4c 89 e6             	mov    %r12,%rsi
    408a:	48 c1 ea 12          	shr    $0x12,%rdx
    408e:	49 89 d1             	mov    %rdx,%r9
    4091:	ba 02 00 00 00       	mov    $0x2,%edx
    4096:	e8 15 e4 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    409b:	41 58                	pop    %r8
    409d:	41 59                	pop    %r9
    409f:	4d 39 be a0 00 00 00 	cmp    %r15,0xa0(%r14)
    40a6:	7f a8                	jg     4050 <main+0x19e0>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    40a8:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    40af:	85 d2                	test   %edx,%edx
    40b1:	0f 8e 0a 01 00 00    	jle    41c1 <main+0x1b51>
    40b7:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    40bc:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    40c0:	45 31 ff             	xor    %r15d,%r15d
    40c3:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    40c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    40d0:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    40d4:	44 89 fb             	mov    %r15d,%ebx
    40d7:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    40df:	8b 30                	mov    (%rax),%esi
    40e1:	85 f6                	test   %esi,%esi
    40e3:	0f 8e c1 00 00 00    	jle    41aa <main+0x1b3a>
    40e9:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    40ee:	31 d2                	xor    %edx,%edx
    40f0:	48 8b 48 08          	mov    0x8(%rax),%rcx
    40f4:	49 89 f8             	mov    %rdi,%r8
    40f7:	48 89 d7             	mov    %rdx,%rdi
    40fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4100:	49 89 fc             	mov    %rdi,%r12
    4103:	45 31 ff             	xor    %r15d,%r15d
    4106:	49 c1 e4 08          	shl    $0x8,%r12
    410a:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    410e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4114:	85 d2                	test   %edx,%edx
    4116:	7e 77                	jle    418f <main+0x1b1f>
    4118:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    411d:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4120:	4c 89 f9             	mov    %r15,%rcx
    4123:	48 83 ec 08          	sub    $0x8,%rsp
    4127:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    412c:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4130:	48 c1 e1 05          	shl    $0x5,%rcx
    4134:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    413b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    413f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    4143:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4146:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    414a:	4c 2b 01             	sub    (%rcx),%r8
    414d:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    414e:	48 f7 e5             	mul    %rbp
    4151:	89 d9                	mov    %ebx,%ecx
    4153:	48 8d 35 66 47 00 00 	lea    0x4766(%rip),%rsi        # 88c0 <_IO_stdin_used+0x8c0>
    415a:	31 c0                	xor    %eax,%eax
    415c:	48 c1 ea 12          	shr    $0x12,%rdx
    4160:	49 89 d1             	mov    %rdx,%r9
    4163:	ba 02 00 00 00       	mov    $0x2,%edx
    4168:	e8 43 e3 ff ff       	call   24b0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    416d:	4d 8b 46 50          	mov    0x50(%r14),%r8
    4171:	5e                   	pop    %rsi
    4172:	5f                   	pop    %rdi
    4173:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    4177:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    417b:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    417f:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    4186:	7f 98                	jg     4120 <main+0x1ab0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4188:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    418d:	8b 32                	mov    (%rdx),%esi
    418f:	48 83 c7 01          	add    $0x1,%rdi
    4193:	39 fe                	cmp    %edi,%esi
    4195:	0f 8f 65 ff ff ff    	jg     4100 <main+0x1a90>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    419b:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    41a0:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    41a7:	4c 89 c7             	mov    %r8,%rdi
    41aa:	49 83 c7 01          	add    $0x1,%r15
    41ae:	44 39 fa             	cmp    %r15d,%edx
    41b1:	0f 8f 19 ff ff ff    	jg     40d0 <main+0x1a60>
    41b7:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    41bc:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    41c1:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    41c7:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    41ce:	44 39 6c 24 48       	cmp    %r13d,0x48(%rsp)
    41d3:	0f 85 10 fc ff ff    	jne    3de9 <main+0x1779>
  for (int k = 0 ; k < group_count ; k++) {
    41d9:	48 83 84 24 90 00 00 00 30 	addq   $0x30,0x90(%rsp)
    41e2:	44 8b 44 24 48       	mov    0x48(%rsp),%r8d
    41e7:	48 81 84 24 a8 00 00 00 b0 01 00 00 	addq   $0x1b0,0xa8(%rsp)
    41f3:	41 83 f8 05          	cmp    $0x5,%r8d
    41f7:	74 08                	je     4201 <main+0x1b91>
    41f9:	45 89 c4             	mov    %r8d,%r12d
    41fc:	e9 c6 fb ff ff       	jmp    3dc7 <main+0x1757>
    4201:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    4206:	bf 01 00 00 00       	mov    $0x1,%edi
    420b:	31 c0                	xor    %eax,%eax
    420d:	49 89 df             	mov    %rbx,%r15
    4210:	48 8d 35 5f 43 00 00 	lea    0x435f(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    4217:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4221:	4c 89 f2             	mov    %r14,%rdx
    4224:	e8 87 e2 ff ff       	call   24b0 <__printf_chk@plt>
    4229:	bf 0a 00 00 00       	mov    $0xa,%edi
    422e:	e8 dd e0 ff ff       	call   2310 <putchar@plt>
    4233:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
    423b:	48 8d 35 d6 46 00 00 	lea    0x46d6(%rip),%rsi        # 8918 <_IO_stdin_used+0x918>
    4242:	31 c0                	xor    %eax,%eax
    4244:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    4248:	bf 01 00 00 00       	mov    $0x1,%edi
    424d:	e8 5e e2 ff ff       	call   24b0 <__printf_chk@plt>
    4252:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    4257:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    425c:	48 8d 35 dd 46 00 00 	lea    0x46dd(%rip),%rsi        # 8940 <_IO_stdin_used+0x940>
    4263:	48 f7 eb             	imul   %rbx
    4266:	48 c1 ff 3f          	sar    $0x3f,%rdi
    426a:	31 c0                	xor    %eax,%eax
    426c:	48 d1 fa             	sar    %rdx
    426f:	48 29 fa             	sub    %rdi,%rdx
    4272:	bf 01 00 00 00       	mov    $0x1,%edi
    4277:	e8 34 e2 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    427c:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4281:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    4286:	48 8d 35 e3 46 00 00 	lea    0x46e3(%rip),%rsi        # 8970 <_IO_stdin_used+0x970>
    428d:	48 f7 eb             	imul   %rbx
    4290:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4294:	31 c0                	xor    %eax,%eax
    4296:	48 d1 fa             	sar    %rdx
    4299:	48 29 fa             	sub    %rdi,%rdx
    429c:	bf 01 00 00 00       	mov    $0x1,%edi
    42a1:	e8 0a e2 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    42a6:	4c 89 f0             	mov    %r14,%rax
    42a9:	bf 01 00 00 00       	mov    $0x1,%edi
    42ae:	48 8d 35 eb 46 00 00 	lea    0x46eb(%rip),%rsi        # 89a0 <_IO_stdin_used+0x9a0>
    42b5:	48 f7 eb             	imul   %rbx
    42b8:	4c 89 f0             	mov    %r14,%rax
    42bb:	48 c1 f8 3f          	sar    $0x3f,%rax
    42bf:	48 d1 fa             	sar    %rdx
    42c2:	48 29 c2             	sub    %rax,%rdx
    42c5:	31 c0                	xor    %eax,%eax
    42c7:	e8 e4 e1 ff ff       	call   24b0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    42cc:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    42d1:	bf 01 00 00 00       	mov    $0x1,%edi
    42d6:	48 8d 35 ad 42 00 00 	lea    0x42ad(%rip),%rsi        # 858a <_IO_stdin_used+0x58a>
    42dd:	48 f7 eb             	imul   %rbx
    42e0:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    42e5:	48 c1 f8 3f          	sar    $0x3f,%rax
    42e9:	48 d1 fa             	sar    %rdx
    42ec:	48 29 c2             	sub    %rax,%rdx
    42ef:	31 c0                	xor    %eax,%eax
    42f1:	48 89 d5             	mov    %rdx,%rbp
    42f4:	e8 b7 e1 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total sents %ld\n", sentdur);
  long recdur = received / DURATION;
    42f9:	4c 89 f8             	mov    %r15,%rax
    42fc:	bf 01 00 00 00       	mov    $0x1,%edi
    4301:	48 8d 35 93 42 00 00 	lea    0x4293(%rip),%rsi        # 859b <_IO_stdin_used+0x59b>
    4308:	48 f7 eb             	imul   %rbx
    430b:	4c 89 f8             	mov    %r15,%rax
    430e:	48 c1 f8 3f          	sar    $0x3f,%rax
    4312:	48 89 d3             	mov    %rdx,%rbx
    4315:	48 d1 fb             	sar    %rbx
    4318:	48 29 c3             	sub    %rax,%rbx
    431b:	31 c0                	xor    %eax,%eax
    431d:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    4320:	48 29 eb             	sub    %rbp,%rbx
    4323:	e8 88 e1 ff ff       	call   24b0 <__printf_chk@plt>
    4328:	31 c0                	xor    %eax,%eax
    432a:	48 89 da             	mov    %rbx,%rdx
    432d:	bf 01 00 00 00       	mov    $0x1,%edi
    4332:	48 8d 35 76 42 00 00 	lea    0x4276(%rip),%rsi        # 85af <_IO_stdin_used+0x5af>
    4339:	e8 72 e1 ff ff       	call   24b0 <__printf_chk@plt>
  return 0;

}
    433e:	48 8b 84 24 f8 00 00 00 	mov    0xf8(%rsp),%rax
    4346:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    434f:	75 25                	jne    4376 <main+0x1d06>
    4351:	48 81 c4 08 01 00 00 	add    $0x108,%rsp
    4358:	31 c0                	xor    %eax,%eax
    435a:	5b                   	pop    %rbx
    435b:	5d                   	pop    %rbp
    435c:	41 5c                	pop    %r12
    435e:	41 5d                	pop    %r13
    4360:	41 5e                	pop    %r14
    4362:	41 5f                	pop    %r15
    4364:	c3                   	ret
      long v = 0;
    4365:	31 d2                	xor    %edx,%edx
    4367:	e9 e6 fa ff ff       	jmp    3e52 <main+0x17e2>
            exit(1);
    436c:	bf 01 00 00 00       	mov    $0x1,%edi
    4371:	e8 9a e1 ff ff       	call   2510 <exit@plt>
}
    4376:	e8 05 e0 ff ff       	call   2380 <__stack_chk_fail@plt>
    437b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004380 <_start>:
    4380:	f3 0f 1e fa          	endbr64
    4384:	31 ed                	xor    %ebp,%ebp
    4386:	49 89 d1             	mov    %rdx,%r9
    4389:	5e                   	pop    %rsi
    438a:	48 89 e2             	mov    %rsp,%rdx
    438d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4391:	50                   	push   %rax
    4392:	54                   	push   %rsp
    4393:	45 31 c0             	xor    %r8d,%r8d
    4396:	31 c9                	xor    %ecx,%ecx
    4398:	48 8d 3d d1 e2 ff ff 	lea    -0x1d2f(%rip),%rdi        # 2670 <main>
    439f:	ff 15 33 6c 00 00    	call   *0x6c33(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    43a5:	f4                   	hlt
    43a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000043b0 <deregister_tm_clones>:
    43b0:	48 8d 3d 69 6c 00 00 	lea    0x6c69(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    43b7:	48 8d 05 62 6c 00 00 	lea    0x6c62(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    43be:	48 39 f8             	cmp    %rdi,%rax
    43c1:	74 15                	je     43d8 <deregister_tm_clones+0x28>
    43c3:	48 8b 05 16 6c 00 00 	mov    0x6c16(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    43ca:	48 85 c0             	test   %rax,%rax
    43cd:	74 09                	je     43d8 <deregister_tm_clones+0x28>
    43cf:	ff e0                	jmp    *%rax
    43d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    43d8:	c3                   	ret
    43d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000043e0 <register_tm_clones>:
    43e0:	48 8d 3d 39 6c 00 00 	lea    0x6c39(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    43e7:	48 8d 35 32 6c 00 00 	lea    0x6c32(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    43ee:	48 29 fe             	sub    %rdi,%rsi
    43f1:	48 89 f0             	mov    %rsi,%rax
    43f4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    43f8:	48 c1 f8 03          	sar    $0x3,%rax
    43fc:	48 01 c6             	add    %rax,%rsi
    43ff:	48 d1 fe             	sar    %rsi
    4402:	74 14                	je     4418 <register_tm_clones+0x38>
    4404:	48 8b 05 e5 6b 00 00 	mov    0x6be5(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    440b:	48 85 c0             	test   %rax,%rax
    440e:	74 08                	je     4418 <register_tm_clones+0x38>
    4410:	ff e0                	jmp    *%rax
    4412:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4418:	c3                   	ret
    4419:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004420 <__do_global_dtors_aux>:
    4420:	f3 0f 1e fa          	endbr64
    4424:	80 3d fd 6b 00 00 00 	cmpb   $0x0,0x6bfd(%rip)        # b028 <completed.0>
    442b:	75 2b                	jne    4458 <__do_global_dtors_aux+0x38>
    442d:	55                   	push   %rbp
    442e:	48 83 3d c2 6b 00 00 00 	cmpq   $0x0,0x6bc2(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    4436:	48 89 e5             	mov    %rsp,%rbp
    4439:	74 0c                	je     4447 <__do_global_dtors_aux+0x27>
    443b:	48 8b 3d c6 6b 00 00 	mov    0x6bc6(%rip),%rdi        # b008 <__dso_handle>
    4442:	e8 a9 de ff ff       	call   22f0 <__cxa_finalize@plt>
    4447:	e8 64 ff ff ff       	call   43b0 <deregister_tm_clones>
    444c:	c6 05 d5 6b 00 00 01 	movb   $0x1,0x6bd5(%rip)        # b028 <completed.0>
    4453:	5d                   	pop    %rbp
    4454:	c3                   	ret
    4455:	0f 1f 00             	nopl   (%rax)
    4458:	c3                   	ret
    4459:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004460 <frame_dummy>:
    4460:	f3 0f 1e fa          	endbr64
    4464:	e9 77 ff ff ff       	jmp    43e0 <register_tm_clones>
    4469:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004470 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4470:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    4474:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    447b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    447f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4487:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    448b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    448f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4496:	48 85 c9             	test   %rcx,%rcx
    4499:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    44a0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    44a4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    44a8:	31 c0                	xor    %eax,%eax
    44aa:	c3                   	ret
    44ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000044b0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    44b0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    44b4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    44bb:	85 c9                	test   %ecx,%ecx
    44bd:	7e 4f                	jle    450e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    44bf:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    44c6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    44cd:	48 c1 e1 09          	shl    $0x9,%rcx
    44d1:	48 8b 50 18          	mov    0x18(%rax),%rdx
    44d5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    44d9:	48 8b 70 38          	mov    0x38(%rax),%rsi
    44dd:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    44df:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    44e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    44e8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    44f0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    44f8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    4503:	48 05 00 02 00 00    	add    $0x200,%rax
    4509:	48 39 c1             	cmp    %rax,%rcx
    450c:	75 da                	jne    44e8 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    450e:	0f ae f8             	sfence
}
    4511:	31 c0                	xor    %eax,%eax
    4513:	c3                   	ret
    4514:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    451f:	90                   	nop

0000000000004520 <external_thread>:
void * external_thread(void *arg) {
    4520:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    4524:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4528:	0f 85 fb 00 00 00    	jne    4629 <external_thread+0x109>
void * external_thread(void *arg) {
    452e:	41 57                	push   %r15
    4530:	49 89 ff             	mov    %rdi,%r15
    4533:	41 56                	push   %r14
    4535:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    4537:	4c 8d 2d c6 3a 00 00 	lea    0x3ac6(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    453e:	41 54                	push   %r12
    4540:	55                   	push   %rbp
    4541:	53                   	push   %rbx
    4542:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    4546:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    454c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    4550:	85 c9                	test   %ecx,%ecx
    4552:	7e 6e                	jle    45c2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4554:	45 31 e4             	xor    %r12d,%r12d
    4557:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4560:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    4568:	31 db                	xor    %ebx,%ebx
    456a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    456e:	48 8b 06             	mov    (%rsi),%rax
    4571:	8b 10                	mov    (%rax),%edx
    4573:	85 d2                	test   %edx,%edx
    4575:	7e 2a                	jle    45a1 <external_thread+0x81>
    4577:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    457b:	48 89 dd             	mov    %rbx,%rbp
    457e:	48 c1 e5 08          	shl    $0x8,%rbp
    4582:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4586:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    458d:	45 85 c0             	test   %r8d,%r8d
    4590:	74 36                	je     45c8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4592:	48 83 c3 01          	add    $0x1,%rbx
    4596:	39 da                	cmp    %ebx,%edx
    4598:	7f e1                	jg     457b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    459a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    45a1:	49 83 c4 01          	add    $0x1,%r12
    45a5:	44 39 e1             	cmp    %r12d,%ecx
    45a8:	7f b6                	jg     4560 <external_thread+0x40>
  while (data->running == 1) {
    45aa:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    45af:	74 9f                	je     4550 <external_thread+0x30>
}
    45b1:	48 83 c4 08          	add    $0x8,%rsp
    45b5:	31 c0                	xor    %eax,%eax
    45b7:	5b                   	pop    %rbx
    45b8:	5d                   	pop    %rbp
    45b9:	41 5c                	pop    %r12
    45bb:	41 5d                	pop    %r13
    45bd:	41 5e                	pop    %r14
    45bf:	41 5f                	pop    %r15
    45c1:	c3                   	ret
  while (data->running == 1) {
    45c2:	eb fe                	jmp    45c2 <external_thread+0xa2>
    45c4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    45c8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    45cb:	48 8b 06             	mov    (%rsi),%rax
    45ce:	48 8b 78 08          	mov    0x8(%rax),%rdi
    45d2:	48 01 ef             	add    %rbp,%rdi
    45d5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    45dc:	48 c1 e6 05          	shl    $0x5,%rsi
    45e0:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    45e7:	bf 04 00 00 00       	mov    $0x4,%edi
    45ec:	e8 5f dd ff ff       	call   2350 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    45f1:	49 8b 47 50          	mov    0x50(%r15),%rax
    45f5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    45f9:	48 8b 40 08          	mov    0x8(%rax),%rax
    45fd:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    4608:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    460b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    460f:	48 83 c3 01          	add    $0x1,%rbx
    4613:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4617:	48 8b 06             	mov    (%rsi),%rax
    461a:	8b 10                	mov    (%rax),%edx
    461c:	39 da                	cmp    %ebx,%edx
    461e:	0f 8f 53 ff ff ff    	jg     4577 <external_thread+0x57>
    4624:	e9 71 ff ff ff       	jmp    459a <external_thread+0x7a>
}
    4629:	31 c0                	xor    %eax,%eax
    462b:	c3                   	ret
    462c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004630 <timer_thread>:
void* timer_thread(void *arg) {
    4630:	f3 0f 1e fa          	endbr64
    4634:	41 57                	push   %r15
    4636:	48 8d 35 d3 39 00 00 	lea    0x39d3(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    463d:	41 56                	push   %r14
    463f:	49 89 fe             	mov    %rdi,%r14
    4642:	41 55                	push   %r13
    4644:	41 54                	push   %r12
    4646:	55                   	push   %rbp
    4647:	53                   	push   %rbx
    4648:	48 83 ec 68          	sub    $0x68,%rsp
    464c:	8b 57 04             	mov    0x4(%rdi),%edx
    464f:	bf 01 00 00 00       	mov    $0x1,%edi
    4654:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    465d:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    4662:	31 c0                	xor    %eax,%eax
    4664:	e8 47 de ff ff       	call   24b0 <__printf_chk@plt>
  struct timespec preempt = {
    4669:	66 0f 6f 05 4f 45 00 00 	movdqa 0x454f(%rip),%xmm0        # 8bc0 <_IO_stdin_used+0xbc0>
    4671:	ba 88 13 00 00       	mov    $0x1388,%edx
    4676:	31 c0                	xor    %eax,%eax
    4678:	48 8d 35 a3 39 00 00 	lea    0x39a3(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    467f:	bf 01 00 00 00       	mov    $0x1,%edi
    4684:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    4689:	e8 22 de ff ff       	call   24b0 <__printf_chk@plt>
  while (data->running && n < times) {
    468e:	41 8b 5e 44          	mov    0x44(%r14),%ebx
    4692:	85 db                	test   %ebx,%ebx
    4694:	0f 84 99 00 00 00    	je     4733 <timer_thread+0x103>
  int n = 0;
    469a:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    469d:	31 db                	xor    %ebx,%ebx
    469f:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    y++;
    46a4:	31 ed                	xor    %ebp,%ebp
    46a6:	4c 8d 64 24 20       	lea    0x20(%rsp),%r12
    nanosleep(&preempt , &rem2);
    46ab:	4c 89 e7             	mov    %r12,%rdi
    46ae:	4c 89 ee             	mov    %r13,%rsi
    n++;
    46b1:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    46b5:	e8 e6 dc ff ff       	call   23a0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46ba:	49 63 46 30          	movslq 0x30(%r14),%rax
    y++;
    46be:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46c1:	85 c0                	test   %eax,%eax
    46c3:	7e 47                	jle    470c <timer_thread+0xdc>
    46c5:	49 8b 4e 18          	mov    0x18(%r14),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    46c9:	4c 63 c3             	movslq %ebx,%r8
    46cc:	49 c1 e0 09          	shl    $0x9,%r8
    46d0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    46d4:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    46d8:	48 8b 19             	mov    (%rcx),%rbx
    46db:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46dd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    46e1:	99                   	cltd
    46e2:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    46e5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    46e9:	48 63 d2             	movslq %edx,%rdx
    46ec:	48 c1 e2 09          	shl    $0x9,%rdx
    46f0:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    46fb:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4707:	49 39 c9             	cmp    %rcx,%r9
    470a:	75 cc                	jne    46d8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    470c:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    470f:	49 8b 46 18          	mov    0x18(%r14),%rax
  while (data->running && n < times) {
    4713:	41 8b 4e 44          	mov    0x44(%r14),%ecx
    y++;
    4717:	89 fb                	mov    %edi,%ebx
    if (y >= data->threads[0]->task_count) {
    4719:	48 8b 00             	mov    (%rax),%rax
    y++;
    471c:	39 78 40             	cmp    %edi,0x40(%rax)
    471f:	0f 4e dd             	cmovle %ebp,%ebx
  while (data->running && n < times) {
    4722:	85 c9                	test   %ecx,%ecx
    4724:	74 0d                	je     4733 <timer_thread+0x103>
    4726:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    472d:	0f 85 78 ff ff ff    	jne    46ab <timer_thread+0x7b>
    4733:	48 8d 3d fe 38 00 00 	lea    0x38fe(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    473a:	e8 f1 db ff ff       	call   2330 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    473f:	49 63 56 30          	movslq 0x30(%r14),%rdx
    4743:	85 d2                	test   %edx,%edx
    4745:	7e 6e                	jle    47b5 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    4747:	49 63 46 40          	movslq 0x40(%r14),%rax
    474b:	85 c0                	test   %eax,%eax
    474d:	7e 66                	jle    47b5 <timer_thread+0x185>
    474f:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4753:	4d 8b 46 18          	mov    0x18(%r14),%r8
    4757:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    475f:	31 c9                	xor    %ecx,%ecx
    4761:	48 89 c6             	mov    %rax,%rsi
    4764:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4768:	48 8b 40 38          	mov    0x38(%rax),%rax
    476c:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4770:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4776:	74 18                	je     4790 <timer_thread+0x160>
    4778:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4782:	48 05 00 02 00 00    	add    $0x200,%rax
    4788:	48 39 c2             	cmp    %rax,%rdx
    478b:	74 1f                	je     47ac <timer_thread+0x17c>
    478d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->tasks[y].sending = 0;
    4790:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    479a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    47a0:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    47a7:	48 39 c2             	cmp    %rax,%rdx
    47aa:	75 e4                	jne    4790 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    47ac:	48 83 c1 08          	add    $0x8,%rcx
    47b0:	48 39 cf             	cmp    %rcx,%rdi
    47b3:	75 af                	jne    4764 <timer_thread+0x134>
  asm volatile ("mfence" ::: "memory");
    47b5:	0f ae f0             	mfence
  struct timespec drain = {
    47b8:	66 0f 6f 05 10 44 00 00 	movdqa 0x4410(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    47c0:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    47c5:	49 63 46 28          	movslq 0x28(%r14),%rax
    y++;
    47c9:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    47cc:	85 c0                	test   %eax,%eax
    47ce:	7e 44                	jle    4814 <timer_thread+0x1e4>
    47d0:	49 8b 4e 18          	mov    0x18(%r14),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    47d4:	4c 63 c3             	movslq %ebx,%r8
    47d7:	49 c1 e0 09          	shl    $0x9,%r8
    47db:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    47df:	90                   	nop
        int next = (y + 1) % data->threads[x]->task_count;
    47e0:	48 8b 19             	mov    (%rcx),%rbx
    47e3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    47e5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    47e9:	99                   	cltd
    47ea:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    47ed:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    47f1:	48 63 d2             	movslq %edx,%rdx
    47f4:	48 c1 e2 09          	shl    $0x9,%rdx
    47f8:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4803:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    480f:	49 39 c9             	cmp    %rcx,%r9
    4812:	75 cc                	jne    47e0 <timer_thread+0x1b0>
    asm volatile ("mfence" ::: "memory");
    4814:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4817:	49 8b 76 18          	mov    0x18(%r14),%rsi
    y++;
    481b:	31 db                	xor    %ebx,%ebx
    if (y >= data->threads[0]->task_count) {
    481d:	48 8b 06             	mov    (%rsi),%rax
    y++;
    4820:	39 78 40             	cmp    %edi,0x40(%rax)
    4823:	0f 4f df             	cmovg  %edi,%ebx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4826:	41 8b 7e 30          	mov    0x30(%r14),%edi
    482a:	85 ff                	test   %edi,%edi
    482c:	0f 8e ca 01 00 00    	jle    49fc <timer_thread+0x3cc>
    int all_empty = 1;
    4832:	89 5c 24 0c          	mov    %ebx,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4836:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    4839:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    483f:	90                   	nop
      for (int y = 0 ; y < 2 ; y++) {
    4840:	45 31 e4             	xor    %r12d,%r12d
    4843:	44 89 eb             	mov    %r13d,%ebx
    4846:	4a 8d 2c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbp
    484e:	44 89 e6             	mov    %r12d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4851:	85 ff                	test   %edi,%edi
    4853:	0f 8e c7 00 00 00    	jle    4920 <timer_thread+0x2f0>
    4859:	4d 89 e2             	mov    %r12,%r10
      y = 0;
    485c:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    485e:	45 31 c0             	xor    %r8d,%r8d
    4861:	49 c1 e2 09          	shl    $0x9,%r10
    4865:	0f 1f 00             	nopl   (%rax)
          if (x == k) { continue; }
    4868:	45 39 e8             	cmp    %r13d,%r8d
    486b:	74 39                	je     48a6 <timer_thread+0x276>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    486d:	49 8b 56 18          	mov    0x18(%r14),%rdx
    4871:	48 8b 14 2a          	mov    (%rdx,%rbp,1),%rdx
    4875:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4879:	4a 8b 8c 12 70 01 00 00 	mov    0x170(%rdx,%r10,1),%rcx
    4881:	48 01 c1             	add    %rax,%rcx
    4884:	48 89 ca             	mov    %rcx,%rdx
    4887:	48 8b 09             	mov    (%rcx),%rcx
    488a:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    488e:	4c 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9
    4895:	4c 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11
    489c:	4d 85 c9             	test   %r9,%r9
    489f:	7f 27                	jg     48c8 <timer_thread+0x298>
    48a1:	4d 85 db             	test   %r11,%r11
    48a4:	7f 22                	jg     48c8 <timer_thread+0x298>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    48a6:	41 83 c0 01          	add    $0x1,%r8d
    48aa:	48 83 c0 38          	add    $0x38,%rax
    48ae:	44 39 c7             	cmp    %r8d,%edi
    48b1:	75 b5                	jne    4868 <timer_thread+0x238>
      for (int y = 0 ; y < 2 ; y++) {
    48b3:	49 83 fc 01          	cmp    $0x1,%r12
    48b7:	74 67                	je     4920 <timer_thread+0x2f0>
    48b9:	49 83 c4 01          	add    $0x1,%r12
    48bd:	44 89 e6             	mov    %r12d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    48c0:	eb 97                	jmp    4859 <timer_thread+0x229>
    48c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    48c8:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    48ce:	48 83 ec 08          	sub    $0x8,%rsp
    48d2:	bf 01 00 00 00       	mov    $0x1,%edi
    48d7:	89 da                	mov    %ebx,%edx
    48d9:	50                   	push   %rax
    48da:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    48e0:	89 f1                	mov    %esi,%ecx
    48e2:	48 8d 35 74 37 00 00 	lea    0x3774(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    48e9:	50                   	push   %rax
    48ea:	31 c0                	xor    %eax,%eax
    48ec:	41 53                	push   %r11
    48ee:	e8 bd db ff ff       	call   24b0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48f3:	41 8b 7e 30          	mov    0x30(%r14),%edi
      for (int y = 0 ; y < 2 ; y++) {
    48f7:	48 83 c4 20          	add    $0x20,%rsp
    48fb:	49 83 fc 01          	cmp    $0x1,%r12
    48ff:	0f 84 8b 00 00 00    	je     4990 <timer_thread+0x360>
    4905:	49 83 c4 01          	add    $0x1,%r12
    4909:	45 31 ff             	xor    %r15d,%r15d
    490c:	44 89 e6             	mov    %r12d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    490f:	85 ff                	test   %edi,%edi
    4911:	0f 8f 42 ff ff ff    	jg     4859 <timer_thread+0x229>
    4917:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4920:	49 83 c5 01          	add    $0x1,%r13
    4924:	44 39 ef             	cmp    %r13d,%edi
    4927:	0f 8f 13 ff ff ff    	jg     4840 <timer_thread+0x210>
    492d:	8b 5c 24 0c          	mov    0xc(%rsp),%ebx
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4931:	85 ff                	test   %edi,%edi
    4933:	7e 38                	jle    496d <timer_thread+0x33d>
    4935:	31 ed                	xor    %ebp,%ebp
    int all_waited = 1;
    4937:	bf 01 00 00 00       	mov    $0x1,%edi
    493c:	49 8b 76 18          	mov    0x18(%r14),%rsi
    4940:	41 8b 56 40          	mov    0x40(%r14),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4944:	48 8b 04 ee          	mov    (%rsi,%rbp,8),%rax
    4948:	48 8b 40 38          	mov    0x38(%rax),%rax
    494c:	8b 88 9c 01 00 00    	mov    0x19c(%rax),%ecx
    4952:	39 d1                	cmp    %edx,%ecx
    4954:	7c 7a                	jl     49d0 <timer_thread+0x3a0>
    4956:	8b 80 9c 03 00 00    	mov    0x39c(%rax),%eax
    495c:	39 d0                	cmp    %edx,%eax
    495e:	7c 48                	jl     49a8 <timer_thread+0x378>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4960:	48 83 c5 01          	add    $0x1,%rbp
    4964:	41 39 6e 30          	cmp    %ebp,0x30(%r14)
    4968:	7f da                	jg     4944 <timer_thread+0x314>
    496a:	41 21 ff             	and    %edi,%r15d
    if (all_empty == 1 && all_waited == 1) {
    496d:	45 85 ff             	test   %r15d,%r15d
    4970:	0f 85 86 00 00 00    	jne    49fc <timer_thread+0x3cc>
      nanosleep(&drain , &drainrem);
    4976:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    497b:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    4980:	e8 1b da ff ff       	call   23a0 <nanosleep@plt>
    4985:	e9 3b fe ff ff       	jmp    47c5 <timer_thread+0x195>
    498a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4990:	49 83 c5 01          	add    $0x1,%r13
    4994:	45 31 ff             	xor    %r15d,%r15d
    4997:	44 39 ef             	cmp    %r13d,%edi
    499a:	0f 8f a0 fe ff ff    	jg     4840 <timer_thread+0x210>
    49a0:	eb 8b                	jmp    492d <timer_thread+0x2fd>
    49a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    49a8:	89 c2                	mov    %eax,%edx
    49aa:	bf 01 00 00 00       	mov    $0x1,%edi
    49af:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    49b1:	48 83 c5 01          	add    $0x1,%rbp
    49b5:	48 8d 35 49 39 00 00 	lea    0x3949(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    49bc:	e8 ef da ff ff       	call   24b0 <__printf_chk@plt>
          all_waited = 0; 
    49c1:	31 ff                	xor    %edi,%edi
    for (int k = 0 ; k < data->my_thread_count; k++) {
    49c3:	41 39 6e 30          	cmp    %ebp,0x30(%r14)
    49c7:	0f 8f 6f ff ff ff    	jg     493c <timer_thread+0x30c>
    49cd:	eb 9b                	jmp    496a <timer_thread+0x33a>
    49cf:	90                   	nop
    49d0:	89 ca                	mov    %ecx,%edx
    49d2:	48 8d 35 2c 39 00 00 	lea    0x392c(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    49d9:	bf 01 00 00 00       	mov    $0x1,%edi
    49de:	31 c0                	xor    %eax,%eax
    49e0:	e8 cb da ff ff       	call   24b0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    49e5:	49 8b 76 18          	mov    0x18(%r14),%rsi
    49e9:	41 8b 56 40          	mov    0x40(%r14),%edx
          all_waited = 0; 
    49ed:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    49ef:	48 8b 04 ee          	mov    (%rsi,%rbp,8),%rax
    49f3:	48 8b 40 38          	mov    0x38(%rax),%rax
    49f7:	e9 5a ff ff ff       	jmp    4956 <timer_thread+0x326>
    49fc:	48 8d 3d 51 36 00 00 	lea    0x3651(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4a03:	e8 28 d9 ff ff       	call   2330 <puts@plt>
  while (data->running) {
    4a08:	41 8b 56 44          	mov    0x44(%r14),%edx
    4a0c:	85 d2                	test   %edx,%edx
    4a0e:	0f 84 eb 00 00 00    	je     4aff <timer_thread+0x4cf>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4a14:	41 8b 46 2c          	mov    0x2c(%r14),%eax
    4a18:	31 db                	xor    %ebx,%ebx
    4a1a:	48 8d 2d 59 36 00 00 	lea    0x3659(%rip),%rbp        # 807a <_IO_stdin_used+0x7a>
    4a21:	4c 8d 25 6d 36 00 00 	lea    0x366d(%rip),%r12        # 8095 <_IO_stdin_used+0x95>
    4a28:	85 c0                	test   %eax,%eax
    4a2a:	7e 38                	jle    4a64 <timer_thread+0x434>
    4a2c:	0f 1f 40 00          	nopl   0x0(%rax)
    4a30:	31 c0                	xor    %eax,%eax
    4a32:	89 da                	mov    %ebx,%edx
    4a34:	48 89 ee             	mov    %rbp,%rsi
    4a37:	bf 01 00 00 00       	mov    $0x1,%edi
    4a3c:	e8 6f da ff ff       	call   24b0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4a41:	49 8b 46 18          	mov    0x18(%r14),%rax
    4a45:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4a49:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4a4d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4a54:	0f 84 d2 00 00 00    	je     4b2c <timer_thread+0x4fc>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4a5a:	48 83 c3 01          	add    $0x1,%rbx
    4a5e:	41 39 5e 2c          	cmp    %ebx,0x2c(%r14)
    4a62:	7f cc                	jg     4a30 <timer_thread+0x400>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4a64:	49 63 56 30          	movslq 0x30(%r14),%rdx
    4a68:	85 d2                	test   %edx,%edx
    4a6a:	7e 7c                	jle    4ae8 <timer_thread+0x4b8>
      for (int y = 0 ; y < data->task_count ; y++) {
    4a6c:	41 8b 46 40          	mov    0x40(%r14),%eax
    4a70:	85 c0                	test   %eax,%eax
    4a72:	7e 74                	jle    4ae8 <timer_thread+0x4b8>
    4a74:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4a77:	4d 8b 46 18          	mov    0x18(%r14),%r8
    4a7b:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4a83:	31 c9                	xor    %ecx,%ecx
    4a85:	48 c1 e6 09          	shl    $0x9,%rsi
    4a89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4a90:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4a94:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a98:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4a9c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4aa2:	74 1c                	je     4ac0 <timer_thread+0x490>
    4aa4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4aae:	48 05 00 02 00 00    	add    $0x200,%rax
    4ab4:	48 39 d0             	cmp    %rdx,%rax
    4ab7:	74 26                	je     4adf <timer_thread+0x4af>
    4ab9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4ac0:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4aca:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4ad0:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4ada:	48 39 d0             	cmp    %rdx,%rax
    4add:	75 e1                	jne    4ac0 <timer_thread+0x490>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4adf:	48 83 c1 08          	add    $0x8,%rcx
    4ae3:	48 39 cf             	cmp    %rcx,%rdi
    4ae6:	75 a8                	jne    4a90 <timer_thread+0x460>
    asm volatile ("mfence" ::: "memory");
    4ae8:	0f ae f0             	mfence
    4aeb:	48 8d 3d b5 35 00 00 	lea    0x35b5(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4af2:	e8 39 d8 ff ff       	call   2330 <puts@plt>
    data->running = 0;
    4af7:	41 c7 46 44 00 00 00 00 	movl   $0x0,0x44(%r14)
    4aff:	48 8d 3d a8 35 00 00 	lea    0x35a8(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4b06:	e8 25 d8 ff ff       	call   2330 <puts@plt>
}
    4b0b:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    4b10:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b19:	75 41                	jne    4b5c <timer_thread+0x52c>
    4b1b:	48 83 c4 68          	add    $0x68,%rsp
    4b1f:	31 c0                	xor    %eax,%eax
    4b21:	5b                   	pop    %rbx
    4b22:	5d                   	pop    %rbp
    4b23:	41 5c                	pop    %r12
    4b25:	41 5d                	pop    %r13
    4b27:	41 5e                	pop    %r14
    4b29:	41 5f                	pop    %r15
    4b2b:	c3                   	ret
    4b2c:	4c 89 e7             	mov    %r12,%rdi
    4b2f:	e8 fc d7 ff ff       	call   2330 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4b34:	49 8b 46 18          	mov    0x18(%r14),%rax
    4b38:	be 01 00 00 00       	mov    $0x1,%esi
    4b3d:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4b41:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4b45:	8b 78 60             	mov    0x60(%rax),%edi
    4b48:	e8 13 d9 ff ff       	call   2460 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4b4d:	41 39 5e 2c          	cmp    %ebx,0x2c(%r14)
    4b51:	0f 8f d9 fe ff ff    	jg     4a30 <timer_thread+0x400>
    4b57:	e9 08 ff ff ff       	jmp    4a64 <timer_thread+0x434>
}
    4b5c:	e8 1f d8 ff ff       	call   2380 <__stack_chk_fail@plt>
    4b61:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4b6c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b70 <minf>:
int minf(int a, int b) {
    4b70:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    4b74:	39 f7                	cmp    %esi,%edi
    4b76:	89 f0                	mov    %esi,%eax
    4b78:	0f 4e c7             	cmovle %edi,%eax
}
    4b7b:	c3                   	ret
    4b7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b80 <maxf>:
int maxf(int a, int b) {
    4b80:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    4b84:	39 f7                	cmp    %esi,%edi
    4b86:	89 f0                	mov    %esi,%eax
    4b88:	0f 4d c7             	cmovge %edi,%eax
}
    4b8b:	c3                   	ret
    4b8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b90 <strtolower>:
void strtolower(char *str) {
    4b90:	f3 0f 1e fa          	endbr64
    4b94:	55                   	push   %rbp
    4b95:	53                   	push   %rbx
    4b96:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    4b9a:	48 0f be 1f          	movsbq (%rdi),%rbx
    4b9e:	84 db                	test   %bl,%bl
    4ba0:	74 24                	je     4bc6 <strtolower+0x36>
    4ba2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4ba5:	e8 e6 d9 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4baa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4bb0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4bb3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4bb7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4bba:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    4bbd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4bc2:	84 db                	test   %bl,%bl
    4bc4:	75 ea                	jne    4bb0 <strtolower+0x20>
}
    4bc6:	48 83 c4 08          	add    $0x8,%rsp
    4bca:	5b                   	pop    %rbx
    4bcb:	5d                   	pop    %rbp
    4bcc:	c3                   	ret
    4bcd:	0f 1f 00             	nopl   (%rax)

0000000000004bd0 <zh_malloc>:
void *zh_malloc(size_t size) {
    4bd0:	f3 0f 1e fa          	endbr64
    4bd4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4bd8:	e8 93 d8 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4bdd:	48 85 c0             	test   %rax,%rax
    4be0:	74 05                	je     4be7 <zh_malloc+0x17>
}
    4be2:	48 83 c4 08          	add    $0x8,%rsp
    4be6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4be7:	48 8b 0d 32 64 00 00 	mov    0x6432(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4bee:	ba 28 00 00 00       	mov    $0x28,%edx
    4bf3:	be 01 00 00 00       	mov    $0x1,%esi
    4bf8:	48 8d 3d c1 39 00 00 	lea    0x39c1(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    4bff:	e8 2c d9 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    4c04:	bf 01 00 00 00       	mov    $0x1,%edi
    4c09:	e8 02 d9 ff ff       	call   2510 <exit@plt>
    4c0e:	66 90                	xchg   %ax,%ax

0000000000004c10 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4c10:	f3 0f 1e fa          	endbr64
    4c14:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4c15:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4c1a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4c1d:	e8 8e d7 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    4c22:	48 85 c0             	test   %rax,%rax
    4c25:	74 11                	je     4c38 <get_filename_ext+0x28>
    4c27:	48 39 c3             	cmp    %rax,%rbx
    4c2a:	74 0c                	je     4c38 <get_filename_ext+0x28>
    return dot + 1;
    4c2c:	48 83 c0 01          	add    $0x1,%rax
}
    4c30:	5b                   	pop    %rbx
    4c31:	c3                   	ret
    4c32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4c38:	48 8d 05 b7 34 00 00 	lea    0x34b7(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4c3f:	5b                   	pop    %rbx
    4c40:	c3                   	ret
    4c41:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4c4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c50 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4c50:	f3 0f 1e fa          	endbr64
    4c54:	41 55                	push   %r13
    4c56:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c59:	48 89 fe             	mov    %rdi,%rsi
    4c5c:	41 54                	push   %r12
    4c5e:	55                   	push   %rbp
    4c5f:	48 89 d5             	mov    %rdx,%rbp
    4c62:	ba 00 04 00 00       	mov    $0x400,%edx
    4c67:	53                   	push   %rbx
    4c68:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4c6f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4c78:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4c80:	31 c0                	xor    %eax,%eax
    4c82:	49 89 e4             	mov    %rsp,%r12
    4c85:	4c 89 e7             	mov    %r12,%rdi
    4c88:	e8 03 d8 ff ff       	call   2490 <__strcpy_chk@plt>
    for (; *str; ++str)
    4c8d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4c92:	84 db                	test   %bl,%bl
    4c94:	74 24                	je     4cba <send_headers+0x6a>
        *str = (char)tolower(*str);
    4c96:	e8 f5 d8 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4c9b:	48 8b 08             	mov    (%rax),%rcx
    4c9e:	4c 89 e0             	mov    %r12,%rax
    4ca1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ca8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4cab:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4caf:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4cb2:	48 0f be 18          	movsbq (%rax),%rbx
    4cb6:	84 db                	test   %bl,%bl
    4cb8:	75 ee                	jne    4ca8 <send_headers+0x58>
    void *buf = malloc(size);
    4cba:	bf 11 00 00 00       	mov    $0x11,%edi
    4cbf:	e8 ac d7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4cc4:	48 85 c0             	test   %rax,%rax
    4cc7:	0f 84 7e 04 00 00    	je     514b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ccd:	66 0f 6f 05 0b 3f 00 00 	movdqa 0x3f0b(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    iov[0].iov_base = zh_malloc(slen);
    4cd5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4cd9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4cde:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4ce6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4cea:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4ced:	e8 7e d7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4cf2:	48 85 c0             	test   %rax,%rax
    4cf5:	0f 84 50 04 00 00    	je     514b <send_headers+0x4fb>
    4cfb:	66 0f 6f 05 ed 3e 00 00 	movdqa 0x3eed(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    iov[1].iov_base = zh_malloc(slen);
    4d03:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4d07:	4c 89 e7             	mov    %r12,%rdi
    4d0a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4d14:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4d1c:	0f 11 00             	movups %xmm0,(%rax)
    4d1f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4d23:	be 2e 00 00 00       	mov    $0x2e,%esi
    4d28:	e8 83 d6 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    4d2d:	48 85 c0             	test   %rax,%rax
    4d30:	0f 84 ea 02 00 00    	je     5020 <send_headers+0x3d0>
    4d36:	4c 39 e0             	cmp    %r12,%rax
    4d39:	0f 84 e1 02 00 00    	je     5020 <send_headers+0x3d0>
    return dot + 1;
    4d3f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4d43:	48 8d 3d 7a 33 00 00 	lea    0x337a(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4d4a:	48 89 de             	mov    %rbx,%rsi
    4d4d:	e8 be d6 ff ff       	call   2410 <strcmp@plt>
    4d52:	85 c0                	test   %eax,%eax
    4d54:	75 20                	jne    4d76 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d56:	66 0f 6f 05 a2 3e 00 00 	movdqa 0x3ea2(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4d5e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d66:	66 0f 6f 05 a2 3e 00 00 	movdqa 0x3ea2(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4d6e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4d76:	48 89 de             	mov    %rbx,%rsi
    4d79:	48 8d 3d 48 33 00 00 	lea    0x3348(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4d80:	e8 8b d6 ff ff       	call   2410 <strcmp@plt>
    4d85:	85 c0                	test   %eax,%eax
    4d87:	75 20                	jne    4da9 <send_headers+0x159>
    4d89:	66 0f 6f 05 6f 3e 00 00 	movdqa 0x3e6f(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4d91:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d99:	66 0f 6f 05 6f 3e 00 00 	movdqa 0x3e6f(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4da1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4da9:	48 89 de             	mov    %rbx,%rsi
    4dac:	48 8d 3d 1a 33 00 00 	lea    0x331a(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4db3:	e8 58 d6 ff ff       	call   2410 <strcmp@plt>
    4db8:	85 c0                	test   %eax,%eax
    4dba:	0f 84 10 02 00 00    	je     4fd0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4dc0:	48 89 de             	mov    %rbx,%rsi
    4dc3:	48 8d 3d 07 33 00 00 	lea    0x3307(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4dca:	e8 41 d6 ff ff       	call   2410 <strcmp@plt>
    4dcf:	85 c0                	test   %eax,%eax
    4dd1:	0f 84 a9 02 00 00    	je     5080 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4dd7:	48 89 de             	mov    %rbx,%rsi
    4dda:	48 8d 3d f4 32 00 00 	lea    0x32f4(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4de1:	e8 2a d6 ff ff       	call   2410 <strcmp@plt>
    4de6:	85 c0                	test   %eax,%eax
    4de8:	0f 84 6a 02 00 00    	je     5058 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4dee:	48 89 de             	mov    %rbx,%rsi
    4df1:	48 8d 3d 20 33 00 00 	lea    0x3320(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4df8:	e8 13 d6 ff ff       	call   2410 <strcmp@plt>
    4dfd:	85 c0                	test   %eax,%eax
    4dff:	0f 84 2b 02 00 00    	je     5030 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4e05:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4e08:	0f 84 52 01 00 00    	je     4f60 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4e0e:	48 89 de             	mov    %rbx,%rsi
    4e11:	48 8d 3d c1 32 00 00 	lea    0x32c1(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4e18:	e8 f3 d5 ff ff       	call   2410 <strcmp@plt>
    4e1d:	85 c0                	test   %eax,%eax
    4e1f:	0f 84 ab 02 00 00    	je     50d0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4e25:	48 89 de             	mov    %rbx,%rsi
    4e28:	48 8d 3d ae 32 00 00 	lea    0x32ae(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4e2f:	e8 dc d5 ff ff       	call   2410 <strcmp@plt>
    4e34:	85 c0                	test   %eax,%eax
    4e36:	0f 84 6c 02 00 00    	je     50a8 <send_headers+0x458>
    slen = strlen(send_buffer);
    4e3c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4e44:	4c 89 e7             	mov    %r12,%rdi
    4e47:	e8 24 d5 ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    4e4c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4e4f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4e52:	e8 19 d6 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4e57:	48 85 c0             	test   %rax,%rax
    4e5a:	0f 84 eb 02 00 00    	je     514b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4e60:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4e64:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4e68:	83 fb 08             	cmp    $0x8,%ebx
    4e6b:	0f 83 3f 01 00 00    	jae    4fb0 <send_headers+0x360>
    4e71:	f6 c3 04             	test   $0x4,%bl
    4e74:	0f 85 7b 02 00 00    	jne    50f5 <send_headers+0x4a5>
    4e7a:	85 db                	test   %ebx,%ebx
    4e7c:	74 13                	je     4e91 <send_headers+0x241>
    4e7e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4e86:	88 10                	mov    %dl,(%rax)
    4e88:	f6 c3 02             	test   $0x2,%bl
    4e8b:	0f 85 96 02 00 00    	jne    5127 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4e91:	4d 89 e8             	mov    %r13,%r8
    4e94:	48 8d 0d 46 32 00 00 	lea    0x3246(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4e9b:	4c 89 e7             	mov    %r12,%rdi
    4e9e:	31 c0                	xor    %eax,%eax
    4ea0:	ba 00 04 00 00       	mov    $0x400,%edx
    4ea5:	be 01 00 00 00       	mov    $0x1,%esi
    4eaa:	e8 f1 d6 ff ff       	call   25a0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4eaf:	4c 89 e7             	mov    %r12,%rdi
    4eb2:	e8 b9 d4 ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    4eb7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4eba:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4ebd:	e8 ae d5 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4ec2:	48 85 c0             	test   %rax,%rax
    4ec5:	0f 84 80 02 00 00    	je     514b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4ecb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4ecf:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4ed3:	83 fb 08             	cmp    $0x8,%ebx
    4ed6:	0f 83 1c 01 00 00    	jae    4ff8 <send_headers+0x3a8>
    4edc:	f6 c3 04             	test   $0x4,%bl
    4edf:	0f 85 29 02 00 00    	jne    510e <send_headers+0x4be>
    4ee5:	85 db                	test   %ebx,%ebx
    4ee7:	74 13                	je     4efc <send_headers+0x2ac>
    4ee9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4ef1:	88 10                	mov    %dl,(%rax)
    4ef3:	f6 c3 02             	test   $0x2,%bl
    4ef6:	0f 85 3d 02 00 00    	jne    5139 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4efc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4f01:	bf 02 00 00 00       	mov    $0x2,%edi
    4f06:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4f0e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4f16:	e8 55 d5 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4f1b:	48 85 c0             	test   %rax,%rax
    4f1e:	0f 84 27 02 00 00    	je     514b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f24:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4f2c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4f30:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4f38:	66 89 10             	mov    %dx,(%rax)
}
    4f3b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4f43:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f4c:	0f 85 20 02 00 00    	jne    5172 <send_headers+0x522>
    4f52:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4f59:	5b                   	pop    %rbx
    4f5a:	5d                   	pop    %rbp
    4f5b:	41 5c                	pop    %r12
    4f5d:	41 5d                	pop    %r13
    4f5f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4f60:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4f64:	0f 85 a4 fe ff ff    	jne    4e0e <send_headers+0x1be>
    4f6a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4f6e:	0f 85 9a fe ff ff    	jne    4e0e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f74:	66 0f 6f 05 e4 3c 00 00 	movdqa 0x3ce4(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    4f7c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4f86:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f8e:	66 0f 6f 05 da 3c 00 00 	movdqa 0x3cda(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    4f96:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4f9e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4fa6:	e9 63 fe ff ff       	jmp    4e0e <send_headers+0x1be>
    4fab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4fb0:	89 da                	mov    %ebx,%edx
    4fb2:	48 89 c7             	mov    %rax,%rdi
    4fb5:	4c 89 e6             	mov    %r12,%rsi
    4fb8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4fbd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4fc2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4fc5:	c1 e9 03             	shr    $0x3,%ecx
    4fc8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4fcb:	e9 c1 fe ff ff       	jmp    4e91 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4fd0:	66 0f 6f 05 28 3c 00 00 	movdqa 0x3c28(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4fd8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fe0:	66 0f 6f 05 38 3c 00 00 	movdqa 0x3c38(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4fe8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ff0:	e9 cb fd ff ff       	jmp    4dc0 <send_headers+0x170>
    4ff5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ff8:	89 da                	mov    %ebx,%edx
    4ffa:	48 89 c7             	mov    %rax,%rdi
    4ffd:	4c 89 e6             	mov    %r12,%rsi
    5000:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    5005:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    500a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    500d:	c1 e9 03             	shr    $0x3,%ecx
    5010:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    5013:	e9 e4 fe ff ff       	jmp    4efc <send_headers+0x2ac>
    5018:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    5020:	48 8d 1d cf 30 00 00 	lea    0x30cf(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    5027:	e9 94 fd ff ff       	jmp    4dc0 <send_headers+0x170>
    502c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5030:	66 0f 6f 05 08 3c 00 00 	movdqa 0x3c08(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    5038:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5040:	66 0f 6f 05 08 3c 00 00 	movdqa 0x3c08(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5048:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5050:	e9 b0 fd ff ff       	jmp    4e05 <send_headers+0x1b5>
    5055:	0f 1f 00             	nopl   (%rax)
    5058:	66 0f 6f 05 e0 3b 00 00 	movdqa 0x3be0(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    5060:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5068:	66 0f 6f 05 e0 3b 00 00 	movdqa 0x3be0(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5070:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5078:	e9 71 fd ff ff       	jmp    4dee <send_headers+0x19e>
    507d:	0f 1f 00             	nopl   (%rax)
    5080:	66 0f 6f 05 78 3b 00 00 	movdqa 0x3b78(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    5088:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5090:	66 0f 6f 05 98 3b 00 00 	movdqa 0x3b98(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    5098:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    50a0:	e9 32 fd ff ff       	jmp    4dd7 <send_headers+0x187>
    50a5:	0f 1f 00             	nopl   (%rax)
    50a8:	66 0f 6f 05 90 3b 00 00 	movdqa 0x3b90(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    50b0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50b8:	66 0f 6f 05 d0 3b 00 00 	movdqa 0x3bd0(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    50c0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    50c8:	e9 6f fd ff ff       	jmp    4e3c <send_headers+0x1ec>
    50cd:	0f 1f 00             	nopl   (%rax)
    50d0:	66 0f 6f 05 68 3b 00 00 	movdqa 0x3b68(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    50d8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50e0:	66 0f 6f 05 98 3b 00 00 	movdqa 0x3b98(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    50e8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    50f0:	e9 30 fd ff ff       	jmp    4e25 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    50f5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    50fc:	89 db                	mov    %ebx,%ebx
    50fe:	89 10                	mov    %edx,(%rax)
    5100:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5105:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5109:	e9 83 fd ff ff       	jmp    4e91 <send_headers+0x241>
    510e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5115:	89 db                	mov    %ebx,%ebx
    5117:	89 10                	mov    %edx,(%rax)
    5119:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    511e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5122:	e9 d5 fd ff ff       	jmp    4efc <send_headers+0x2ac>
    5127:	89 db                	mov    %ebx,%ebx
    5129:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    512f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5134:	e9 58 fd ff ff       	jmp    4e91 <send_headers+0x241>
    5139:	89 db                	mov    %ebx,%ebx
    513b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    5141:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5146:	e9 b1 fd ff ff       	jmp    4efc <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    514b:	48 8b 0d ce 5e 00 00 	mov    0x5ece(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5152:	ba 28 00 00 00       	mov    $0x28,%edx
    5157:	be 01 00 00 00       	mov    $0x1,%esi
    515c:	48 8d 3d 5d 34 00 00 	lea    0x345d(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    5163:	e8 c8 d3 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5168:	bf 01 00 00 00       	mov    $0x1,%edi
    516d:	e8 9e d3 ff ff       	call   2510 <exit@plt>
}
    5172:	e8 09 d2 ff ff       	call   2380 <__stack_chk_fail@plt>
    5177:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005180 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5180:	f3 0f 1e fa          	endbr64
    5184:	41 55                	push   %r13
    5186:	49 89 d5             	mov    %rdx,%r13
    5189:	41 54                	push   %r12
    518b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    518e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5191:	55                   	push   %rbp
    5192:	53                   	push   %rbx
    5193:	48 89 f3             	mov    %rsi,%rbx
    5196:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    519a:	e8 d1 d2 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    519f:	48 85 c0             	test   %rax,%rax
    51a2:	74 6b                	je     520f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    51a4:	4c 89 e7             	mov    %r12,%rdi
    51a7:	48 89 c5             	mov    %rax,%rbp
    51aa:	31 f6                	xor    %esi,%esi
    51ac:	31 c0                	xor    %eax,%eax
    51ae:	e8 2d d3 ff ff       	call   24e0 <open@plt>
    51b3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    51b6:	85 c0                	test   %eax,%eax
    51b8:	0f 88 18 d4 ff ff    	js     25d6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    51be:	48 89 da             	mov    %rbx,%rdx
    51c1:	48 89 ee             	mov    %rbp,%rsi
    51c4:	89 c7                	mov    %eax,%edi
    51c6:	e8 25 d2 ff ff       	call   23f0 <read@plt>
    if (ret < file_size) {
    51cb:	48 98                	cltq
    51cd:	48 39 d8             	cmp    %rbx,%rax
    51d0:	7c 1e                	jl     51f0 <copy_file_contents+0x70>
    close(fd);
    51d2:	44 89 e7             	mov    %r12d,%edi
    51d5:	e8 f6 d1 ff ff       	call   23d0 <close@plt>
    iov->iov_base = buf;
    51da:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    51de:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    51e2:	48 83 c4 08          	add    $0x8,%rsp
    51e6:	5b                   	pop    %rbx
    51e7:	5d                   	pop    %rbp
    51e8:	41 5c                	pop    %r12
    51ea:	41 5d                	pop    %r13
    51ec:	c3                   	ret
    51ed:	0f 1f 00             	nopl   (%rax)
    51f0:	48 8b 0d 29 5e 00 00 	mov    0x5e29(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    51f7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    51fc:	be 01 00 00 00       	mov    $0x1,%esi
    5201:	48 8d 3d ef 2e 00 00 	lea    0x2eef(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    5208:	e8 23 d3 ff ff       	call   2530 <fwrite@plt>
    520d:	eb c3                	jmp    51d2 <copy_file_contents+0x52>
    520f:	48 8b 0d 0a 5e 00 00 	mov    0x5e0a(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5216:	ba 28 00 00 00       	mov    $0x28,%edx
    521b:	be 01 00 00 00       	mov    $0x1,%esi
    5220:	48 8d 3d 99 33 00 00 	lea    0x3399(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    5227:	e8 04 d3 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    522c:	bf 01 00 00 00       	mov    $0x1,%edi
    5231:	e8 da d2 ff ff       	call   2510 <exit@plt>
    5236:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005240 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    5240:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    5244:	8b 46 44             	mov    0x44(%rsi),%eax
    5247:	48 89 fa             	mov    %rdi,%rdx
    524a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    524d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5253:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5256:	48 8b 07             	mov    (%rdi),%rax
    5259:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    525c:	f6 c1 02             	test   $0x2,%cl
    525f:	74 00                	je     5261 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    5261:	89 f0                	mov    %esi,%eax
    5263:	44 29 c0             	sub    %r8d,%eax
    5266:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5269:	0f 82 73 d3 ff ff    	jb     25e2 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    526f:	c1 e9 0a             	shr    $0xa,%ecx
    5272:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5276:	8b 47 44             	mov    0x44(%rdi),%eax
    5279:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    527c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    527f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5282:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    5285:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5289:	d3 e0                	shl    %cl,%eax
    528b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    528e:	48 c1 e0 06          	shl    $0x6,%rax
    5292:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    5296:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    529c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    529f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    52a3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    52a9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    52b1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    52b5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    52b8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    52bf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    52c7:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    52cb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    52cf:	e8 bc d0 ff ff       	call   2390 <io_uring_submit@plt>
}
    52d4:	31 c0                	xor    %eax,%eax
    52d6:	48 83 c4 08          	add    $0x8,%rsp
    52da:	c3                   	ret
    52db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000052e0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    52e0:	f3 0f 1e fa          	endbr64
    52e4:	41 55                	push   %r13
    52e6:	41 89 fd             	mov    %edi,%r13d
    52e9:	41 54                	push   %r12
    52eb:	55                   	push   %rbp
    52ec:	53                   	push   %rbx
    52ed:	48 89 f3             	mov    %rsi,%rbx
    52f0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    52f4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    52f7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    52fd:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    5300:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5303:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5305:	f6 c1 02             	test   $0x2,%cl
    5308:	74 00                	je     530a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    530a:	89 c2                	mov    %eax,%edx
    530c:	29 f2                	sub    %esi,%edx
    530e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5311:	0f 82 db d2 ff ff    	jb     25f2 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5317:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    531a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    531d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5320:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    5325:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5328:	23 6b 58             	and    0x58(%rbx),%ebp
    532b:	d3 e5                	shl    %cl,%ebp
    532d:	48 c1 e5 06          	shl    $0x6,%rbp
    5331:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5335:	e8 36 d1 ff ff       	call   2470 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    533a:	be 01 00 00 00       	mov    $0x1,%esi
    533f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5344:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    5347:	e8 b4 d0 ff ff       	call   2400 <calloc@plt>
    req->client_socket = client_socket;
    534c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5351:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5355:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5358:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    535d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    5362:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    536b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    5373:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    5377:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    537b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    5382:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    538a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    538e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    5396:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    539e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    53a2:	e8 e9 cf ff ff       	call   2390 <io_uring_submit@plt>
}
    53a7:	48 83 c4 08          	add    $0x8,%rsp
    53ab:	31 c0                	xor    %eax,%eax
    53ad:	5b                   	pop    %rbx
    53ae:	5d                   	pop    %rbp
    53af:	41 5c                	pop    %r12
    53b1:	41 5d                	pop    %r13
    53b3:	c3                   	ret
    53b4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    53bf:	90                   	nop

00000000000053c0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    53c0:	f3 0f 1e fa          	endbr64
    53c4:	41 56                	push   %r14
    53c6:	41 89 f6             	mov    %esi,%r14d
    53c9:	41 55                	push   %r13
    53cb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    53ce:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    53d3:	41 54                	push   %r12
    53d5:	55                   	push   %rbp
    53d6:	48 89 d5             	mov    %rdx,%rbp
    53d9:	53                   	push   %rbx
    void *buf = malloc(size);
    53da:	e8 91 d0 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    53df:	48 85 c0             	test   %rax,%rax
    53e2:	0f 84 dd 00 00 00    	je     54c5 <_send_static_string_content+0x105>
    53e8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    53eb:	4c 89 ef             	mov    %r13,%rdi
    53ee:	e8 7d cf ff ff       	call   2370 <strlen@plt>
    req->iovec_count = 1;
    53f3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    53fa:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    53fe:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    5401:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    5404:	e8 67 d0 ff ff       	call   2470 <malloc@plt>
    5409:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    540c:	48 85 c0             	test   %rax,%rax
    540f:	0f 84 b0 00 00 00    	je     54c5 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    5415:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5419:	4c 89 e2             	mov    %r12,%rdx
    541c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    541f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5423:	e8 18 d0 ff ff       	call   2440 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5428:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    542b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5431:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5434:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5438:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    543a:	f6 c1 02             	test   $0x2,%cl
    543d:	0f 85 7d 00 00 00    	jne    54c0 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    5443:	89 d0                	mov    %edx,%eax
    5445:	29 f0                	sub    %esi,%eax
    5447:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    544a:	0f 82 ac d1 ff ff    	jb     25fc <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5450:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5453:	8b 45 44             	mov    0x44(%rbp),%eax
    5456:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    5459:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    545c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    545f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    5462:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    5468:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    546c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    546e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    5471:	48 89 ef             	mov    %rbp,%rdi
    5474:	48 c1 e0 06          	shl    $0x6,%rax
    5478:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    547c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    547f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    5483:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5489:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5491:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5495:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5498:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    549f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    54a7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    54ab:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    54af:	5b                   	pop    %rbx
    54b0:	5d                   	pop    %rbp
    54b1:	41 5c                	pop    %r12
    54b3:	41 5d                	pop    %r13
    54b5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    54b7:	e9 d4 ce ff ff       	jmp    2390 <io_uring_submit@plt>
    54bc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    54c0:	e9 7e ff ff ff       	jmp    5443 <_send_static_string_content+0x83>
    54c5:	48 8b 0d 54 5b 00 00 	mov    0x5b54(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    54cc:	ba 28 00 00 00       	mov    $0x28,%edx
    54d1:	be 01 00 00 00       	mov    $0x1,%esi
    54d6:	48 8d 3d e3 30 00 00 	lea    0x30e3(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    54dd:	e8 4e d0 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    54e2:	bf 01 00 00 00       	mov    $0x1,%edi
    54e7:	e8 24 d0 ff ff       	call   2510 <exit@plt>
    54ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000054f0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    54f0:	f3 0f 1e fa          	endbr64
    54f4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    54f7:	89 fe                	mov    %edi,%esi
    54f9:	48 8b 3d 18 5b 00 00 	mov    0x5b18(%rip),%rdi        # b018 <unimplemented_content>
    5500:	e9 bb fe ff ff       	jmp    53c0 <_send_static_string_content>
    5505:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005510 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5510:	f3 0f 1e fa          	endbr64
    5514:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5517:	89 fe                	mov    %edi,%esi
    5519:	48 8b 3d f0 5a 00 00 	mov    0x5af0(%rip),%rdi        # b010 <http_404_content>
    5520:	e9 9b fe ff ff       	jmp    53c0 <_send_static_string_content>
    5525:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005530 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    5530:	f3 0f 1e fa          	endbr64
    5534:	41 56                	push   %r14
    5536:	41 55                	push   %r13
    5538:	49 89 d5             	mov    %rdx,%r13
    553b:	41 54                	push   %r12
    553d:	41 89 f4             	mov    %esi,%r12d
    5540:	55                   	push   %rbp
    5541:	48 89 fd             	mov    %rdi,%rbp
    5544:	53                   	push   %rbx
    5545:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    554c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5555:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    555d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    555f:	e8 0c ce ff ff       	call   2370 <strlen@plt>
    5564:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    5569:	48 89 c3             	mov    %rax,%rbx
    556c:	0f 84 b6 00 00 00    	je     5628 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5572:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5577:	48 89 ee             	mov    %rbp,%rsi
    557a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    557e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5583:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    558b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5593:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    559e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55a6:	e8 75 ce ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    55ab:	48 89 e6             	mov    %rsp,%rsi
    55ae:	4c 89 f7             	mov    %r14,%rdi
    55b1:	e8 7a ce ff ff       	call   2430 <stat@plt>
    55b6:	83 f8 ff             	cmp    $0xffffffff,%eax
    55b9:	0f 84 d3 00 00 00    	je     5692 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    55bf:	8b 44 24 18          	mov    0x18(%rsp),%eax
    55c3:	25 00 f0 00 00       	and    $0xf000,%eax
    55c8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    55cd:	0f 84 f5 00 00 00    	je     56c8 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    55d3:	48 8b 3d 36 5a 00 00 	mov    0x5a36(%rip),%rdi        # b010 <http_404_content>
    55da:	4c 89 ea             	mov    %r13,%rdx
    55dd:	44 89 e6             	mov    %r12d,%esi
    55e0:	e8 db fd ff ff       	call   53c0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    55e5:	4c 89 f2             	mov    %r14,%rdx
    55e8:	bf 01 00 00 00       	mov    $0x1,%edi
    55ed:	31 c0                	xor    %eax,%eax
    55ef:	48 8d 35 51 2b 00 00 	lea    0x2b51(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    55f6:	e8 b5 ce ff ff       	call   24b0 <__printf_chk@plt>
}
    55fb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5603:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    560c:	0f 85 20 01 00 00    	jne    5732 <handle_get_method+0x202>
    5612:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5619:	5b                   	pop    %rbx
    561a:	5d                   	pop    %rbp
    561b:	41 5c                	pop    %r12
    561d:	41 5d                	pop    %r13
    561f:	41 5e                	pop    %r14
    5621:	c3                   	ret
    5622:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5628:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    562d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5635:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    563a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    563d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5645:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5648:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5650:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    565b:	e8 c0 cd ff ff       	call   2420 <__memcpy_chk@plt>
    5660:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5665:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    566a:	48 8d 35 a1 2a 00 00 	lea    0x2aa1(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    5671:	48 29 d9             	sub    %rbx,%rcx
    5674:	ba 0b 00 00 00       	mov    $0xb,%edx
    5679:	e8 a2 cd ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    567e:	48 89 e6             	mov    %rsp,%rsi
    5681:	4c 89 f7             	mov    %r14,%rdi
    5684:	e8 a7 cd ff ff       	call   2430 <stat@plt>
    5689:	83 f8 ff             	cmp    $0xffffffff,%eax
    568c:	0f 85 2d ff ff ff    	jne    55bf <handle_get_method+0x8f>
    5692:	4c 89 f2             	mov    %r14,%rdx
    5695:	48 89 e9             	mov    %rbp,%rcx
    5698:	48 8d 35 7e 2a 00 00 	lea    0x2a7e(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    569f:	31 c0                	xor    %eax,%eax
    56a1:	bf 01 00 00 00       	mov    $0x1,%edi
    56a6:	e8 05 ce ff ff       	call   24b0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    56ab:	48 8b 3d 5e 59 00 00 	mov    0x595e(%rip),%rdi        # b010 <http_404_content>
    56b2:	4c 89 ea             	mov    %r13,%rdx
    56b5:	44 89 e6             	mov    %r12d,%esi
    56b8:	e8 03 fd ff ff       	call   53c0 <_send_static_string_content>
}
    56bd:	e9 39 ff ff ff       	jmp    55fb <handle_get_method+0xcb>
    56c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    56c8:	bf 70 00 00 00       	mov    $0x70,%edi
    56cd:	e8 9e cd ff ff       	call   2470 <malloc@plt>
    56d2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    56d5:	48 85 c0             	test   %rax,%rax
    56d8:	74 5d                	je     5737 <handle_get_method+0x207>
            req->client_socket = client_socket;
    56da:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    56de:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    56e3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    56e7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    56ea:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    56f1:	e8 5a f5 ff ff       	call   4c50 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    56f6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    56fb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    56ff:	4c 89 f7             	mov    %r14,%rdi
    5702:	e8 79 fa ff ff       	call   5180 <copy_file_contents>
    5707:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    570c:	4c 89 f2             	mov    %r14,%rdx
    570f:	31 c0                	xor    %eax,%eax
    5711:	48 8d 35 1d 2a 00 00 	lea    0x2a1d(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    5718:	bf 01 00 00 00       	mov    $0x1,%edi
    571d:	e8 8e cd ff ff       	call   24b0 <__printf_chk@plt>
            add_write_request(req, ring);
    5722:	4c 89 ee             	mov    %r13,%rsi
    5725:	48 89 df             	mov    %rbx,%rdi
    5728:	e8 13 fb ff ff       	call   5240 <add_write_request>
    572d:	e9 c9 fe ff ff       	jmp    55fb <handle_get_method+0xcb>
}
    5732:	e8 49 cc ff ff       	call   2380 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5737:	48 8b 0d e2 58 00 00 	mov    0x58e2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    573e:	ba 28 00 00 00       	mov    $0x28,%edx
    5743:	be 01 00 00 00       	mov    $0x1,%esi
    5748:	48 8d 3d 71 2e 00 00 	lea    0x2e71(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    574f:	e8 dc cd ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5754:	bf 01 00 00 00       	mov    $0x1,%edi
    5759:	e8 b2 cd ff ff       	call   2510 <exit@plt>
    575e:	66 90                	xchg   %ax,%ax

0000000000005760 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5760:	f3 0f 1e fa          	endbr64
    5764:	41 57                	push   %r15
    5766:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5768:	4c 8d 35 3d 29 00 00 	lea    0x293d(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    576f:	41 55                	push   %r13
    5771:	49 89 d5             	mov    %rdx,%r13
    5774:	41 54                	push   %r12
    5776:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5779:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    577c:	55                   	push   %rbp
    577d:	53                   	push   %rbx
    577e:	48 83 ec 18          	sub    $0x18,%rsp
    5782:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    578b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5790:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5792:	49 89 e7             	mov    %rsp,%r15
    5795:	4c 89 fa             	mov    %r15,%rdx
    5798:	e8 43 cc ff ff       	call   23e0 <strtok_r@plt>
    for (; *str; ++str)
    579d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    57a1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    57a4:	84 db                	test   %bl,%bl
    57a6:	74 1d                	je     57c5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    57a8:	e8 e3 cd ff ff       	call   2590 <__ctype_tolower_loc@plt>
    57ad:	48 89 ea             	mov    %rbp,%rdx
    57b0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    57b3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    57b7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    57ba:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    57bd:	48 0f be 1a          	movsbq (%rdx),%rbx
    57c1:	84 db                	test   %bl,%bl
    57c3:	75 eb                	jne    57b0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    57c5:	4c 89 fa             	mov    %r15,%rdx
    57c8:	4c 89 f6             	mov    %r14,%rsi
    57cb:	31 ff                	xor    %edi,%edi
    57cd:	e8 0e cc ff ff       	call   23e0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    57d2:	48 8d 35 81 29 00 00 	lea    0x2981(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    57d9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    57dc:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    57df:	e8 2c cc ff ff       	call   2410 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    57e4:	4c 89 ea             	mov    %r13,%rdx
    57e7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    57ea:	85 c0                	test   %eax,%eax
    57ec:	75 2a                	jne    5818 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    57ee:	48 89 df             	mov    %rbx,%rdi
    57f1:	e8 3a fd ff ff       	call   5530 <handle_get_method>
}
    57f6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    57fb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5804:	75 20                	jne    5826 <handle_http_method+0xc6>
    5806:	48 83 c4 18          	add    $0x18,%rsp
    580a:	5b                   	pop    %rbx
    580b:	5d                   	pop    %rbp
    580c:	41 5c                	pop    %r12
    580e:	41 5d                	pop    %r13
    5810:	41 5e                	pop    %r14
    5812:	41 5f                	pop    %r15
    5814:	c3                   	ret
    5815:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5818:	48 8b 3d f9 57 00 00 	mov    0x57f9(%rip),%rdi        # b018 <unimplemented_content>
    581f:	e8 9c fb ff ff       	call   53c0 <_send_static_string_content>
}
    5824:	eb d0                	jmp    57f6 <handle_http_method+0x96>
    5826:	e8 55 cb ff ff       	call   2380 <__stack_chk_fail@plt>
    582b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005830 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5830:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5834:	85 d2                	test   %edx,%edx
    5836:	7e 38                	jle    5870 <get_line+0x40>
    5838:	48 63 d2             	movslq %edx,%rdx
    583b:	48 83 c7 01          	add    $0x1,%rdi
    583f:	48 01 f2             	add    %rsi,%rdx
    5842:	eb 11                	jmp    5855 <get_line+0x25>
    5844:	0f 1f 40 00          	nopl   0x0(%rax)
    5848:	48 83 c6 01          	add    $0x1,%rsi
    584c:	48 83 c7 01          	add    $0x1,%rdi
    5850:	48 39 d6             	cmp    %rdx,%rsi
    5853:	74 1b                	je     5870 <get_line+0x40>
        dest[i] = src[i];
    5855:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5859:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    585b:	3c 0d                	cmp    $0xd,%al
    585d:	75 e9                	jne    5848 <get_line+0x18>
    585f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5862:	75 e4                	jne    5848 <get_line+0x18>
            dest[i] = '\0';
    5864:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5867:	31 c0                	xor    %eax,%eax
    5869:	c3                   	ret
    586a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5870:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5875:	c3                   	ret
    5876:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005880 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5880:	f3 0f 1e fa          	endbr64
    5884:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    588b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    588f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5898:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    58a0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    58a2:	49 89 e2             	mov    %rsp,%r10
    58a5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    58ad:	4c 89 d0             	mov    %r10,%rax
    58b0:	eb 13                	jmp    58c5 <handle_client_request+0x45>
    58b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    58b8:	48 83 c0 01          	add    $0x1,%rax
    58bc:	48 83 c1 01          	add    $0x1,%rcx
    58c0:	4c 39 c8             	cmp    %r9,%rax
    58c3:	74 4b                	je     5910 <handle_client_request+0x90>
        dest[i] = src[i];
    58c5:	44 0f b6 01          	movzbl (%rcx),%r8d
    58c9:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    58cc:	41 80 f8 0d          	cmp    $0xd,%r8b
    58d0:	75 e6                	jne    58b8 <handle_client_request+0x38>
    58d2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    58d6:	75 e0                	jne    58b8 <handle_client_request+0x38>
            dest[i] = '\0';
    58d8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    58db:	8b 47 08             	mov    0x8(%rdi),%eax
    58de:	48 89 f2             	mov    %rsi,%rdx
    58e1:	4c 89 d7             	mov    %r10,%rdi
    58e4:	89 c6                	mov    %eax,%esi
    58e6:	e8 75 fe ff ff       	call   5760 <handle_http_method>
}
    58eb:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    58f3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    58fc:	75 39                	jne    5937 <handle_client_request+0xb7>
    58fe:	31 c0                	xor    %eax,%eax
    5900:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5907:	c3                   	ret
    5908:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5910:	48 8b 0d 09 57 00 00 	mov    0x5709(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5917:	ba 12 00 00 00       	mov    $0x12,%edx
    591c:	be 01 00 00 00       	mov    $0x1,%esi
    5921:	48 8d 3d 36 28 00 00 	lea    0x2836(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5928:	e8 03 cc ff ff       	call   2530 <fwrite@plt>
        exit(1);
    592d:	bf 01 00 00 00       	mov    $0x1,%edi
    5932:	e8 d9 cb ff ff       	call   2510 <exit@plt>
}
    5937:	e8 44 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    593c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005940 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5940:	f3 0f 1e fa          	endbr64
    5944:	55                   	push   %rbp
    5945:	53                   	push   %rbx
    5946:	48 89 cb             	mov    %rcx,%rbx
    5949:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    594d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5950:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5953:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5959:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    595c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    595f:	f6 c1 02             	test   $0x2,%cl
    5962:	74 00                	je     5964 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5964:	41 89 c0             	mov    %eax,%r8d
    5967:	45 29 c8             	sub    %r9d,%r8d
    596a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    596e:	0f 82 98 cc ff ff    	jb     260c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5974:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5977:	8b 6b 44             	mov    0x44(%rbx),%ebp
    597a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    597d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5980:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5983:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5987:	d3 e5                	shl    %cl,%ebp
    5989:	48 c1 e5 06          	shl    $0x6,%rbp
    598d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5991:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5994:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5999:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    59a0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    59a4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    59a8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    59b0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    59b8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    59bc:	e8 af ca ff ff       	call   2470 <malloc@plt>
  io_uring_submit(ring);
    59c1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    59c4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    59ca:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    59ce:	48 83 c4 08          	add    $0x8,%rsp
    59d2:	5b                   	pop    %rbx
    59d3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    59d4:	e9 b7 c9 ff ff       	jmp    2390 <io_uring_submit@plt>
    59d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000059e0 <io_thread>:
void* io_thread(void *arg) {
    59e0:	f3 0f 1e fa          	endbr64
    59e4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    59e6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    59e8:	41 56                	push   %r14
    59ea:	41 55                	push   %r13
    59ec:	41 54                	push   %r12
    59ee:	55                   	push   %rbp
    59ef:	48 89 fd             	mov    %rdi,%rbp
    59f2:	53                   	push   %rbx
    59f3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    59fa:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5a03:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    5a0b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a0f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5a14:	bf 00 01 00 00       	mov    $0x100,%edi
    5a19:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    5a1c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5a20:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5a25:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5a2a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    5a2f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5a34:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    5a3c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5a41:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5a49:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5a4e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5a56:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5a5b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5a63:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5a68:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5a70:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5a75:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    5a7d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5a85:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5a8d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5a95:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5a9d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5aa5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5aad:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5ab5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5abd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5ac5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5acd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5ad4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5adc:	e8 6f c9 ff ff       	call   2450 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5ae1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5ae5:	31 f6                	xor    %esi,%esi
    5ae7:	e8 64 ca ff ff       	call   2550 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5aec:	31 d2                	xor    %edx,%edx
    5aee:	be 01 00 00 00       	mov    $0x1,%esi
    5af3:	bf 02 00 00 00       	mov    $0x2,%edi
    5af8:	e8 b3 ca ff ff       	call   25b0 <socket@plt>
  if (sock == -1)
    5afd:	83 f8 ff             	cmp    $0xffffffff,%eax
    5b00:	0f 84 48 cb ff ff    	je     264e <io_thread.cold+0x38>
  if (setsockopt(sock,
    5b06:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5b0b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5b11:	89 c7                	mov    %eax,%edi
    5b13:	41 89 c4             	mov    %eax,%r12d
    5b16:	ba 02 00 00 00       	mov    $0x2,%edx
    5b1b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5b20:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5b28:	e8 13 c8 ff ff       	call   2340 <setsockopt@plt>
    5b2d:	85 c0                	test   %eax,%eax
    5b2f:	0f 88 ed ca ff ff    	js     2622 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5b35:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    5b3a:	ba 10 00 00 00       	mov    $0x10,%edx
    5b3f:	44 89 e7             	mov    %r12d,%edi
    5b42:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5b4b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5b53:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    5b5b:	e8 60 c9 ff ff       	call   24c0 <bind@plt>
    5b60:	85 c0                	test   %eax,%eax
    5b62:	0f 88 f2 ca ff ff    	js     265a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5b68:	be 0a 00 00 00       	mov    $0xa,%esi
    5b6d:	44 89 e7             	mov    %r12d,%edi
    5b70:	e8 0b c9 ff ff       	call   2480 <listen@plt>
    5b75:	85 c0                	test   %eax,%eax
    5b77:	0f 88 b1 ca ff ff    	js     262e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5b7d:	ba db 18 00 00       	mov    $0x18db,%edx
    5b82:	48 8d 35 1a 26 00 00 	lea    0x261a(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5b89:	bf 01 00 00 00       	mov    $0x1,%edi
    5b8e:	31 c0                	xor    %eax,%eax
    5b90:	e8 1b c9 ff ff       	call   24b0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5b95:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5b9a:	48 89 d9             	mov    %rbx,%rcx
    5b9d:	44 89 e7             	mov    %r12d,%edi
    5ba0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5ba5:	48 89 c6             	mov    %rax,%rsi
    5ba8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5bad:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5bb2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5bba:	e8 81 fd ff ff       	call   5940 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5bbf:	bf 01 00 00 00       	mov    $0x1,%edi
    5bc4:	be 10 00 00 00       	mov    $0x10,%esi
    5bc9:	e8 32 c8 ff ff       	call   2400 <calloc@plt>
    void *buf = malloc(size);
    5bce:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5bd3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5bd6:	e8 95 c8 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5bdb:	48 85 c0             	test   %rax,%rax
    5bde:	0f 84 ae 04 00 00    	je     6092 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5be4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5be8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5bef:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5bf6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5bfe:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5c01:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5c06:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5c08:	f6 c1 02             	test   $0x2,%cl
    5c0b:	0f 85 0f 04 00 00    	jne    6020 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5c11:	89 d0                	mov    %edx,%eax
    5c13:	29 f0                	sub    %esi,%eax
    5c15:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5c1c:	0f 82 22 ca ff ff    	jb     2644 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5c22:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5c25:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5c29:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5c2d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c30:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5c37:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c3a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5c41:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c48:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5c4a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5c4d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5c52:	48 c1 e0 06          	shl    $0x6,%rax
    5c56:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5c5e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5c64:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5c67:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5c6f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5c73:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5c7b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5c83:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5c87:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5c8b:	e8 00 c7 ff ff       	call   2390 <io_uring_submit@plt>
  while (data->running == 1) {
    5c90:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5c94:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5c99:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5ca1:	0f 85 d7 01 00 00    	jne    5e7e <io_thread+0x49e>
    5ca7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5cac:	4d 89 ce             	mov    %r9,%r14
    5caf:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5cb4:	0f 1f 40 00          	nopl   0x0(%rax)
    5cb8:	48 8d 3d fa 24 00 00 	lea    0x24fa(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5cbf:	e8 6c c6 ff ff       	call   2330 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5cc4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5ccb:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5cd2:	c1 e9 0b             	shr    $0xb,%ecx
    5cd5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5cd8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5ce0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5ce2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5cea:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5cec:	39 d0                	cmp    %edx,%eax
    5cee:	74 36                	je     5d26 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5cf0:	89 f8                	mov    %edi,%eax
    5cf2:	21 d0                	and    %edx,%eax
    5cf4:	d3 e0                	shl    %cl,%eax
    5cf6:	48 c1 e0 04          	shl    $0x4,%rax
    5cfa:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5d02:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5d0a:	0f 85 a8 01 00 00    	jne    5eb8 <io_thread+0x4d8>
    5d10:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5d14:	0f 85 0e 03 00 00    	jne    6028 <io_thread+0x648>
			if (cqe->res < 0)
    5d1a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5d1d:	83 c2 01             	add    $0x1,%edx
    5d20:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5d22:	85 c0                	test   %eax,%eax
    5d24:	79 b2                	jns    5cd8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5d26:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5d2f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5d30:	45 31 c0             	xor    %r8d,%r8d
    5d33:	31 d2                	xor    %edx,%edx
    5d35:	b9 01 00 00 00       	mov    $0x1,%ecx
    5d3a:	4c 89 f6             	mov    %r14,%rsi
    5d3d:	48 89 df             	mov    %rbx,%rdi
    5d40:	e8 5b c7 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5d45:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5d48:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5d4d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5d51:	0f 84 e1 02 00 00    	je     6038 <io_thread+0x658>
    5d57:	48 8d 3d 81 24 00 00 	lea    0x2481(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5d5e:	e8 cd c5 ff ff       	call   2330 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5d63:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5d68:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5d6b:	45 85 ff             	test   %r15d,%r15d
    5d6e:	0f 88 a2 c8 ff ff    	js     2616 <io_thread.cold>
      if (cqe->res < 0) {
    5d74:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5d77:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    5d7b:	85 c0                	test   %eax,%eax
    5d7d:	0f 88 d5 02 00 00    	js     6058 <io_thread+0x678>
      switch (req->event_type) {
    5d83:	41 83 f8 01          	cmp    $0x1,%r8d
    5d87:	0f 84 7b 01 00 00    	je     5f08 <io_thread+0x528>
    5d8d:	41 83 f8 02          	cmp    $0x2,%r8d
    5d91:	0f 84 a1 01 00 00    	je     5f38 <io_thread+0x558>
    5d97:	45 85 c0             	test   %r8d,%r8d
    5d9a:	0f 85 50 01 00 00    	jne    5ef0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5da0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5da5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5daa:	48 89 d9             	mov    %rbx,%rcx
    5dad:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5db1:	e8 8a fb ff ff       	call   5940 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5db6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5dbb:	48 89 de             	mov    %rbx,%rsi
    5dbe:	8b 78 08             	mov    0x8(%rax),%edi
    5dc1:	e8 1a f5 ff ff       	call   52e0 <add_read_request>
              free(req);
    5dc6:	4c 89 e7             	mov    %r12,%rdi
    5dc9:	e8 32 c5 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5dce:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5dd3:	48 85 c0             	test   %rax,%rax
    5dd6:	0f 85 14 01 00 00    	jne    5ef0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    5ddc:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5de3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5dea:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5ded:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5df2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5df4:	f6 c1 02             	test   $0x2,%cl
    5df7:	74 00                	je     5df9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5df9:	89 d0                	mov    %edx,%eax
    5dfb:	29 f0                	sub    %esi,%eax
    5dfd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5e04:	0f 82 30 c8 ff ff    	jb     263a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5e0a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5e0d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5e12:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5e16:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e19:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5e20:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e23:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5e2a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e31:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5e33:	8b 55 60             	mov    0x60(%rbp),%edx
    5e36:	48 c1 e0 06          	shl    $0x6,%rax
    5e3a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5e42:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5e48:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5e4b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5e53:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5e57:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5e5f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5e67:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5e6b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5e6f:	e8 1c c5 ff ff       	call   2390 <io_uring_submit@plt>
  while (data->running == 1) {
    5e74:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5e78:	0f 84 3a fe ff ff    	je     5cb8 <io_thread+0x2d8>
    5e7e:	48 8d 3d 93 23 00 00 	lea    0x2393(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5e85:	e8 a6 c4 ff ff       	call   2330 <puts@plt>
}
    5e8a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5e92:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5e9b:	0f 85 18 02 00 00    	jne    60b9 <io_thread+0x6d9>
    5ea1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5ea8:	31 c0                	xor    %eax,%eax
    5eaa:	5b                   	pop    %rbx
    5eab:	5d                   	pop    %rbp
    5eac:	41 5c                	pop    %r12
    5eae:	41 5d                	pop    %r13
    5eb0:	41 5e                	pop    %r14
    5eb2:	41 5f                	pop    %r15
    5eb4:	c3                   	ret
    5eb5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5eb8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5ebd:	48 85 c0             	test   %rax,%rax
    5ec0:	0f 84 6a fe ff ff    	je     5d30 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5ec6:	48 83 38 01          	cmpq   $0x1,(%rax)
    5eca:	0f 84 68 01 00 00    	je     6038 <io_thread+0x658>
    5ed0:	48 8d 3d 08 23 00 00 	lea    0x2308(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5ed7:	e8 54 c4 ff ff       	call   2330 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5edc:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5ee1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5ee4:	e9 8b fe ff ff       	jmp    5d74 <io_thread+0x394>
    5ee9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5ef0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5ef8:	8b 02                	mov    (%rdx),%eax
    5efa:	83 c0 01             	add    $0x1,%eax
    5efd:	89 02                	mov    %eax,(%rdx)
}
    5eff:	e9 d8 fe ff ff       	jmp    5ddc <io_thread+0x3fc>
    5f04:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5f08:	85 c0                	test   %eax,%eax
    5f0a:	75 74                	jne    5f80 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5f0c:	48 8b 0d 0d 51 00 00 	mov    0x510d(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5f13:	ba 0f 00 00 00       	mov    $0xf,%edx
    5f18:	be 01 00 00 00       	mov    $0x1,%esi
    5f1d:	48 8d 3d e4 22 00 00 	lea    0x22e4(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5f24:	e8 07 c6 ff ff       	call   2530 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5f29:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f2e:	e9 a0 fe ff ff       	jmp    5dd3 <io_thread+0x3f3>
    5f33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5f38:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5f3d:	45 31 ff             	xor    %r15d,%r15d
    5f40:	85 c0                	test   %eax,%eax
    5f42:	7e 20                	jle    5f64 <io_thread+0x584>
    5f44:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5f48:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5f4b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5f4f:	48 c1 e0 04          	shl    $0x4,%rax
    5f53:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5f58:	e8 a3 c3 ff ff       	call   2300 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5f5d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5f62:	7f e4                	jg     5f48 <io_thread+0x568>
              close(req->client_socket);
    5f64:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5f69:	e8 62 c4 ff ff       	call   23d0 <close@plt>
              free(req);
    5f6e:	4c 89 e7             	mov    %r12,%rdi
    5f71:	e8 8a c3 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5f76:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5f7b:	e9 53 fe ff ff       	jmp    5dd3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5f80:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5f85:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5f8a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5f92:	eb 11                	jmp    5fa5 <io_thread+0x5c5>
    5f94:	0f 1f 40 00          	nopl   0x0(%rax)
    5f98:	48 83 c0 01          	add    $0x1,%rax
    5f9c:	48 83 c2 01          	add    $0x1,%rdx
    5fa0:	48 39 c6             	cmp    %rax,%rsi
    5fa3:	74 4b                	je     5ff0 <io_thread+0x610>
        dest[i] = src[i];
    5fa5:	0f b6 0a             	movzbl (%rdx),%ecx
    5fa8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5faa:	80 f9 0d             	cmp    $0xd,%cl
    5fad:	75 e9                	jne    5f98 <io_thread+0x5b8>
    5faf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5fb3:	75 e3                	jne    5f98 <io_thread+0x5b8>
            dest[i] = '\0';
    5fb5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5fb8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5fbd:	48 89 da             	mov    %rbx,%rdx
    5fc0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5fc5:	e8 96 f7 ff ff       	call   5760 <handle_http_method>
              free(req->iov[0].iov_base);
    5fca:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5fcf:	e8 2c c3 ff ff       	call   2300 <free@plt>
              free(req);
    5fd4:	4c 89 e7             	mov    %r12,%rdi
    5fd7:	e8 24 c3 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5fdc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5fe1:	e9 ed fd ff ff       	jmp    5dd3 <io_thread+0x3f3>
    5fe6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5ff0:	48 8b 0d 29 50 00 00 	mov    0x5029(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5ff7:	ba 12 00 00 00       	mov    $0x12,%edx
    5ffc:	be 01 00 00 00       	mov    $0x1,%esi
    6001:	48 8d 3d 56 21 00 00 	lea    0x2156(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6008:	e8 23 c5 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    600d:	bf 01 00 00 00       	mov    $0x1,%edi
    6012:	e8 f9 c4 ff ff       	call   2510 <exit@plt>
    6017:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    6020:	e9 ec fb ff ff       	jmp    5c11 <io_thread+0x231>
    6025:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    6028:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    602d:	e9 94 fe ff ff       	jmp    5ec6 <io_thread+0x4e6>
    6032:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6038:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6040:	48 8d 3d 84 21 00 00 	lea    0x2184(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    6047:	8b 02                	mov    (%rdx),%eax
    6049:	83 c0 01             	add    $0x1,%eax
    604c:	89 02                	mov    %eax,(%rdx)
    604e:	e8 dd c2 ff ff       	call   2330 <puts@plt>
    6053:	e9 26 fe ff ff       	jmp    5e7e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    6058:	f7 d8                	neg    %eax
    605a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    605f:	89 c7                	mov    %eax,%edi
    6061:	e8 0a c5 ff ff       	call   2570 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6066:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    606b:	be 01 00 00 00       	mov    $0x1,%esi
    6070:	48 8b 3d a9 4f 00 00 	mov    0x4fa9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    6077:	48 89 c1             	mov    %rax,%rcx
    607a:	48 8d 15 6f 25 00 00 	lea    0x256f(%rip),%rdx        # 85f0 <_IO_stdin_used+0x5f0>
    6081:	31 c0                	xor    %eax,%eax
    6083:	e8 b8 c4 ff ff       	call   2540 <__fprintf_chk@plt>
          exit(1);
    6088:	bf 01 00 00 00       	mov    $0x1,%edi
    608d:	e8 7e c4 ff ff       	call   2510 <exit@plt>
    6092:	48 8b 0d 87 4f 00 00 	mov    0x4f87(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6099:	ba 28 00 00 00       	mov    $0x28,%edx
    609e:	be 01 00 00 00       	mov    $0x1,%esi
    60a3:	48 8d 3d 16 25 00 00 	lea    0x2516(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    60aa:	e8 81 c4 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    60af:	bf 01 00 00 00       	mov    $0x1,%edi
    60b4:	e8 57 c4 ff ff       	call   2510 <exit@plt>
}
    60b9:	e8 c2 c2 ff ff       	call   2380 <__stack_chk_fail@plt>
    60be:	66 90                	xchg   %ax,%ax

00000000000060c0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    60c0:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    60c4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    60cb:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    60d1:	85 c9                	test   %ecx,%ecx
    60d3:	0f 8e ea 00 00 00    	jle    61c3 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    60d9:	41 56                	push   %r14
    60db:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    60dd:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    60e0:	41 54                	push   %r12
    60e2:	49 89 fc             	mov    %rdi,%r12
    60e5:	55                   	push   %rbp
    60e6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    60e7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    60eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60f0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    60f4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    60fc:	31 db                	xor    %ebx,%ebx
    60fe:	8b 10                	mov    (%rax),%edx
    6100:	85 d2                	test   %edx,%edx
    6102:	7e 26                	jle    612a <barriered_work_ingest+0x6a>
    6104:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    6108:	48 89 dd             	mov    %rbx,%rbp
    610b:	48 c1 e5 08          	shl    $0x8,%rbp
    610f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    6113:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    611a:	74 24                	je     6140 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    611c:	48 83 c3 01          	add    $0x1,%rbx
    6120:	39 da                	cmp    %ebx,%edx
    6122:	7f e4                	jg     6108 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6124:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    612a:	49 83 c5 01          	add    $0x1,%r13
    612e:	44 39 e9             	cmp    %r13d,%ecx
    6131:	7f bd                	jg     60f0 <barriered_work_ingest+0x30>
}
    6133:	5b                   	pop    %rbx
    6134:	31 c0                	xor    %eax,%eax
    6136:	5d                   	pop    %rbp
    6137:	41 5c                	pop    %r12
    6139:	41 5d                	pop    %r13
    613b:	41 5e                	pop    %r14
    613d:	c3                   	ret
    613e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    6140:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    6149:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    6150:	bf 04 00 00 00       	mov    $0x4,%edi
    6155:	48 c1 e6 05          	shl    $0x5,%rsi
    6159:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    6160:	48 83 c6 10          	add    $0x10,%rsi
    6164:	e8 e7 c1 ff ff       	call   2350 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6169:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    6171:	48 8b 40 50          	mov    0x50(%rax),%rax
    6175:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    6179:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    617d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6187:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    618d:	83 c0 01             	add    $0x1,%eax
    6190:	99                   	cltd
    6191:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    6197:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    619d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    61a0:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    61a8:	48 83 c3 01          	add    $0x1,%rbx
    61ac:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    61b0:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    61b4:	8b 10                	mov    (%rax),%edx
    61b6:	39 da                	cmp    %ebx,%edx
    61b8:	0f 8f 46 ff ff ff    	jg     6104 <barriered_work_ingest+0x44>
    61be:	e9 61 ff ff ff       	jmp    6124 <barriered_work_ingest+0x64>
}
    61c3:	31 c0                	xor    %eax,%eax
    61c5:	c3                   	ret
    61c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000061d0 <barriered_thread>:
void* barriered_thread(void *arg) {
    61d0:	f3 0f 1e fa          	endbr64
    61d4:	41 56                	push   %r14
    61d6:	41 55                	push   %r13
    61d8:	41 54                	push   %r12
  int t = 0;
    61da:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    61dd:	55                   	push   %rbp
  int waiting = 0;
    61de:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    61e0:	53                   	push   %rbx
    61e1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    61e4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    61e8:	0f 85 74 02 00 00    	jne    6462 <barriered_thread+0x292>
    if (t >= data->task_count) {
    61ee:	8b 43 40             	mov    0x40(%rbx),%eax
    61f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    61f8:	41 39 c4             	cmp    %eax,%r12d
    61fb:	0f 8d 6f 01 00 00    	jge    6370 <barriered_thread+0x1a0>
    6201:	49 63 fc             	movslq %r12d,%rdi
    6204:	48 c1 e7 09          	shl    $0x9,%rdi
    6208:	49 89 fd             	mov    %rdi,%r13
    620b:	eb 32                	jmp    623f <barriered_thread+0x6f>
    620d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    6210:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6214:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6218:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    621c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6220:	4c 01 ef             	add    %r13,%rdi
    6223:	e8 98 fe ff ff       	call   60c0 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    6228:	8b 43 40             	mov    0x40(%rbx),%eax
    622b:	41 83 c4 01          	add    $0x1,%r12d
    622f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    6236:	44 39 e0             	cmp    %r12d,%eax
    6239:	0f 8e 19 02 00 00    	jle    6458 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    623f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6243:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    6247:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    624e:	75 c0                	jne    6210 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6250:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    6254:	83 e8 01             	sub    $0x1,%eax
    6257:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    625c:	45 85 e4             	test   %r12d,%r12d
    625f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6262:	45 85 c0             	test   %r8d,%r8d
    6265:	0f 8e 2d 01 00 00    	jle    6398 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    626b:	48 63 c8             	movslq %eax,%rcx
    626e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6272:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    6275:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    627b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    6282:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    6286:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    6289:	45 31 f6             	xor    %r14d,%r14d
    628c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6290:	48 8b 10             	mov    (%rax),%rdx
    6293:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6297:	49 01 cb             	add    %rcx,%r11
    629a:	4c 89 da             	mov    %r11,%rdx
    629d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    62a4:	75 04                	jne    62aa <barriered_thread+0xda>
            arrived++;
    62a6:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    62aa:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    62b0:	75 04                	jne    62b6 <barriered_thread+0xe6>
            prearrive++;
    62b2:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    62b6:	48 83 c0 08          	add    $0x8,%rax
    62ba:	48 39 c6             	cmp    %rax,%rsi
    62bd:	75 d1                	jne    6290 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    62bf:	45 85 d2             	test   %r10d,%r10d
    62c2:	0f 84 c0 00 00 00    	je     6388 <barriered_thread+0x1b8>
    62c8:	45 39 d0             	cmp    %r10d,%r8d
    62cb:	0f 84 b7 00 00 00    	je     6388 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    62d1:	45 85 f6             	test   %r14d,%r14d
    62d4:	74 0a                	je     62e0 <barriered_thread+0x110>
    62d6:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    62da:	0f 85 ae 01 00 00    	jne    648e <barriered_thread+0x2be>
    62e0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    62e4:	4c 01 ea             	add    %r13,%rdx
    62e7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    62ee:	45 85 e4             	test   %r12d,%r12d
    62f1:	75 14                	jne    6307 <barriered_thread+0x137>
    62f3:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    62fa:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6301:	0f 8c 69 01 00 00    	jl     6470 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6307:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    630b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    630f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6319:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    631d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6321:	4c 01 ef             	add    %r13,%rdi
    6324:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    632a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    632e:	4c 01 e8             	add    %r13,%rax
    6331:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6338:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    633b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6340:	83 e8 01             	sub    $0x1,%eax
    6343:	44 39 e0             	cmp    %r12d,%eax
    6346:	0f 84 a4 00 00 00    	je     63f0 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    634c:	0f ae f8             	sfence
          if (waiting == 0) {
    634f:	85 ed                	test   %ebp,%ebp
    6351:	0f 84 d1 00 00 00    	je     6428 <barriered_thread+0x258>
        int arrived = 0; 
    6357:	bd 01 00 00 00       	mov    $0x1,%ebp
    635c:	e9 c7 fe ff ff       	jmp    6228 <barriered_thread+0x58>
  while (data->running == 1) {
    6361:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6365:	0f 85 f7 00 00 00    	jne    6462 <barriered_thread+0x292>
    636b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    6370:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    6378:	85 c0                	test   %eax,%eax
    637a:	7e e5                	jle    6361 <barriered_thread+0x191>
    637c:	45 31 e4             	xor    %r12d,%r12d
    637f:	e9 7d fe ff ff       	jmp    6201 <barriered_thread+0x31>
    6384:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6388:	83 fd 01             	cmp    $0x1,%ebp
    638b:	74 1b                	je     63a8 <barriered_thread+0x1d8>
        int arrived = 0; 
    638d:	31 ed                	xor    %ebp,%ebp
    638f:	e9 3d ff ff ff       	jmp    62d1 <barriered_thread+0x101>
    6394:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6398:	83 fd 01             	cmp    $0x1,%ebp
    639b:	0f 85 43 ff ff ff    	jne    62e4 <barriered_thread+0x114>
        int arrived = 0; 
    63a1:	45 31 f6             	xor    %r14d,%r14d
    63a4:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    63a8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    63af:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    63b4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    63b6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    63ba:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    63c1:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    63c6:	e8 85 bf ff ff       	call   2350 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    63cb:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    63d2:	48 83 c0 01          	add    $0x1,%rax
    63d6:	48 99                	cqto
    63d8:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    63df:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    63e6:	e9 e6 fe ff ff       	jmp    62d1 <barriered_thread+0x101>
    63eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    63f0:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    63f7:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    63fe:	0f 8d 48 ff ff ff    	jge    634c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    6404:	48 c1 e6 04          	shl    $0x4,%rsi
    6408:	bf 04 00 00 00       	mov    $0x4,%edi
    640d:	48 03 73 70          	add    0x70(%rbx),%rsi
    6411:	e8 3a bf ff ff       	call   2350 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6416:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    641e:	e9 29 ff ff ff       	jmp    634c <barriered_thread+0x17c>
    6423:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    6428:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    642f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    6434:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6438:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    643f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6443:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6447:	e8 04 bf ff ff       	call   2350 <clock_gettime@plt>
            waiting = 1;
    644c:	e9 06 ff ff ff       	jmp    6357 <barriered_thread+0x187>
    6451:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    6458:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    645c:	0f 84 96 fd ff ff    	je     61f8 <barriered_thread+0x28>
}
    6462:	5b                   	pop    %rbx
    6463:	31 c0                	xor    %eax,%eax
    6465:	5d                   	pop    %rbp
    6466:	41 5c                	pop    %r12
    6468:	41 5d                	pop    %r13
    646a:	41 5e                	pop    %r14
    646c:	c3                   	ret
    646d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    6470:	48 c1 e6 04          	shl    $0x4,%rsi
    6474:	bf 04 00 00 00       	mov    $0x4,%edi
    6479:	48 03 73 68          	add    0x68(%rbx),%rsi
    647d:	e8 ce be ff ff       	call   2350 <clock_gettime@plt>
          data->tasks[t].available = 0;
    6482:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6486:	4c 01 ea             	add    %r13,%rdx
    6489:	e9 79 fe ff ff       	jmp    6307 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    648e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6492:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6496:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    649a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    649e:	4c 01 ef             	add    %r13,%rdi
    64a1:	e8 1a fc ff ff       	call   60c0 <barriered_work_ingest>
          break;
    64a6:	e9 39 fd ff ff       	jmp    61e4 <barriered_thread+0x14>
    64ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000064b0 <receive>:
int receive(struct BarrierTask *data) {
    64b0:	f3 0f 1e fa          	endbr64
    64b4:	41 57                	push   %r15
    64b6:	41 56                	push   %r14
    64b8:	41 55                	push   %r13
    64ba:	41 54                	push   %r12
    64bc:	55                   	push   %rbp
    64bd:	53                   	push   %rbx
    64be:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    64c2:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    64c9:	45 85 f6             	test   %r14d,%r14d
    64cc:	0f 8e 37 01 00 00    	jle    6609 <receive+0x159>
    if (n == data->thread->real_thread_index) { continue; }
    64d2:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    64d9:	48 89 f9             	mov    %rdi,%rcx
    64dc:	45 31 e4             	xor    %r12d,%r12d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    64df:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    64e1:	49 63 6f 08          	movslq 0x8(%r15),%rbp
    64e5:	49 89 ed             	mov    %rbp,%r13
    64e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    64f0:	41 39 dd             	cmp    %ebx,%r13d
    64f3:	0f 84 00 01 00 00    	je     65f9 <receive+0x149>
    struct Data *me = data->mailboxes[n].lower;
    64f9:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    6500:	4a 8b 34 20          	mov    (%rax,%r12,1),%rsi
    if (me->available_reading == 1) {
    6504:	8b 86 00 02 00 00    	mov    0x200(%rsi),%eax
    650a:	83 f8 01             	cmp    $0x1,%eax
    650d:	74 11                	je     6520 <receive+0x70>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    650f:	83 be 18 03 00 00 02 	cmpl   $0x2,0x318(%rsi)
    6516:	75 08                	jne    6520 <receive+0x70>
    6518:	85 c0                	test   %eax,%eax
    651a:	0f 84 d9 00 00 00    	je     65f9 <receive+0x149>
    for (int x = 0 ; x < me->messages_count ; x++) {
    6520:	48 8b be 80 00 00 00 	mov    0x80(%rsi),%rdi
    6527:	48 85 ff             	test   %rdi,%rdi
    652a:	0f 8e a0 00 00 00    	jle    65d0 <receive+0x120>
      data->sends++;
    6530:	48 8b 91 78 01 00 00 	mov    0x178(%rcx),%rdx
    6537:	4c 8b 06             	mov    (%rsi),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    653a:	4c 63 59 04          	movslq 0x4(%rcx),%r11
    653e:	49 89 d1             	mov    %rdx,%r9
    6541:	48 8d 42 01          	lea    0x1(%rdx),%rax
    6545:	49 f7 d9             	neg    %r9
    6548:	48 01 c7             	add    %rax,%rdi
    654b:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    654f:	4c 8b 89 08 01 00 00 	mov    0x108(%rcx),%r9
      me->received++;
    6556:	4c 8b 86 10 03 00 00 	mov    0x310(%rsi),%r8
      data->n++;
    655d:	49 29 d1             	sub    %rdx,%r9
      me->received++;
    6560:	49 29 d0             	sub    %rdx,%r8
    6563:	eb 0c                	jmp    6571 <receive+0xc1>
    6565:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    6568:	48 83 c0 01          	add    $0x1,%rax
    656c:	48 39 c7             	cmp    %rax,%rdi
    656f:	74 5f                	je     65d0 <receive+0x120>
      data->n++;
    6571:	49 8d 14 01          	lea    (%r9,%rax,1),%rdx
      data->sends++;
    6575:	48 89 81 78 01 00 00 	mov    %rax,0x178(%rcx)
      data->n++;
    657c:	48 89 91 08 01 00 00 	mov    %rdx,0x108(%rcx)
      me->received++;
    6583:	49 8d 14 00          	lea    (%r8,%rax,1),%rdx
    6587:	48 89 96 10 03 00 00 	mov    %rdx,0x310(%rsi)
      if (me->messages[x]->group == data->group) {
    658e:	49 8b 54 c2 f8       	mov    -0x8(%r10,%rax,8),%rdx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    6593:	4c 39 5a 10          	cmp    %r11,0x10(%rdx)
    6597:	75 cf                	jne    6568 <receive+0xb8>
    6599:	48 39 6a 08          	cmp    %rbp,0x8(%rdx)
    659d:	75 c9                	jne    6568 <receive+0xb8>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    659f:	49 63 47 04          	movslq 0x4(%r15),%rax
    65a3:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    65a5:	bf 01 00 00 00       	mov    $0x1,%edi
    65aa:	ba 01 00 00 00       	mov    $0x1,%edx
    65af:	48 8d 35 62 20 00 00 	lea    0x2062(%rip),%rsi        # 8618 <_IO_stdin_used+0x618>
    65b6:	48 39 e8             	cmp    %rbp,%rax
    65b9:	0f 94 c1             	sete   %cl
    65bc:	31 c0                	xor    %eax,%eax
    65be:	e8 ed be ff ff       	call   24b0 <__printf_chk@plt>
        exit(1);
    65c3:	bf 01 00 00 00       	mov    $0x1,%edi
    65c8:	e8 43 bf ff ff       	call   2510 <exit@plt>
    65cd:	0f 1f 00             	nopl   (%rax)
    me->messages_count = 0;
    65d0:	48 c7 86 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rsi)
      me->available_reading = 0;
    65db:	c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi)
      me->finished_reading = 1;
    65e5:	c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rsi)
      me->available_sending = 1;
    65ef:	c7 86 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rsi)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    65f9:	83 c3 01             	add    $0x1,%ebx
    65fc:	49 83 c4 38          	add    $0x38,%r12
    6600:	44 39 f3             	cmp    %r14d,%ebx
    6603:	0f 85 e7 fe ff ff    	jne    64f0 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    6609:	0f ae f8             	sfence
}
    660c:	48 83 c4 08          	add    $0x8,%rsp
    6610:	31 c0                	xor    %eax,%eax
    6612:	5b                   	pop    %rbx
    6613:	5d                   	pop    %rbp
    6614:	41 5c                	pop    %r12
    6616:	41 5d                	pop    %r13
    6618:	41 5e                	pop    %r14
    661a:	41 5f                	pop    %r15
    661c:	c3                   	ret
    661d:	0f 1f 00             	nopl   (%rax)

0000000000006620 <sendm>:
int sendm(struct BarrierTask *data) {
    6620:	f3 0f 1e fa          	endbr64
    6624:	41 57                	push   %r15
    6626:	41 56                	push   %r14
    6628:	41 55                	push   %r13
    662a:	41 54                	push   %r12
    662c:	55                   	push   %rbp
    662d:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    662e:	44 8b a7 40 01 00 00 	mov    0x140(%rdi),%r12d
    6635:	45 85 e4             	test   %r12d,%r12d
    6638:	7e 63                	jle    669d <sendm+0x7d>
        if (n == data->thread->real_thread_index) { continue; }
    663a:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    6641:	48 89 fe             	mov    %rdi,%rsi
    6644:	31 d2                	xor    %edx,%edx
    6646:	44 8b 68 08          	mov    0x8(%rax),%r13d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    664a:	31 c0                	xor    %eax,%eax
    664c:	0f 1f 40 00          	nopl   0x0(%rax)
        if (n == data->thread->real_thread_index) { continue; }
    6650:	41 39 c5             	cmp    %eax,%r13d
    6653:	74 3c                	je     6691 <sendm+0x71>
        struct Data *them = data->mailboxes[n].higher;
    6655:	48 8b 8e 70 01 00 00 	mov    0x170(%rsi),%rcx
    665c:	48 8b 4c 11 08       	mov    0x8(%rcx,%rdx,1),%rcx
        if (them->messages_count > 0) {
    6661:	48 8b b9 80 00 00 00 	mov    0x80(%rcx),%rdi
    6668:	48 85 ff             	test   %rdi,%rdi
    666b:	7f 24                	jg     6691 <sendm+0x71>
        if (them->available_sending == 1) {
    666d:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    6674:	41 83 f8 01          	cmp    $0x1,%r8d
    6678:	74 0e                	je     6688 <sendm+0x68>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    667a:	83 b9 18 03 00 00 02 	cmpl   $0x2,0x318(%rcx)
    6681:	75 05                	jne    6688 <sendm+0x68>
    6683:	45 85 c0             	test   %r8d,%r8d
    6686:	74 09                	je     6691 <sendm+0x71>
        if (data->sending == 1) {
    6688:	83 be 80 01 00 00 01 	cmpl   $0x1,0x180(%rsi)
    668f:	74 1f                	je     66b0 <sendm+0x90>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6691:	83 c0 01             	add    $0x1,%eax
    6694:	48 83 c2 38          	add    $0x38,%rdx
    6698:	44 39 e0             	cmp    %r12d,%eax
    669b:	75 b3                	jne    6650 <sendm+0x30>
      asm volatile ("sfence" ::: "memory");
    669d:	0f ae f8             	sfence
}
    66a0:	31 c0                	xor    %eax,%eax
    66a2:	5b                   	pop    %rbx
    66a3:	5d                   	pop    %rbp
    66a4:	41 5c                	pop    %r12
    66a6:	41 5d                	pop    %r13
    66a8:	41 5e                	pop    %r14
    66aa:	41 5f                	pop    %r15
    66ac:	c3                   	ret
    66ad:	0f 1f 00             	nopl   (%rax)
          for (; them->messages_count < min;) {
    66b0:	48 63 99 88 00 00 00 	movslq 0x88(%rcx),%rbx
    66b7:	48 39 df             	cmp    %rbx,%rdi
    66ba:	0f 8d b2 00 00 00    	jge    6772 <sendm+0x152>
    66c0:	49 89 db             	mov    %rbx,%r11
    66c3:	4c 8b be 08 01 00 00 	mov    0x108(%rsi),%r15
    66ca:	4c 8b b1 08 03 00 00 	mov    0x308(%rcx),%r14
    66d1:	49 29 fb             	sub    %rdi,%r11
            them->messages[them->messages_count++] = data->message; 
    66d4:	4c 8b 11             	mov    (%rcx),%r10
    66d7:	4d 8d 43 ff          	lea    -0x1(%r11),%r8
    66db:	4c 89 7c 24 e8       	mov    %r15,-0x18(%rsp)
    66e0:	4c 89 74 24 f0       	mov    %r14,-0x10(%rsp)
    66e5:	49 83 f8 02          	cmp    $0x2,%r8
    66e9:	0f 86 21 01 00 00    	jbe    6810 <sendm+0x1f0>
    66ef:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    66f7:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    66ff:	4f 8d 34 0a          	lea    (%r10,%r9,1),%r14
    6703:	4c 8d be 88 01 00 00 	lea    0x188(%rsi),%r15
    670a:	4b 8d 2c 02          	lea    (%r10,%r8,1),%rbp
    670e:	4d 39 f7             	cmp    %r14,%r15
    6711:	0f 83 81 00 00 00    	jae    6798 <sendm+0x178>
    6717:	4c 8d b6 90 01 00 00 	lea    0x190(%rsi),%r14
    671e:	4c 39 f5             	cmp    %r14,%rbp
    6721:	73 75                	jae    6798 <sendm+0x178>
    6723:	4d 01 d0             	add    %r10,%r8
    6726:	4b 8d 3c 0a          	lea    (%r10,%r9,1),%rdi
    672a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6730:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
          for (; them->messages_count < min;) {
    6737:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    673b:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    673f:	4c 39 c7             	cmp    %r8,%rdi
    6742:	75 ec                	jne    6730 <sendm+0x110>
    6744:	0f 1f 40 00          	nopl   0x0(%rax)
    6748:	48 8b 7c 24 e8       	mov    -0x18(%rsp),%rdi
    674d:	4c 01 df             	add    %r11,%rdi
    6750:	48 89 be 08 01 00 00 	mov    %rdi,0x108(%rsi)
    6757:	48 8b 7c 24 f0       	mov    -0x10(%rsp),%rdi
    675c:	48 89 99 80 00 00 00 	mov    %rbx,0x80(%rcx)
    6763:	4c 01 df             	add    %r11,%rdi
    6766:	48 89 b9 08 03 00 00 	mov    %rdi,0x308(%rcx)
    676d:	4d 89 4c da f8       	mov    %r9,-0x8(%r10,%rbx,8)
          them->available_sending = 0;
    6772:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_reading = 1;
    677c:	c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rcx)
          them->available_receiving = 1;
    6786:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    6790:	e9 fc fe ff ff       	jmp    6691 <sendm+0x71>
    6795:	0f 1f 00             	nopl   (%rax)
    6798:	4d 89 de             	mov    %r11,%r14
    679b:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
    67a2:	49 89 e8             	mov    %rbp,%r8
    67a5:	49 d1 ee             	shr    %r14
    67a8:	49 c1 e6 04          	shl    $0x4,%r14
    67ac:	66 49 0f 6e c1       	movq   %r9,%xmm0
    67b1:	4e 8d 7c 35 00       	lea    0x0(%rbp,%r14,1),%r15
    67b6:	41 83 e6 10          	and    $0x10,%r14d
    67ba:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    67be:	74 10                	je     67d0 <sendm+0x1b0>
            them->messages[them->messages_count++] = data->message; 
    67c0:	49 83 c0 10          	add    $0x10,%r8
    67c4:	0f 11 45 00          	movups %xmm0,0x0(%rbp)
          for (; them->messages_count < min;) {
    67c8:	4d 39 f8             	cmp    %r15,%r8
    67cb:	74 15                	je     67e2 <sendm+0x1c2>
    67cd:	0f 1f 00             	nopl   (%rax)
            them->messages[them->messages_count++] = data->message; 
    67d0:	41 0f 11 00          	movups %xmm0,(%r8)
    67d4:	49 83 c0 20          	add    $0x20,%r8
    67d8:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    67dd:	4d 39 f8             	cmp    %r15,%r8
    67e0:	75 ee                	jne    67d0 <sendm+0x1b0>
    67e2:	4d 89 d8             	mov    %r11,%r8
    67e5:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    67e9:	4c 01 c7             	add    %r8,%rdi
    67ec:	41 f6 c3 01          	test   $0x1,%r11b
    67f0:	0f 84 52 ff ff ff    	je     6748 <sendm+0x128>
            them->messages[them->messages_count++] = data->message; 
    67f6:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
    67fd:	4d 89 0c fa          	mov    %r9,(%r10,%rdi,8)
          for (; them->messages_count < min;) {
    6801:	e9 42 ff ff ff       	jmp    6748 <sendm+0x128>
    6806:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6810:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    6818:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    6820:	e9 fe fe ff ff       	jmp    6723 <sendm+0x103>
    6825:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000006830 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6830:	f3 0f 1e fa          	endbr64
    6834:	41 57                	push   %r15
    6836:	41 56                	push   %r14
    6838:	41 55                	push   %r13
    683a:	41 54                	push   %r12
    683c:	55                   	push   %rbp
    683d:	48 89 fd             	mov    %rdi,%rbp
    6840:	53                   	push   %rbx
    6841:	48 83 ec 58          	sub    $0x58,%rsp
        int t = data->task_index;
    6845:	8b 47 04             	mov    0x4(%rdi),%eax
    6848:	89 44 24 20          	mov    %eax,0x20(%rsp)
  if (data->thread_index == data->task_index) {
    684c:	39 87 30 01 00 00    	cmp    %eax,0x130(%rdi)
    6852:	74 63                	je     68b7 <barriered_work+0x87>
    receive(data);
    6854:	e8 57 fc ff ff       	call   64b0 <receive>
    while (data->scheduled == 1) {
    6859:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    6860:	75 1a                	jne    687c <barriered_work+0x4c>
    6862:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      data->n++;
    6868:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      asm volatile ("sfence" ::: "memory");
    6870:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6873:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    687a:	74 ec                	je     6868 <barriered_work+0x38>
    sendm(data);
    687c:	48 89 ef             	mov    %rbp,%rdi
    687f:	e8 9c fd ff ff       	call   6620 <sendm>
  if (t == data->thread_count - 1) {
    6884:	8b 85 34 01 00 00    	mov    0x134(%rbp),%eax
    688a:	8b 4c 24 20          	mov    0x20(%rsp),%ecx
    688e:	83 e8 01             	sub    $0x1,%eax
    6891:	39 c8                	cmp    %ecx,%eax
    6893:	0f 84 1d 05 00 00    	je     6db6 <barriered_work+0x586>
  data->swap = 0;
    6899:	c7 85 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbp)
  asm volatile ("sfence" ::: "memory");
    68a3:	0f ae f8             	sfence
}
    68a6:	48 83 c4 58          	add    $0x58,%rsp
    68aa:	31 c0                	xor    %eax,%eax
    68ac:	5b                   	pop    %rbx
    68ad:	5d                   	pop    %rbp
    68ae:	41 5c                	pop    %r12
    68b0:	41 5d                	pop    %r13
    68b2:	41 5e                	pop    %r14
    68b4:	41 5f                	pop    %r15
    68b6:	c3                   	ret
      receive(data);
    68b7:	e8 f4 fb ff ff       	call   64b0 <receive>
        if (data->thread->real_thread_index == 0) {
    68bc:	4c 8b bd 28 01 00 00 	mov    0x128(%rbp),%r15
    68c3:	45 8b 57 08          	mov    0x8(%r15),%r10d
    68c7:	45 85 d2             	test   %r10d,%r10d
    68ca:	0f 85 8e 02 00 00    	jne    6b5e <barriered_work+0x32e>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    68d0:	8b 9d 40 01 00 00    	mov    0x140(%rbp),%ebx
    68d6:	85 db                	test   %ebx,%ebx
    68d8:	0f 8e 80 02 00 00    	jle    6b5e <barriered_work+0x32e>
              int next_task = abs((t + 1) % (data->thread_count));
    68de:	48 63 85 34 01 00 00 	movslq 0x134(%rbp),%rax
    68e5:	49 89 e8             	mov    %rbp,%r8
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    68e8:	45 31 ed             	xor    %r13d,%r13d
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    68eb:	45 31 f6             	xor    %r14d,%r14d
    68ee:	4c 63 5c 24 20       	movslq 0x20(%rsp),%r11
    68f3:	45 31 e4             	xor    %r12d,%r12d
              int next_task = abs((t + 1) % (data->thread_count));
    68f6:	89 44 24 44          	mov    %eax,0x44(%rsp)
    68fa:	48 c1 e0 09          	shl    $0x9,%rax
    68fe:	48 8d 88 98 01 00 00 	lea    0x198(%rax),%rcx
    6905:	48 05 70 01 00 00    	add    $0x170,%rax
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    690b:	49 c1 e3 09          	shl    $0x9,%r11
    690f:	48 89 4c 24 48       	mov    %rcx,0x48(%rsp)
    6914:	48 89 c5             	mov    %rax,%rbp
    6917:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        for (int b = 0; b < data->mailbox_thread_count ; b++) {
    6920:	31 c9                	xor    %ecx,%ecx
    6922:	31 f6                	xor    %esi,%esi
    6924:	31 ff                	xor    %edi,%edi
    6926:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    692a:	4c 89 c1             	mov    %r8,%rcx
    692d:	eb 1d                	jmp    694c <barriered_work+0x11c>
    692f:	90                   	nop
    6930:	83 44 24 08 01       	addl   $0x1,0x8(%rsp)
    6935:	8b 44 24 08          	mov    0x8(%rsp),%eax
    6939:	48 83 c7 38          	add    $0x38,%rdi
    693d:	48 81 c6 d8 00 00 00 	add    $0xd8,%rsi
    6944:	39 d8                	cmp    %ebx,%eax
    6946:	0f 84 f4 01 00 00    	je     6b40 <barriered_work+0x310>
              if (y == b) { continue; }
    694c:	8b 44 24 08          	mov    0x8(%rsp),%eax
    6950:	41 39 c5             	cmp    %eax,%r13d
    6953:	74 db                	je     6930 <barriered_work+0x100>
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6955:	49 8b 57 20          	mov    0x20(%r15),%rdx
    6959:	4e 8b 44 32 38       	mov    0x38(%rdx,%r14,1),%r8
    695e:	4b 8d 04 18          	lea    (%r8,%r11,1),%rax
    6962:	44 8b 88 98 01 00 00 	mov    0x198(%rax),%r9d
    6969:	45 85 c9             	test   %r9d,%r9d
    696c:	75 c2                	jne    6930 <barriered_work+0x100>
    696e:	4c 8b 4c 32 38       	mov    0x38(%rdx,%rsi,1),%r9
    6973:	4b 8d 14 19          	lea    (%r9,%r11,1),%rdx
    6977:	44 8b 92 98 01 00 00 	mov    0x198(%rdx),%r10d
    697e:	45 85 d2             	test   %r10d,%r10d
    6981:	75 ad                	jne    6930 <barriered_work+0x100>
    6983:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    698a:	42 83 7c 22 30 02    	cmpl   $0x2,0x30(%rdx,%r12,1)
    6990:	75 9e                	jne    6930 <barriered_work+0x100>
    6992:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6999:	83 7c 38 30 02       	cmpl   $0x2,0x30(%rax,%rdi,1)
    699e:	75 90                	jne    6930 <barriered_work+0x100>
                    for (int nn = 0; nn < data->thread_count; nn++) {
    69a0:	8b 44 24 44          	mov    0x44(%rsp),%eax
    69a4:	85 c0                	test   %eax,%eax
    69a6:	7e 88                	jle    6930 <barriered_work+0x100>
    69a8:	ba 70 01 00 00       	mov    $0x170,%edx
    69ad:	4c 89 5c 24 18       	mov    %r11,0x18(%rsp)
    69b2:	89 5c 24 40          	mov    %ebx,0x40(%rsp)
    69b6:	49 89 d3             	mov    %rdx,%r11
    69b9:	89 c3                	mov    %eax,%ebx
    69bb:	48 89 74 24 30       	mov    %rsi,0x30(%rsp)
    69c0:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    69c5:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    69ca:	44 89 6c 24 24       	mov    %r13d,0x24(%rsp)
    69cf:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
    69d4:	48 89 4c 24 38       	mov    %rcx,0x38(%rsp)
    69d9:	eb 15                	jmp    69f0 <barriered_work+0x1c0>
    69db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    69e0:	49 81 c3 00 02 00 00 	add    $0x200,%r11
    69e7:	44 39 d3             	cmp    %r10d,%ebx
    69ea:	0f 84 e0 00 00 00    	je     6ad0 <barriered_work+0x2a0>
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    69f0:	4b 8b 0c 19          	mov    (%r9,%r11,1),%rcx
                      int next_task = abs((nn + 1) % data->thread_count);
    69f4:	41 83 c2 01          	add    $0x1,%r10d
    69f8:	44 89 d0             	mov    %r10d,%eax
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    69fb:	4c 01 e1             	add    %r12,%rcx
                      int next_task = abs((nn + 1) % data->thread_count);
    69fe:	99                   	cltd
    69ff:	f7 fb                	idiv   %ebx
    return mailbox->lower;
    6a01:	4c 8b 29             	mov    (%rcx),%r13
                      if (source2->messages_count != 0) { 
    6a04:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    6a0c:	0f 85 be 00 00 00    	jne    6ad0 <barriered_work+0x2a0>
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6a12:	48 63 d2             	movslq %edx,%rdx
    6a15:	48 c1 e2 09          	shl    $0x9,%rdx
    6a19:	49 8b 84 10 70 01 00 00 	mov    0x170(%r8,%rdx,1),%rax
    6a21:	48 01 f8             	add    %rdi,%rax
    return mailbox->lower;
    6a24:	4c 8b 30             	mov    (%rax),%r14
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6a27:	48 89 c2             	mov    %rax,%rdx
                      if (dest->messages_count != 0) { 
    6a2a:	49 83 be 80 00 00 00 00 	cmpq   $0x0,0x80(%r14)
    6a32:	75 ac                	jne    69e0 <barriered_work+0x1b0>
    return mailbox->higher;
    6a34:	4c 8b 78 08          	mov    0x8(%rax),%r15
    mailbox->lower = data;
    6a38:	48 8b 41 08          	mov    0x8(%rcx),%rax
    6a3c:	48 89 02             	mov    %rax,(%rdx)
    6a3f:	b8 98 01 00 00       	mov    $0x198,%eax
    6a44:	4c 89 39             	mov    %r15,(%rcx)
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
    6a47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
    6a50:	41 c7 04 01 01 00 00 00 	movl   $0x1,(%r9,%rax,1)
                        data->thread->all_threads[t2].tasks[jj].swap = 1;
    6a58:	41 c7 04 00 01 00 00 00 	movl   $0x1,(%r8,%rax,1)
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
    6a60:	48 05 00 02 00 00    	add    $0x200,%rax
    6a66:	48 39 c6             	cmp    %rax,%rsi
    6a69:	75 e5                	jne    6a50 <barriered_work+0x220>
    mailbox->higher = data;
    6a6b:	4c 89 71 08          	mov    %r14,0x8(%rcx)
    6a6f:	4c 89 6a 08          	mov    %r13,0x8(%rdx)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6a73:	4b 8b 04 18          	mov    (%r8,%r11,1),%rax
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6a77:	49 81 c3 00 02 00 00 	add    $0x200,%r11
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6a7e:	48 8b 49 08          	mov    0x8(%rcx),%rcx
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6a82:	48 8b 44 38 08       	mov    0x8(%rax,%rdi,1),%rax
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6a87:	c7 81 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rcx)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6a91:	c7 80 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rax)
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    6a9b:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6aa5:	c7 80 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rax)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6aaf:	48 8b 02             	mov    (%rdx),%rax
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6ab2:	41 c7 87 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%r15)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6abd:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6ac7:	44 39 d3             	cmp    %r10d,%ebx
    6aca:	0f 85 20 ff ff ff    	jne    69f0 <barriered_work+0x1c0>
    6ad0:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    6ad5:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    mailbox->lower = data;
    6ada:	b8 70 01 00 00       	mov    $0x170,%eax
    6adf:	44 8b 6c 24 24       	mov    0x24(%rsp),%r13d
    6ae4:	8b 5c 24 40          	mov    0x40(%rsp),%ebx
    6ae8:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    6aed:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    6af2:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6af7:	eb 16                	jmp    6b0f <barriered_work+0x2df>
    6af9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6b00:	48 05 00 02 00 00    	add    $0x200,%rax
    6b06:	48 39 c5             	cmp    %rax,%rbp
    6b09:	0f 84 21 fe ff ff    	je     6930 <barriered_work+0x100>
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6b0f:	49 8b 14 00          	mov    (%r8,%rax,1),%rdx
    6b13:	4d 8b 14 01          	mov    (%r9,%rax,1),%r10
    6b17:	48 8b 14 3a          	mov    (%rdx,%rdi,1),%rdx
    6b1b:	4b 39 14 22          	cmp    %rdx,(%r10,%r12,1)
    6b1f:	75 df                	jne    6b00 <barriered_work+0x2d0>
    6b21:	bf 01 00 00 00       	mov    $0x1,%edi
    6b26:	48 8d 35 fe 16 00 00 	lea    0x16fe(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6b2d:	31 c0                	xor    %eax,%eax
    6b2f:	e8 7c b9 ff ff       	call   24b0 <__printf_chk@plt>
                          exit(1);
    6b34:	bf 01 00 00 00       	mov    $0x1,%edi
    6b39:	e8 d2 b9 ff ff       	call   2510 <exit@plt>
    6b3e:	66 90                	xchg   %ax,%ax
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6b40:	41 83 c5 01          	add    $0x1,%r13d
    6b44:	49 89 c8             	mov    %rcx,%r8
    6b47:	49 83 c4 38          	add    $0x38,%r12
    6b4b:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    6b52:	41 39 dd             	cmp    %ebx,%r13d
    6b55:	0f 85 c5 fd ff ff    	jne    6920 <barriered_work+0xf0>
    6b5b:	48 89 cd             	mov    %rcx,%rbp
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6b5e:	49 63 97 c4 00 00 00 	movslq 0xc4(%r15),%rdx
          int k = data->group;
    6b65:	8b 85 94 01 00 00    	mov    0x194(%rbp),%eax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6b6b:	85 d2                	test   %edx,%edx
    6b6d:	0f 8e 64 01 00 00    	jle    6cd7 <barriered_work+0x4a7>
            int y = (k * data->thread->threads_per_group) + d;
    6b73:	0f af c2             	imul   %edx,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6b76:	48 63 4c 24 20       	movslq 0x20(%rsp),%rcx
              int next_task = abs((t + 1) % (data->thread_count));
    6b7b:	44 8b 8d 34 01 00 00 	mov    0x134(%rbp),%r9d
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6b82:	48 c1 e1 09          	shl    $0x9,%rcx
    6b86:	48 98                	cltq
    6b88:	49 89 ce             	mov    %rcx,%r14
    6b8b:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    6b8f:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    6b94:	48 8d 34 c9          	lea    (%rcx,%rcx,8),%rsi
    6b98:	49 8b 4f 20          	mov    0x20(%r15),%rcx
    6b9c:	4c 8d 3c f1          	lea    (%rcx,%rsi,8),%r15
    6ba0:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    6ba8:	48 29 c1             	sub    %rax,%rcx
    6bab:	48 01 d0             	add    %rdx,%rax
    6bae:	4d 89 fd             	mov    %r15,%r13
    6bb1:	4c 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%r10
    6bb9:	4c 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r8
    6bc1:	49 29 c2             	sub    %rax,%r10
    6bc4:	4d 89 c3             	mov    %r8,%r11
    6bc7:	4d 89 c4             	mov    %r8,%r12
    6bca:	49 89 e8             	mov    %rbp,%r8
    6bcd:	49 c1 e2 03          	shl    $0x3,%r10
    6bd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6bd8:	49 8b 6d 38          	mov    0x38(%r13),%rbp
    6bdc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6be1:	4c 89 ff             	mov    %r15,%rdi
    6be4:	4c 89 e6             	mov    %r12,%rsi
    6be7:	48 8b 9c 05 70 01 00 00 	mov    0x170(%rbp,%rax,1),%rbx
    6bef:	eb 1b                	jmp    6c0c <barriered_work+0x3dc>
    6bf1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6bf8:	48 83 c6 38          	add    $0x38,%rsi
    6bfc:	48 81 c7 d8 00 00 00 	add    $0xd8,%rdi
    6c03:	49 39 f2             	cmp    %rsi,%r10
    6c06:	0f 84 b4 00 00 00    	je     6cc0 <barriered_work+0x490>
              if (kind == MAILBOX_FRIEND) {
    6c0c:	83 7c 33 30 01       	cmpl   $0x1,0x30(%rbx,%rsi,1)
    6c11:	75 e5                	jne    6bf8 <barriered_work+0x3c8>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6c13:	4c 8b 77 38          	mov    0x38(%rdi),%r14
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6c17:	45 85 c9             	test   %r9d,%r9d
    6c1a:	7e dc                	jle    6bf8 <barriered_work+0x3c8>
    6c1c:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    6c21:	49 81 c6 70 01 00 00 	add    $0x170,%r14
    6c28:	31 c9                	xor    %ecx,%ecx
    6c2a:	48 89 7c 24 10       	mov    %rdi,0x10(%rsp)
    6c2f:	eb 4e                	jmp    6c7f <barriered_work+0x44f>
    6c31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6c38:	48 63 d2             	movslq %edx,%rdx
    6c3b:	48 c1 e2 09          	shl    $0x9,%rdx
    6c3f:	48 8b 84 15 70 01 00 00 	mov    0x170(%rbp,%rdx,1),%rax
    6c47:	48 01 f0             	add    %rsi,%rax
    return mailbox->lower;
    6c4a:	48 8b 10             	mov    (%rax),%rdx
                      if (dest->messages_count != 0) { 
    6c4d:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    6c55:	75 1c                	jne    6c73 <barriered_work+0x443>
    return mailbox->higher;
    6c57:	f3 0f 7e 40 08       	movq   0x8(%rax),%xmm0
    6c5c:	66 48 0f 6e ca       	movq   %rdx,%xmm1
    mailbox->lower = data;
    6c61:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    6c65:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
    6c69:	48 89 10             	mov    %rdx,(%rax)
    6c6c:	0f 11 07             	movups %xmm0,(%rdi)
    mailbox->higher = data;
    6c6f:	48 89 58 08          	mov    %rbx,0x8(%rax)
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6c73:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    6c7a:	41 39 c9             	cmp    %ecx,%r9d
    6c7d:	74 1c                	je     6c9b <barriered_work+0x46b>
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6c7f:	49 8b 3e             	mov    (%r14),%rdi
                    int next_task = abs((nn + 1) % (data->thread_count));
    6c82:	83 c1 01             	add    $0x1,%ecx
    6c85:	89 c8                	mov    %ecx,%eax
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6c87:	4c 01 df             	add    %r11,%rdi
                    int next_task = abs((nn + 1) % (data->thread_count));
    6c8a:	99                   	cltd
    6c8b:	41 f7 f9             	idiv   %r9d
    return mailbox->lower;
    6c8e:	48 8b 1f             	mov    (%rdi),%rbx
                      if (source2->messages_count != 0) { 
    6c91:	48 83 bb 80 00 00 00 00 	cmpq   $0x0,0x80(%rbx)
    6c99:	74 9d                	je     6c38 <barriered_work+0x408>
    6c9b:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6ca0:	48 83 c6 38          	add    $0x38,%rsi
    6ca4:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    6ca9:	48 81 c7 d8 00 00 00 	add    $0xd8,%rdi
    6cb0:	49 39 f2             	cmp    %rsi,%r10
    6cb3:	0f 85 53 ff ff ff    	jne    6c0c <barriered_work+0x3dc>
    6cb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6cc0:	49 83 c3 38          	add    $0x38,%r11
    6cc4:	49 81 c5 d8 00 00 00 	add    $0xd8,%r13
    6ccb:	4d 39 da             	cmp    %r11,%r10
    6cce:	0f 85 04 ff ff ff    	jne    6bd8 <barriered_work+0x3a8>
    6cd4:	4c 89 c5             	mov    %r8,%rbp
      receive(data);
    6cd7:	48 89 ef             	mov    %rbp,%rdi
    6cda:	e8 d1 f7 ff ff       	call   64b0 <receive>
      asm volatile ("sfence" ::: "memory");
    6cdf:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6ce2:	48 8b b5 60 01 00 00 	mov    0x160(%rbp),%rsi
    6ce9:	31 ff                	xor    %edi,%edi
    6ceb:	48 c1 e6 05          	shl    $0x5,%rsi
    6cef:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    6cf6:	e8 55 b6 ff ff       	call   2350 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6cfb:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    while (data->scheduled == 1) {
    6d02:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    int modcount = ++data->thread->protected_state->modcount;
    6d09:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6d0d:	8b 4a 10             	mov    0x10(%rdx),%ecx
    6d10:	8d 59 01             	lea    0x1(%rcx),%ebx
    6d13:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6d16:	75 59                	jne    6d71 <barriered_work+0x541>
    6d18:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6d20:	48 63 95 30 01 00 00 	movslq 0x130(%rbp),%rdx
    6d27:	48 8b 40 18          	mov    0x18(%rax),%rax
    6d2b:	48 63 7d 04          	movslq 0x4(%rbp),%rdi
      data->n++;
    6d2f:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6d37:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6d3b:	48 c1 e7 09          	shl    $0x9,%rdi
    6d3f:	48 03 78 38          	add    0x38(%rax),%rdi
    6d43:	ff 95 20 01 00 00    	call   *0x120(%rbp)
      asm volatile ("sfence" ::: "memory");
    6d49:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6d4c:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    if (modcount != data->thread->protected_state->modcount) {
    6d53:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
    while (data->scheduled == 1) {
    6d5a:	74 c4                	je     6d20 <barriered_work+0x4f0>
    if (modcount != data->thread->protected_state->modcount) {
    6d5c:	48 8b 40 48          	mov    0x48(%rax),%rax
    6d60:	3b 58 10             	cmp    0x10(%rax),%ebx
    6d63:	74 0c                	je     6d71 <barriered_work+0x541>
    6d65:	48 8d 3d da 14 00 00 	lea    0x14da(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6d6c:	e8 bf b5 ff ff       	call   2330 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6d71:	48 8b b5 60 01 00 00 	mov    0x160(%rbp),%rsi
    6d78:	31 ff                	xor    %edi,%edi
    6d7a:	48 c1 e6 05          	shl    $0x5,%rsi
    6d7e:	48 03 b5 50 01 00 00 	add    0x150(%rbp),%rsi
    6d85:	48 83 c6 10          	add    $0x10,%rsi
    6d89:	e8 c2 b5 ff ff       	call   2350 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6d8e:	48 8b 85 60 01 00 00 	mov    0x160(%rbp),%rax
    sendm(data);
    6d95:	48 89 ef             	mov    %rbp,%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6d98:	48 83 c0 01          	add    $0x1,%rax
    6d9c:	48 99                	cqto
    6d9e:	48 f7 bd 58 01 00 00 	idivq  0x158(%rbp)
    6da5:	48 89 95 60 01 00 00 	mov    %rdx,0x160(%rbp)
    sendm(data);
    6dac:	e8 6f f8 ff ff       	call   6620 <sendm>
    6db1:	e9 ce fa ff ff       	jmp    6884 <barriered_work+0x54>
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6db6:	48 63 95 48 01 00 00 	movslq 0x148(%rbp),%rdx
    6dbd:	85 d2                	test   %edx,%edx
    6dbf:	0f 8e d4 fa ff ff    	jle    6899 <barriered_work+0x69>
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6dc5:	48 8b 8d 28 01 00 00 	mov    0x128(%rbp),%rcx
    6dcc:	48 c1 e2 09          	shl    $0x9,%rdx
    6dd0:	48 63 41 08          	movslq 0x8(%rcx),%rax
    6dd4:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    6dd8:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    6ddc:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    6de0:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    6de4:	48 8b 40 38          	mov    0x38(%rax),%rax
    6de8:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    6dec:	80 e6 02             	and    $0x2,%dh
    6def:	74 1f                	je     6e10 <barriered_work+0x5e0>
    6df1:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6df8:	48 05 00 02 00 00    	add    $0x200,%rax
    6dfe:	48 39 c8             	cmp    %rcx,%rax
    6e01:	0f 84 92 fa ff ff    	je     6899 <barriered_work+0x69>
    6e07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6e10:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
    6e17:	83 80 9c 03 00 00 01 	addl   $0x1,0x39c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6e1e:	48 05 00 04 00 00    	add    $0x400,%rax
    6e24:	48 39 c8             	cmp    %rcx,%rax
    6e27:	75 e7                	jne    6e10 <barriered_work+0x5e0>
    6e29:	e9 6b fa ff ff       	jmp    6899 <barriered_work+0x69>
    6e2e:	66 90                	xchg   %ax,%ax

0000000000006e30 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6e30:	f3 0f 1e fa          	endbr64
    6e34:	53                   	push   %rbx
    6e35:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6e38:	e8 83 f2 ff ff       	call   60c0 <barriered_work_ingest>
  barriered_work(data);
    6e3d:	48 89 df             	mov    %rbx,%rdi
}
    6e40:	5b                   	pop    %rbx
  barriered_work(data);
    6e41:	e9 ea f9 ff ff       	jmp    6830 <barriered_work>
    6e46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006e50 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6e50:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6e54:	85 f6                	test   %esi,%esi
    6e56:	74 10                	je     6e68 <mailboxkind+0x18>
  return NULL;
    6e58:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    6e5a:	83 fe 01             	cmp    $0x1,%esi
    6e5d:	74 01                	je     6e60 <mailboxkind+0x10>
}
    6e5f:	c3                   	ret
    return mailbox->higher;
    6e60:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    6e64:	c3                   	ret
    6e65:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
    6e68:	48 8b 07             	mov    (%rdi),%rax
    6e6b:	c3                   	ret
    6e6c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006e70 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    6e70:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6e74:	85 d2                	test   %edx,%edx
    6e76:	75 08                	jne    6e80 <setmailboxkind+0x10>
    mailbox->lower = data;
    6e78:	48 89 37             	mov    %rsi,(%rdi)
}
    6e7b:	31 c0                	xor    %eax,%eax
    6e7d:	c3                   	ret
    6e7e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    6e80:	83 fa 01             	cmp    $0x1,%edx
    6e83:	74 13                	je     6e98 <setmailboxkind+0x28>
  if (kind == 2) {
    6e85:	83 fa 02             	cmp    $0x2,%edx
    6e88:	75 f1                	jne    6e7b <setmailboxkind+0xb>
    mailbox->pending = data;
    6e8a:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
    6e8e:	31 c0                	xor    %eax,%eax
    6e90:	c3                   	ret
    6e91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    mailbox->higher = data;
    6e98:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    6e9c:	31 c0                	xor    %eax,%eax
    6e9e:	c3                   	ret
    6e9f:	90                   	nop

0000000000006ea0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6ea0:	f3 0f 1e fa          	endbr64
}
    6ea4:	31 c0                	xor    %eax,%eax
    6ea6:	c3                   	ret
    6ea7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006eb0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6eb0:	f3 0f 1e fa          	endbr64
    6eb4:	31 c0                	xor    %eax,%eax
    6eb6:	c3                   	ret
    6eb7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006ec0 <after>:
int after(struct timespec left, struct timespec right) {
    6ec0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6ec4:	31 c0                	xor    %eax,%eax
    6ec6:	48 39 d7             	cmp    %rdx,%rdi
    6ec9:	7e 08                	jle    6ed3 <after+0x13>
    6ecb:	31 c0                	xor    %eax,%eax
    6ecd:	48 39 ce             	cmp    %rcx,%rsi
    6ed0:	0f 9f c0             	setg   %al
}
    6ed3:	c3                   	ret
    6ed4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6edf:	90                   	nop

0000000000006ee0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6ee0:	f3 0f 1e fa          	endbr64
    6ee4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6ee9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    6eee:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6ef0:	48 39 d7             	cmp    %rdx,%rdi
    6ef3:	7f 18                	jg     6f0d <within+0x2d>
    6ef5:	4d 39 d8             	cmp    %r11,%r8
    6ef8:	0f 9e c2             	setle  %dl
    6efb:	48 39 ce             	cmp    %rcx,%rsi
    6efe:	0f 9e c0             	setle  %al
    6f01:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6f03:	31 c0                	xor    %eax,%eax
    6f05:	4d 39 d1             	cmp    %r10,%r9
    6f08:	0f 9e c0             	setle  %al
    6f0b:	21 d0                	and    %edx,%eax
}
    6f0d:	c3                   	ret
    6f0e:	66 90                	xchg   %ax,%ax

0000000000006f10 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6f10:	f3 0f 1e fa          	endbr64
    6f14:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6f19:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6f1e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6f23:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6f28:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6f2d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6f32:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6f37:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6f3c:	48 39 fe             	cmp    %rdi,%rsi
    6f3f:	7d 2f                	jge    6f70 <overlap+0x60>
    6f41:	48 39 ca             	cmp    %rcx,%rdx
    6f44:	7d 62                	jge    6fa8 <overlap+0x98>
    6f46:	4d 39 da             	cmp    %r11,%r10
    6f49:	7d 0e                	jge    6f59 <overlap+0x49>
    return 1;
    6f4b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6f50:	4d 39 c1             	cmp    %r8,%r9
    6f53:	0f 8c 7f 00 00 00    	jl     6fd8 <overlap+0xc8>
  return 0;
    6f59:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f5b:	4d 39 c1             	cmp    %r8,%r9
    6f5e:	7f 4c                	jg     6fac <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6f60:	31 c0                	xor    %eax,%eax
    6f62:	4d 39 da             	cmp    %r11,%r10
    6f65:	0f 9e c0             	setle  %al
    6f68:	c3                   	ret
    6f69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6f70:	7e 4e                	jle    6fc0 <overlap+0xb0>
    6f72:	48 39 ca             	cmp    %rcx,%rdx
    6f75:	7f 39                	jg     6fb0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f77:	75 31                	jne    6faa <overlap+0x9a>
    6f79:	4d 39 c1             	cmp    %r8,%r9
    6f7c:	7c 2c                	jl     6faa <overlap+0x9a>
    return 1;
    6f7e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6f83:	4d 39 da             	cmp    %r11,%r10
    6f86:	7d 24                	jge    6fac <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f88:	48 39 ca             	cmp    %rcx,%rdx
    6f8b:	0f 94 c2             	sete   %dl
    6f8e:	48 39 fe             	cmp    %rdi,%rsi
    6f91:	0f 94 c0             	sete   %al
    6f94:	21 c2                	and    %eax,%edx
    6f96:	31 c0                	xor    %eax,%eax
    6f98:	4d 39 c1             	cmp    %r8,%r9
    6f9b:	0f 94 c0             	sete   %al
    6f9e:	21 d0                	and    %edx,%eax
    6fa0:	c3                   	ret
    6fa1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6fa8:	74 af                	je     6f59 <overlap+0x49>
  return 0;
    6faa:	31 c0                	xor    %eax,%eax
}
    6fac:	c3                   	ret
    6fad:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6fb0:	4d 39 da             	cmp    %r11,%r10
    6fb3:	7e c4                	jle    6f79 <overlap+0x69>
    return 1;
    6fb5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6fba:	4d 39 c1             	cmp    %r8,%r9
    6fbd:	7e ba                	jle    6f79 <overlap+0x69>
    6fbf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6fc0:	48 39 ca             	cmp    %rcx,%rdx
    6fc3:	7c 94                	jl     6f59 <overlap+0x49>
    6fc5:	4d 39 c1             	cmp    %r8,%r9
    6fc8:	7d b4                	jge    6f7e <overlap+0x6e>
    6fca:	48 39 ca             	cmp    %rcx,%rdx
    6fcd:	74 91                	je     6f60 <overlap+0x50>
    6fcf:	eb d9                	jmp    6faa <overlap+0x9a>
    6fd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6fd8:	c3                   	ret
    6fd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006fe0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6fe0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6fe4:	85 f6                	test   %esi,%esi
    6fe6:	0f 8e 44 03 00 00    	jle    7330 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    6fec:	41 57                	push   %r15
    6fee:	41 89 f7             	mov    %esi,%r15d
    6ff1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6ff3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6ff6:	41 55                	push   %r13
    6ff8:	41 54                	push   %r12
    6ffa:	55                   	push   %rbp
    6ffb:	53                   	push   %rbx
    6ffc:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    7000:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    7004:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    7009:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    700e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    7011:	45 39 e6             	cmp    %r12d,%r14d
    7014:	0f 84 4e 02 00 00    	je     7268 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    701a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    701f:	8b 50 08             	mov    0x8(%rax),%edx
    7022:	85 d2                	test   %edx,%edx
    7024:	0f 8e 3e 02 00 00    	jle    7268 <verify+0x288>
    702a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    702f:	31 c9                	xor    %ecx,%ecx
    7031:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    7036:	31 c0                	xor    %eax,%eax
    7038:	44 89 f2             	mov    %r14d,%edx
    703b:	bf 01 00 00 00       	mov    $0x1,%edi
    7040:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    7045:	48 8d 35 0a 12 00 00 	lea    0x120a(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    704c:	e8 5f b4 ff ff       	call   24b0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    7051:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7056:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    705b:	8b 40 08             	mov    0x8(%rax),%eax
    705e:	85 c0                	test   %eax,%eax
    7060:	0f 8e e6 01 00 00    	jle    724c <verify+0x26c>
    7066:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    7069:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    706e:	31 db                	xor    %ebx,%ebx
    7070:	48 c1 e0 09          	shl    $0x9,%rax
    7074:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    7079:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    707e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7083:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    7088:	4c 8b 20             	mov    (%rax),%r12
    708b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7090:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    7095:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    709a:	49 89 de             	mov    %rbx,%r14
    709d:	48 8d 35 c7 11 00 00 	lea    0x11c7(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    70a4:	49 c1 e6 09          	shl    $0x9,%r14
    70a8:	bf 01 00 00 00       	mov    $0x1,%edi
    70ad:	48 8b 45 00          	mov    0x0(%rbp),%rax
    70b1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    70b9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    70be:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    70c6:	31 c0                	xor    %eax,%eax
    70c8:	e8 e3 b3 ff ff       	call   24b0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    70cd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    70d2:	4c 8b 20             	mov    (%rax),%r12
    70d5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    70de:	0f 8e 47 01 00 00    	jle    722b <verify+0x24b>
    70e4:	4c 03 75 00          	add    0x0(%rbp),%r14
    70e8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    70ed:	ba 01 00 00 00       	mov    $0x1,%edx
    70f2:	4d 89 f5             	mov    %r14,%r13
    70f5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    70fc:	4d 85 f6             	test   %r14,%r14
    70ff:	0f 8e 21 01 00 00    	jle    7226 <verify+0x246>
    7105:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    7108:	48 89 d5             	mov    %rdx,%rbp
    710b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7110:	31 db                	xor    %ebx,%ebx
    7112:	4d 89 f2             	mov    %r14,%r10
    7115:	48 c1 e5 05          	shl    $0x5,%rbp
    7119:	48 83 ed 20          	sub    $0x20,%rbp
    711d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    7121:	49 89 ee             	mov    %rbp,%r14
    7124:	48 89 dd             	mov    %rbx,%rbp
    7127:	48 89 d3             	mov    %rdx,%rbx
    712a:	eb 31                	jmp    715d <verify+0x17d>
    712c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    7130:	4c 39 c2             	cmp    %r8,%rdx
    7133:	0f 8d 57 01 00 00    	jge    7290 <verify+0x2b0>
    7139:	4c 39 df             	cmp    %r11,%rdi
    713c:	7e 05                	jle    7143 <verify+0x163>
    713e:	49 39 c1             	cmp    %rax,%r9
    7141:	7c 75                	jl     71b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7143:	4c 39 df             	cmp    %r11,%rdi
    7146:	0f 8d ab 01 00 00    	jge    72f7 <verify+0x317>
    714c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7150:	48 83 c5 01          	add    $0x1,%rbp
    7154:	49 39 ea             	cmp    %rbp,%r10
    7157:	0f 8e a9 00 00 00    	jle    7206 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    715d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    7164:	48 89 e8             	mov    %rbp,%rax
    7167:	48 c1 e0 05          	shl    $0x5,%rax
    716b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    7172:	4c 01 f2             	add    %r14,%rdx
    7175:	48 8b 08             	mov    (%rax),%rcx
    7178:	48 8b 78 10          	mov    0x10(%rax),%rdi
    717c:	48 8b 32             	mov    (%rdx),%rsi
    717f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    7183:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    7187:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    718b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    718f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    7193:	48 39 f1             	cmp    %rsi,%rcx
    7196:	7c 98                	jl     7130 <verify+0x150>
    7198:	0f 8e 42 01 00 00    	jle    72e0 <verify+0x300>
    719e:	4c 39 c2             	cmp    %r8,%rdx
    71a1:	0f 8f f9 00 00 00    	jg     72a0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71a7:	75 a7                	jne    7150 <verify+0x170>
    71a9:	4c 39 df             	cmp    %r11,%rdi
    71ac:	7f a2                	jg     7150 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    71ae:	49 39 c1             	cmp    %rax,%r9
    71b1:	7c 9d                	jl     7150 <verify+0x170>
    71b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    71b8:	49 89 c1             	mov    %rax,%r9
    71bb:	48 89 f9             	mov    %rdi,%rcx
    71be:	48 89 f2             	mov    %rsi,%rdx
    71c1:	bf 01 00 00 00       	mov    $0x1,%edi
    71c6:	48 8d 35 73 14 00 00 	lea    0x1473(%rip),%rsi        # 8640 <_IO_stdin_used+0x640>
    71cd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    71cf:	48 83 c5 01          	add    $0x1,%rbp
    71d3:	e8 d8 b2 ff ff       	call   24b0 <__printf_chk@plt>
    71d8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    71dd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    71e2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    71e5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    71ea:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    71f1:	4c 8b 20             	mov    (%rax),%r12
    71f4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    71f9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    71fd:	49 39 ea             	cmp    %rbp,%r10
    7200:	0f 8f 57 ff ff ff    	jg     715d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7206:	48 89 da             	mov    %rbx,%rdx
    7209:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7210:	7d 14                	jge    7226 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7212:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7219:	48 83 c2 01          	add    $0x1,%rdx
    721d:	4d 85 f6             	test   %r14,%r14
    7220:	0f 8f e2 fe ff ff    	jg     7108 <verify+0x128>
    7226:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    722b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7230:	48 83 c3 01          	add    $0x1,%rbx
    7234:	39 58 08             	cmp    %ebx,0x8(%rax)
    7237:	0f 8f 53 fe ff ff    	jg     7090 <verify+0xb0>
    723d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    7242:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    7247:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    724c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7251:	48 83 c1 01          	add    $0x1,%rcx
    7255:	39 48 08             	cmp    %ecx,0x8(%rax)
    7258:	0f 8f d8 fd ff ff    	jg     7036 <verify+0x56>
    725e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    7263:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    7268:	48 81 44 24 10 d8 00 00 00 	addq   $0xd8,0x10(%rsp)
    7271:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    7276:	41 39 c7             	cmp    %eax,%r15d
    7279:	0f 84 86 00 00 00    	je     7305 <verify+0x325>
    727f:	41 89 c4             	mov    %eax,%r12d
    7282:	e9 8a fd ff ff       	jmp    7011 <verify+0x31>
    7287:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7290:	0f 85 ba fe ff ff    	jne    7150 <verify+0x170>
    7296:	e9 a8 fe ff ff       	jmp    7143 <verify+0x163>
    729b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    72a0:	49 39 c1             	cmp    %rax,%r9
    72a3:	7e 09                	jle    72ae <verify+0x2ce>
    72a5:	4c 39 df             	cmp    %r11,%rdi
    72a8:	0f 8c 0a ff ff ff    	jl     71b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    72ae:	4c 39 df             	cmp    %r11,%rdi
    72b1:	0f 8f 99 fe ff ff    	jg     7150 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    72b7:	49 39 c1             	cmp    %rax,%r9
    72ba:	0f 8d f8 fe ff ff    	jge    71b8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    72c0:	48 39 f1             	cmp    %rsi,%rcx
    72c3:	0f 85 87 fe ff ff    	jne    7150 <verify+0x170>
    72c9:	4c 39 c2             	cmp    %r8,%rdx
    72cc:	0f 85 7e fe ff ff    	jne    7150 <verify+0x170>
    72d2:	4c 39 df             	cmp    %r11,%rdi
    72d5:	0f 84 dd fe ff ff    	je     71b8 <verify+0x1d8>
    72db:	e9 70 fe ff ff       	jmp    7150 <verify+0x170>
    72e0:	4c 39 c2             	cmp    %r8,%rdx
    72e3:	0f 8c 5a fe ff ff    	jl     7143 <verify+0x163>
    72e9:	4c 39 df             	cmp    %r11,%rdi
    72ec:	7e c9                	jle    72b7 <verify+0x2d7>
    72ee:	4c 39 c2             	cmp    %r8,%rdx
    72f1:	0f 85 59 fe ff ff    	jne    7150 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    72f7:	49 39 c1             	cmp    %rax,%r9
    72fa:	0f 8f 50 fe ff ff    	jg     7150 <verify+0x170>
    7300:	e9 b3 fe ff ff       	jmp    71b8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    7305:	48 81 44 24 18 d8 00 00 00 	addq   $0xd8,0x18(%rsp)
    730e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7312:	45 39 e6             	cmp    %r12d,%r14d
    7315:	74 08                	je     731f <verify+0x33f>
    7317:	41 89 c6             	mov    %eax,%r14d
    731a:	e9 ea fc ff ff       	jmp    7009 <verify+0x29>
}
    731f:	48 83 c4 58          	add    $0x58,%rsp
    7323:	31 c0                	xor    %eax,%eax
    7325:	5b                   	pop    %rbx
    7326:	5d                   	pop    %rbp
    7327:	41 5c                	pop    %r12
    7329:	41 5d                	pop    %r13
    732b:	41 5e                	pop    %r14
    732d:	41 5f                	pop    %r15
    732f:	c3                   	ret
    7330:	31 c0                	xor    %eax,%eax
    7332:	c3                   	ret

Disassembly of section .fini:

0000000000007334 <_fini>:
    7334:	f3 0f 1e fa          	endbr64
    7338:	48 83 ec 08          	sub    $0x8,%rsp
    733c:	48 83 c4 08          	add    $0x8,%rsp
    7340:	c3                   	ret
