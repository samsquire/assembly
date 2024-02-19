
multibarrier-evented3:     file format elf64-x86-64


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
    26a4:	48 8d 05 e5 1d 00 00 	lea    0x1de5(%rip),%rax        # 4490 <barriered_reset>
    26ab:	66 48 0f 6e e0       	movq   %rax,%xmm4
    26b0:	0f 16 25 a1 85 00 00 	movhps 0x85a1(%rip),%xmm4        # ac58 <__do_global_dtors_aux_fini_array_entry+0x8>
    26b7:	0f 29 a4 24 b0 00 00 00 	movaps %xmm4,0xb0(%rsp)
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
    2888:	42 8d 14 2b          	lea    (%rbx,%r13,1),%edx
    288c:	41 89 d8             	mov    %ebx,%r8d
    288f:	44 89 f1             	mov    %r14d,%ecx
    2892:	48 89 ee             	mov    %rbp,%rsi
    2895:	bf 01 00 00 00       	mov    $0x1,%edi
    289a:	31 c0                	xor    %eax,%eax
    289c:	83 c3 01             	add    $0x1,%ebx
    289f:	e8 0c fc ff ff       	call   24b0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    28a4:	4c 89 e7             	mov    %r12,%rdi
    28a7:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    28a9:	49 83 c4 28          	add    $0x28,%r12
      pthread_mutex_init(&swapmutex[cc++], NULL);
    28ad:	e8 ce fc ff ff       	call   2580 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    28b2:	83 fb 0a             	cmp    $0xa,%ebx
    28b5:	75 d1                	jne    2888 <main+0x218>
    28b7:	41 83 c5 0a          	add    $0xa,%r13d
  for (int x = 0 ; x < total_threads; x++) {
    28bb:	41 83 c6 01          	add    $0x1,%r14d
    28bf:	49 81 c7 90 01 00 00 	add    $0x190,%r15
    28c6:	41 83 fd 64          	cmp    $0x64,%r13d
    28ca:	75 b4                	jne    2880 <main+0x210>
    28cc:	ba 06 00 00 00       	mov    $0x6,%edx
    28d1:	48 8d 35 b4 5a 00 00 	lea    0x5ab4(%rip),%rsi        # 838c <_IO_stdin_used+0x38c>
    28d8:	bf 01 00 00 00       	mov    $0x1,%edi
    28dd:	31 c0                	xor    %eax,%eax
    28df:	e8 cc fb ff ff       	call   24b0 <__printf_chk@plt>
    28e4:	ba 0c 00 00 00       	mov    $0xc,%edx
    28e9:	48 8d 35 b2 5a 00 00 	lea    0x5ab2(%rip),%rsi        # 83a2 <_IO_stdin_used+0x3a2>
    28f0:	31 c0                	xor    %eax,%eax
    28f2:	bf 01 00 00 00       	mov    $0x1,%edi
    28f7:	e8 b4 fb ff ff       	call   24b0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    28fc:	be 10 00 00 00       	mov    $0x10,%esi
    2901:	bf 0c 00 00 00       	mov    $0xc,%edi
    2906:	e8 f5 fa ff ff       	call   2400 <calloc@plt>
    290b:	48 89 84 24 c0 00 00 00 	mov    %rax,0xc0(%rsp)
    2913:	49 89 c7             	mov    %rax,%r15
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2916:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    291d:	49 89 c5             	mov    %rax,%r13
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2920:	be 00 01 00 00       	mov    $0x100,%esi
    buffers[x].count = buffer_size;
    2925:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    292d:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2932:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2936:	e8 c5 fa ff ff       	call   2400 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    293b:	be 20 00 00 00       	mov    $0x20,%esi
    2940:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2945:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    2949:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    294c:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2956:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2960:	e8 9b fa ff ff       	call   2400 <calloc@plt>
    2965:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    296c:	4c 39 eb             	cmp    %r13,%rbx
    296f:	75 af                	jne    2920 <main+0x2b0>
    2971:	48 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%rsi
    2979:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  int swap = 0;
    297e:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    2986:	45 31 f6             	xor    %r14d,%r14d
  int cur_buffer = 0;
    2989:	c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rsp)
  int dataid = 0;
    2994:	45 31 e4             	xor    %r12d,%r12d
    2997:	48 89 b4 24 98 00 00 00 	mov    %rsi,0x98(%rsp)
    299f:	48 89 dd             	mov    %rbx,%rbp
  int curcpu = 0;
    29a2:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
    29aa:	48 89 9c 24 a8 00 00 00 	mov    %rbx,0xa8(%rsp)
    29b2:	4c 89 fb             	mov    %r15,%rbx
    29b5:	45 89 f7             	mov    %r14d,%r15d
    for (int d = 0 ; d < threads_per_group ; d++) {
    29b8:	48 63 84 24 80 00 00 00 	movslq 0x80(%rsp),%rax
    29c0:	44 89 bc 24 84 00 00 00 	mov    %r15d,0x84(%rsp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    29c8:	49 89 e9             	mov    %rbp,%r9
    29cb:	48 89 ac 24 e0 00 00 00 	mov    %rbp,0xe0(%rsp)
    29d3:	48 c1 e0 04          	shl    $0x4,%rax
    29d7:	48 89 b4 24 c8 00 00 00 	mov    %rsi,0xc8(%rsp)
    29df:	48 01 d8             	add    %rbx,%rax
    29e2:	48 89 9c 24 e8 00 00 00 	mov    %rbx,0xe8(%rsp)
    29ea:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    29ef:	43 8d 04 3f          	lea    (%r15,%r15,1),%eax
    29f3:	8d 78 01             	lea    0x1(%rax),%edi
    29f6:	83 c0 03             	add    $0x3,%eax
    29f9:	89 7c 24 20          	mov    %edi,0x20(%rsp)
    29fd:	89 84 24 94 00 00 00 	mov    %eax,0x94(%rsp)
    2a04:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
    2a09:	8b 94 24 84 00 00 00 	mov    0x84(%rsp),%edx
    2a10:	48 8d 35 09 5d 00 00 	lea    0x5d09(%rip),%rsi        # 8720 <_IO_stdin_used+0x720>
    2a17:	31 c0                	xor    %eax,%eax
    2a19:	bf 01 00 00 00       	mov    $0x1,%edi
    2a1e:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      int x = (k * threads_per_group) + d;
    2a23:	45 8d 7e ff          	lea    -0x1(%r14),%r15d
    2a27:	44 89 f9             	mov    %r15d,%ecx
    2a2a:	e8 81 fa ff ff       	call   24b0 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a2f:	be 08 00 00 00       	mov    $0x8,%esi
    2a34:	bf 02 00 00 00       	mov    $0x2,%edi
    2a39:	e8 c2 f9 ff ff       	call   2400 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a3e:	be 80 00 00 00       	mov    $0x80,%esi
    2a43:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a48:	48 89 c3             	mov    %rax,%rbx
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a4b:	e8 b0 f9 ff ff       	call   2400 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2a50:	45 89 f8             	mov    %r15d,%r8d
    2a53:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2a58:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a5c:	48 89 c5             	mov    %rax,%rbp
      if (x % 2 == 1) {
    2a5f:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2a64:	0f 84 e0 10 00 00    	je     3b4a <main+0x14da>
        other = abs(x - 1) % total_threads;
    2a6a:	45 89 f5             	mov    %r14d,%r13d
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    2a6d:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
        my_thread_data[1] = &thread_data[x]; 
    2a72:	4c 89 ca             	mov    %r9,%rdx
        other = abs(x - 1) % total_threads;
    2a75:	41 8d 45 fe          	lea    -0x2(%r13),%eax
    2a79:	49 89 c6             	mov    %rax,%r14
        my_thread_data[0] = &thread_data[other]; 
    2a7c:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2a80:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    2a84:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2a88:	48 8d 73 08          	lea    0x8(%rbx),%rsi
    2a8c:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    2a91:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
    2a99:	48 89 03             	mov    %rax,(%rbx)
    2a9c:	44 89 f1             	mov    %r14d,%ecx
    2a9f:	48 8d 35 aa 5c 00 00 	lea    0x5caa(%rip),%rsi        # 8750 <_IO_stdin_used+0x750>
        thread_data[x].thread_index = 1;
    2aa6:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2aaa:	31 c0                	xor    %eax,%eax
        thread_data[x].protected_state = &protected_state[k];
    2aac:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2ab0:	bf 01 00 00 00       	mov    $0x1,%edi
    2ab5:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    2ab9:	44 89 fa             	mov    %r15d,%edx
    2abc:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2ac1:	e8 ea f9 ff ff       	call   24b0 <__printf_chk@plt>
      thread_data[x].other = other;
    2ac6:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2acb:	8b 4c 24 7c          	mov    0x7c(%rsp),%ecx
    2acf:	31 c0                	xor    %eax,%eax
    2ad1:	44 89 fa             	mov    %r15d,%edx
    2ad4:	48 8d 35 a5 5c 00 00 	lea    0x5ca5(%rip),%rsi        # 8780 <_IO_stdin_used+0x780>
    2adb:	bf 01 00 00 00       	mov    $0x1,%edi
    2ae0:	45 89 b1 b8 00 00 00 	mov    %r14d,0xb8(%r9)
    2ae7:	e8 c4 f9 ff ff       	call   24b0 <__printf_chk@plt>
        if (x < thread_count) {
    2aec:	41 83 ff 01          	cmp    $0x1,%r15d
    2af0:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2af5:	0f 87 79 10 00 00    	ja     3b74 <main+0x1504>
          CPU_SET(curcpu, sendercpu);
    2afb:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2b00:	48 89 c7             	mov    %rax,%rdi
    2b03:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2b09:	77 13                	ja     2b1e <main+0x4ae>
    2b0b:	48 c1 e8 06          	shr    $0x6,%rax
    2b0f:	ba 01 00 00 00       	mov    $0x1,%edx
    2b14:	89 f9                	mov    %edi,%ecx
    2b16:	48 d3 e2             	shl    %cl,%rdx
    2b19:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
          curcpu += 2;
    2b1e:	83 44 24 7c 02       	addl   $0x2,0x7c(%rsp)
      thread_data[x].real_thread_index = x;
    2b23:	45 89 79 08          	mov    %r15d,0x8(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b27:	be 10 00 00 00       	mov    $0x10,%esi
    2b2c:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].swapmutex = swapmutex;
    2b31:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    2b39:	49 89 a9 b0 00 00 00 	mov    %rbp,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2b40:	31 ed                	xor    %ebp,%ebp
      thread_data[x].swapmutex = swapmutex;
    2b42:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2b49:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2b51:	49 89 59 18          	mov    %rbx,0x18(%r9)
            data[0].messages_count = 0;
    2b55:	44 89 fb             	mov    %r15d,%ebx
      thread_data[x].mswapmutex = mswapmutex;
    2b58:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].all_threads = thread_data;
    2b5f:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].kind = KERNEL_THREAD;
    2b64:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].all_threads = thread_data;
    2b6b:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2b6f:	48 8b 05 6a 61 00 00 	mov    0x616a(%rip),%rax        # 8ce0 <_IO_stdin_used+0xce0>
      thread_data[x].task_count = total_barrier_count;
    2b76:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].group_count = group_count;
    2b7e:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2b85:	48 8b 05 5c 61 00 00 	mov    0x615c(%rip),%rax        # 8ce8 <_IO_stdin_used+0xce8>
      thread_data[x].task_count = total_barrier_count;
    2b8c:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].thread_count = 2;
    2b91:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b95:	e8 66 f8 ff ff       	call   2400 <calloc@plt>
    2b9a:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2b9f:	be 10 00 00 00       	mov    $0x10,%esi
    2ba4:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2ba9:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2bad:	e8 4e f8 ff ff       	call   2400 <calloc@plt>
    2bb2:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bb7:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2bbc:	66 0f 6f 25 ec 60 00 00 	movdqa 0x60ec(%rip),%xmm4        # 8cb0 <_IO_stdin_used+0xcb0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bc4:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2bc9:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2bcd:	41 0f 11 a1 80 00 00 00 	movups %xmm4,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bd5:	e8 26 f8 ff ff       	call   2400 <calloc@plt>
    2bda:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2bdf:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2be4:	66 0f 6f 0d c4 60 00 00 	movdqa 0x60c4(%rip),%xmm1        # 8cb0 <_IO_stdin_used+0xcb0>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2bec:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bf1:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2bf8:	41 0f 11 89 98 00 00 00 	movups %xmm1,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c00:	e8 fb f7 ff ff       	call   2400 <calloc@plt>
        thread_data[x].tasks = barriers;
    2c05:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c0a:	4c 89 ef             	mov    %r13,%rdi
            data[0].messages_count = 0;
    2c0d:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c15:	49 89 c6             	mov    %rax,%r14
        thread_data[x].tasks = barriers;
    2c18:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c1c:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
            data[0].messages_count = 0;
    2c21:	4c 89 f1             	mov    %r14,%rcx
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c24:	48 0f af f8          	imul   %rax,%rdi
            data[0].messages_count = 0;
    2c28:	4c 89 4c 24 50       	mov    %r9,0x50(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c2d:	48 c1 ef 22          	shr    $0x22,%rdi
    2c31:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2c34:	8b 7c 24 20          	mov    0x20(%rsp),%edi
    2c38:	01 c0                	add    %eax,%eax
    2c3a:	29 c7                	sub    %eax,%edi
            data[0].messages_count = 0;
    2c3c:	89 bc 24 90 00 00 00 	mov    %edi,0x90(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c43:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c46:	be 40 00 00 00       	mov    $0x40,%esi
    2c4b:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c50:	45 31 f6             	xor    %r14d,%r14d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c53:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2c58:	48 c1 e0 09          	shl    $0x9,%rax
    2c5c:	4c 8d 2c 01          	lea    (%rcx,%rax,1),%r13
    2c60:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2c65:	48 8d 05 e4 17 00 00 	lea    0x17e4(%rip),%rax        # 4450 <do_protected_write>
    2c6c:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c73:	e8 88 f7 ff ff       	call   2400 <calloc@plt>
    2c78:	8b 74 24 58          	mov    0x58(%rsp),%esi
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2c7c:	49 89 85 70 01 00 00 	mov    %rax,0x170(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c83:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c86:	85 f6                	test   %esi,%esi
    2c88:	0f 84 53 06 00 00    	je     32e1 <main+0xc71>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2c8e:	8b 44 24 20          	mov    0x20(%rsp),%eax
    2c92:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    2c96:	49 89 cd             	mov    %rcx,%r13
    2c99:	48 89 8c 24 88 00 00 00 	mov    %rcx,0x88(%rsp)
    2ca1:	83 e8 02             	sub    $0x2,%eax
    2ca4:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2ca8:	eb 18                	jmp    2cc2 <main+0x652>
    2caa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cb0:	41 83 c6 01          	add    $0x1,%r14d
    2cb4:	49 83 c5 40          	add    $0x40,%r13
    2cb8:	41 83 fe 06          	cmp    $0x6,%r14d
    2cbc:	0f 84 52 01 00 00    	je     2e14 <main+0x7a4>
            int group_of = b / threads_per_group;
    2cc2:	44 89 f3             	mov    %r14d,%ebx
    2cc5:	31 c0                	xor    %eax,%eax
    2cc7:	44 89 f2             	mov    %r14d,%edx
    2cca:	bf 01 00 00 00       	mov    $0x1,%edi
    2ccf:	d1 fb                	sar    %ebx
    2cd1:	48 8d 35 e4 56 00 00 	lea    0x56e4(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2cd8:	89 d9                	mov    %ebx,%ecx
    2cda:	e8 d1 f7 ff ff       	call   24b0 <__printf_chk@plt>
            if (k == group_of) {
    2cdf:	41 39 df             	cmp    %ebx,%r15d
    2ce2:	75 cc                	jne    2cb0 <main+0x640>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2ce4:	be 08 00 00 00       	mov    $0x8,%esi
    2ce9:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cee:	49 83 c5 40          	add    $0x40,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2cf2:	e8 09 f7 ff ff       	call   2400 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cf7:	be 08 00 00 00       	mov    $0x8,%esi
    2cfc:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d01:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d06:	e8 f5 f6 ff ff       	call   2400 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2d0b:	be 80 03 00 00       	mov    $0x380,%esi
    2d10:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d15:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2d1a:	e8 e1 f6 ff ff       	call   2400 <calloc@plt>
              data[0].a = x;
    2d1f:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
              mailboxes[b].pending_lower = NULL;
    2d23:	66 0f ef ff          	pxor   %xmm7,%xmm7
    2d27:	44 89 f2             	mov    %r14d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    2d2a:	49 89 c1             	mov    %rax,%r9
              mailboxes[b].pending_lower = NULL;
    2d2d:	41 0f 11 7d d0       	movups %xmm7,-0x30(%r13)
    2d32:	bf 01 00 00 00       	mov    $0x1,%edi
    2d37:	48 8d 35 62 5a 00 00 	lea    0x5a62(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
              data[0].c = b;
    2d3e:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
              data[0].kind = MAILBOX_LOWER;
    2d45:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].a = x;
    2d4f:	89 98 1c 03 00 00    	mov    %ebx,0x31c(%rax)
              data[0].b = y;
    2d55:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    2d5b:	41 8d 44 24 01       	lea    0x1(%r12),%eax
              data[1].id = dataid++;
    2d60:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2d67:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2d6e:	49 89 45 c8          	mov    %rax,-0x38(%r13)
    2d72:	8b 44 24 70          	mov    0x70(%rsp),%eax
              data[0].id = dataid++;
    2d76:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
              data[1].id = dataid++;
    2d7d:	41 83 c4 02          	add    $0x2,%r12d
              data[1].c = b;
    2d81:	45 89 b1 a4 06 00 00 	mov    %r14d,0x6a4(%r9)
    2d88:	89 c1                	mov    %eax,%ecx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d8a:	41 83 c6 01          	add    $0x1,%r14d
              mailboxes[b].lower = &data[0];
    2d8e:	4d 89 4d c0          	mov    %r9,-0x40(%r13)
    2d92:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    2d96:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    2d98:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].a = x;
    2da3:	41 89 99 9c 06 00 00 	mov    %ebx,0x69c(%r9)
              data[1].b = y;
    2daa:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    2db1:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    2dbc:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2dc7:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    2dcf:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2dd4:	e8 d7 f6 ff ff       	call   24b0 <__printf_chk@plt>
              data[0].messages = messages;
    2dd9:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2dde:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
              data[0].messages_count = 0;
    2de3:	66 0f 6f 3d d5 5e 00 00 	movdqa 0x5ed5(%rip),%xmm7        # 8cc0 <_IO_stdin_used+0xcc0>
              data[1].messages = messages2;
    2deb:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
              data[0].messages = messages;
    2df0:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2df3:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2dfa:	41 0f 29 b9 80 00 00 00 	movaps %xmm7,0x80(%r9)
              data[1].messages_count = 0;
    2e02:	41 0f 29 b9 00 04 00 00 	movaps %xmm7,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e0a:	41 83 fe 06          	cmp    $0x6,%r14d
    2e0e:	0f 85 ae fe ff ff    	jne    2cc2 <main+0x652>
    2e14:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2e18:	48 8b 8c 24 88 00 00 00 	mov    0x88(%rsp),%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e20:	45 31 ed             	xor    %r13d,%r13d
            mailboxes[b].pending_lower = NULL;
    2e23:	44 89 7c 24 08       	mov    %r15d,0x8(%rsp)
    2e28:	41 89 e8             	mov    %ebp,%r8d
    2e2b:	41 89 df             	mov    %ebx,%r15d
    2e2e:	44 89 eb             	mov    %r13d,%ebx
    2e31:	49 89 cd             	mov    %rcx,%r13
    2e34:	0f 1f 40 00          	nopl   0x0(%rax)
            int group_of = b / threads_per_group;
    2e38:	89 d8                	mov    %ebx,%eax
    2e3a:	d1 f8                	sar    %eax
            if (k == group_of) {
    2e3c:	39 44 24 08          	cmp    %eax,0x8(%rsp)
    2e40:	0f 84 59 01 00 00    	je     2f9f <main+0x92f>
    2e46:	89 da                	mov    %ebx,%edx
    2e48:	48 8d 35 7d 55 00 00 	lea    0x557d(%rip),%rsi        # 83cc <_IO_stdin_used+0x3cc>
    2e4f:	bf 01 00 00 00       	mov    $0x1,%edi
    2e54:	31 c0                	xor    %eax,%eax
    2e56:	44 89 44 24 18       	mov    %r8d,0x18(%rsp)
    2e5b:	e8 50 f6 ff ff       	call   24b0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e60:	be 08 00 00 00       	mov    $0x8,%esi
    2e65:	bf 01 00 00 00       	mov    $0x1,%edi
    2e6a:	e8 91 f5 ff ff       	call   2400 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e6f:	be 08 00 00 00       	mov    $0x8,%esi
    2e74:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e79:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e7e:	e8 7d f5 ff ff       	call   2400 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2e83:	be 80 03 00 00       	mov    $0x380,%esi
    2e88:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e8d:	48 89 c5             	mov    %rax,%rbp
            struct Data *data = calloc(3, sizeof(struct Data));
    2e90:	e8 6b f5 ff ff       	call   2400 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2e95:	be 80 03 00 00       	mov    $0x380,%esi
    2e9a:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2e9f:	49 89 c6             	mov    %rax,%r14
            struct Data **stack = calloc(3, sizeof(struct Data));
    2ea2:	e8 59 f5 ff ff       	call   2400 <calloc@plt>
            data[0].id = dataid++;
    2ea7:	41 8d 74 24 01       	lea    0x1(%r12),%esi
            data[0].b = y;
    2eac:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
            data[0].messages = messages;
    2eb1:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
            data[1].id = dataid++;
    2eb6:	41 89 b6 a8 06 00 00 	mov    %esi,0x6a8(%r14)
            mailboxes[b].higher = &data[1];
    2ebd:	49 8d b6 80 03 00 00 	lea    0x380(%r14),%rsi
            mailboxes[b].pending_lower = NULL;
    2ec4:	66 0f ef ed          	pxor   %xmm5,%xmm5
            data[0].messages_count = 0;
    2ec8:	66 0f 6f 35 f0 5d 00 00 	movdqa 0x5df0(%rip),%xmm6        # 8cc0 <_IO_stdin_used+0xcc0>
            data[0].kind = MAILBOX_LOWER;
    2ed0:	41 c7 86 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r14)
            data[0].a = x;
    2edb:	45 89 be 1c 03 00 00 	mov    %r15d,0x31c(%r14)
            data[0].b = y;
    2ee2:	45 89 86 20 03 00 00 	mov    %r8d,0x320(%r14)
            data[0].c = b;
    2ee9:	41 89 9e 24 03 00 00 	mov    %ebx,0x324(%r14)
            data[1].kind = MAILBOX_HIGHER;
    2ef0:	41 c7 86 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r14)
            data[1].a = x;
    2efb:	45 89 be 9c 06 00 00 	mov    %r15d,0x69c(%r14)
            data[1].b = y;
    2f02:	45 89 86 a0 06 00 00 	mov    %r8d,0x6a0(%r14)
            data[1].c = b;
    2f09:	41 89 9e a4 06 00 00 	mov    %ebx,0x6a4(%r14)
            mailboxes[b].lower = &data[0];
    2f10:	4d 89 75 00          	mov    %r14,0x0(%r13)
            mailboxes[b].my_lower = &data[0];
    2f14:	4d 89 75 28          	mov    %r14,0x28(%r13)
            mailboxes[b].higher = &data[1];
    2f18:	49 89 75 08          	mov    %rsi,0x8(%r13)
            data[0].finished_reading = 1;
    2f1c:	41 c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r14)
            data[1].finished_reading = 1;
    2f27:	41 c7 86 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r14)
            mailboxes[b].my_higher = &data[1];
    2f32:	49 89 75 30          	mov    %rsi,0x30(%r13)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2f36:	41 c7 45 38 02 00 00 00 	movl   $0x2,0x38(%r13)
            stack[0] = mailboxes[b].lower;
    2f3e:	4c 89 30             	mov    %r14,(%rax)
            stack[1] = mailboxes[b].higher;
    2f41:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2f45:	49 89 45 20          	mov    %rax,0x20(%r13)
            data[0].available_sending = 0;
    2f49:	41 c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r14)
            data[0].available_receiving = 0;
    2f54:	41 c7 86 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r14)
            data[0].messages = messages;
    2f5f:	49 89 16             	mov    %rdx,(%r14)
            data[1].messages = messages2;
    2f62:	49 89 ae 80 03 00 00 	mov    %rbp,0x380(%r14)
            data[1].available_sending = 1;
    2f69:	41 c7 86 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r14)
            data[1].available_receiving = 0;
    2f74:	41 c7 86 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r14)
            data[0].id = dataid++;
    2f7f:	45 89 a6 28 03 00 00 	mov    %r12d,0x328(%r14)
            data[1].id = dataid++;
    2f86:	41 83 c4 02          	add    $0x2,%r12d
            mailboxes[b].pending_lower = NULL;
    2f8a:	41 0f 11 6d 10       	movups %xmm5,0x10(%r13)
            data[0].messages_count = 0;
    2f8f:	41 0f 29 b6 80 00 00 00 	movaps %xmm6,0x80(%r14)
            data[1].messages_count = 0;
    2f97:	41 0f 29 b6 00 04 00 00 	movaps %xmm6,0x400(%r14)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2f9f:	83 c3 01             	add    $0x1,%ebx
    2fa2:	49 83 c5 40          	add    $0x40,%r13
    2fa6:	83 fb 06             	cmp    $0x6,%ebx
    2fa9:	0f 85 89 fe ff ff    	jne    2e38 <main+0x7c8>
          char *message = malloc(sizeof(char) * 256);
    2faf:	be 01 00 00 00       	mov    $0x1,%esi
    2fb4:	bf 00 01 00 00       	mov    $0x100,%edi
    2fb9:	44 89 c5             	mov    %r8d,%ebp
    2fbc:	44 89 fb             	mov    %r15d,%ebx
    2fbf:	44 8b 7c 24 08       	mov    0x8(%rsp),%r15d
    2fc4:	e8 37 f4 ff ff       	call   2400 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2fc9:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2fce:	49 89 c5             	mov    %rax,%r13
          struct Message *messaged = malloc(sizeof(struct Message));
    2fd1:	e8 9a f4 ff ff       	call   2470 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2fd6:	48 83 ec 08          	sub    $0x8,%rsp
    2fda:	4c 89 ef             	mov    %r13,%rdi
    2fdd:	41 89 e9             	mov    %ebp,%r9d
    2fe0:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2fe5:	41 89 d8             	mov    %ebx,%r8d
    2fe8:	ba 00 01 00 00       	mov    $0x100,%edx
    2fed:	31 c0                	xor    %eax,%eax
    2fef:	41 57                	push   %r15
    2ff1:	48 8d 0d d0 57 00 00 	lea    0x57d0(%rip),%rcx        # 87c8 <_IO_stdin_used+0x7c8>
    2ff8:	be 01 00 00 00       	mov    $0x1,%esi
    2ffd:	e8 9e f5 ff ff       	call   25a0 <__sprintf_chk@plt>
          messaged->message = message;
    3002:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
          messaged->thread_index = thread_data[x].real_thread_index;
    3007:	4c 8b 74 24 60       	mov    0x60(%rsp),%r14
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    300c:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->task_index = y;
    3011:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
          thread_data[x].tasks[y].swap = swap;
    3016:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    301b:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].swap = swap;
    3020:	49 8b 4e 38          	mov    0x38(%r14),%rcx
          messaged->message = message;
    3024:	4d 89 2a             	mov    %r13,(%r10)
          messaged->task_index = y;
    3027:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    302b:	49 63 46 08          	movslq 0x8(%r14),%rax
          thread_data[x].tasks[y].swap = swap;
    302f:	48 01 ca             	add    %rcx,%rdx
          messaged->group = k;
    3032:	45 89 7a 18          	mov    %r15d,0x18(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    3036:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].swap = swap;
    303a:	8b 44 24 38          	mov    0x38(%rsp),%eax
          thread_data[x].tasks[y].group = k;
    303e:	44 89 ba 94 01 00 00 	mov    %r15d,0x194(%rdx)
          thread_data[x].tasks[y].swap = swap;
    3045:	89 82 98 01 00 00    	mov    %eax,0x198(%rdx)
          swap += 1;
    304b:	83 c0 01             	add    $0x1,%eax
    304e:	89 44 24 38          	mov    %eax,0x38(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3052:	8d 45 01             	lea    0x1(%rbp),%eax
    3055:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    3058:	c7 02 41 00 00 00    	movl   $0x41,(%rdx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    305e:	89 82 90 01 00 00    	mov    %eax,0x190(%rdx)
          thread_data[x].tasks[y].message = messaged;
    3064:	4c 89 92 88 01 00 00 	mov    %r10,0x188(%rdx)
          thread_data[x].tasks[y].sending = 1;
    306b:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
          thread_data[x].tasks[y].snapshot_count = 99;
    3075:	48 c7 82 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rdx)
    3080:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
          thread_data[x].tasks[y].swap = swap;
    3085:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    308a:	e8 71 f3 ff ff       	call   2400 <calloc@plt>
    308f:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    3094:	48 89 82 50 01 00 00 	mov    %rax,0x150(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    309b:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    30a0:	48 c7 82 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    30ab:	48 8b 00             	mov    (%rax),%rax
    30ae:	8b 70 04             	mov    0x4(%rax),%esi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    30b1:	4c 39 f0             	cmp    %r14,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    30b4:	48 89 82 28 01 00 00 	mov    %rax,0x128(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    30bb:	89 b2 30 01 00 00    	mov    %esi,0x130(%rdx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    30c1:	41 5d                	pop    %r13
    30c3:	59                   	pop    %rcx
    30c4:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    30c9:	0f 85 7d 12 00 00    	jne    434c <main+0x1cdc>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    30cf:	66 0f 6f 05 f9 5b 00 00 	movdqa 0x5bf9(%rip),%xmm0        # 8cd0 <_IO_stdin_used+0xcd0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    30d7:	89 6a 04             	mov    %ebp,0x4(%rdx)
          thread_data[x].tasks[y].available = 1;
    30da:	4c 8b 2d 0f 5c 00 00 	mov    0x5c0f(%rip),%r13        # 8cf0 <_IO_stdin_used+0xcf0>
          thread_data[x].tasks[y].arrived = 0;
    30e1:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
          thread_data[x].tasks[y].worker_count = thread_count;
    30eb:	c7 82 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rdx)
          thread_data[x].tasks[y].available = 1;
    30f5:	4c 89 aa 44 01 00 00 	mov    %r13,0x144(%rdx)
          thread_data[x].tasks[y].thread_count = 2;
    30fc:	0f 11 82 34 01 00 00 	movups %xmm0,0x134(%rdx)
          if (y == barrier_count - 1) {
    3103:	83 fd 01             	cmp    $0x1,%ebp
    3106:	0f 84 71 03 00 00    	je     347d <main+0xe0d>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    310c:	85 ed                	test   %ebp,%ebp
    310e:	0f 84 51 03 00 00    	je     3465 <main+0xdf5>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    3114:	4c 8b 4c 24 50       	mov    0x50(%rsp),%r9
    3119:	48 8d 05 b0 36 00 00 	lea    0x36b0(%rip),%rax        # 67d0 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3120:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    3125:	49 89 ce             	mov    %rcx,%r14
    3128:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    312f:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
    3134:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    313f:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3144:	e8 b7 f2 ff ff       	call   2400 <calloc@plt>
    3149:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    314e:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3153:	66 0f 6f bc 24 b0 00 00 00 	movdqa 0xb0(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    315c:	83 44 24 20 01       	addl   $0x1,0x20(%rsp)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3161:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3164:	48 83 c3 10          	add    $0x10,%rbx
    3168:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    316f:	49 89 81 78 ff ff ff 	mov    %rax,-0x88(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3176:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    317b:	83 84 24 80 00 00 00 01 	addl   $0x1,0x80(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3183:	48 8b 00             	mov    (%rax),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    3186:	48 89 5c 24 68       	mov    %rbx,0x68(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    318b:	41 c7 86 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r14)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3196:	49 89 86 28 05 00 00 	mov    %rax,0x528(%r14)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    319d:	41 c7 86 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r14)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    31a8:	41 c7 86 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    31b3:	41 8b 81 2c ff ff ff 	mov    -0xd4(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    31ba:	41 0f 11 be 18 05 00 00 	movups %xmm7,0x518(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    31c2:	41 89 86 30 05 00 00 	mov    %eax,0x530(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    31c9:	8b 44 24 20          	mov    0x20(%rsp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    31cd:	41 c7 86 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r14)
        thread_data[x].tasks[barrier_count].available = 1; 
    31d8:	4d 89 ae 44 05 00 00 	mov    %r13,0x544(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    31df:	39 84 24 94 00 00 00 	cmp    %eax,0x94(%rsp)
    31e6:	0f 85 18 f8 ff ff    	jne    2a04 <main+0x394>
    31ec:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
    31f4:	48 8b ac 24 e0 00 00 00 	mov    0xe0(%rsp),%rbp
    31fc:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    3204:	48 8b 9c 24 e8 00 00 00 	mov    0xe8(%rsp),%rbx
  for (int k = 0 ; k < group_count ; k++) {
    320c:	41 83 c7 01          	add    $0x1,%r15d
    3210:	48 81 c5 b0 01 00 00 	add    $0x1b0,%rbp
    3217:	48 83 c6 18          	add    $0x18,%rsi
    321b:	41 83 ff 03          	cmp    $0x3,%r15d
    321f:	0f 85 93 f7 ff ff    	jne    29b8 <main+0x348>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3225:	be 08 00 00 00       	mov    $0x8,%esi
    322a:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    322f:	31 ed                	xor    %ebp,%ebp
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3231:	e8 ca f1 ff ff       	call   2400 <calloc@plt>
    3236:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    323b:	49 89 c7             	mov    %rax,%r15
    323e:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3240:	49 89 d1             	mov    %rdx,%r9
    3243:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3245:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3249:	45 85 d2             	test   %r10d,%r10d
    324c:	7e 7a                	jle    32c8 <main+0xc58>
    324e:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3252:	4d 63 c2             	movslq %r10d,%r8
    3255:	48 63 cd             	movslq %ebp,%rcx
    3258:	49 c1 e0 09          	shl    $0x9,%r8
    325c:	49 8d 0c cf          	lea    (%r15,%rcx,8),%rcx
    3260:	49 01 f8             	add    %rdi,%r8
    3263:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3268:	48 8b b7 70 01 00 00 	mov    0x170(%rdi),%rsi
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    326f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3276:	48 83 c1 60          	add    $0x60,%rcx
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    327a:	f3 0f 6f 66 40       	movdqu 0x40(%rsi),%xmm4
    327f:	f3 0f 6f 9e 80 00 00 00 	movdqu 0x80(%rsi),%xmm3
    3287:	f3 0f 6f 96 c0 00 00 00 	movdqu 0xc0(%rsi),%xmm2
    328f:	f3 0f 6f 8e 00 01 00 00 	movdqu 0x100(%rsi),%xmm1
    3297:	f3 0f 6f 86 40 01 00 00 	movdqu 0x140(%rsi),%xmm0
    329f:	f3 0f 6f 2e          	movdqu (%rsi),%xmm5
    32a3:	0f 11 61 b0          	movups %xmm4,-0x50(%rcx)
    32a7:	0f 11 59 c0          	movups %xmm3,-0x40(%rcx)
    32ab:	0f 11 69 a0          	movups %xmm5,-0x60(%rcx)
    32af:	0f 11 51 d0          	movups %xmm2,-0x30(%rcx)
    32b3:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    32b7:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    32bb:	49 39 f8             	cmp    %rdi,%r8
    32be:	75 a8                	jne    3268 <main+0xbf8>
    32c0:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    32c4:	8d 6c 8d 00          	lea    0x0(%rbp,%rcx,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    32c8:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    32cf:	85 db                	test   %ebx,%ebx
    32d1:	0f 85 b4 01 00 00    	jne    348b <main+0xe1b>
    32d7:	bb 01 00 00 00       	mov    $0x1,%ebx
    32dc:	e9 64 ff ff ff       	jmp    3245 <main+0xbd5>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    32e1:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    32e5:	49 89 c5             	mov    %rax,%r13
    32e8:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
    32ed:	eb 13                	jmp    3302 <main+0xc92>
    32ef:	90                   	nop
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    32f0:	41 83 c6 01          	add    $0x1,%r14d
    32f4:	49 83 c5 40          	add    $0x40,%r13
    32f8:	41 83 fe 06          	cmp    $0x6,%r14d
    32fc:	0f 84 55 01 00 00    	je     3457 <main+0xde7>
            int group_of = b / threads_per_group;
    3302:	44 89 f3             	mov    %r14d,%ebx
    3305:	31 c0                	xor    %eax,%eax
    3307:	44 89 f2             	mov    %r14d,%edx
    330a:	bf 01 00 00 00       	mov    $0x1,%edi
    330f:	d1 fb                	sar    %ebx
    3311:	48 8d 35 a4 50 00 00 	lea    0x50a4(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    3318:	89 d9                	mov    %ebx,%ecx
    331a:	e8 91 f1 ff ff       	call   24b0 <__printf_chk@plt>
            if (k == group_of) {
    331f:	41 39 df             	cmp    %ebx,%r15d
    3322:	75 cc                	jne    32f0 <main+0xc80>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3324:	be 08 00 00 00       	mov    $0x8,%esi
    3329:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    332e:	49 83 c5 40          	add    $0x40,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3332:	e8 c9 f0 ff ff       	call   2400 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3337:	be 08 00 00 00       	mov    $0x8,%esi
    333c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3341:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3346:	e8 b5 f0 ff ff       	call   2400 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    334b:	be 80 03 00 00       	mov    $0x380,%esi
    3350:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3355:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    335a:	e8 a1 f0 ff ff       	call   2400 <calloc@plt>
              data[0].a = x;
    335f:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
              mailboxes[b].pending_lower = NULL;
    3363:	66 0f ef c9          	pxor   %xmm1,%xmm1
    3367:	44 89 f2             	mov    %r14d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    336a:	49 89 c1             	mov    %rax,%r9
              mailboxes[b].pending_lower = NULL;
    336d:	41 0f 11 4d d0       	movups %xmm1,-0x30(%r13)
    3372:	bf 01 00 00 00       	mov    $0x1,%edi
    3377:	48 8d 35 22 54 00 00 	lea    0x5422(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
              data[0].c = b;
    337e:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
              data[0].kind = MAILBOX_LOWER;
    3385:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].a = x;
    338f:	89 98 1c 03 00 00    	mov    %ebx,0x31c(%rax)
              data[0].b = y;
    3395:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    339b:	41 8d 44 24 01       	lea    0x1(%r12),%eax
              data[1].id = dataid++;
    33a0:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    33a7:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    33ae:	49 89 45 c8          	mov    %rax,-0x38(%r13)
    33b2:	8b 84 24 90 00 00 00 	mov    0x90(%rsp),%eax
              data[0].id = dataid++;
    33b9:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
              data[1].id = dataid++;
    33c0:	41 83 c4 02          	add    $0x2,%r12d
              data[1].c = b;
    33c4:	45 89 b1 a4 06 00 00 	mov    %r14d,0x6a4(%r9)
    33cb:	89 c1                	mov    %eax,%ecx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    33cd:	41 83 c6 01          	add    $0x1,%r14d
              mailboxes[b].lower = &data[0];
    33d1:	4d 89 4d c0          	mov    %r9,-0x40(%r13)
    33d5:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    33d9:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    33db:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].a = x;
    33e6:	41 89 99 9c 06 00 00 	mov    %ebx,0x69c(%r9)
              data[1].b = y;
    33ed:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    33f4:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    33ff:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    340a:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    3412:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    3417:	e8 94 f0 ff ff       	call   24b0 <__printf_chk@plt>
              data[0].messages = messages;
    341c:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3421:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
              data[0].messages_count = 0;
    3426:	66 0f 6f 15 92 58 00 00 	movdqa 0x5892(%rip),%xmm2        # 8cc0 <_IO_stdin_used+0xcc0>
              data[1].messages = messages2;
    342e:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
              data[0].messages = messages;
    3433:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    3436:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    343d:	41 0f 29 91 80 00 00 00 	movaps %xmm2,0x80(%r9)
              data[1].messages_count = 0;
    3445:	41 0f 29 91 00 04 00 00 	movaps %xmm2,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    344d:	41 83 fe 06          	cmp    $0x6,%r14d
    3451:	0f 85 ab fe ff ff    	jne    3302 <main+0xc92>
    3457:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    345b:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    3460:	e9 bb f9 ff ff       	jmp    2e20 <main+0x7b0>
    3465:	48 8d 05 c4 38 00 00 	lea    0x38c4(%rip),%rax        # 6d30 <barriered_work_ingest_andwork>
    346c:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    3471:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    3478:	e9 c6 f7 ff ff       	jmp    2c43 <main+0x5d3>
    347d:	48 8d 05 4c 33 00 00 	lea    0x334c(%rip),%rax        # 67d0 <barriered_work>
    3484:	bd 02 00 00 00       	mov    $0x2,%ebp
    3489:	eb e6                	jmp    3471 <main+0xe01>
  for (int k = 0 ; k < group_count ; k++) {
    348b:	83 c0 02             	add    $0x2,%eax
    348e:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3495:	83 f8 06             	cmp    $0x6,%eax
    3498:	0f 85 a2 fd ff ff    	jne    3240 <main+0xbd0>
    349e:	48 8d 3d 45 4f 00 00 	lea    0x4f45(%rip),%rdi        # 83ea <_IO_stdin_used+0x3ea>
    34a5:	e8 86 ee ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    34aa:	48 8d 35 4e 4f 00 00 	lea    0x4f4e(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    34b1:	48 8d 3d 49 4f 00 00 	lea    0x4f49(%rip),%rdi        # 8401 <_IO_stdin_used+0x401>
    34b8:	e8 33 f0 ff ff       	call   24f0 <fopen@plt>
    34bd:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas_size; x++) {
    34c0:	85 ed                	test   %ebp,%ebp
    34c2:	7e 76                	jle    353a <main+0xeca>
    34c4:	48 63 ed             	movslq %ebp,%rbp
    34c7:	4c 8d 2d 10 4f 00 00 	lea    0x4f10(%rip),%r13        # 83de <_IO_stdin_used+0x3de>
    34ce:	4c 8d 25 4d 4f 00 00 	lea    0x4f4d(%rip),%r12        # 8422 <_IO_stdin_used+0x422>
    34d5:	49 8d 04 ef          	lea    (%r15,%rbp,8),%rax
    34d9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    char * c = calloc(250, sizeof(char));
    34de:	be 01 00 00 00       	mov    $0x1,%esi
    34e3:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    34e8:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    34ec:	e8 0f ef ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    34f1:	4c 89 e9             	mov    %r13,%rcx
    34f4:	ba fa 00 00 00       	mov    $0xfa,%edx
    34f9:	be 01 00 00 00       	mov    $0x1,%esi
    34fe:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    3501:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3505:	48 89 ef             	mov    %rbp,%rdi
    3508:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    350f:	31 c0                	xor    %eax,%eax
    3511:	e8 8a f0 ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3516:	48 89 ea             	mov    %rbp,%rdx
    3519:	4c 89 e6             	mov    %r12,%rsi
    351c:	bf 01 00 00 00       	mov    $0x1,%edi
    3521:	31 c0                	xor    %eax,%eax
    3523:	e8 88 ef ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3528:	4c 89 f6             	mov    %r14,%rsi
    352b:	48 89 ef             	mov    %rbp,%rdi
    352e:	e8 8d ee ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    3533:	4c 39 7c 24 08       	cmp    %r15,0x8(%rsp)
    3538:	75 a4                	jne    34de <main+0xe6e>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    353a:	4c 89 f7             	mov    %r14,%rdi

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    353d:	45 31 f6             	xor    %r14d,%r14d
    3540:	4c 8d 25 05 4f 00 00 	lea    0x4f05(%rip),%r12        # 844c <_IO_stdin_used+0x44c>
  fclose(m1);
    3547:	e8 14 ee ff ff       	call   2360 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    354c:	48 8d 3d b7 4e 00 00 	lea    0x4eb7(%rip),%rdi        # 840a <_IO_stdin_used+0x40a>
    3553:	45 89 f7             	mov    %r14d,%r15d
    3556:	41 89 de             	mov    %ebx,%r14d
    3559:	e8 d2 ed ff ff       	call   2330 <puts@plt>
    355e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3563:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3568:	44 89 fa             	mov    %r15d,%edx
    356b:	48 8d 35 b3 4e 00 00 	lea    0x4eb3(%rip),%rsi        # 8425 <_IO_stdin_used+0x425>
    3572:	31 c0                	xor    %eax,%eax
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    3574:	31 ed                	xor    %ebp,%ebp
    3576:	bf 01 00 00 00       	mov    $0x1,%edi
    357b:	47 8d 2c 3f          	lea    (%r15,%r15,1),%r13d
    357f:	e8 2c ef ff ff       	call   24b0 <__printf_chk@plt>
    3584:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    3589:	44 89 7c 24 18       	mov    %r15d,0x18(%rsp)
    358e:	48 89 d8             	mov    %rbx,%rax
    3591:	89 eb                	mov    %ebp,%ebx
    3593:	48 89 c5             	mov    %rax,%rbp
      int x = (k * threads_per_group) + d;
    3596:	42 8d 0c 2b          	lea    (%rbx,%r13,1),%ecx
    359a:	89 da                	mov    %ebx,%edx
    359c:	48 8d 35 8c 4e 00 00 	lea    0x4e8c(%rip),%rsi        # 842f <_IO_stdin_used+0x42f>
    35a3:	31 c0                	xor    %eax,%eax
    35a5:	bf 01 00 00 00       	mov    $0x1,%edi
    35aa:	45 31 ff             	xor    %r15d,%r15d
    35ad:	e8 fe ee ff ff       	call   24b0 <__printf_chk@plt>
    35b2:	89 5c 24 20          	mov    %ebx,0x20(%rsp)
    35b6:	4c 89 f9             	mov    %r15,%rcx
    35b9:	45 89 ef             	mov    %r13d,%r15d
    35bc:	44 89 74 24 28       	mov    %r14d,0x28(%rsp)
    35c1:	89 ca                	mov    %ecx,%edx
    35c3:	48 8d 35 77 4e 00 00 	lea    0x4e77(%rip),%rsi        # 8441 <_IO_stdin_used+0x441>
    35ca:	bf 01 00 00 00       	mov    $0x1,%edi
    35cf:	31 c0                	xor    %eax,%eax
    35d1:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    35d6:	45 31 ed             	xor    %r13d,%r13d
    35d9:	e8 d2 ee ff ff       	call   24b0 <__printf_chk@plt>
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    35de:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    35e3:	48 c1 e3 09          	shl    $0x9,%rbx
    35e7:	eb 30                	jmp    3619 <main+0xfa9>
    35e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    35f0:	83 fe 01             	cmp    $0x1,%esi
    35f3:	0f 84 9f 00 00 00    	je     3698 <main+0x1028>
    35f9:	44 8b 40 3c          	mov    0x3c(%rax),%r8d
    35fd:	44 89 f2             	mov    %r14d,%edx
    3600:	4c 89 e6             	mov    %r12,%rsi
    3603:	bf 01 00 00 00       	mov    $0x1,%edi
    3608:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    360a:	49 83 c5 01          	add    $0x1,%r13
    360e:	e8 9d ee ff ff       	call   24b0 <__printf_chk@plt>
    3613:	49 83 fd 06          	cmp    $0x6,%r13
    3617:	74 4d                	je     3666 <main+0xff6>
          char * mailbox_kind = calloc(100, sizeof(char));
    3619:	be 01 00 00 00       	mov    $0x1,%esi
    361e:	bf 64 00 00 00       	mov    $0x64,%edi
    3623:	45 89 ee             	mov    %r13d,%r14d
    3626:	e8 d5 ed ff ff       	call   2400 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    362b:	4c 8b 45 38          	mov    0x38(%rbp),%r8
    362f:	4c 89 ef             	mov    %r13,%rdi
          char * mailbox_kind = calloc(100, sizeof(char));
    3632:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3635:	48 c1 e7 06          	shl    $0x6,%rdi
    3639:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3641:	48 01 f8             	add    %rdi,%rax
    3644:	8b 70 38             	mov    0x38(%rax),%esi
    3647:	83 fe 02             	cmp    $0x2,%esi
    364a:	75 a4                	jne    35f0 <main+0xf80>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    364c:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    3656:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3659:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3661:	48 01 f8             	add    %rdi,%rax
    3664:	eb 93                	jmp    35f9 <main+0xf89>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3666:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    366b:	48 83 c1 01          	add    $0x1,%rcx
    366f:	48 83 f9 03          	cmp    $0x3,%rcx
    3673:	0f 85 48 ff ff ff    	jne    35c1 <main+0xf51>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3679:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    367d:	44 8b 74 24 28       	mov    0x28(%rsp),%r14d
    3682:	45 89 fd             	mov    %r15d,%r13d
    3685:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
    368c:	85 db                	test   %ebx,%ebx
    368e:	75 25                	jne    36b5 <main+0x1045>
    3690:	44 89 f3             	mov    %r14d,%ebx
    3693:	e9 fe fe ff ff       	jmp    3596 <main+0xf26>
    3698:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    369e:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    36a5:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    36ad:	48 01 f8             	add    %rdi,%rax
    36b0:	e9 44 ff ff ff       	jmp    35f9 <main+0xf89>
  for (int k = 0 ; k < group_count ; k++) {
    36b5:	48 81 44 24 10 b0 01 00 00 	addq   $0x1b0,0x10(%rsp)
    36be:	44 8b 7c 24 18       	mov    0x18(%rsp),%r15d
    36c3:	41 83 c7 01          	add    $0x1,%r15d
    36c7:	41 83 ff 03          	cmp    $0x3,%r15d
    36cb:	0f 85 97 fe ff ff    	jne    3568 <main+0xef8>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    36d1:	ba 07 00 00 00       	mov    $0x7,%edx
    36d6:	bf 01 00 00 00       	mov    $0x1,%edi
    36db:	31 c0                	xor    %eax,%eax
    36dd:	41 89 df             	mov    %ebx,%r15d
    36e0:	48 8d 35 80 4d 00 00 	lea    0x4d80(%rip),%rsi        # 8467 <_IO_stdin_used+0x467>
    36e7:	e8 c4 ed ff ff       	call   24b0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    36ec:	be 08 00 00 00       	mov    $0x8,%esi
    36f1:	bf 02 00 00 00       	mov    $0x2,%edi
    36f6:	e8 05 ed ff ff       	call   2400 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    36fb:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3700:	be 38 00 00 00       	mov    $0x38,%esi
    my_thread_data[0] = &thread_data[x]; 
    3705:	4c 8d af e8 05 00 00 	lea    0x5e8(%rdi),%r13
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    370c:	48 89 78 08          	mov    %rdi,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3710:	4c 8d a7 d8 00 00 00 	lea    0xd8(%rdi),%r12
    thread_data[x].threads = my_thread_data;
    3717:	48 89 87 00 06 00 00 	mov    %rax,0x600(%rdi)
    my_thread_data[0] = &thread_data[x]; 
    371e:	4c 89 28             	mov    %r13,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3721:	48 8b 47 38          	mov    0x38(%rdi),%rax
    thread_data[x].thread_count = 2;
    3725:	c7 87 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%rdi)
    thread_data[x].thread_index = 0;
    372f:	c7 87 ec 05 00 00 00 00 00 00 	movl   $0x0,0x5ec(%rdi)
    thread_data[x].task_count = total_barrier_count;
    3739:	c7 87 28 06 00 00 03 00 00 00 	movl   $0x3,0x628(%rdi)
    thread_data[n].tasks[0].scheduled = 1;
    3743:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    374d:	48 8b 87 10 01 00 00 	mov    0x110(%rdi),%rax
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3754:	bf 0a 00 00 00       	mov    $0xa,%edi
    thread_data[n].tasks[0].scheduled = 1;
    3759:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3763:	e8 98 ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3768:	be 38 00 00 00       	mov    $0x38,%esi
    376d:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3772:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3775:	e8 86 ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    377a:	be 38 00 00 00       	mov    $0x38,%esi
    377f:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3784:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3787:	e8 74 ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    378c:	be 38 00 00 00       	mov    $0x38,%esi
    3791:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3796:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    379b:	e8 60 ec ff ff       	call   2400 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37a0:	be 08 00 00 00       	mov    $0x8,%esi
    37a5:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37aa:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37af:	e8 4c ec ff ff       	call   2400 <calloc@plt>


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
    37b4:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    37b9:	be 08 00 00 00       	mov    $0x8,%esi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37be:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    37c1:	48 8b 05 30 55 00 00 	mov    0x5530(%rip),%rax        # 8cf8 <_IO_stdin_used+0xcf8>
  thread_data[timer_threadi].type = TIMER;
    37c8:	c7 87 1c 05 00 00 00 00 00 00 	movl   $0x0,0x51c(%rdi)
  thread_data[timer_threadi].task_count = total_barrier_count;
    37d2:	48 89 87 50 05 00 00 	mov    %rax,0x550(%rdi)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    37d9:	bf 0a 00 00 00       	mov    $0xa,%edi
    37de:	e8 1d ec ff ff       	call   2400 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    37e3:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    37e8:	4c 89 60 08          	mov    %r12,0x8(%rax)
    37ec:	48 8d 97 b0 01 00 00 	lea    0x1b0(%rdi),%rdx
    37f3:	48 8d 8f 10 05 00 00 	lea    0x510(%rdi),%rcx
    37fa:	48 89 38             	mov    %rdi,(%rax)
    37fd:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3801:	48 8d 97 88 02 00 00 	lea    0x288(%rdi),%rdx
    3808:	48 8d b7 c0 06 00 00 	lea    0x6c0(%rdi),%rsi
    380f:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3813:	48 8d 97 60 03 00 00 	lea    0x360(%rdi),%rdx
    381a:	48 89 50 20          	mov    %rdx,0x20(%rax)
    381e:	48 8d 97 38 04 00 00 	lea    0x438(%rdi),%rdx
    3825:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3829:	48 8d 97 98 07 00 00 	lea    0x798(%rdi),%rdx
    3830:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3834:	48 89 70 40          	mov    %rsi,0x40(%rax)
    3838:	48 89 50 48          	mov    %rdx,0x48(%rax)
    383c:	ba 06 00 00 00       	mov    $0x6,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3841:	48 89 87 28 05 00 00 	mov    %rax,0x528(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    3848:	4c 89 68 38          	mov    %r13,0x38(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    384c:	48 8b 05 ad 54 00 00 	mov    0x54ad(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3853:	c7 87 40 05 00 00 06 00 00 00 	movl   $0x6,0x540(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    385d:	48 89 87 38 05 00 00 	mov    %rax,0x538(%rdi)
    3864:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3866:	c7 87 14 05 00 00 00 00 00 00 	movl   $0x0,0x514(%rdi)
    3870:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    3875:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    387a:	48 8d 35 f5 4b 00 00 	lea    0x4bf5(%rip),%rsi        # 8476 <_IO_stdin_used+0x476>
    3881:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    3886:	e8 25 ec ff ff       	call   24b0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    388b:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    3890:	48 8d 15 79 0d 00 00 	lea    0xd79(%rip),%rdx        # 4610 <timer_thread>
    3897:	48 8d b5 50 01 00 00 	lea    0x150(%rbp),%rsi
    389e:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    38a2:	e8 29 ec ff ff       	call   24d0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    38a7:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    38ac:	4c 89 f0             	mov    %r14,%rax
    38af:	48 89 d9             	mov    %rbx,%rcx
    38b2:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38b7:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    38bc:	41 ba 02 00 00 00    	mov    $0x2,%r10d
  for (int k = 0 ; k < group_count ; k++) {
    38c2:	45 31 f6             	xor    %r14d,%r14d
    38c5:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
    38ca:	44 89 7c 24 20       	mov    %r15d,0x20(%rsp)
    38cf:	49 89 c7             	mov    %rax,%r15
    for (int d = 0 ; d < threads_per_group ; d++) {
    38d2:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
    38d7:	4d 89 fd             	mov    %r15,%r13
    38da:	43 8d 1c 36          	lea    (%r14,%r14,1),%ebx
    38de:	49 89 cc             	mov    %rcx,%r12
    38e1:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    38e6:	48 89 d5             	mov    %rdx,%rbp
    38e9:	4c 89 7c 24 48       	mov    %r15,0x48(%rsp)
    38ee:	45 89 d7             	mov    %r10d,%r15d
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    38f1:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    38f8:	89 da                	mov    %ebx,%edx
    38fa:	44 89 f1             	mov    %r14d,%ecx
    38fd:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    38ff:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    3906:	48 8d 35 eb 4e 00 00 	lea    0x4eeb(%rip),%rsi        # 87f8 <_IO_stdin_used+0x7f8>
    390d:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    3912:	83 c3 01             	add    $0x1,%ebx
    3915:	e8 96 eb ff ff       	call   24b0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    391a:	48 89 e9             	mov    %rbp,%rcx
    391d:	4c 89 ee             	mov    %r13,%rsi
    3920:	4c 89 e7             	mov    %r12,%rdi
    3923:	48 8d 15 66 28 00 00 	lea    0x2866(%rip),%rdx        # 6190 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    392a:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
    3931:	49 83 c4 08          	add    $0x8,%r12
    3935:	49 83 c5 38          	add    $0x38,%r13
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3939:	e8 92 eb ff ff       	call   24d0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    393e:	48 8b 55 d8          	mov    -0x28(%rbp),%rdx
    3942:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    3947:	be 08 00 00 00       	mov    $0x8,%esi
    394c:	e8 cf e9 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3951:	44 39 fb             	cmp    %r15d,%ebx
    3954:	75 9b                	jne    38f1 <main+0x1281>
  for (int k = 0 ; k < group_count ; k++) {
    3956:	4c 8b 7c 24 48       	mov    0x48(%rsp),%r15
    395b:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    3960:	41 83 c6 01          	add    $0x1,%r14d
    3964:	44 8d 53 02          	lea    0x2(%rbx),%r10d
    3968:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    396d:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3974:	49 83 c7 70          	add    $0x70,%r15
    3978:	48 83 c1 10          	add    $0x10,%rcx
    397c:	41 83 fe 03          	cmp    $0x3,%r14d
    3980:	0f 85 4c ff ff ff    	jne    38d2 <main+0x1262>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    3986:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    398b:	be d8 00 00 00       	mov    $0xd8,%esi
    3990:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3995:	48 8b 05 6c 53 00 00 	mov    0x536c(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    thread_data[x].type = IO;
    399c:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    39a1:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    39a6:	41 c7 86 f4 05 00 00 02 00 00 00 	movl   $0x2,0x5f4(%r14)
    39b1:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    thread_data[x].task_count = 0;
    39b6:	49 89 86 28 06 00 00 	mov    %rax,0x628(%r14)
    thread_data[x].type = IO;
    39bd:	44 8b 7c 24 20       	mov    0x20(%rsp),%r15d
    39c2:	48 8d 6b 40          	lea    0x40(%rbx),%rbp
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39c6:	e8 35 ea ff ff       	call   2400 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    39cb:	be 00 08 00 00       	mov    $0x800,%esi
    39d0:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39d2:	49 89 86 40 06 00 00 	mov    %rax,0x640(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    39d9:	e8 42 eb ff ff       	call   2520 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39de:	be 08 00 00 00       	mov    $0x8,%esi
    39e3:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    39e8:	41 89 86 48 06 00 00 	mov    %eax,0x648(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39ef:	e8 0c ea ff ff       	call   2400 <calloc@plt>
    39f4:	ba 07 00 00 00       	mov    $0x7,%edx
    39f9:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    39fe:	41 c7 86 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3a09:	4c 89 30             	mov    %r14,(%rax)
    3a0c:	48 8d 35 81 4a 00 00 	lea    0x4a81(%rip),%rsi        # 8494 <_IO_stdin_used+0x494>
    thread_data[x].threads = my_thread_data;
    3a13:	49 89 86 00 06 00 00 	mov    %rax,0x600(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3a1a:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3a1e:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3a20:	41 c7 86 ec 05 00 00 07 00 00 00 	movl   $0x7,0x5ec(%r14)
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a2b:	41 be 08 00 00 00    	mov    $0x8,%r14d
    3a31:	e8 7a ea ff ff       	call   24b0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3a36:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3a3b:	4c 89 e9             	mov    %r13,%rcx
    3a3e:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3a42:	48 8d 15 57 1f 00 00 	lea    0x1f57(%rip),%rdx        # 59a0 <io_thread>
    3a49:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3a50:	e8 7b ea ff ff       	call   24d0 <pthread_create@plt>
    3a55:	ba 08 00 00 00       	mov    $0x8,%edx
    3a5a:	48 8d 35 4a 4a 00 00 	lea    0x4a4a(%rip),%rsi        # 84ab <_IO_stdin_used+0x4ab>
    3a61:	31 c0                	xor    %eax,%eax
    3a63:	bf 01 00 00 00       	mov    $0x1,%edi
    3a68:	e8 43 ea ff ff       	call   24b0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a6d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3a72:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    3a77:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    3a7d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3a82:	44 89 f2             	mov    %r14d,%edx
    3a85:	48 8d 35 35 4a 00 00 	lea    0x4a35(%rip),%rsi        # 84c1 <_IO_stdin_used+0x4c1>
    3a8c:	bf 01 00 00 00       	mov    $0x1,%edi
    3a91:	31 c0                	xor    %eax,%eax
    3a93:	e8 18 ea ff ff       	call   24b0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3a98:	be 08 00 00 00       	mov    $0x8,%esi
    3a9d:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3aa2:	48 8b 05 5f 52 00 00 	mov    0x525f(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    thread_data[x].type = EXTERNAL;
    3aa9:	41 c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%r13)
    thread_data[x].task_count = 0;
    3ab1:	49 89 45 40          	mov    %rax,0x40(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3ab5:	e8 46 e9 ff ff       	call   2400 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3aba:	48 8b bc 24 c0 00 00 00 	mov    0xc0(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3ac2:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3ac7:	41 c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3ad2:	49 89 45 50          	mov    %rax,0x50(%r13)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3ad6:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3ad9:	bf 02 00 00 00       	mov    $0x2,%edi
    3ade:	e8 1d e9 ff ff       	call   2400 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3ae3:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3ae8:	4c 89 e9             	mov    %r13,%rcx
    3aeb:	48 89 ef             	mov    %rbp,%rdi
    thread_data[x].threads = my_thread_data;
    3aee:	49 89 45 18          	mov    %rax,0x18(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3af2:	48 8d 15 07 0a 00 00 	lea    0xa07(%rip),%rdx        # 4500 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3af9:	48 83 c5 08          	add    $0x8,%rbp
    3afd:	49 81 c5 d8 00 00 00 	add    $0xd8,%r13
      my_thread_data[n] = &thread_data[n]; 
    3b04:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b07:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3b0c:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3b10:	48 8b 05 d1 51 00 00 	mov    0x51d1(%rip),%rax        # 8ce8 <_IO_stdin_used+0xce8>
    thread_data[x].thread_index = x;
    3b17:	45 89 b5 2c ff ff ff 	mov    %r14d,-0xd4(%r13)
    thread_data[x].thread_count = thread_count;
    3b1e:	49 89 85 50 ff ff ff 	mov    %rax,-0xb0(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b25:	e8 a6 e9 ff ff       	call   24d0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b2a:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3b30:	48 83 84 24 c0 00 00 00 10 	addq   $0x10,0xc0(%rsp)
    3b39:	41 83 fe 08          	cmp    $0x8,%r14d
    3b3d:	75 42                	jne    3b81 <main+0x1511>
    3b3f:	41 be 09 00 00 00    	mov    $0x9,%r14d
    3b45:	e9 38 ff ff ff       	jmp    3a82 <main+0x1412>
        other = (x + 1) % total_threads;
    3b4a:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
        my_thread_data[1] = &thread_data[other]; 
    3b4f:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3b54:	48 89 5c 24 48       	mov    %rbx,0x48(%rsp)
    3b59:	45 31 c0             	xor    %r8d,%r8d
    3b5c:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
        other = (x + 1) % total_threads;
    3b61:	45 89 ee             	mov    %r13d,%r14d
        my_thread_data[1] = &thread_data[other]; 
    3b64:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3b68:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        my_thread_data[0] = &thread_data[x]; 
    3b6c:	4c 89 c8             	mov    %r9,%rax
    3b6f:	e9 1d ef ff ff       	jmp    2a91 <main+0x421>
            CPU_SET(j, sendercpu);
    3b74:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
    3b7c:	e9 a2 ef ff ff       	jmp    2b23 <main+0x4b3>
    3b81:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3b86:	48 8d 2d 51 49 00 00 	lea    0x4951(%rip),%rbp        # 84de <_IO_stdin_used+0x4de>
    3b8d:	4c 8d 68 04          	lea    0x4(%rax),%r13
    3b91:	4c 8d a0 74 08 00 00 	lea    0x874(%rax),%r12
    3b98:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    3b9c:	41 8b 55 00          	mov    0x0(%r13),%edx
    3ba0:	48 89 ee             	mov    %rbp,%rsi
    3ba3:	bf 01 00 00 00       	mov    $0x1,%edi
    3ba8:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3baa:	49 81 c5 d8 00 00 00 	add    $0xd8,%r13
    3bb1:	e8 fa e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bb6:	4d 39 ec             	cmp    %r13,%r12
    3bb9:	75 dd                	jne    3b98 <main+0x1528>
    3bbb:	48 8d 3d 2f 49 00 00 	lea    0x492f(%rip),%rdi        # 84f1 <_IO_stdin_used+0x4f1>
    3bc2:	45 31 ed             	xor    %r13d,%r13d
    3bc5:	4c 8d a4 24 f0 00 00 00 	lea    0xf0(%rsp),%r12
    3bcd:	e8 5e e7 ff ff       	call   2330 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3bd2:	48 8d 2d 36 49 00 00 	lea    0x4936(%rip),%rbp        # 850f <_IO_stdin_used+0x50f>
    void * result; 
    pthread_join(thread[x], &result);
    3bd9:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    3bdd:	4c 89 e6             	mov    %r12,%rsi
    3be0:	e8 7b e9 ff ff       	call   2560 <pthread_join@plt>
    3be5:	44 89 ea             	mov    %r13d,%edx
    3be8:	48 89 ee             	mov    %rbp,%rsi
    3beb:	bf 01 00 00 00       	mov    $0x1,%edi
    3bf0:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3bf2:	49 83 c5 01          	add    $0x1,%r13
    3bf6:	e8 b5 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bfb:	49 83 fd 0a          	cmp    $0xa,%r13
    3bff:	75 d8                	jne    3bd9 <main+0x1569>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c01:	be 08 00 00 00       	mov    $0x8,%esi
    3c06:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3c0b:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c0d:	e8 ee e7 ff ff       	call   2400 <calloc@plt>
    3c12:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3c17:	48 89 c5             	mov    %rax,%rbp
    3c1a:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c1c:	49 89 d1             	mov    %rdx,%r9
    3c1f:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c22:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3c26:	45 85 d2             	test   %r10d,%r10d
    3c29:	7e 7c                	jle    3ca7 <main+0x1637>
    3c2b:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3c2f:	4d 63 c2             	movslq %r10d,%r8
    3c32:	48 63 cb             	movslq %ebx,%rcx
    3c35:	49 c1 e0 09          	shl    $0x9,%r8
    3c39:	48 8d 4c cd 00       	lea    0x0(%rbp,%rcx,8),%rcx
    3c3e:	49 01 f8             	add    %rdi,%r8
    3c41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c48:	48 8b b7 70 01 00 00 	mov    0x170(%rdi),%rsi
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c4f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3c56:	48 83 c1 60          	add    $0x60,%rcx
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c5a:	f3 0f 6f 66 40       	movdqu 0x40(%rsi),%xmm4
    3c5f:	f3 0f 6f 9e 80 00 00 00 	movdqu 0x80(%rsi),%xmm3
    3c67:	f3 0f 6f 96 c0 00 00 00 	movdqu 0xc0(%rsi),%xmm2
    3c6f:	f3 0f 6f 8e 00 01 00 00 	movdqu 0x100(%rsi),%xmm1
    3c77:	f3 0f 6f 86 40 01 00 00 	movdqu 0x140(%rsi),%xmm0
    3c7f:	f3 0f 6f 36          	movdqu (%rsi),%xmm6
    3c83:	0f 11 61 b0          	movups %xmm4,-0x50(%rcx)
    3c87:	0f 11 59 c0          	movups %xmm3,-0x40(%rcx)
    3c8b:	0f 11 71 a0          	movups %xmm6,-0x60(%rcx)
    3c8f:	0f 11 51 d0          	movups %xmm2,-0x30(%rcx)
    3c93:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    3c97:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c9b:	4c 39 c7             	cmp    %r8,%rdi
    3c9e:	75 a8                	jne    3c48 <main+0x15d8>
    3ca0:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3ca4:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3ca7:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    3cae:	45 85 db             	test   %r11d,%r11d
    3cb1:	75 08                	jne    3cbb <main+0x164b>
    3cb3:	45 89 fb             	mov    %r15d,%r11d
    3cb6:	e9 67 ff ff ff       	jmp    3c22 <main+0x15b2>
  for (int k = 0 ; k < group_count ; k++) {
    3cbb:	83 c0 02             	add    $0x2,%eax
    3cbe:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3cc5:	83 f8 06             	cmp    $0x6,%eax
    3cc8:	0f 85 4e ff ff ff    	jne    3c1c <main+0x15ac>
    3cce:	48 8d 3d 4e 48 00 00 	lea    0x484e(%rip),%rdi        # 8523 <_IO_stdin_used+0x523>
    3cd5:	e8 56 e6 ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3cda:	48 8d 35 1e 47 00 00 	lea    0x471e(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3ce1:	48 8d 3d 53 48 00 00 	lea    0x4853(%rip),%rdi        # 853b <_IO_stdin_used+0x53b>
    3ce8:	e8 03 e8 ff ff       	call   24f0 <fopen@plt>
    3ced:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas2_size; x++) {
    3cf0:	85 db                	test   %ebx,%ebx
    3cf2:	7e 73                	jle    3d67 <main+0x16f7>
    3cf4:	48 63 db             	movslq %ebx,%rbx
    3cf7:	49 89 ef             	mov    %rbp,%r15
    3cfa:	4c 8d 2d dd 46 00 00 	lea    0x46dd(%rip),%r13        # 83de <_IO_stdin_used+0x3de>
    3d01:	48 8d 6c dd 00       	lea    0x0(%rbp,%rbx,8),%rbp
    3d06:	4c 8d 25 15 47 00 00 	lea    0x4715(%rip),%r12        # 8422 <_IO_stdin_used+0x422>
    char * c = calloc(250, sizeof(char));
    3d0d:	be 01 00 00 00       	mov    $0x1,%esi
    3d12:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3d17:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    3d1b:	e8 e0 e6 ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3d20:	4c 89 e9             	mov    %r13,%rcx
    3d23:	ba fa 00 00 00       	mov    $0xfa,%edx
    3d28:	be 01 00 00 00       	mov    $0x1,%esi
    3d2d:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3d30:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3d34:	48 89 df             	mov    %rbx,%rdi
    3d37:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3d3e:	31 c0                	xor    %eax,%eax
    3d40:	e8 5b e8 ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3d45:	48 89 da             	mov    %rbx,%rdx
    3d48:	4c 89 e6             	mov    %r12,%rsi
    3d4b:	bf 01 00 00 00       	mov    $0x1,%edi
    3d50:	31 c0                	xor    %eax,%eax
    3d52:	e8 59 e7 ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3d57:	4c 89 f6             	mov    %r14,%rsi
    3d5a:	48 89 df             	mov    %rbx,%rdi
    3d5d:	e8 5e e6 ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3d62:	49 39 ef             	cmp    %rbp,%r15
    3d65:	75 a6                	jne    3d0d <main+0x169d>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    3d67:	4c 89 f7             	mov    %r14,%rdi
    3d6a:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    3d70:	31 db                	xor    %ebx,%ebx
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3d72:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    3d7c:	e8 df e5 ff ff       	call   2360 <fclose@plt>
  long sents = 0;
    3d81:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long sends = 0;
    3d8a:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long ingests = 0;
    3d93:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long total = 0;
    3d9c:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  int datas2_size = 0; 
    3da5:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    3dad:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    3db2:	4c 8b b4 24 a8 00 00 00 	mov    0xa8(%rsp),%r14
    3dba:	45 89 e5             	mov    %r12d,%r13d
    3dbd:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    3dc2:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
      int x = (k * threads_per_group) + d;
    3dc7:	44 89 e8             	mov    %r13d,%eax
    3dca:	41 83 c5 01          	add    $0x1,%r13d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3dce:	bf 0a 00 00 00       	mov    $0xa,%edi
        other = abs(x - 1) % total_threads;
    3dd3:	41 f6 c5 01          	test   $0x1,%r13b
    3dd7:	8d 50 02             	lea    0x2(%rax),%edx
    3dda:	0f 44 c2             	cmove  %edx,%eax
    3ddd:	4c 63 e0             	movslq %eax,%r12
    3de0:	e8 2b e5 ff ff       	call   2310 <putchar@plt>
    3de5:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3dea:	bf 01 00 00 00       	mov    $0x1,%edi
    3def:	48 8d 35 4e 47 00 00 	lea    0x474e(%rip),%rsi        # 8544 <_IO_stdin_used+0x544>
    3df6:	48 8b 10             	mov    (%rax),%rdx
    3df9:	31 c0                	xor    %eax,%eax
    3dfb:	e8 b0 e6 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e00:	41 8b 56 40          	mov    0x40(%r14),%edx
    3e04:	85 d2                	test   %edx,%edx
    3e06:	0f 8e 39 05 00 00    	jle    4345 <main+0x1cd5>
    3e0c:	48 63 ca             	movslq %edx,%rcx
    3e0f:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    3e13:	31 d2                	xor    %edx,%edx
    3e15:	48 c1 e1 09          	shl    $0x9,%rcx
    3e19:	48 01 c1             	add    %rax,%rcx
    3e1c:	0f 1f 40 00          	nopl   0x0(%rax)
        v += thread_data[me].tasks[n].v;
    3e20:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e27:	48 05 00 02 00 00    	add    $0x200,%rax
    3e2d:	48 39 c8             	cmp    %rcx,%rax
    3e30:	75 ee                	jne    3e20 <main+0x17b0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3e32:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3e37:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
    3e3b:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3e3f:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3e43:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3e47:	85 c9                	test   %ecx,%ecx
    3e49:	7e 27                	jle    3e72 <main+0x1802>
    3e4b:	48 8b 40 38          	mov    0x38(%rax),%rax
    3e4f:	48 c1 e1 09          	shl    $0x9,%rcx
    3e53:	48 01 c1             	add    %rax,%rcx
    3e56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3e60:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3e67:	48 05 00 02 00 00    	add    $0x200,%rax
    3e6d:	48 39 c8             	cmp    %rcx,%rax
    3e70:	75 ee                	jne    3e60 <main+0x17f0>
    3e72:	48 8d 35 e0 46 00 00 	lea    0x46e0(%rip),%rsi        # 8559 <_IO_stdin_used+0x559>
    3e79:	bf 01 00 00 00       	mov    $0x1,%edi
    3e7e:	31 c0                	xor    %eax,%eax
    3e80:	e8 2b e6 ff ff       	call   24b0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3e85:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3e8a:	bf 01 00 00 00       	mov    $0x1,%edi
    3e8f:	48 8d 35 92 49 00 00 	lea    0x4992(%rip),%rsi        # 8828 <_IO_stdin_used+0x828>
    3e96:	48 8b 08             	mov    (%rax),%rcx
    3e99:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3ea3:	48 f7 e9             	imul   %rcx
    3ea6:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3eaa:	31 c0                	xor    %eax,%eax
    3eac:	48 d1 fa             	sar    %rdx
    3eaf:	48 29 ca             	sub    %rcx,%rdx
    3eb2:	e8 f9 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3eb7:	bf 0a 00 00 00       	mov    $0xa,%edi
    3ebc:	e8 4f e4 ff ff       	call   2310 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3ec1:	45 8b 66 40          	mov    0x40(%r14),%r12d
    3ec5:	45 85 e4             	test   %r12d,%r12d
    3ec8:	0f 8e 44 01 00 00    	jle    4012 <main+0x19a2>
    3ece:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    3ed3:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    3ed8:	31 d2                	xor    %edx,%edx
    3eda:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3edf:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3ee4:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    3ee9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        total += thread_data[x].tasks[n].n;
    3ef0:	49 8b 46 38          	mov    0x38(%r14),%rax
    3ef4:	49 89 d1             	mov    %rdx,%r9
        sends += thread_data[x].tasks[n].sends;
    3ef7:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    3efc:	41 89 d5             	mov    %edx,%r13d
        total += thread_data[x].tasks[n].n;
    3eff:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    3f03:	45 31 e4             	xor    %r12d,%r12d
        total += thread_data[x].tasks[n].n;
    3f06:	4c 01 c8             	add    %r9,%rax
        sends += thread_data[x].tasks[n].sends;
    3f09:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
        total += thread_data[x].tasks[n].n;
    3f0e:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
        ingests += thread_data[x].tasks[n].ingest_count;
    3f15:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
        sends += thread_data[x].tasks[n].sends;
    3f1c:	48 03 b8 78 01 00 00 	add    0x178(%rax),%rdi
    3f23:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    3f28:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3f2d:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3f32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3f38:	8b 54 24 08          	mov    0x8(%rsp),%edx
    3f3c:	45 89 e0             	mov    %r12d,%r8d
    3f3f:	44 89 e9             	mov    %r13d,%ecx
    3f42:	bf 01 00 00 00       	mov    $0x1,%edi
    3f47:	48 8d 35 18 46 00 00 	lea    0x4618(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    3f4e:	31 c0                	xor    %eax,%eax
    3f50:	e8 5b e5 ff ff       	call   24b0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f55:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    3f5a:	4c 89 e0             	mov    %r12,%rax
    3f5d:	45 89 e0             	mov    %r12d,%r8d
    3f60:	49 8b 56 38          	mov    0x38(%r14),%rdx
    3f64:	48 c1 e0 06          	shl    $0x6,%rax
    3f68:	48 83 ec 08          	sub    $0x8,%rsp
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3f6c:	49 83 c4 01          	add    $0x1,%r12
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f70:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    3f78:	48 8b 38             	mov    (%rax),%rdi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3f7b:	48 8b 70 08          	mov    0x8(%rax),%rsi
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3f7f:	48 8b 87 10 03 00 00 	mov    0x310(%rdi),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3f86:	48 8b 96 08 03 00 00 	mov    0x308(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3f8d:	48 8b b6 10 03 00 00 	mov    0x310(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f94:	48 8b 8f 08 03 00 00 	mov    0x308(%rdi),%rcx
    3f9b:	bf 01 00 00 00       	mov    $0x1,%edi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3fa0:	48 01 c3             	add    %rax,%rbx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3fa3:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fa6:	49 01 cf             	add    %rcx,%r15
    3fa9:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3fad:	48 01 f3             	add    %rsi,%rbx
    3fb0:	50                   	push   %rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3fb1:	49 01 d7             	add    %rdx,%r15
    3fb4:	8b 54 24 18          	mov    0x18(%rsp),%edx
    3fb8:	44 89 e9             	mov    %r13d,%ecx
    3fbb:	48 8d 35 86 48 00 00 	lea    0x4886(%rip),%rsi        # 8848 <_IO_stdin_used+0x848>
    3fc2:	31 c0                	xor    %eax,%eax
    3fc4:	e8 e7 e4 ff ff       	call   24b0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3fc9:	41 5a                	pop    %r10
    3fcb:	41 5b                	pop    %r11
    3fcd:	49 83 fc 06          	cmp    $0x6,%r12
    3fd1:	0f 85 61 ff ff ff    	jne    3f38 <main+0x18c8>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3fd7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    3fdc:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    3fe1:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3fe6:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3feb:	48 83 c2 01          	add    $0x1,%rdx
    3fef:	41 39 56 40          	cmp    %edx,0x40(%r14)
    3ff3:	0f 8f f7 fe ff ff    	jg     3ef0 <main+0x1880>
    3ff9:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    3ffe:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    4003:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    4008:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    400d:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    4012:	45 31 ff             	xor    %r15d,%r15d
    4015:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    401d:	4c 8d 25 44 48 00 00 	lea    0x4844(%rip),%r12        # 8868 <_IO_stdin_used+0x868>
    4024:	7e 62                	jle    4088 <main+0x1a18>
    4026:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4030:	49 8b 86 90 00 00 00 	mov    0x90(%r14),%rax
    4037:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    403b:	48 83 ec 08          	sub    $0x8,%rsp
    403f:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    4044:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4048:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    404c:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    4050:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    4054:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4057:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    405b:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    405e:	48 f7 e5             	mul    %rbp
    4061:	8b 49 20             	mov    0x20(%rcx),%ecx
    4064:	56                   	push   %rsi
    4065:	31 c0                	xor    %eax,%eax
    4067:	4c 89 e6             	mov    %r12,%rsi
    406a:	48 c1 ea 12          	shr    $0x12,%rdx
    406e:	49 89 d1             	mov    %rdx,%r9
    4071:	ba 02 00 00 00       	mov    $0x2,%edx
    4076:	e8 35 e4 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    407b:	41 58                	pop    %r8
    407d:	41 59                	pop    %r9
    407f:	4d 39 be a0 00 00 00 	cmp    %r15,0xa0(%r14)
    4086:	7f a8                	jg     4030 <main+0x19c0>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4088:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    408f:	85 d2                	test   %edx,%edx
    4091:	0f 8e 0a 01 00 00    	jle    41a1 <main+0x1b31>
    4097:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    409c:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    40a0:	45 31 ff             	xor    %r15d,%r15d
    40a3:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    40a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    40b0:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    40b4:	44 89 fb             	mov    %r15d,%ebx
    40b7:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    40bf:	8b 30                	mov    (%rax),%esi
    40c1:	85 f6                	test   %esi,%esi
    40c3:	0f 8e c1 00 00 00    	jle    418a <main+0x1b1a>
    40c9:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    40ce:	31 d2                	xor    %edx,%edx
    40d0:	48 8b 48 08          	mov    0x8(%rax),%rcx
    40d4:	49 89 f8             	mov    %rdi,%r8
    40d7:	48 89 d7             	mov    %rdx,%rdi
    40da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    40e0:	49 89 fc             	mov    %rdi,%r12
    40e3:	45 31 ff             	xor    %r15d,%r15d
    40e6:	49 c1 e4 08          	shl    $0x8,%r12
    40ea:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    40ee:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    40f4:	85 d2                	test   %edx,%edx
    40f6:	7e 77                	jle    416f <main+0x1aff>
    40f8:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    40fd:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4100:	4c 89 f9             	mov    %r15,%rcx
    4103:	48 83 ec 08          	sub    $0x8,%rsp
    4107:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    410c:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4110:	48 c1 e1 05          	shl    $0x5,%rcx
    4114:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    411b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    411f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    4123:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4126:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    412a:	4c 2b 01             	sub    (%rcx),%r8
    412d:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    412e:	48 f7 e5             	mul    %rbp
    4131:	89 d9                	mov    %ebx,%ecx
    4133:	48 8d 35 7e 47 00 00 	lea    0x477e(%rip),%rsi        # 88b8 <_IO_stdin_used+0x8b8>
    413a:	31 c0                	xor    %eax,%eax
    413c:	48 c1 ea 12          	shr    $0x12,%rdx
    4140:	49 89 d1             	mov    %rdx,%r9
    4143:	ba 02 00 00 00       	mov    $0x2,%edx
    4148:	e8 63 e3 ff ff       	call   24b0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    414d:	4d 8b 46 50          	mov    0x50(%r14),%r8
    4151:	5e                   	pop    %rsi
    4152:	5f                   	pop    %rdi
    4153:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    4157:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    415b:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    415f:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    4166:	7f 98                	jg     4100 <main+0x1a90>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4168:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    416d:	8b 32                	mov    (%rdx),%esi
    416f:	48 83 c7 01          	add    $0x1,%rdi
    4173:	39 fe                	cmp    %edi,%esi
    4175:	0f 8f 65 ff ff ff    	jg     40e0 <main+0x1a70>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    417b:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    4180:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    4187:	4c 89 c7             	mov    %r8,%rdi
    418a:	49 83 c7 01          	add    $0x1,%r15
    418e:	44 39 fa             	cmp    %r15d,%edx
    4191:	0f 8f 19 ff ff ff    	jg     40b0 <main+0x1a40>
    4197:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    419c:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    41a1:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    41a7:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    41ae:	44 39 6c 24 48       	cmp    %r13d,0x48(%rsp)
    41b3:	0f 85 0e fc ff ff    	jne    3dc7 <main+0x1757>
  for (int k = 0 ; k < group_count ; k++) {
    41b9:	48 83 84 24 98 00 00 00 30 	addq   $0x30,0x98(%rsp)
    41c2:	44 8b 44 24 48       	mov    0x48(%rsp),%r8d
    41c7:	48 81 84 24 a8 00 00 00 b0 01 00 00 	addq   $0x1b0,0xa8(%rsp)
    41d3:	41 83 f8 05          	cmp    $0x5,%r8d
    41d7:	74 08                	je     41e1 <main+0x1b71>
    41d9:	45 89 c4             	mov    %r8d,%r12d
    41dc:	e9 c4 fb ff ff       	jmp    3da5 <main+0x1735>
    41e1:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    41e6:	bf 01 00 00 00       	mov    $0x1,%edi
    41eb:	31 c0                	xor    %eax,%eax
    41ed:	49 89 df             	mov    %rbx,%r15
    41f0:	48 8d 35 7f 43 00 00 	lea    0x437f(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    41f7:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4201:	4c 89 f2             	mov    %r14,%rdx
    4204:	e8 a7 e2 ff ff       	call   24b0 <__printf_chk@plt>
    4209:	bf 0a 00 00 00       	mov    $0xa,%edi
    420e:	e8 fd e0 ff ff       	call   2310 <putchar@plt>
    4213:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
    421b:	48 8d 35 ee 46 00 00 	lea    0x46ee(%rip),%rsi        # 8910 <_IO_stdin_used+0x910>
    4222:	31 c0                	xor    %eax,%eax
    4224:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    4228:	bf 01 00 00 00       	mov    $0x1,%edi
    422d:	e8 7e e2 ff ff       	call   24b0 <__printf_chk@plt>
    4232:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    4237:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    423c:	48 8d 35 f5 46 00 00 	lea    0x46f5(%rip),%rsi        # 8938 <_IO_stdin_used+0x938>
    4243:	48 f7 eb             	imul   %rbx
    4246:	48 c1 ff 3f          	sar    $0x3f,%rdi
    424a:	31 c0                	xor    %eax,%eax
    424c:	48 d1 fa             	sar    %rdx
    424f:	48 29 fa             	sub    %rdi,%rdx
    4252:	bf 01 00 00 00       	mov    $0x1,%edi
    4257:	e8 54 e2 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    425c:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4261:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    4266:	48 8d 35 fb 46 00 00 	lea    0x46fb(%rip),%rsi        # 8968 <_IO_stdin_used+0x968>
    426d:	48 f7 eb             	imul   %rbx
    4270:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4274:	31 c0                	xor    %eax,%eax
    4276:	48 d1 fa             	sar    %rdx
    4279:	48 29 fa             	sub    %rdi,%rdx
    427c:	bf 01 00 00 00       	mov    $0x1,%edi
    4281:	e8 2a e2 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    4286:	4c 89 f0             	mov    %r14,%rax
    4289:	bf 01 00 00 00       	mov    $0x1,%edi
    428e:	48 8d 35 03 47 00 00 	lea    0x4703(%rip),%rsi        # 8998 <_IO_stdin_used+0x998>
    4295:	48 f7 eb             	imul   %rbx
    4298:	4c 89 f0             	mov    %r14,%rax
    429b:	48 c1 f8 3f          	sar    $0x3f,%rax
    429f:	48 d1 fa             	sar    %rdx
    42a2:	48 29 c2             	sub    %rax,%rdx
    42a5:	31 c0                	xor    %eax,%eax
    42a7:	e8 04 e2 ff ff       	call   24b0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    42ac:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    42b1:	bf 01 00 00 00       	mov    $0x1,%edi
    42b6:	48 8d 35 cd 42 00 00 	lea    0x42cd(%rip),%rsi        # 858a <_IO_stdin_used+0x58a>
    42bd:	48 f7 eb             	imul   %rbx
    42c0:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    42c5:	48 c1 f8 3f          	sar    $0x3f,%rax
    42c9:	48 d1 fa             	sar    %rdx
    42cc:	48 29 c2             	sub    %rax,%rdx
    42cf:	31 c0                	xor    %eax,%eax
    42d1:	48 89 d5             	mov    %rdx,%rbp
    42d4:	e8 d7 e1 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
    42d9:	4c 89 f8             	mov    %r15,%rax
    42dc:	bf 01 00 00 00       	mov    $0x1,%edi
    42e1:	48 8d 35 d0 46 00 00 	lea    0x46d0(%rip),%rsi        # 89b8 <_IO_stdin_used+0x9b8>
    42e8:	48 f7 eb             	imul   %rbx
    42eb:	4c 89 f8             	mov    %r15,%rax
    42ee:	48 c1 f8 3f          	sar    $0x3f,%rax
    42f2:	48 89 d3             	mov    %rdx,%rbx
    42f5:	48 d1 fb             	sar    %rbx
    42f8:	48 29 c3             	sub    %rax,%rbx
    42fb:	31 c0                	xor    %eax,%eax
    42fd:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    4300:	48 29 eb             	sub    %rbp,%rbx
    4303:	e8 a8 e1 ff ff       	call   24b0 <__printf_chk@plt>
    4308:	31 c0                	xor    %eax,%eax
    430a:	48 89 da             	mov    %rbx,%rdx
    430d:	bf 01 00 00 00       	mov    $0x1,%edi
    4312:	48 8d 35 8d 42 00 00 	lea    0x428d(%rip),%rsi        # 85a6 <_IO_stdin_used+0x5a6>
    4319:	e8 92 e1 ff ff       	call   24b0 <__printf_chk@plt>
  return 0;

}
    431e:	48 8b 84 24 f8 00 00 00 	mov    0xf8(%rsp),%rax
    4326:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    432f:	75 25                	jne    4356 <main+0x1ce6>
    4331:	48 81 c4 08 01 00 00 	add    $0x108,%rsp
    4338:	31 c0                	xor    %eax,%eax
    433a:	5b                   	pop    %rbx
    433b:	5d                   	pop    %rbp
    433c:	41 5c                	pop    %r12
    433e:	41 5d                	pop    %r13
    4340:	41 5e                	pop    %r14
    4342:	41 5f                	pop    %r15
    4344:	c3                   	ret
      long v = 0;
    4345:	31 d2                	xor    %edx,%edx
    4347:	e9 e6 fa ff ff       	jmp    3e32 <main+0x17c2>
            exit(1);
    434c:	bf 01 00 00 00       	mov    $0x1,%edi
    4351:	e8 ba e1 ff ff       	call   2510 <exit@plt>
}
    4356:	e8 25 e0 ff ff       	call   2380 <__stack_chk_fail@plt>
    435b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004360 <_start>:
    4360:	f3 0f 1e fa          	endbr64
    4364:	31 ed                	xor    %ebp,%ebp
    4366:	49 89 d1             	mov    %rdx,%r9
    4369:	5e                   	pop    %rsi
    436a:	48 89 e2             	mov    %rsp,%rdx
    436d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4371:	50                   	push   %rax
    4372:	54                   	push   %rsp
    4373:	45 31 c0             	xor    %r8d,%r8d
    4376:	31 c9                	xor    %ecx,%ecx
    4378:	48 8d 3d f1 e2 ff ff 	lea    -0x1d0f(%rip),%rdi        # 2670 <main>
    437f:	ff 15 53 6c 00 00    	call   *0x6c53(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    4385:	f4                   	hlt
    4386:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004390 <deregister_tm_clones>:
    4390:	48 8d 3d 89 6c 00 00 	lea    0x6c89(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4397:	48 8d 05 82 6c 00 00 	lea    0x6c82(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    439e:	48 39 f8             	cmp    %rdi,%rax
    43a1:	74 15                	je     43b8 <deregister_tm_clones+0x28>
    43a3:	48 8b 05 36 6c 00 00 	mov    0x6c36(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    43aa:	48 85 c0             	test   %rax,%rax
    43ad:	74 09                	je     43b8 <deregister_tm_clones+0x28>
    43af:	ff e0                	jmp    *%rax
    43b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    43b8:	c3                   	ret
    43b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000043c0 <register_tm_clones>:
    43c0:	48 8d 3d 59 6c 00 00 	lea    0x6c59(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    43c7:	48 8d 35 52 6c 00 00 	lea    0x6c52(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    43ce:	48 29 fe             	sub    %rdi,%rsi
    43d1:	48 89 f0             	mov    %rsi,%rax
    43d4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    43d8:	48 c1 f8 03          	sar    $0x3,%rax
    43dc:	48 01 c6             	add    %rax,%rsi
    43df:	48 d1 fe             	sar    %rsi
    43e2:	74 14                	je     43f8 <register_tm_clones+0x38>
    43e4:	48 8b 05 05 6c 00 00 	mov    0x6c05(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    43eb:	48 85 c0             	test   %rax,%rax
    43ee:	74 08                	je     43f8 <register_tm_clones+0x38>
    43f0:	ff e0                	jmp    *%rax
    43f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    43f8:	c3                   	ret
    43f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004400 <__do_global_dtors_aux>:
    4400:	f3 0f 1e fa          	endbr64
    4404:	80 3d 1d 6c 00 00 00 	cmpb   $0x0,0x6c1d(%rip)        # b028 <completed.0>
    440b:	75 2b                	jne    4438 <__do_global_dtors_aux+0x38>
    440d:	55                   	push   %rbp
    440e:	48 83 3d e2 6b 00 00 00 	cmpq   $0x0,0x6be2(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    4416:	48 89 e5             	mov    %rsp,%rbp
    4419:	74 0c                	je     4427 <__do_global_dtors_aux+0x27>
    441b:	48 8b 3d e6 6b 00 00 	mov    0x6be6(%rip),%rdi        # b008 <__dso_handle>
    4422:	e8 c9 de ff ff       	call   22f0 <__cxa_finalize@plt>
    4427:	e8 64 ff ff ff       	call   4390 <deregister_tm_clones>
    442c:	c6 05 f5 6b 00 00 01 	movb   $0x1,0x6bf5(%rip)        # b028 <completed.0>
    4433:	5d                   	pop    %rbp
    4434:	c3                   	ret
    4435:	0f 1f 00             	nopl   (%rax)
    4438:	c3                   	ret
    4439:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004440 <frame_dummy>:
    4440:	f3 0f 1e fa          	endbr64
    4444:	e9 77 ff ff ff       	jmp    43c0 <register_tm_clones>
    4449:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004450 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4450:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    4454:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    445b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    445f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4467:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    446b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    446f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4476:	48 85 c9             	test   %rcx,%rcx
    4479:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4480:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4484:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4488:	31 c0                	xor    %eax,%eax
    448a:	c3                   	ret
    448b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004490 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4490:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4494:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    449b:	85 c9                	test   %ecx,%ecx
    449d:	7e 4f                	jle    44ee <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    449f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    44a6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    44ad:	48 c1 e1 09          	shl    $0x9,%rcx
    44b1:	48 8b 50 18          	mov    0x18(%rax),%rdx
    44b5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    44b9:	48 8b 70 38          	mov    0x38(%rax),%rsi
    44bd:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    44bf:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    44c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    44c8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    44d0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    44d8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    44e3:	48 05 00 02 00 00    	add    $0x200,%rax
    44e9:	48 39 c1             	cmp    %rax,%rcx
    44ec:	75 da                	jne    44c8 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    44ee:	0f ae f8             	sfence
}
    44f1:	31 c0                	xor    %eax,%eax
    44f3:	c3                   	ret
    44f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    44ff:	90                   	nop

0000000000004500 <external_thread>:
void * external_thread(void *arg) {
    4500:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    4504:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4508:	0f 85 fb 00 00 00    	jne    4609 <external_thread+0x109>
void * external_thread(void *arg) {
    450e:	41 57                	push   %r15
    4510:	49 89 ff             	mov    %rdi,%r15
    4513:	41 56                	push   %r14
    4515:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    4517:	4c 8d 2d e6 3a 00 00 	lea    0x3ae6(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    451e:	41 54                	push   %r12
    4520:	55                   	push   %rbp
    4521:	53                   	push   %rbx
    4522:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    4526:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    452c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    4530:	85 c9                	test   %ecx,%ecx
    4532:	7e 6e                	jle    45a2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4534:	45 31 e4             	xor    %r12d,%r12d
    4537:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4540:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    4548:	31 db                	xor    %ebx,%ebx
    454a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    454e:	48 8b 06             	mov    (%rsi),%rax
    4551:	8b 10                	mov    (%rax),%edx
    4553:	85 d2                	test   %edx,%edx
    4555:	7e 2a                	jle    4581 <external_thread+0x81>
    4557:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    455b:	48 89 dd             	mov    %rbx,%rbp
    455e:	48 c1 e5 08          	shl    $0x8,%rbp
    4562:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4566:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    456d:	45 85 c0             	test   %r8d,%r8d
    4570:	74 36                	je     45a8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4572:	48 83 c3 01          	add    $0x1,%rbx
    4576:	39 da                	cmp    %ebx,%edx
    4578:	7f e1                	jg     455b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    457a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4581:	49 83 c4 01          	add    $0x1,%r12
    4585:	44 39 e1             	cmp    %r12d,%ecx
    4588:	7f b6                	jg     4540 <external_thread+0x40>
  while (data->running == 1) {
    458a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    458f:	74 9f                	je     4530 <external_thread+0x30>
}
    4591:	48 83 c4 08          	add    $0x8,%rsp
    4595:	31 c0                	xor    %eax,%eax
    4597:	5b                   	pop    %rbx
    4598:	5d                   	pop    %rbp
    4599:	41 5c                	pop    %r12
    459b:	41 5d                	pop    %r13
    459d:	41 5e                	pop    %r14
    459f:	41 5f                	pop    %r15
    45a1:	c3                   	ret
  while (data->running == 1) {
    45a2:	eb fe                	jmp    45a2 <external_thread+0xa2>
    45a4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    45a8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    45ab:	48 8b 06             	mov    (%rsi),%rax
    45ae:	48 8b 78 08          	mov    0x8(%rax),%rdi
    45b2:	48 01 ef             	add    %rbp,%rdi
    45b5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    45bc:	48 c1 e6 05          	shl    $0x5,%rsi
    45c0:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    45c7:	bf 04 00 00 00       	mov    $0x4,%edi
    45cc:	e8 7f dd ff ff       	call   2350 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    45d1:	49 8b 47 50          	mov    0x50(%r15),%rax
    45d5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    45d9:	48 8b 40 08          	mov    0x8(%rax),%rax
    45dd:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    45e8:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    45eb:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    45ef:	48 83 c3 01          	add    $0x1,%rbx
    45f3:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    45f7:	48 8b 06             	mov    (%rsi),%rax
    45fa:	8b 10                	mov    (%rax),%edx
    45fc:	39 da                	cmp    %ebx,%edx
    45fe:	0f 8f 53 ff ff ff    	jg     4557 <external_thread+0x57>
    4604:	e9 71 ff ff ff       	jmp    457a <external_thread+0x7a>
}
    4609:	31 c0                	xor    %eax,%eax
    460b:	c3                   	ret
    460c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004610 <timer_thread>:
void* timer_thread(void *arg) {
    4610:	f3 0f 1e fa          	endbr64
    4614:	41 57                	push   %r15
    4616:	48 8d 35 f3 39 00 00 	lea    0x39f3(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    461d:	49 89 ff             	mov    %rdi,%r15
    4620:	41 56                	push   %r14
    4622:	41 55                	push   %r13
    4624:	41 54                	push   %r12
    4626:	55                   	push   %rbp
    4627:	53                   	push   %rbx
    4628:	48 83 ec 58          	sub    $0x58,%rsp
    462c:	8b 57 04             	mov    0x4(%rdi),%edx
    462f:	bf 01 00 00 00       	mov    $0x1,%edi
    4634:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    463d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    4642:	31 c0                	xor    %eax,%eax
    4644:	e8 67 de ff ff       	call   24b0 <__printf_chk@plt>
  struct timespec preempt = {
    4649:	66 0f 6f 05 7f 45 00 00 	movdqa 0x457f(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4651:	ba 88 13 00 00       	mov    $0x1388,%edx
    4656:	31 c0                	xor    %eax,%eax
    4658:	48 8d 35 c3 39 00 00 	lea    0x39c3(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    465f:	bf 01 00 00 00       	mov    $0x1,%edi
    4664:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4669:	e8 42 de ff ff       	call   24b0 <__printf_chk@plt>
  while (data->running && n < times) {
    466e:	41 8b 47 44          	mov    0x44(%r15),%eax
    4672:	89 c3                	mov    %eax,%ebx
    4674:	85 c0                	test   %eax,%eax
    4676:	0f 84 9a 00 00 00    	je     4716 <timer_thread+0x106>
  int n = 0;
    467c:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    467f:	31 db                	xor    %ebx,%ebx
    4681:	49 89 e5             	mov    %rsp,%r13
    y++;
    4684:	31 ed                	xor    %ebp,%ebp
    4686:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    nanosleep(&preempt , &rem2);
    468b:	4c 89 e7             	mov    %r12,%rdi
    468e:	4c 89 ee             	mov    %r13,%rsi
    n++;
    4691:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    4695:	e8 06 dd ff ff       	call   23a0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    469a:	49 63 47 30          	movslq 0x30(%r15),%rax
    y++;
    469e:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46a1:	85 c0                	test   %eax,%eax
    46a3:	7e 4a                	jle    46ef <timer_thread+0xdf>
    46a5:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    46a9:	4c 63 c3             	movslq %ebx,%r8
    46ac:	49 c1 e0 09          	shl    $0x9,%r8
    46b0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    46b4:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    46b8:	48 8b 19             	mov    (%rcx),%rbx
    46bb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46bd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    46c1:	99                   	cltd
    46c2:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    46c5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    46c9:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    46cc:	48 63 d2             	movslq %edx,%rdx
    46cf:	48 c1 e2 09          	shl    $0x9,%rdx
    46d3:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    46de:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46ea:	49 39 c9             	cmp    %rcx,%r9
    46ed:	75 c9                	jne    46b8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    46ef:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    46f2:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
    46f6:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    y++;
    46fa:	89 fb                	mov    %edi,%ebx
    if (y >= data->threads[0]->task_count) {
    46fc:	48 8b 00             	mov    (%rax),%rax
    y++;
    46ff:	39 78 40             	cmp    %edi,0x40(%rax)
    4702:	0f 4e dd             	cmovle %ebp,%ebx
  while (data->running && n < times) {
    4705:	85 c9                	test   %ecx,%ecx
    4707:	74 0d                	je     4716 <timer_thread+0x106>
    4709:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    4710:	0f 85 75 ff ff ff    	jne    468b <timer_thread+0x7b>
    4716:	48 8d 3d 1b 39 00 00 	lea    0x391b(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    471d:	e8 0e dc ff ff       	call   2330 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    4722:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4726:	85 d2                	test   %edx,%edx
    4728:	7e 6b                	jle    4795 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    472a:	49 63 47 40          	movslq 0x40(%r15),%rax
    472e:	85 c0                	test   %eax,%eax
    4730:	7e 63                	jle    4795 <timer_thread+0x185>
    4732:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4736:	4d 8b 47 18          	mov    0x18(%r15),%r8
    473a:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4742:	31 c9                	xor    %ecx,%ecx
    4744:	48 89 c6             	mov    %rax,%rsi
    4747:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    474b:	48 8b 40 38          	mov    0x38(%rax),%rax
    474f:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4753:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4759:	74 15                	je     4770 <timer_thread+0x160>
    475b:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4765:	48 05 00 02 00 00    	add    $0x200,%rax
    476b:	48 39 c2             	cmp    %rax,%rdx
    476e:	74 1c                	je     478c <timer_thread+0x17c>
      data->threads[x]->tasks[y].sending = 0;
    4770:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    477a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4780:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4787:	48 39 c2             	cmp    %rax,%rdx
    478a:	75 e4                	jne    4770 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    478c:	48 83 c1 08          	add    $0x8,%rcx
    4790:	48 39 cf             	cmp    %rcx,%rdi
    4793:	75 b2                	jne    4747 <timer_thread+0x137>
  asm volatile ("mfence" ::: "memory");
    4795:	0f ae f0             	mfence
  struct timespec drain = {
    4798:	66 0f 6f 05 40 44 00 00 	movdqa 0x4440(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    47a0:	41 89 dc             	mov    %ebx,%r12d
    47a3:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    47a8:	49 63 47 28          	movslq 0x28(%r15),%rax
    y++;
    47ac:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    47b1:	85 c0                	test   %eax,%eax
    47b3:	7e 46                	jle    47fb <timer_thread+0x1eb>
    47b5:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    47b9:	49 63 ec             	movslq %r12d,%rbp
    47bc:	48 c1 e5 09          	shl    $0x9,%rbp
    47c0:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    47c4:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    47c8:	48 8b 19             	mov    (%rcx),%rbx
    47cb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    47cd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    47d1:	99                   	cltd
    47d2:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    47d5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    47d9:	48 63 d2             	movslq %edx,%rdx
    47dc:	48 c1 e2 09          	shl    $0x9,%rdx
    47e0:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    47eb:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    47f6:	49 39 c8             	cmp    %rcx,%r8
    47f9:	75 cd                	jne    47c8 <timer_thread+0x1b8>
    asm volatile ("mfence" ::: "memory");
    47fb:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    47fe:	49 8b 77 18          	mov    0x18(%r15),%rsi
    y++;
    4802:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    4805:	48 8b 06             	mov    (%rsi),%rax
    y++;
    4808:	39 78 40             	cmp    %edi,0x40(%rax)
    480b:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    480f:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4813:	85 ff                	test   %edi,%edi
    4815:	0f 8e a1 01 00 00    	jle    49bc <timer_thread+0x3ac>
    481b:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    481e:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    4824:	4c 89 f5             	mov    %r14,%rbp
    4827:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4830:	89 eb                	mov    %ebp,%ebx
      for (int y = 0 ; y < 2 ; y++) {
    4832:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    483a:	45 31 f6             	xor    %r14d,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    483d:	85 ff                	test   %edi,%edi
    483f:	7e 6f                	jle    48b0 <timer_thread+0x2a0>
    4841:	4c 89 f6             	mov    %r14,%rsi
    4844:	48 63 cf             	movslq %edi,%rcx
    4847:	45 31 c0             	xor    %r8d,%r8d
    484a:	48 c1 e6 09          	shl    $0x9,%rsi
    484e:	66 90                	xchg   %ax,%ax
          if (x == k) { continue; }
    4850:	41 39 e8             	cmp    %ebp,%r8d
    4853:	74 42                	je     4897 <timer_thread+0x287>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4855:	49 8b 47 18          	mov    0x18(%r15),%rax
    4859:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    485d:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4861:	4c 89 c0             	mov    %r8,%rax
    4864:	48 c1 e0 06          	shl    $0x6,%rax
    4868:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4870:	48 8b 10             	mov    (%rax),%rdx
    4873:	48 8b 40 08          	mov    0x8(%rax),%rax
    4877:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    487e:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4885:	4d 85 c9             	test   %r9,%r9
    4888:	0f 8f 92 00 00 00    	jg     4920 <timer_thread+0x310>
    488e:	4d 85 db             	test   %r11,%r11
    4891:	0f 8f 89 00 00 00    	jg     4920 <timer_thread+0x310>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4897:	49 83 c0 01          	add    $0x1,%r8
    489b:	4c 39 c1             	cmp    %r8,%rcx
    489e:	75 b0                	jne    4850 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    48a0:	49 83 fe 01          	cmp    $0x1,%r14
    48a4:	74 0a                	je     48b0 <timer_thread+0x2a0>
    48a6:	41 be 01 00 00 00    	mov    $0x1,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    48ac:	85 ff                	test   %edi,%edi
    48ae:	7f 91                	jg     4841 <timer_thread+0x231>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48b0:	48 83 c5 01          	add    $0x1,%rbp
    48b4:	39 ef                	cmp    %ebp,%edi
    48b6:	0f 8f 74 ff ff ff    	jg     4830 <timer_thread+0x220>
    48bc:	44 89 d5             	mov    %r10d,%ebp
    for (int k = 0 ; k < data->my_thread_count; k++) {
    48bf:	85 ff                	test   %edi,%edi
    48c1:	7e 3b                	jle    48fe <timer_thread+0x2ee>
    48c3:	31 db                	xor    %ebx,%ebx
    int all_waited = 1;
    48c5:	bf 01 00 00 00       	mov    $0x1,%edi
    48ca:	49 8b 77 18          	mov    0x18(%r15),%rsi
    48ce:	41 8b 57 40          	mov    0x40(%r15),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    48d2:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    48d6:	48 8b 40 38          	mov    0x38(%rax),%rax
    48da:	8b 88 9c 01 00 00    	mov    0x19c(%rax),%ecx
    48e0:	39 d1                	cmp    %edx,%ecx
    48e2:	0f 8c a8 00 00 00    	jl     4990 <timer_thread+0x380>
    48e8:	8b 80 9c 03 00 00    	mov    0x39c(%rax),%eax
    48ee:	39 d0                	cmp    %edx,%eax
    48f0:	7c 6e                	jl     4960 <timer_thread+0x350>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    48f2:	48 83 c3 01          	add    $0x1,%rbx
    48f6:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    48fa:	7f d6                	jg     48d2 <timer_thread+0x2c2>
    48fc:	21 fd                	and    %edi,%ebp
    if (all_empty == 1 && all_waited == 1) {
    48fe:	85 ed                	test   %ebp,%ebp
    4900:	0f 85 b6 00 00 00    	jne    49bc <timer_thread+0x3ac>
      nanosleep(&drain , &drainrem);
    4906:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    490b:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4910:	e8 8b da ff ff       	call   23a0 <nanosleep@plt>
    4915:	e9 8e fe ff ff       	jmp    47a8 <timer_thread+0x198>
    491a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4920:	8b 80 28 03 00 00    	mov    0x328(%rax),%eax
    4926:	48 83 ec 08          	sub    $0x8,%rsp
    492a:	bf 01 00 00 00       	mov    $0x1,%edi
    492f:	44 89 f1             	mov    %r14d,%ecx
    4932:	48 8d 35 24 37 00 00 	lea    0x3724(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    4939:	50                   	push   %rax
    493a:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    4940:	89 da                	mov    %ebx,%edx
    4942:	50                   	push   %rax
    4943:	31 c0                	xor    %eax,%eax
    4945:	41 53                	push   %r11
    4947:	e8 64 db ff ff       	call   24b0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    494c:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4950:	48 83 c4 20          	add    $0x20,%rsp
            all_empty = 0;
    4954:	45 31 d2             	xor    %r10d,%r10d
    4957:	e9 44 ff ff ff       	jmp    48a0 <timer_thread+0x290>
    495c:	0f 1f 40 00          	nopl   0x0(%rax)
    4960:	89 c2                	mov    %eax,%edx
    4962:	bf 01 00 00 00       	mov    $0x1,%edi
    4967:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4969:	48 83 c3 01          	add    $0x1,%rbx
    496d:	48 8d 35 91 39 00 00 	lea    0x3991(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4974:	e8 37 db ff ff       	call   24b0 <__printf_chk@plt>
          all_waited = 0; 
    4979:	31 ff                	xor    %edi,%edi
    for (int k = 0 ; k < data->my_thread_count; k++) {
    497b:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    497f:	0f 8f 45 ff ff ff    	jg     48ca <timer_thread+0x2ba>
    4985:	e9 72 ff ff ff       	jmp    48fc <timer_thread+0x2ec>
    498a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4990:	89 ca                	mov    %ecx,%edx
    4992:	48 8d 35 6c 39 00 00 	lea    0x396c(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4999:	bf 01 00 00 00       	mov    $0x1,%edi
    499e:	31 c0                	xor    %eax,%eax
    49a0:	e8 0b db ff ff       	call   24b0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    49a5:	49 8b 77 18          	mov    0x18(%r15),%rsi
    49a9:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    49ad:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    49af:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    49b3:	48 8b 40 38          	mov    0x38(%rax),%rax
    49b7:	e9 2c ff ff ff       	jmp    48e8 <timer_thread+0x2d8>
    49bc:	48 8d 3d 91 36 00 00 	lea    0x3691(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    49c3:	e8 68 d9 ff ff       	call   2330 <puts@plt>
  while (data->running) {
    49c8:	41 8b 57 44          	mov    0x44(%r15),%edx
    49cc:	85 d2                	test   %edx,%edx
    49ce:	0f 84 eb 00 00 00    	je     4abf <timer_thread+0x4af>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    49d4:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    49d8:	31 db                	xor    %ebx,%ebx
    49da:	48 8d 2d 99 36 00 00 	lea    0x3699(%rip),%rbp        # 807a <_IO_stdin_used+0x7a>
    49e1:	4c 8d 25 ad 36 00 00 	lea    0x36ad(%rip),%r12        # 8095 <_IO_stdin_used+0x95>
    49e8:	85 c0                	test   %eax,%eax
    49ea:	7e 38                	jle    4a24 <timer_thread+0x414>
    49ec:	0f 1f 40 00          	nopl   0x0(%rax)
    49f0:	31 c0                	xor    %eax,%eax
    49f2:	89 da                	mov    %ebx,%edx
    49f4:	48 89 ee             	mov    %rbp,%rsi
    49f7:	bf 01 00 00 00       	mov    $0x1,%edi
    49fc:	e8 af da ff ff       	call   24b0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4a01:	49 8b 47 18          	mov    0x18(%r15),%rax
    4a05:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4a09:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4a0d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4a14:	0f 84 d2 00 00 00    	je     4aec <timer_thread+0x4dc>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4a1a:	48 83 c3 01          	add    $0x1,%rbx
    4a1e:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4a22:	7f cc                	jg     49f0 <timer_thread+0x3e0>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4a24:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4a28:	85 d2                	test   %edx,%edx
    4a2a:	7e 7c                	jle    4aa8 <timer_thread+0x498>
      for (int y = 0 ; y < data->task_count ; y++) {
    4a2c:	41 8b 47 40          	mov    0x40(%r15),%eax
    4a30:	85 c0                	test   %eax,%eax
    4a32:	7e 74                	jle    4aa8 <timer_thread+0x498>
    4a34:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4a37:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4a3b:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4a43:	31 c9                	xor    %ecx,%ecx
    4a45:	48 c1 e6 09          	shl    $0x9,%rsi
    4a49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4a50:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4a54:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a58:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4a5c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4a62:	74 1c                	je     4a80 <timer_thread+0x470>
    4a64:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4a6e:	48 05 00 02 00 00    	add    $0x200,%rax
    4a74:	48 39 d0             	cmp    %rdx,%rax
    4a77:	74 26                	je     4a9f <timer_thread+0x48f>
    4a79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4a80:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4a8a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4a90:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4a9a:	48 39 d0             	cmp    %rdx,%rax
    4a9d:	75 e1                	jne    4a80 <timer_thread+0x470>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4a9f:	48 83 c1 08          	add    $0x8,%rcx
    4aa3:	48 39 cf             	cmp    %rcx,%rdi
    4aa6:	75 a8                	jne    4a50 <timer_thread+0x440>
    asm volatile ("mfence" ::: "memory");
    4aa8:	0f ae f0             	mfence
    4aab:	48 8d 3d f5 35 00 00 	lea    0x35f5(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4ab2:	e8 79 d8 ff ff       	call   2330 <puts@plt>
    data->running = 0;
    4ab7:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4abf:	48 8d 3d e8 35 00 00 	lea    0x35e8(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4ac6:	e8 65 d8 ff ff       	call   2330 <puts@plt>
}
    4acb:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4ad0:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ad9:	75 41                	jne    4b1c <timer_thread+0x50c>
    4adb:	48 83 c4 58          	add    $0x58,%rsp
    4adf:	31 c0                	xor    %eax,%eax
    4ae1:	5b                   	pop    %rbx
    4ae2:	5d                   	pop    %rbp
    4ae3:	41 5c                	pop    %r12
    4ae5:	41 5d                	pop    %r13
    4ae7:	41 5e                	pop    %r14
    4ae9:	41 5f                	pop    %r15
    4aeb:	c3                   	ret
    4aec:	4c 89 e7             	mov    %r12,%rdi
    4aef:	e8 3c d8 ff ff       	call   2330 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4af4:	49 8b 47 18          	mov    0x18(%r15),%rax
    4af8:	be 01 00 00 00       	mov    $0x1,%esi
    4afd:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4b01:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4b05:	8b 78 60             	mov    0x60(%rax),%edi
    4b08:	e8 53 d9 ff ff       	call   2460 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4b0d:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4b11:	0f 8f d9 fe ff ff    	jg     49f0 <timer_thread+0x3e0>
    4b17:	e9 08 ff ff ff       	jmp    4a24 <timer_thread+0x414>
}
    4b1c:	e8 5f d8 ff ff       	call   2380 <__stack_chk_fail@plt>
    4b21:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4b2c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b30 <minf>:
int minf(int a, int b) {
    4b30:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    4b34:	39 f7                	cmp    %esi,%edi
    4b36:	89 f0                	mov    %esi,%eax
    4b38:	0f 4e c7             	cmovle %edi,%eax
}
    4b3b:	c3                   	ret
    4b3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b40 <maxf>:
int maxf(int a, int b) {
    4b40:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    4b44:	39 f7                	cmp    %esi,%edi
    4b46:	89 f0                	mov    %esi,%eax
    4b48:	0f 4d c7             	cmovge %edi,%eax
}
    4b4b:	c3                   	ret
    4b4c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b50 <strtolower>:
void strtolower(char *str) {
    4b50:	f3 0f 1e fa          	endbr64
    4b54:	55                   	push   %rbp
    4b55:	53                   	push   %rbx
    4b56:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    4b5a:	48 0f be 1f          	movsbq (%rdi),%rbx
    4b5e:	84 db                	test   %bl,%bl
    4b60:	74 24                	je     4b86 <strtolower+0x36>
    4b62:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4b65:	e8 26 da ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4b6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b70:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4b73:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4b77:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4b7a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    4b7d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4b82:	84 db                	test   %bl,%bl
    4b84:	75 ea                	jne    4b70 <strtolower+0x20>
}
    4b86:	48 83 c4 08          	add    $0x8,%rsp
    4b8a:	5b                   	pop    %rbx
    4b8b:	5d                   	pop    %rbp
    4b8c:	c3                   	ret
    4b8d:	0f 1f 00             	nopl   (%rax)

0000000000004b90 <zh_malloc>:
void *zh_malloc(size_t size) {
    4b90:	f3 0f 1e fa          	endbr64
    4b94:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4b98:	e8 d3 d8 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4b9d:	48 85 c0             	test   %rax,%rax
    4ba0:	74 05                	je     4ba7 <zh_malloc+0x17>
}
    4ba2:	48 83 c4 08          	add    $0x8,%rsp
    4ba6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4ba7:	48 8b 0d 72 64 00 00 	mov    0x6472(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4bae:	ba 28 00 00 00       	mov    $0x28,%edx
    4bb3:	be 01 00 00 00       	mov    $0x1,%esi
    4bb8:	48 8d 3d f9 39 00 00 	lea    0x39f9(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    4bbf:	e8 6c d9 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    4bc4:	bf 01 00 00 00       	mov    $0x1,%edi
    4bc9:	e8 42 d9 ff ff       	call   2510 <exit@plt>
    4bce:	66 90                	xchg   %ax,%ax

0000000000004bd0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4bd0:	f3 0f 1e fa          	endbr64
    4bd4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4bd5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4bda:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4bdd:	e8 ce d7 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    4be2:	48 85 c0             	test   %rax,%rax
    4be5:	74 11                	je     4bf8 <get_filename_ext+0x28>
    4be7:	48 39 c3             	cmp    %rax,%rbx
    4bea:	74 0c                	je     4bf8 <get_filename_ext+0x28>
    return dot + 1;
    4bec:	48 83 c0 01          	add    $0x1,%rax
}
    4bf0:	5b                   	pop    %rbx
    4bf1:	c3                   	ret
    4bf2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4bf8:	48 8d 05 f7 34 00 00 	lea    0x34f7(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4bff:	5b                   	pop    %rbx
    4c00:	c3                   	ret
    4c01:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4c0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c10 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4c10:	f3 0f 1e fa          	endbr64
    4c14:	41 55                	push   %r13
    4c16:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c19:	48 89 fe             	mov    %rdi,%rsi
    4c1c:	41 54                	push   %r12
    4c1e:	55                   	push   %rbp
    4c1f:	48 89 d5             	mov    %rdx,%rbp
    4c22:	ba 00 04 00 00       	mov    $0x400,%edx
    4c27:	53                   	push   %rbx
    4c28:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4c2f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4c38:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4c40:	31 c0                	xor    %eax,%eax
    4c42:	49 89 e4             	mov    %rsp,%r12
    4c45:	4c 89 e7             	mov    %r12,%rdi
    4c48:	e8 43 d8 ff ff       	call   2490 <__strcpy_chk@plt>
    for (; *str; ++str)
    4c4d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4c52:	84 db                	test   %bl,%bl
    4c54:	74 24                	je     4c7a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4c56:	e8 35 d9 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4c5b:	48 8b 08             	mov    (%rax),%rcx
    4c5e:	4c 89 e0             	mov    %r12,%rax
    4c61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c68:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4c6b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4c6f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4c72:	48 0f be 18          	movsbq (%rax),%rbx
    4c76:	84 db                	test   %bl,%bl
    4c78:	75 ee                	jne    4c68 <send_headers+0x58>
    void *buf = malloc(size);
    4c7a:	bf 11 00 00 00       	mov    $0x11,%edi
    4c7f:	e8 ec d7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4c84:	48 85 c0             	test   %rax,%rax
    4c87:	0f 84 7e 04 00 00    	je     510b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4c8d:	66 0f 6f 05 5b 3f 00 00 	movdqa 0x3f5b(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    iov[0].iov_base = zh_malloc(slen);
    4c95:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4c99:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4c9e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4ca6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4caa:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4cad:	e8 be d7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4cb2:	48 85 c0             	test   %rax,%rax
    4cb5:	0f 84 50 04 00 00    	je     510b <send_headers+0x4fb>
    4cbb:	66 0f 6f 05 3d 3f 00 00 	movdqa 0x3f3d(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    iov[1].iov_base = zh_malloc(slen);
    4cc3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4cc7:	4c 89 e7             	mov    %r12,%rdi
    4cca:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4cd4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4cdc:	0f 11 00             	movups %xmm0,(%rax)
    4cdf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4ce3:	be 2e 00 00 00       	mov    $0x2e,%esi
    4ce8:	e8 c3 d6 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    4ced:	48 85 c0             	test   %rax,%rax
    4cf0:	0f 84 ea 02 00 00    	je     4fe0 <send_headers+0x3d0>
    4cf6:	4c 39 e0             	cmp    %r12,%rax
    4cf9:	0f 84 e1 02 00 00    	je     4fe0 <send_headers+0x3d0>
    return dot + 1;
    4cff:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4d03:	48 8d 3d ba 33 00 00 	lea    0x33ba(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4d0a:	48 89 de             	mov    %rbx,%rsi
    4d0d:	e8 fe d6 ff ff       	call   2410 <strcmp@plt>
    4d12:	85 c0                	test   %eax,%eax
    4d14:	75 20                	jne    4d36 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d16:	66 0f 6f 05 f2 3e 00 00 	movdqa 0x3ef2(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4d1e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d26:	66 0f 6f 05 f2 3e 00 00 	movdqa 0x3ef2(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4d2e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4d36:	48 89 de             	mov    %rbx,%rsi
    4d39:	48 8d 3d 88 33 00 00 	lea    0x3388(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4d40:	e8 cb d6 ff ff       	call   2410 <strcmp@plt>
    4d45:	85 c0                	test   %eax,%eax
    4d47:	75 20                	jne    4d69 <send_headers+0x159>
    4d49:	66 0f 6f 05 bf 3e 00 00 	movdqa 0x3ebf(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4d51:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d59:	66 0f 6f 05 bf 3e 00 00 	movdqa 0x3ebf(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4d61:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4d69:	48 89 de             	mov    %rbx,%rsi
    4d6c:	48 8d 3d 5a 33 00 00 	lea    0x335a(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4d73:	e8 98 d6 ff ff       	call   2410 <strcmp@plt>
    4d78:	85 c0                	test   %eax,%eax
    4d7a:	0f 84 10 02 00 00    	je     4f90 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4d80:	48 89 de             	mov    %rbx,%rsi
    4d83:	48 8d 3d 47 33 00 00 	lea    0x3347(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4d8a:	e8 81 d6 ff ff       	call   2410 <strcmp@plt>
    4d8f:	85 c0                	test   %eax,%eax
    4d91:	0f 84 a9 02 00 00    	je     5040 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4d97:	48 89 de             	mov    %rbx,%rsi
    4d9a:	48 8d 3d 34 33 00 00 	lea    0x3334(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4da1:	e8 6a d6 ff ff       	call   2410 <strcmp@plt>
    4da6:	85 c0                	test   %eax,%eax
    4da8:	0f 84 6a 02 00 00    	je     5018 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4dae:	48 89 de             	mov    %rbx,%rsi
    4db1:	48 8d 3d 60 33 00 00 	lea    0x3360(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4db8:	e8 53 d6 ff ff       	call   2410 <strcmp@plt>
    4dbd:	85 c0                	test   %eax,%eax
    4dbf:	0f 84 2b 02 00 00    	je     4ff0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4dc5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4dc8:	0f 84 52 01 00 00    	je     4f20 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4dce:	48 89 de             	mov    %rbx,%rsi
    4dd1:	48 8d 3d 01 33 00 00 	lea    0x3301(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4dd8:	e8 33 d6 ff ff       	call   2410 <strcmp@plt>
    4ddd:	85 c0                	test   %eax,%eax
    4ddf:	0f 84 ab 02 00 00    	je     5090 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4de5:	48 89 de             	mov    %rbx,%rsi
    4de8:	48 8d 3d ee 32 00 00 	lea    0x32ee(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4def:	e8 1c d6 ff ff       	call   2410 <strcmp@plt>
    4df4:	85 c0                	test   %eax,%eax
    4df6:	0f 84 6c 02 00 00    	je     5068 <send_headers+0x458>
    slen = strlen(send_buffer);
    4dfc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4e04:	4c 89 e7             	mov    %r12,%rdi
    4e07:	e8 64 d5 ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    4e0c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4e0f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4e12:	e8 59 d6 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4e17:	48 85 c0             	test   %rax,%rax
    4e1a:	0f 84 eb 02 00 00    	je     510b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4e20:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4e24:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4e28:	83 fb 08             	cmp    $0x8,%ebx
    4e2b:	0f 83 3f 01 00 00    	jae    4f70 <send_headers+0x360>
    4e31:	f6 c3 04             	test   $0x4,%bl
    4e34:	0f 85 7b 02 00 00    	jne    50b5 <send_headers+0x4a5>
    4e3a:	85 db                	test   %ebx,%ebx
    4e3c:	74 13                	je     4e51 <send_headers+0x241>
    4e3e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4e46:	88 10                	mov    %dl,(%rax)
    4e48:	f6 c3 02             	test   $0x2,%bl
    4e4b:	0f 85 96 02 00 00    	jne    50e7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4e51:	4d 89 e8             	mov    %r13,%r8
    4e54:	48 8d 0d 86 32 00 00 	lea    0x3286(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4e5b:	4c 89 e7             	mov    %r12,%rdi
    4e5e:	31 c0                	xor    %eax,%eax
    4e60:	ba 00 04 00 00       	mov    $0x400,%edx
    4e65:	be 01 00 00 00       	mov    $0x1,%esi
    4e6a:	e8 31 d7 ff ff       	call   25a0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4e6f:	4c 89 e7             	mov    %r12,%rdi
    4e72:	e8 f9 d4 ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    4e77:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4e7a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4e7d:	e8 ee d5 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4e82:	48 85 c0             	test   %rax,%rax
    4e85:	0f 84 80 02 00 00    	je     510b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4e8b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4e8f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4e93:	83 fb 08             	cmp    $0x8,%ebx
    4e96:	0f 83 1c 01 00 00    	jae    4fb8 <send_headers+0x3a8>
    4e9c:	f6 c3 04             	test   $0x4,%bl
    4e9f:	0f 85 29 02 00 00    	jne    50ce <send_headers+0x4be>
    4ea5:	85 db                	test   %ebx,%ebx
    4ea7:	74 13                	je     4ebc <send_headers+0x2ac>
    4ea9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4eb1:	88 10                	mov    %dl,(%rax)
    4eb3:	f6 c3 02             	test   $0x2,%bl
    4eb6:	0f 85 3d 02 00 00    	jne    50f9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ebc:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4ec1:	bf 02 00 00 00       	mov    $0x2,%edi
    4ec6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4ece:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4ed6:	e8 95 d5 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4edb:	48 85 c0             	test   %rax,%rax
    4ede:	0f 84 27 02 00 00    	je     510b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ee4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4eec:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4ef0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4ef8:	66 89 10             	mov    %dx,(%rax)
}
    4efb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4f03:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f0c:	0f 85 20 02 00 00    	jne    5132 <send_headers+0x522>
    4f12:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4f19:	5b                   	pop    %rbx
    4f1a:	5d                   	pop    %rbp
    4f1b:	41 5c                	pop    %r12
    4f1d:	41 5d                	pop    %r13
    4f1f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4f20:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4f24:	0f 85 a4 fe ff ff    	jne    4dce <send_headers+0x1be>
    4f2a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4f2e:	0f 85 9a fe ff ff    	jne    4dce <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f34:	66 0f 6f 05 34 3d 00 00 	movdqa 0x3d34(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    4f3c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4f46:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f4e:	66 0f 6f 05 2a 3d 00 00 	movdqa 0x3d2a(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    4f56:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4f5e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4f66:	e9 63 fe ff ff       	jmp    4dce <send_headers+0x1be>
    4f6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f70:	89 da                	mov    %ebx,%edx
    4f72:	48 89 c7             	mov    %rax,%rdi
    4f75:	4c 89 e6             	mov    %r12,%rsi
    4f78:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4f7d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4f82:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4f85:	c1 e9 03             	shr    $0x3,%ecx
    4f88:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4f8b:	e9 c1 fe ff ff       	jmp    4e51 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f90:	66 0f 6f 05 78 3c 00 00 	movdqa 0x3c78(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4f98:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fa0:	66 0f 6f 05 88 3c 00 00 	movdqa 0x3c88(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4fa8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4fb0:	e9 cb fd ff ff       	jmp    4d80 <send_headers+0x170>
    4fb5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4fb8:	89 da                	mov    %ebx,%edx
    4fba:	48 89 c7             	mov    %rax,%rdi
    4fbd:	4c 89 e6             	mov    %r12,%rsi
    4fc0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4fc5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4fca:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4fcd:	c1 e9 03             	shr    $0x3,%ecx
    4fd0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4fd3:	e9 e4 fe ff ff       	jmp    4ebc <send_headers+0x2ac>
    4fd8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4fe0:	48 8d 1d 0f 31 00 00 	lea    0x310f(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    4fe7:	e9 94 fd ff ff       	jmp    4d80 <send_headers+0x170>
    4fec:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ff0:	66 0f 6f 05 58 3c 00 00 	movdqa 0x3c58(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4ff8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5000:	66 0f 6f 05 58 3c 00 00 	movdqa 0x3c58(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5008:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5010:	e9 b0 fd ff ff       	jmp    4dc5 <send_headers+0x1b5>
    5015:	0f 1f 00             	nopl   (%rax)
    5018:	66 0f 6f 05 30 3c 00 00 	movdqa 0x3c30(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5020:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5028:	66 0f 6f 05 30 3c 00 00 	movdqa 0x3c30(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5030:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5038:	e9 71 fd ff ff       	jmp    4dae <send_headers+0x19e>
    503d:	0f 1f 00             	nopl   (%rax)
    5040:	66 0f 6f 05 c8 3b 00 00 	movdqa 0x3bc8(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    5048:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5050:	66 0f 6f 05 e8 3b 00 00 	movdqa 0x3be8(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    5058:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5060:	e9 32 fd ff ff       	jmp    4d97 <send_headers+0x187>
    5065:	0f 1f 00             	nopl   (%rax)
    5068:	66 0f 6f 05 e0 3b 00 00 	movdqa 0x3be0(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5070:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5078:	66 0f 6f 05 20 3c 00 00 	movdqa 0x3c20(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    5080:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5088:	e9 6f fd ff ff       	jmp    4dfc <send_headers+0x1ec>
    508d:	0f 1f 00             	nopl   (%rax)
    5090:	66 0f 6f 05 b8 3b 00 00 	movdqa 0x3bb8(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5098:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50a0:	66 0f 6f 05 e8 3b 00 00 	movdqa 0x3be8(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    50a8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    50b0:	e9 30 fd ff ff       	jmp    4de5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    50b5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    50bc:	89 db                	mov    %ebx,%ebx
    50be:	89 10                	mov    %edx,(%rax)
    50c0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    50c5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    50c9:	e9 83 fd ff ff       	jmp    4e51 <send_headers+0x241>
    50ce:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    50d5:	89 db                	mov    %ebx,%ebx
    50d7:	89 10                	mov    %edx,(%rax)
    50d9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    50de:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    50e2:	e9 d5 fd ff ff       	jmp    4ebc <send_headers+0x2ac>
    50e7:	89 db                	mov    %ebx,%ebx
    50e9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    50ef:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    50f4:	e9 58 fd ff ff       	jmp    4e51 <send_headers+0x241>
    50f9:	89 db                	mov    %ebx,%ebx
    50fb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    5101:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5106:	e9 b1 fd ff ff       	jmp    4ebc <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    510b:	48 8b 0d 0e 5f 00 00 	mov    0x5f0e(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5112:	ba 28 00 00 00       	mov    $0x28,%edx
    5117:	be 01 00 00 00       	mov    $0x1,%esi
    511c:	48 8d 3d 95 34 00 00 	lea    0x3495(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    5123:	e8 08 d4 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5128:	bf 01 00 00 00       	mov    $0x1,%edi
    512d:	e8 de d3 ff ff       	call   2510 <exit@plt>
}
    5132:	e8 49 d2 ff ff       	call   2380 <__stack_chk_fail@plt>
    5137:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005140 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5140:	f3 0f 1e fa          	endbr64
    5144:	41 55                	push   %r13
    5146:	49 89 d5             	mov    %rdx,%r13
    5149:	41 54                	push   %r12
    514b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    514e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5151:	55                   	push   %rbp
    5152:	53                   	push   %rbx
    5153:	48 89 f3             	mov    %rsi,%rbx
    5156:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    515a:	e8 11 d3 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    515f:	48 85 c0             	test   %rax,%rax
    5162:	74 6b                	je     51cf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    5164:	4c 89 e7             	mov    %r12,%rdi
    5167:	48 89 c5             	mov    %rax,%rbp
    516a:	31 f6                	xor    %esi,%esi
    516c:	31 c0                	xor    %eax,%eax
    516e:	e8 6d d3 ff ff       	call   24e0 <open@plt>
    5173:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    5176:	85 c0                	test   %eax,%eax
    5178:	0f 88 58 d4 ff ff    	js     25d6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    517e:	48 89 da             	mov    %rbx,%rdx
    5181:	48 89 ee             	mov    %rbp,%rsi
    5184:	89 c7                	mov    %eax,%edi
    5186:	e8 65 d2 ff ff       	call   23f0 <read@plt>
    if (ret < file_size) {
    518b:	48 98                	cltq
    518d:	48 39 d8             	cmp    %rbx,%rax
    5190:	7c 1e                	jl     51b0 <copy_file_contents+0x70>
    close(fd);
    5192:	44 89 e7             	mov    %r12d,%edi
    5195:	e8 36 d2 ff ff       	call   23d0 <close@plt>
    iov->iov_base = buf;
    519a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    519e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    51a2:	48 83 c4 08          	add    $0x8,%rsp
    51a6:	5b                   	pop    %rbx
    51a7:	5d                   	pop    %rbp
    51a8:	41 5c                	pop    %r12
    51aa:	41 5d                	pop    %r13
    51ac:	c3                   	ret
    51ad:	0f 1f 00             	nopl   (%rax)
    51b0:	48 8b 0d 69 5e 00 00 	mov    0x5e69(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    51b7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    51bc:	be 01 00 00 00       	mov    $0x1,%esi
    51c1:	48 8d 3d 2f 2f 00 00 	lea    0x2f2f(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    51c8:	e8 63 d3 ff ff       	call   2530 <fwrite@plt>
    51cd:	eb c3                	jmp    5192 <copy_file_contents+0x52>
    51cf:	48 8b 0d 4a 5e 00 00 	mov    0x5e4a(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    51d6:	ba 28 00 00 00       	mov    $0x28,%edx
    51db:	be 01 00 00 00       	mov    $0x1,%esi
    51e0:	48 8d 3d d1 33 00 00 	lea    0x33d1(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    51e7:	e8 44 d3 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    51ec:	bf 01 00 00 00       	mov    $0x1,%edi
    51f1:	e8 1a d3 ff ff       	call   2510 <exit@plt>
    51f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005200 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    5200:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    5204:	8b 46 44             	mov    0x44(%rsi),%eax
    5207:	48 89 fa             	mov    %rdi,%rdx
    520a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    520d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5213:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5216:	48 8b 07             	mov    (%rdi),%rax
    5219:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    521c:	f6 c1 02             	test   $0x2,%cl
    521f:	74 00                	je     5221 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    5221:	89 f0                	mov    %esi,%eax
    5223:	44 29 c0             	sub    %r8d,%eax
    5226:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5229:	0f 82 b3 d3 ff ff    	jb     25e2 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    522f:	c1 e9 0a             	shr    $0xa,%ecx
    5232:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5236:	8b 47 44             	mov    0x44(%rdi),%eax
    5239:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    523c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    523f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5242:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    5245:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5249:	d3 e0                	shl    %cl,%eax
    524b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    524e:	48 c1 e0 06          	shl    $0x6,%rax
    5252:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    5256:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    525c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    525f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    5263:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5269:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5271:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    5275:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    5278:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    527f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5287:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    528b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    528f:	e8 fc d0 ff ff       	call   2390 <io_uring_submit@plt>
}
    5294:	31 c0                	xor    %eax,%eax
    5296:	48 83 c4 08          	add    $0x8,%rsp
    529a:	c3                   	ret
    529b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000052a0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    52a0:	f3 0f 1e fa          	endbr64
    52a4:	41 55                	push   %r13
    52a6:	41 89 fd             	mov    %edi,%r13d
    52a9:	41 54                	push   %r12
    52ab:	55                   	push   %rbp
    52ac:	53                   	push   %rbx
    52ad:	48 89 f3             	mov    %rsi,%rbx
    52b0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    52b4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    52b7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    52bd:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    52c0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    52c3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    52c5:	f6 c1 02             	test   $0x2,%cl
    52c8:	74 00                	je     52ca <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    52ca:	89 c2                	mov    %eax,%edx
    52cc:	29 f2                	sub    %esi,%edx
    52ce:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    52d1:	0f 82 1b d3 ff ff    	jb     25f2 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52d7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    52da:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    52dd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    52e0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    52e5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52e8:	23 6b 58             	and    0x58(%rbx),%ebp
    52eb:	d3 e5                	shl    %cl,%ebp
    52ed:	48 c1 e5 06          	shl    $0x6,%rbp
    52f1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    52f5:	e8 76 d1 ff ff       	call   2470 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    52fa:	be 01 00 00 00       	mov    $0x1,%esi
    52ff:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5304:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    5307:	e8 f4 d0 ff ff       	call   2400 <calloc@plt>
    req->client_socket = client_socket;
    530c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5311:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5315:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5318:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    531d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    5322:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    532b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    5333:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    5337:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    533b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    5342:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    534a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    534e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    5356:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    535e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    5362:	e8 29 d0 ff ff       	call   2390 <io_uring_submit@plt>
}
    5367:	48 83 c4 08          	add    $0x8,%rsp
    536b:	31 c0                	xor    %eax,%eax
    536d:	5b                   	pop    %rbx
    536e:	5d                   	pop    %rbp
    536f:	41 5c                	pop    %r12
    5371:	41 5d                	pop    %r13
    5373:	c3                   	ret
    5374:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    537f:	90                   	nop

0000000000005380 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5380:	f3 0f 1e fa          	endbr64
    5384:	41 56                	push   %r14
    5386:	41 89 f6             	mov    %esi,%r14d
    5389:	41 55                	push   %r13
    538b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    538e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5393:	41 54                	push   %r12
    5395:	55                   	push   %rbp
    5396:	48 89 d5             	mov    %rdx,%rbp
    5399:	53                   	push   %rbx
    void *buf = malloc(size);
    539a:	e8 d1 d0 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    539f:	48 85 c0             	test   %rax,%rax
    53a2:	0f 84 dd 00 00 00    	je     5485 <_send_static_string_content+0x105>
    53a8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    53ab:	4c 89 ef             	mov    %r13,%rdi
    53ae:	e8 bd cf ff ff       	call   2370 <strlen@plt>
    req->iovec_count = 1;
    53b3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    53ba:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    53be:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    53c1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    53c4:	e8 a7 d0 ff ff       	call   2470 <malloc@plt>
    53c9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    53cc:	48 85 c0             	test   %rax,%rax
    53cf:	0f 84 b0 00 00 00    	je     5485 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    53d5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    53d9:	4c 89 e2             	mov    %r12,%rdx
    53dc:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    53df:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    53e3:	e8 58 d0 ff ff       	call   2440 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    53e8:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    53eb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    53f1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    53f4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    53f8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    53fa:	f6 c1 02             	test   $0x2,%cl
    53fd:	0f 85 7d 00 00 00    	jne    5480 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    5403:	89 d0                	mov    %edx,%eax
    5405:	29 f0                	sub    %esi,%eax
    5407:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    540a:	0f 82 ec d1 ff ff    	jb     25fc <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5410:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5413:	8b 45 44             	mov    0x44(%rbp),%eax
    5416:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    5419:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    541c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    541f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    5422:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    5428:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    542c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    542e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    5431:	48 89 ef             	mov    %rbp,%rdi
    5434:	48 c1 e0 06          	shl    $0x6,%rax
    5438:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    543c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    543f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    5443:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5449:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5451:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5455:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5458:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    545f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5467:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    546b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    546f:	5b                   	pop    %rbx
    5470:	5d                   	pop    %rbp
    5471:	41 5c                	pop    %r12
    5473:	41 5d                	pop    %r13
    5475:	41 5e                	pop    %r14
    io_uring_submit(ring);
    5477:	e9 14 cf ff ff       	jmp    2390 <io_uring_submit@plt>
    547c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    5480:	e9 7e ff ff ff       	jmp    5403 <_send_static_string_content+0x83>
    5485:	48 8b 0d 94 5b 00 00 	mov    0x5b94(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    548c:	ba 28 00 00 00       	mov    $0x28,%edx
    5491:	be 01 00 00 00       	mov    $0x1,%esi
    5496:	48 8d 3d 1b 31 00 00 	lea    0x311b(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    549d:	e8 8e d0 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    54a2:	bf 01 00 00 00       	mov    $0x1,%edi
    54a7:	e8 64 d0 ff ff       	call   2510 <exit@plt>
    54ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000054b0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    54b0:	f3 0f 1e fa          	endbr64
    54b4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    54b7:	89 fe                	mov    %edi,%esi
    54b9:	48 8b 3d 58 5b 00 00 	mov    0x5b58(%rip),%rdi        # b018 <unimplemented_content>
    54c0:	e9 bb fe ff ff       	jmp    5380 <_send_static_string_content>
    54c5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000054d0 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    54d0:	f3 0f 1e fa          	endbr64
    54d4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    54d7:	89 fe                	mov    %edi,%esi
    54d9:	48 8b 3d 30 5b 00 00 	mov    0x5b30(%rip),%rdi        # b010 <http_404_content>
    54e0:	e9 9b fe ff ff       	jmp    5380 <_send_static_string_content>
    54e5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000054f0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    54f0:	f3 0f 1e fa          	endbr64
    54f4:	41 56                	push   %r14
    54f6:	41 55                	push   %r13
    54f8:	49 89 d5             	mov    %rdx,%r13
    54fb:	41 54                	push   %r12
    54fd:	41 89 f4             	mov    %esi,%r12d
    5500:	55                   	push   %rbp
    5501:	48 89 fd             	mov    %rdi,%rbp
    5504:	53                   	push   %rbx
    5505:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    550c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5515:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    551d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    551f:	e8 4c ce ff ff       	call   2370 <strlen@plt>
    5524:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    5529:	48 89 c3             	mov    %rax,%rbx
    552c:	0f 84 b6 00 00 00    	je     55e8 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5532:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5537:	48 89 ee             	mov    %rbp,%rsi
    553a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    553e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5543:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    554b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5553:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    555e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5566:	e8 b5 ce ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    556b:	48 89 e6             	mov    %rsp,%rsi
    556e:	4c 89 f7             	mov    %r14,%rdi
    5571:	e8 ba ce ff ff       	call   2430 <stat@plt>
    5576:	83 f8 ff             	cmp    $0xffffffff,%eax
    5579:	0f 84 d3 00 00 00    	je     5652 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    557f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5583:	25 00 f0 00 00       	and    $0xf000,%eax
    5588:	3d 00 80 00 00       	cmp    $0x8000,%eax
    558d:	0f 84 f5 00 00 00    	je     5688 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    5593:	48 8b 3d 76 5a 00 00 	mov    0x5a76(%rip),%rdi        # b010 <http_404_content>
    559a:	4c 89 ea             	mov    %r13,%rdx
    559d:	44 89 e6             	mov    %r12d,%esi
    55a0:	e8 db fd ff ff       	call   5380 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    55a5:	4c 89 f2             	mov    %r14,%rdx
    55a8:	bf 01 00 00 00       	mov    $0x1,%edi
    55ad:	31 c0                	xor    %eax,%eax
    55af:	48 8d 35 91 2b 00 00 	lea    0x2b91(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    55b6:	e8 f5 ce ff ff       	call   24b0 <__printf_chk@plt>
}
    55bb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    55c3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    55cc:	0f 85 20 01 00 00    	jne    56f2 <handle_get_method+0x202>
    55d2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    55d9:	5b                   	pop    %rbx
    55da:	5d                   	pop    %rbp
    55db:	41 5c                	pop    %r12
    55dd:	41 5d                	pop    %r13
    55df:	41 5e                	pop    %r14
    55e1:	c3                   	ret
    55e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55e8:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55ed:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    55f5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    55fa:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55fd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5605:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5608:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5610:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    561b:	e8 00 ce ff ff       	call   2420 <__memcpy_chk@plt>
    5620:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5625:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    562a:	48 8d 35 e1 2a 00 00 	lea    0x2ae1(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    5631:	48 29 d9             	sub    %rbx,%rcx
    5634:	ba 0b 00 00 00       	mov    $0xb,%edx
    5639:	e8 e2 cd ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    563e:	48 89 e6             	mov    %rsp,%rsi
    5641:	4c 89 f7             	mov    %r14,%rdi
    5644:	e8 e7 cd ff ff       	call   2430 <stat@plt>
    5649:	83 f8 ff             	cmp    $0xffffffff,%eax
    564c:	0f 85 2d ff ff ff    	jne    557f <handle_get_method+0x8f>
    5652:	4c 89 f2             	mov    %r14,%rdx
    5655:	48 89 e9             	mov    %rbp,%rcx
    5658:	48 8d 35 be 2a 00 00 	lea    0x2abe(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    565f:	31 c0                	xor    %eax,%eax
    5661:	bf 01 00 00 00       	mov    $0x1,%edi
    5666:	e8 45 ce ff ff       	call   24b0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    566b:	48 8b 3d 9e 59 00 00 	mov    0x599e(%rip),%rdi        # b010 <http_404_content>
    5672:	4c 89 ea             	mov    %r13,%rdx
    5675:	44 89 e6             	mov    %r12d,%esi
    5678:	e8 03 fd ff ff       	call   5380 <_send_static_string_content>
}
    567d:	e9 39 ff ff ff       	jmp    55bb <handle_get_method+0xcb>
    5682:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5688:	bf 70 00 00 00       	mov    $0x70,%edi
    568d:	e8 de cd ff ff       	call   2470 <malloc@plt>
    5692:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5695:	48 85 c0             	test   %rax,%rax
    5698:	74 5d                	je     56f7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    569a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    569e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    56a3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    56a7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    56aa:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    56b1:	e8 5a f5 ff ff       	call   4c10 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    56b6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    56bb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    56bf:	4c 89 f7             	mov    %r14,%rdi
    56c2:	e8 79 fa ff ff       	call   5140 <copy_file_contents>
    56c7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    56cc:	4c 89 f2             	mov    %r14,%rdx
    56cf:	31 c0                	xor    %eax,%eax
    56d1:	48 8d 35 5d 2a 00 00 	lea    0x2a5d(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    56d8:	bf 01 00 00 00       	mov    $0x1,%edi
    56dd:	e8 ce cd ff ff       	call   24b0 <__printf_chk@plt>
            add_write_request(req, ring);
    56e2:	4c 89 ee             	mov    %r13,%rsi
    56e5:	48 89 df             	mov    %rbx,%rdi
    56e8:	e8 13 fb ff ff       	call   5200 <add_write_request>
    56ed:	e9 c9 fe ff ff       	jmp    55bb <handle_get_method+0xcb>
}
    56f2:	e8 89 cc ff ff       	call   2380 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    56f7:	48 8b 0d 22 59 00 00 	mov    0x5922(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    56fe:	ba 28 00 00 00       	mov    $0x28,%edx
    5703:	be 01 00 00 00       	mov    $0x1,%esi
    5708:	48 8d 3d a9 2e 00 00 	lea    0x2ea9(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    570f:	e8 1c ce ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5714:	bf 01 00 00 00       	mov    $0x1,%edi
    5719:	e8 f2 cd ff ff       	call   2510 <exit@plt>
    571e:	66 90                	xchg   %ax,%ax

0000000000005720 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5720:	f3 0f 1e fa          	endbr64
    5724:	41 57                	push   %r15
    5726:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5728:	4c 8d 35 7d 29 00 00 	lea    0x297d(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    572f:	41 55                	push   %r13
    5731:	49 89 d5             	mov    %rdx,%r13
    5734:	41 54                	push   %r12
    5736:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5739:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    573c:	55                   	push   %rbp
    573d:	53                   	push   %rbx
    573e:	48 83 ec 18          	sub    $0x18,%rsp
    5742:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    574b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5750:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5752:	49 89 e7             	mov    %rsp,%r15
    5755:	4c 89 fa             	mov    %r15,%rdx
    5758:	e8 83 cc ff ff       	call   23e0 <strtok_r@plt>
    for (; *str; ++str)
    575d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5761:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5764:	84 db                	test   %bl,%bl
    5766:	74 1d                	je     5785 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5768:	e8 23 ce ff ff       	call   2590 <__ctype_tolower_loc@plt>
    576d:	48 89 ea             	mov    %rbp,%rdx
    5770:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    5773:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    5777:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    577a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    577d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5781:	84 db                	test   %bl,%bl
    5783:	75 eb                	jne    5770 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5785:	4c 89 fa             	mov    %r15,%rdx
    5788:	4c 89 f6             	mov    %r14,%rsi
    578b:	31 ff                	xor    %edi,%edi
    578d:	e8 4e cc ff ff       	call   23e0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5792:	48 8d 35 c1 29 00 00 	lea    0x29c1(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    5799:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    579c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    579f:	e8 6c cc ff ff       	call   2410 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    57a4:	4c 89 ea             	mov    %r13,%rdx
    57a7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    57aa:	85 c0                	test   %eax,%eax
    57ac:	75 2a                	jne    57d8 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    57ae:	48 89 df             	mov    %rbx,%rdi
    57b1:	e8 3a fd ff ff       	call   54f0 <handle_get_method>
}
    57b6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    57bb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    57c4:	75 20                	jne    57e6 <handle_http_method+0xc6>
    57c6:	48 83 c4 18          	add    $0x18,%rsp
    57ca:	5b                   	pop    %rbx
    57cb:	5d                   	pop    %rbp
    57cc:	41 5c                	pop    %r12
    57ce:	41 5d                	pop    %r13
    57d0:	41 5e                	pop    %r14
    57d2:	41 5f                	pop    %r15
    57d4:	c3                   	ret
    57d5:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    57d8:	48 8b 3d 39 58 00 00 	mov    0x5839(%rip),%rdi        # b018 <unimplemented_content>
    57df:	e8 9c fb ff ff       	call   5380 <_send_static_string_content>
}
    57e4:	eb d0                	jmp    57b6 <handle_http_method+0x96>
    57e6:	e8 95 cb ff ff       	call   2380 <__stack_chk_fail@plt>
    57eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000057f0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    57f0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    57f4:	85 d2                	test   %edx,%edx
    57f6:	7e 38                	jle    5830 <get_line+0x40>
    57f8:	48 63 d2             	movslq %edx,%rdx
    57fb:	48 83 c7 01          	add    $0x1,%rdi
    57ff:	48 01 f2             	add    %rsi,%rdx
    5802:	eb 11                	jmp    5815 <get_line+0x25>
    5804:	0f 1f 40 00          	nopl   0x0(%rax)
    5808:	48 83 c6 01          	add    $0x1,%rsi
    580c:	48 83 c7 01          	add    $0x1,%rdi
    5810:	48 39 d6             	cmp    %rdx,%rsi
    5813:	74 1b                	je     5830 <get_line+0x40>
        dest[i] = src[i];
    5815:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5819:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    581b:	3c 0d                	cmp    $0xd,%al
    581d:	75 e9                	jne    5808 <get_line+0x18>
    581f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5822:	75 e4                	jne    5808 <get_line+0x18>
            dest[i] = '\0';
    5824:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5827:	31 c0                	xor    %eax,%eax
    5829:	c3                   	ret
    582a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5830:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5835:	c3                   	ret
    5836:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005840 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5840:	f3 0f 1e fa          	endbr64
    5844:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    584b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    584f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5858:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5860:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5862:	49 89 e2             	mov    %rsp,%r10
    5865:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    586d:	4c 89 d0             	mov    %r10,%rax
    5870:	eb 13                	jmp    5885 <handle_client_request+0x45>
    5872:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5878:	48 83 c0 01          	add    $0x1,%rax
    587c:	48 83 c1 01          	add    $0x1,%rcx
    5880:	4c 39 c8             	cmp    %r9,%rax
    5883:	74 4b                	je     58d0 <handle_client_request+0x90>
        dest[i] = src[i];
    5885:	44 0f b6 01          	movzbl (%rcx),%r8d
    5889:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    588c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5890:	75 e6                	jne    5878 <handle_client_request+0x38>
    5892:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5896:	75 e0                	jne    5878 <handle_client_request+0x38>
            dest[i] = '\0';
    5898:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    589b:	8b 47 08             	mov    0x8(%rdi),%eax
    589e:	48 89 f2             	mov    %rsi,%rdx
    58a1:	4c 89 d7             	mov    %r10,%rdi
    58a4:	89 c6                	mov    %eax,%esi
    58a6:	e8 75 fe ff ff       	call   5720 <handle_http_method>
}
    58ab:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    58b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    58bc:	75 39                	jne    58f7 <handle_client_request+0xb7>
    58be:	31 c0                	xor    %eax,%eax
    58c0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    58c7:	c3                   	ret
    58c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    58d0:	48 8b 0d 49 57 00 00 	mov    0x5749(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    58d7:	ba 12 00 00 00       	mov    $0x12,%edx
    58dc:	be 01 00 00 00       	mov    $0x1,%esi
    58e1:	48 8d 3d 76 28 00 00 	lea    0x2876(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    58e8:	e8 43 cc ff ff       	call   2530 <fwrite@plt>
        exit(1);
    58ed:	bf 01 00 00 00       	mov    $0x1,%edi
    58f2:	e8 19 cc ff ff       	call   2510 <exit@plt>
}
    58f7:	e8 84 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    58fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005900 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5900:	f3 0f 1e fa          	endbr64
    5904:	55                   	push   %rbp
    5905:	53                   	push   %rbx
    5906:	48 89 cb             	mov    %rcx,%rbx
    5909:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    590d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5910:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5913:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5919:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    591c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    591f:	f6 c1 02             	test   $0x2,%cl
    5922:	74 00                	je     5924 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5924:	41 89 c0             	mov    %eax,%r8d
    5927:	45 29 c8             	sub    %r9d,%r8d
    592a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    592e:	0f 82 d8 cc ff ff    	jb     260c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5934:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5937:	8b 6b 44             	mov    0x44(%rbx),%ebp
    593a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    593d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5940:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5943:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5947:	d3 e5                	shl    %cl,%ebp
    5949:	48 c1 e5 06          	shl    $0x6,%rbp
    594d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5951:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5954:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5959:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5960:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5964:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5968:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5970:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5978:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    597c:	e8 ef ca ff ff       	call   2470 <malloc@plt>
  io_uring_submit(ring);
    5981:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5984:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    598a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    598e:	48 83 c4 08          	add    $0x8,%rsp
    5992:	5b                   	pop    %rbx
    5993:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5994:	e9 f7 c9 ff ff       	jmp    2390 <io_uring_submit@plt>
    5999:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000059a0 <io_thread>:
void* io_thread(void *arg) {
    59a0:	f3 0f 1e fa          	endbr64
    59a4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    59a6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    59a8:	41 56                	push   %r14
    59aa:	41 55                	push   %r13
    59ac:	41 54                	push   %r12
    59ae:	55                   	push   %rbp
    59af:	48 89 fd             	mov    %rdi,%rbp
    59b2:	53                   	push   %rbx
    59b3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    59ba:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    59c3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    59cb:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    59cf:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    59d4:	bf 00 01 00 00       	mov    $0x100,%edi
    59d9:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    59dc:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    59e0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    59e5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    59ea:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    59ef:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    59f4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    59fc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5a01:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5a09:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5a0e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5a16:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5a1b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5a23:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5a28:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5a30:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5a35:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    5a3d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5a45:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5a4d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5a55:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5a5d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5a65:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5a6d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5a75:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5a7d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5a85:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5a8d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5a94:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a9c:	e8 af c9 ff ff       	call   2450 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5aa1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5aa5:	31 f6                	xor    %esi,%esi
    5aa7:	e8 a4 ca ff ff       	call   2550 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5aac:	31 d2                	xor    %edx,%edx
    5aae:	be 01 00 00 00       	mov    $0x1,%esi
    5ab3:	bf 02 00 00 00       	mov    $0x2,%edi
    5ab8:	e8 f3 ca ff ff       	call   25b0 <socket@plt>
  if (sock == -1)
    5abd:	83 f8 ff             	cmp    $0xffffffff,%eax
    5ac0:	0f 84 88 cb ff ff    	je     264e <io_thread.cold+0x38>
  if (setsockopt(sock,
    5ac6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5acb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5ad1:	89 c7                	mov    %eax,%edi
    5ad3:	41 89 c4             	mov    %eax,%r12d
    5ad6:	ba 02 00 00 00       	mov    $0x2,%edx
    5adb:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5ae0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5ae8:	e8 53 c8 ff ff       	call   2340 <setsockopt@plt>
    5aed:	85 c0                	test   %eax,%eax
    5aef:	0f 88 2d cb ff ff    	js     2622 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5af5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    5afa:	ba 10 00 00 00       	mov    $0x10,%edx
    5aff:	44 89 e7             	mov    %r12d,%edi
    5b02:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5b0b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5b13:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    5b1b:	e8 a0 c9 ff ff       	call   24c0 <bind@plt>
    5b20:	85 c0                	test   %eax,%eax
    5b22:	0f 88 32 cb ff ff    	js     265a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5b28:	be 0a 00 00 00       	mov    $0xa,%esi
    5b2d:	44 89 e7             	mov    %r12d,%edi
    5b30:	e8 4b c9 ff ff       	call   2480 <listen@plt>
    5b35:	85 c0                	test   %eax,%eax
    5b37:	0f 88 f1 ca ff ff    	js     262e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5b3d:	ba db 18 00 00       	mov    $0x18db,%edx
    5b42:	48 8d 35 5a 26 00 00 	lea    0x265a(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5b49:	bf 01 00 00 00       	mov    $0x1,%edi
    5b4e:	31 c0                	xor    %eax,%eax
    5b50:	e8 5b c9 ff ff       	call   24b0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5b55:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5b5a:	48 89 d9             	mov    %rbx,%rcx
    5b5d:	44 89 e7             	mov    %r12d,%edi
    5b60:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5b65:	48 89 c6             	mov    %rax,%rsi
    5b68:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5b6d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5b72:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5b7a:	e8 81 fd ff ff       	call   5900 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5b7f:	bf 01 00 00 00       	mov    $0x1,%edi
    5b84:	be 10 00 00 00       	mov    $0x10,%esi
    5b89:	e8 72 c8 ff ff       	call   2400 <calloc@plt>
    void *buf = malloc(size);
    5b8e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5b93:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5b96:	e8 d5 c8 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5b9b:	48 85 c0             	test   %rax,%rax
    5b9e:	0f 84 ae 04 00 00    	je     6052 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5ba4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5ba8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5baf:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5bb6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5bbe:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5bc1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5bc6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5bc8:	f6 c1 02             	test   $0x2,%cl
    5bcb:	0f 85 0f 04 00 00    	jne    5fe0 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5bd1:	89 d0                	mov    %edx,%eax
    5bd3:	29 f0                	sub    %esi,%eax
    5bd5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5bdc:	0f 82 62 ca ff ff    	jb     2644 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5be2:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5be5:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5be9:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5bed:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5bf0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5bf7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5bfa:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5c01:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c08:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5c0a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5c0d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5c12:	48 c1 e0 06          	shl    $0x6,%rax
    5c16:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5c1e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5c24:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5c27:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5c2f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5c33:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5c3b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5c43:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5c47:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5c4b:	e8 40 c7 ff ff       	call   2390 <io_uring_submit@plt>
  while (data->running == 1) {
    5c50:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5c54:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5c59:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5c61:	0f 85 d7 01 00 00    	jne    5e3e <io_thread+0x49e>
    5c67:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5c6c:	4d 89 ce             	mov    %r9,%r14
    5c6f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5c74:	0f 1f 40 00          	nopl   0x0(%rax)
    5c78:	48 8d 3d 3a 25 00 00 	lea    0x253a(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5c7f:	e8 ac c6 ff ff       	call   2330 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5c84:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5c8b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5c92:	c1 e9 0b             	shr    $0xb,%ecx
    5c95:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5c98:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5ca0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5ca2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5caa:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5cac:	39 d0                	cmp    %edx,%eax
    5cae:	74 36                	je     5ce6 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5cb0:	89 f8                	mov    %edi,%eax
    5cb2:	21 d0                	and    %edx,%eax
    5cb4:	d3 e0                	shl    %cl,%eax
    5cb6:	48 c1 e0 04          	shl    $0x4,%rax
    5cba:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5cc2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5cca:	0f 85 a8 01 00 00    	jne    5e78 <io_thread+0x4d8>
    5cd0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5cd4:	0f 85 0e 03 00 00    	jne    5fe8 <io_thread+0x648>
			if (cqe->res < 0)
    5cda:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5cdd:	83 c2 01             	add    $0x1,%edx
    5ce0:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5ce2:	85 c0                	test   %eax,%eax
    5ce4:	79 b2                	jns    5c98 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5ce6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5cef:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5cf0:	45 31 c0             	xor    %r8d,%r8d
    5cf3:	31 d2                	xor    %edx,%edx
    5cf5:	b9 01 00 00 00       	mov    $0x1,%ecx
    5cfa:	4c 89 f6             	mov    %r14,%rsi
    5cfd:	48 89 df             	mov    %rbx,%rdi
    5d00:	e8 9b c7 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5d05:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5d08:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5d0d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5d11:	0f 84 e1 02 00 00    	je     5ff8 <io_thread+0x658>
    5d17:	48 8d 3d c1 24 00 00 	lea    0x24c1(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5d1e:	e8 0d c6 ff ff       	call   2330 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5d23:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5d28:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5d2b:	45 85 ff             	test   %r15d,%r15d
    5d2e:	0f 88 e2 c8 ff ff    	js     2616 <io_thread.cold>
      if (cqe->res < 0) {
    5d34:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5d37:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    5d3b:	85 c0                	test   %eax,%eax
    5d3d:	0f 88 d5 02 00 00    	js     6018 <io_thread+0x678>
      switch (req->event_type) {
    5d43:	41 83 f8 01          	cmp    $0x1,%r8d
    5d47:	0f 84 7b 01 00 00    	je     5ec8 <io_thread+0x528>
    5d4d:	41 83 f8 02          	cmp    $0x2,%r8d
    5d51:	0f 84 a1 01 00 00    	je     5ef8 <io_thread+0x558>
    5d57:	45 85 c0             	test   %r8d,%r8d
    5d5a:	0f 85 50 01 00 00    	jne    5eb0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5d60:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5d65:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5d6a:	48 89 d9             	mov    %rbx,%rcx
    5d6d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5d71:	e8 8a fb ff ff       	call   5900 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5d76:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5d7b:	48 89 de             	mov    %rbx,%rsi
    5d7e:	8b 78 08             	mov    0x8(%rax),%edi
    5d81:	e8 1a f5 ff ff       	call   52a0 <add_read_request>
              free(req);
    5d86:	4c 89 e7             	mov    %r12,%rdi
    5d89:	e8 72 c5 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5d8e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5d93:	48 85 c0             	test   %rax,%rax
    5d96:	0f 85 14 01 00 00    	jne    5eb0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    5d9c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5da3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5daa:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5dad:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5db2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5db4:	f6 c1 02             	test   $0x2,%cl
    5db7:	74 00                	je     5db9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5db9:	89 d0                	mov    %edx,%eax
    5dbb:	29 f0                	sub    %esi,%eax
    5dbd:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5dc4:	0f 82 70 c8 ff ff    	jb     263a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5dca:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5dcd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5dd2:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5dd6:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5dd9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5de0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5de3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5dea:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5df1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5df3:	8b 55 60             	mov    0x60(%rbp),%edx
    5df6:	48 c1 e0 06          	shl    $0x6,%rax
    5dfa:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5e02:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5e08:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5e0b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5e13:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5e17:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5e1f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5e27:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5e2b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5e2f:	e8 5c c5 ff ff       	call   2390 <io_uring_submit@plt>
  while (data->running == 1) {
    5e34:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5e38:	0f 84 3a fe ff ff    	je     5c78 <io_thread+0x2d8>
    5e3e:	48 8d 3d d3 23 00 00 	lea    0x23d3(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5e45:	e8 e6 c4 ff ff       	call   2330 <puts@plt>
}
    5e4a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5e52:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5e5b:	0f 85 18 02 00 00    	jne    6079 <io_thread+0x6d9>
    5e61:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5e68:	31 c0                	xor    %eax,%eax
    5e6a:	5b                   	pop    %rbx
    5e6b:	5d                   	pop    %rbp
    5e6c:	41 5c                	pop    %r12
    5e6e:	41 5d                	pop    %r13
    5e70:	41 5e                	pop    %r14
    5e72:	41 5f                	pop    %r15
    5e74:	c3                   	ret
    5e75:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5e78:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5e7d:	48 85 c0             	test   %rax,%rax
    5e80:	0f 84 6a fe ff ff    	je     5cf0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5e86:	48 83 38 01          	cmpq   $0x1,(%rax)
    5e8a:	0f 84 68 01 00 00    	je     5ff8 <io_thread+0x658>
    5e90:	48 8d 3d 48 23 00 00 	lea    0x2348(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5e97:	e8 94 c4 ff ff       	call   2330 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5e9c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5ea1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5ea4:	e9 8b fe ff ff       	jmp    5d34 <io_thread+0x394>
    5ea9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5eb0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5eb8:	8b 02                	mov    (%rdx),%eax
    5eba:	83 c0 01             	add    $0x1,%eax
    5ebd:	89 02                	mov    %eax,(%rdx)
}
    5ebf:	e9 d8 fe ff ff       	jmp    5d9c <io_thread+0x3fc>
    5ec4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5ec8:	85 c0                	test   %eax,%eax
    5eca:	75 74                	jne    5f40 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5ecc:	48 8b 0d 4d 51 00 00 	mov    0x514d(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5ed3:	ba 0f 00 00 00       	mov    $0xf,%edx
    5ed8:	be 01 00 00 00       	mov    $0x1,%esi
    5edd:	48 8d 3d 24 23 00 00 	lea    0x2324(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5ee4:	e8 47 c6 ff ff       	call   2530 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5ee9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5eee:	e9 a0 fe ff ff       	jmp    5d93 <io_thread+0x3f3>
    5ef3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5ef8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5efd:	45 31 ff             	xor    %r15d,%r15d
    5f00:	85 c0                	test   %eax,%eax
    5f02:	7e 20                	jle    5f24 <io_thread+0x584>
    5f04:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5f08:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5f0b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5f0f:	48 c1 e0 04          	shl    $0x4,%rax
    5f13:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5f18:	e8 e3 c3 ff ff       	call   2300 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5f1d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5f22:	7f e4                	jg     5f08 <io_thread+0x568>
              close(req->client_socket);
    5f24:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5f29:	e8 a2 c4 ff ff       	call   23d0 <close@plt>
              free(req);
    5f2e:	4c 89 e7             	mov    %r12,%rdi
    5f31:	e8 ca c3 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5f36:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5f3b:	e9 53 fe ff ff       	jmp    5d93 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5f40:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5f45:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5f4a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5f52:	eb 11                	jmp    5f65 <io_thread+0x5c5>
    5f54:	0f 1f 40 00          	nopl   0x0(%rax)
    5f58:	48 83 c0 01          	add    $0x1,%rax
    5f5c:	48 83 c2 01          	add    $0x1,%rdx
    5f60:	48 39 c6             	cmp    %rax,%rsi
    5f63:	74 4b                	je     5fb0 <io_thread+0x610>
        dest[i] = src[i];
    5f65:	0f b6 0a             	movzbl (%rdx),%ecx
    5f68:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5f6a:	80 f9 0d             	cmp    $0xd,%cl
    5f6d:	75 e9                	jne    5f58 <io_thread+0x5b8>
    5f6f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5f73:	75 e3                	jne    5f58 <io_thread+0x5b8>
            dest[i] = '\0';
    5f75:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5f78:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5f7d:	48 89 da             	mov    %rbx,%rdx
    5f80:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5f85:	e8 96 f7 ff ff       	call   5720 <handle_http_method>
              free(req->iov[0].iov_base);
    5f8a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5f8f:	e8 6c c3 ff ff       	call   2300 <free@plt>
              free(req);
    5f94:	4c 89 e7             	mov    %r12,%rdi
    5f97:	e8 64 c3 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5f9c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5fa1:	e9 ed fd ff ff       	jmp    5d93 <io_thread+0x3f3>
    5fa6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5fb0:	48 8b 0d 69 50 00 00 	mov    0x5069(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5fb7:	ba 12 00 00 00       	mov    $0x12,%edx
    5fbc:	be 01 00 00 00       	mov    $0x1,%esi
    5fc1:	48 8d 3d 96 21 00 00 	lea    0x2196(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5fc8:	e8 63 c5 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5fcd:	bf 01 00 00 00       	mov    $0x1,%edi
    5fd2:	e8 39 c5 ff ff       	call   2510 <exit@plt>
    5fd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5fe0:	e9 ec fb ff ff       	jmp    5bd1 <io_thread+0x231>
    5fe5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5fe8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5fed:	e9 94 fe ff ff       	jmp    5e86 <io_thread+0x4e6>
    5ff2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5ff8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6000:	48 8d 3d c4 21 00 00 	lea    0x21c4(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    6007:	8b 02                	mov    (%rdx),%eax
    6009:	83 c0 01             	add    $0x1,%eax
    600c:	89 02                	mov    %eax,(%rdx)
    600e:	e8 1d c3 ff ff       	call   2330 <puts@plt>
    6013:	e9 26 fe ff ff       	jmp    5e3e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    6018:	f7 d8                	neg    %eax
    601a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    601f:	89 c7                	mov    %eax,%edi
    6021:	e8 4a c5 ff ff       	call   2570 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6026:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    602b:	be 01 00 00 00       	mov    $0x1,%esi
    6030:	48 8b 3d e9 4f 00 00 	mov    0x4fe9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    6037:	48 89 c1             	mov    %rax,%rcx
    603a:	48 8d 15 a7 25 00 00 	lea    0x25a7(%rip),%rdx        # 85e8 <_IO_stdin_used+0x5e8>
    6041:	31 c0                	xor    %eax,%eax
    6043:	e8 f8 c4 ff ff       	call   2540 <__fprintf_chk@plt>
          exit(1);
    6048:	bf 01 00 00 00       	mov    $0x1,%edi
    604d:	e8 be c4 ff ff       	call   2510 <exit@plt>
    6052:	48 8b 0d c7 4f 00 00 	mov    0x4fc7(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6059:	ba 28 00 00 00       	mov    $0x28,%edx
    605e:	be 01 00 00 00       	mov    $0x1,%esi
    6063:	48 8d 3d 4e 25 00 00 	lea    0x254e(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    606a:	e8 c1 c4 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    606f:	bf 01 00 00 00       	mov    $0x1,%edi
    6074:	e8 97 c4 ff ff       	call   2510 <exit@plt>
}
    6079:	e8 02 c3 ff ff       	call   2380 <__stack_chk_fail@plt>
    607e:	66 90                	xchg   %ax,%ax

0000000000006080 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    6080:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6084:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    608b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    6091:	85 c9                	test   %ecx,%ecx
    6093:	0f 8e ea 00 00 00    	jle    6183 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    6099:	41 56                	push   %r14
    609b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    609d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    60a0:	41 54                	push   %r12
    60a2:	49 89 fc             	mov    %rdi,%r12
    60a5:	55                   	push   %rbp
    60a6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    60a7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    60ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60b0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    60b4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    60bc:	31 db                	xor    %ebx,%ebx
    60be:	8b 10                	mov    (%rax),%edx
    60c0:	85 d2                	test   %edx,%edx
    60c2:	7e 26                	jle    60ea <barriered_work_ingest+0x6a>
    60c4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    60c8:	48 89 dd             	mov    %rbx,%rbp
    60cb:	48 c1 e5 08          	shl    $0x8,%rbp
    60cf:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    60d3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    60da:	74 24                	je     6100 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    60dc:	48 83 c3 01          	add    $0x1,%rbx
    60e0:	39 da                	cmp    %ebx,%edx
    60e2:	7f e4                	jg     60c8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    60e4:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    60ea:	49 83 c5 01          	add    $0x1,%r13
    60ee:	44 39 e9             	cmp    %r13d,%ecx
    60f1:	7f bd                	jg     60b0 <barriered_work_ingest+0x30>
}
    60f3:	5b                   	pop    %rbx
    60f4:	31 c0                	xor    %eax,%eax
    60f6:	5d                   	pop    %rbp
    60f7:	41 5c                	pop    %r12
    60f9:	41 5d                	pop    %r13
    60fb:	41 5e                	pop    %r14
    60fd:	c3                   	ret
    60fe:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    6100:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    6109:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    6110:	bf 04 00 00 00       	mov    $0x4,%edi
    6115:	48 c1 e6 05          	shl    $0x5,%rsi
    6119:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    6120:	48 83 c6 10          	add    $0x10,%rsi
    6124:	e8 27 c2 ff ff       	call   2350 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6129:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    6131:	48 8b 40 50          	mov    0x50(%rax),%rax
    6135:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    6139:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    613d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6147:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    614d:	83 c0 01             	add    $0x1,%eax
    6150:	99                   	cltd
    6151:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    6157:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    615d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6160:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    6168:	48 83 c3 01          	add    $0x1,%rbx
    616c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6170:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    6174:	8b 10                	mov    (%rax),%edx
    6176:	39 da                	cmp    %ebx,%edx
    6178:	0f 8f 46 ff ff ff    	jg     60c4 <barriered_work_ingest+0x44>
    617e:	e9 61 ff ff ff       	jmp    60e4 <barriered_work_ingest+0x64>
}
    6183:	31 c0                	xor    %eax,%eax
    6185:	c3                   	ret
    6186:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006190 <barriered_thread>:
void* barriered_thread(void *arg) {
    6190:	f3 0f 1e fa          	endbr64
    6194:	41 56                	push   %r14
    6196:	41 55                	push   %r13
    6198:	41 54                	push   %r12
  int t = 0;
    619a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    619d:	55                   	push   %rbp
  int waiting = 0;
    619e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    61a0:	53                   	push   %rbx
    61a1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    61a4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    61a8:	0f 85 74 02 00 00    	jne    6422 <barriered_thread+0x292>
    if (t >= data->task_count) {
    61ae:	8b 43 40             	mov    0x40(%rbx),%eax
    61b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    61b8:	41 39 c4             	cmp    %eax,%r12d
    61bb:	0f 8d 6f 01 00 00    	jge    6330 <barriered_thread+0x1a0>
    61c1:	49 63 fc             	movslq %r12d,%rdi
    61c4:	48 c1 e7 09          	shl    $0x9,%rdi
    61c8:	49 89 fd             	mov    %rdi,%r13
    61cb:	eb 32                	jmp    61ff <barriered_thread+0x6f>
    61cd:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    61d0:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    61d4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    61d8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    61dc:	48 8b 78 38          	mov    0x38(%rax),%rdi
    61e0:	4c 01 ef             	add    %r13,%rdi
    61e3:	e8 98 fe ff ff       	call   6080 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    61e8:	8b 43 40             	mov    0x40(%rbx),%eax
    61eb:	41 83 c4 01          	add    $0x1,%r12d
    61ef:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    61f6:	44 39 e0             	cmp    %r12d,%eax
    61f9:	0f 8e 19 02 00 00    	jle    6418 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    61ff:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6203:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    6207:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    620e:	75 c0                	jne    61d0 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6210:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    6214:	83 e8 01             	sub    $0x1,%eax
    6217:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    621c:	45 85 e4             	test   %r12d,%r12d
    621f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6222:	45 85 c0             	test   %r8d,%r8d
    6225:	0f 8e 2d 01 00 00    	jle    6358 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    622b:	48 63 c8             	movslq %eax,%rcx
    622e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6232:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    6235:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    623b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    6242:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    6246:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    6249:	45 31 f6             	xor    %r14d,%r14d
    624c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6250:	48 8b 10             	mov    (%rax),%rdx
    6253:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6257:	49 01 cb             	add    %rcx,%r11
    625a:	4c 89 da             	mov    %r11,%rdx
    625d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6264:	75 04                	jne    626a <barriered_thread+0xda>
            arrived++;
    6266:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    626a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6270:	75 04                	jne    6276 <barriered_thread+0xe6>
            prearrive++;
    6272:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6276:	48 83 c0 08          	add    $0x8,%rax
    627a:	48 39 c6             	cmp    %rax,%rsi
    627d:	75 d1                	jne    6250 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    627f:	45 85 d2             	test   %r10d,%r10d
    6282:	0f 84 c0 00 00 00    	je     6348 <barriered_thread+0x1b8>
    6288:	45 39 d0             	cmp    %r10d,%r8d
    628b:	0f 84 b7 00 00 00    	je     6348 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    6291:	45 85 f6             	test   %r14d,%r14d
    6294:	74 0a                	je     62a0 <barriered_thread+0x110>
    6296:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    629a:	0f 85 ae 01 00 00    	jne    644e <barriered_thread+0x2be>
    62a0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    62a4:	4c 01 ea             	add    %r13,%rdx
    62a7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    62ae:	45 85 e4             	test   %r12d,%r12d
    62b1:	75 14                	jne    62c7 <barriered_thread+0x137>
    62b3:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    62ba:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    62c1:	0f 8c 69 01 00 00    	jl     6430 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    62c7:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    62cb:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    62cf:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    62d9:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    62dd:	48 8b 78 38          	mov    0x38(%rax),%rdi
    62e1:	4c 01 ef             	add    %r13,%rdi
    62e4:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    62ea:	48 8b 43 38          	mov    0x38(%rbx),%rax
    62ee:	4c 01 e8             	add    %r13,%rax
    62f1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    62f8:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    62fb:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6300:	83 e8 01             	sub    $0x1,%eax
    6303:	44 39 e0             	cmp    %r12d,%eax
    6306:	0f 84 a4 00 00 00    	je     63b0 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    630c:	0f ae f8             	sfence
          if (waiting == 0) {
    630f:	85 ed                	test   %ebp,%ebp
    6311:	0f 84 d1 00 00 00    	je     63e8 <barriered_thread+0x258>
        int arrived = 0; 
    6317:	bd 01 00 00 00       	mov    $0x1,%ebp
    631c:	e9 c7 fe ff ff       	jmp    61e8 <barriered_thread+0x58>
  while (data->running == 1) {
    6321:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6325:	0f 85 f7 00 00 00    	jne    6422 <barriered_thread+0x292>
    632b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    6330:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    6338:	85 c0                	test   %eax,%eax
    633a:	7e e5                	jle    6321 <barriered_thread+0x191>
    633c:	45 31 e4             	xor    %r12d,%r12d
    633f:	e9 7d fe ff ff       	jmp    61c1 <barriered_thread+0x31>
    6344:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6348:	83 fd 01             	cmp    $0x1,%ebp
    634b:	74 1b                	je     6368 <barriered_thread+0x1d8>
        int arrived = 0; 
    634d:	31 ed                	xor    %ebp,%ebp
    634f:	e9 3d ff ff ff       	jmp    6291 <barriered_thread+0x101>
    6354:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6358:	83 fd 01             	cmp    $0x1,%ebp
    635b:	0f 85 43 ff ff ff    	jne    62a4 <barriered_thread+0x114>
        int arrived = 0; 
    6361:	45 31 f6             	xor    %r14d,%r14d
    6364:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6368:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    636f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    6374:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6376:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    637a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6381:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6386:	e8 c5 bf ff ff       	call   2350 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    638b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6392:	48 83 c0 01          	add    $0x1,%rax
    6396:	48 99                	cqto
    6398:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    639f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    63a6:	e9 e6 fe ff ff       	jmp    6291 <barriered_thread+0x101>
    63ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    63b0:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    63b7:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    63be:	0f 8d 48 ff ff ff    	jge    630c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    63c4:	48 c1 e6 04          	shl    $0x4,%rsi
    63c8:	bf 04 00 00 00       	mov    $0x4,%edi
    63cd:	48 03 73 70          	add    0x70(%rbx),%rsi
    63d1:	e8 7a bf ff ff       	call   2350 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    63d6:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    63de:	e9 29 ff ff ff       	jmp    630c <barriered_thread+0x17c>
    63e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    63e8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    63ef:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    63f4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    63f8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    63ff:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6403:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6407:	e8 44 bf ff ff       	call   2350 <clock_gettime@plt>
            waiting = 1;
    640c:	e9 06 ff ff ff       	jmp    6317 <barriered_thread+0x187>
    6411:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    6418:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    641c:	0f 84 96 fd ff ff    	je     61b8 <barriered_thread+0x28>
}
    6422:	5b                   	pop    %rbx
    6423:	31 c0                	xor    %eax,%eax
    6425:	5d                   	pop    %rbp
    6426:	41 5c                	pop    %r12
    6428:	41 5d                	pop    %r13
    642a:	41 5e                	pop    %r14
    642c:	c3                   	ret
    642d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    6430:	48 c1 e6 04          	shl    $0x4,%rsi
    6434:	bf 04 00 00 00       	mov    $0x4,%edi
    6439:	48 03 73 68          	add    0x68(%rbx),%rsi
    643d:	e8 0e bf ff ff       	call   2350 <clock_gettime@plt>
          data->tasks[t].available = 0;
    6442:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6446:	4c 01 ea             	add    %r13,%rdx
    6449:	e9 79 fe ff ff       	jmp    62c7 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    644e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6452:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6456:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    645a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    645e:	4c 01 ef             	add    %r13,%rdi
    6461:	e8 1a fc ff ff       	call   6080 <barriered_work_ingest>
          break;
    6466:	e9 39 fd ff ff       	jmp    61a4 <barriered_thread+0x14>
    646b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006470 <receive>:
int receive(struct BarrierTask *data) {
    6470:	f3 0f 1e fa          	endbr64
    6474:	41 56                	push   %r14
    6476:	41 55                	push   %r13
    6478:	41 54                	push   %r12
    647a:	55                   	push   %rbp
    647b:	53                   	push   %rbx
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    647c:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    6483:	45 85 e4             	test   %r12d,%r12d
    6486:	0f 8e 27 01 00 00    	jle    65b3 <receive+0x143>
    if (n == data->thread->real_thread_index) { continue; }
    648c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    6493:	48 89 fe             	mov    %rdi,%rsi
    6496:	31 db                	xor    %ebx,%ebx
    6498:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    649c:	49 89 ed             	mov    %rbp,%r13
    649f:	90                   	nop
    64a0:	41 39 dd             	cmp    %ebx,%r13d
    64a3:	0f 84 fd 00 00 00    	je     65a6 <receive+0x136>
    struct Data *me = data->mailboxes[n].lower;
    64a9:	48 89 d8             	mov    %rbx,%rax
    64ac:	48 c1 e0 06          	shl    $0x6,%rax
    64b0:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    64b7:	48 8b 10             	mov    (%rax),%rdx
    if (me->available_reading == 1) {
    64ba:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    64c0:	83 f8 01             	cmp    $0x1,%eax
    64c3:	74 11                	je     64d6 <receive+0x66>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    64c5:	83 ba 18 03 00 00 02 	cmpl   $0x2,0x318(%rdx)
    64cc:	75 08                	jne    64d6 <receive+0x66>
    64ce:	85 c0                	test   %eax,%eax
    64d0:	0f 84 d0 00 00 00    	je     65a6 <receive+0x136>
    for (; me->messages_count > 0 ; ) {
    64d6:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    64dd:	48 85 ff             	test   %rdi,%rdi
    64e0:	0f 8e a2 00 00 00    	jle    6588 <receive+0x118>
    64e6:	4c 8b 8e 78 01 00 00 	mov    0x178(%rsi),%r9
    64ed:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    64f4:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
    64f8:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    64fb:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    64ff:	49 01 f9             	add    %rdi,%r9
    6502:	49 01 f8             	add    %rdi,%r8
    6505:	48 03 ba 10 03 00 00 	add    0x310(%rdx),%rdi
    650c:	eb 08                	jmp    6516 <receive+0xa6>
    650e:	66 90                	xchg   %ax,%ax
    for (; me->messages_count > 0 ; ) {
    6510:	48 83 e8 01          	sub    $0x1,%rax
    6514:	72 72                	jb     6588 <receive+0x118>
      data->sends++;
    6516:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
    6519:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
    6520:	48 29 c1             	sub    %rax,%rcx
    6523:	48 89 8e 78 01 00 00 	mov    %rcx,0x178(%rsi)
      data->n++;
    652a:	4c 89 c1             	mov    %r8,%rcx
    652d:	48 29 c1             	sub    %rax,%rcx
    6530:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
    6537:	48 89 f9             	mov    %rdi,%rcx
    653a:	48 29 c1             	sub    %rax,%rcx
    653d:	48 89 8a 10 03 00 00 	mov    %rcx,0x310(%rdx)
      if (me->messages[x]->group == data->group) {
    6544:	48 63 c8             	movslq %eax,%rcx
    6547:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    654b:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    654f:	75 bf                	jne    6510 <receive+0xa0>
    6551:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    6555:	75 b9                	jne    6510 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    6557:	49 63 46 04          	movslq 0x4(%r14),%rax
    655b:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    655d:	bf 01 00 00 00       	mov    $0x1,%edi
    6562:	ba 01 00 00 00       	mov    $0x1,%edx
    6567:	48 8d 35 a2 20 00 00 	lea    0x20a2(%rip),%rsi        # 8610 <_IO_stdin_used+0x610>
    656e:	48 39 e8             	cmp    %rbp,%rax
    6571:	0f 94 c1             	sete   %cl
    6574:	31 c0                	xor    %eax,%eax
    6576:	e8 35 bf ff ff       	call   24b0 <__printf_chk@plt>
        exit(1);
    657b:	bf 01 00 00 00       	mov    $0x1,%edi
    6580:	e8 8b bf ff ff       	call   2510 <exit@plt>
    6585:	0f 1f 00             	nopl   (%rax)
      me->available_reading = 0;
    6588:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    6592:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
    659c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    65a6:	48 83 c3 01          	add    $0x1,%rbx
    65aa:	49 39 dc             	cmp    %rbx,%r12
    65ad:	0f 85 ed fe ff ff    	jne    64a0 <receive+0x30>
  asm volatile ("sfence" ::: "memory");
    65b3:	0f ae f8             	sfence
}
    65b6:	31 c0                	xor    %eax,%eax
    65b8:	5b                   	pop    %rbx
    65b9:	5d                   	pop    %rbp
    65ba:	41 5c                	pop    %r12
    65bc:	41 5d                	pop    %r13
    65be:	41 5e                	pop    %r14
    65c0:	c3                   	ret
    65c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    65cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000065d0 <sendm>:
int sendm(struct BarrierTask *data) {
    65d0:	f3 0f 1e fa          	endbr64
    65d4:	41 57                	push   %r15
    65d6:	48 89 f9             	mov    %rdi,%rcx
    65d9:	41 56                	push   %r14
    65db:	41 55                	push   %r13
    65dd:	41 54                	push   %r12
    65df:	55                   	push   %rbp
    65e0:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    65e1:	48 63 bf 40 01 00 00 	movslq 0x140(%rdi),%rdi
    65e8:	85 ff                	test   %edi,%edi
    65ea:	7e 64                	jle    6650 <sendm+0x80>
        if (n == data->thread->real_thread_index) { continue; }
    65ec:	48 8b 81 28 01 00 00 	mov    0x128(%rcx),%rax
    65f3:	44 8b 48 08          	mov    0x8(%rax),%r9d
    65f7:	31 c0                	xor    %eax,%eax
    65f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6600:	41 39 c1             	cmp    %eax,%r9d
    6603:	74 42                	je     6647 <sendm+0x77>
        struct Data *them = data->mailboxes[n].higher;
    6605:	48 89 c2             	mov    %rax,%rdx
    6608:	48 c1 e2 06          	shl    $0x6,%rdx
    660c:	48 03 91 70 01 00 00 	add    0x170(%rcx),%rdx
    6613:	48 8b 52 08          	mov    0x8(%rdx),%rdx
        if (them->messages_count > 0) {
    6617:	48 8b b2 80 00 00 00 	mov    0x80(%rdx),%rsi
    661e:	48 85 f6             	test   %rsi,%rsi
    6621:	7f 24                	jg     6647 <sendm+0x77>
        if (them->available_sending == 1) {
    6623:	44 8b 82 00 01 00 00 	mov    0x100(%rdx),%r8d
    662a:	41 83 f8 01          	cmp    $0x1,%r8d
    662e:	74 0e                	je     663e <sendm+0x6e>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    6630:	83 ba 18 03 00 00 02 	cmpl   $0x2,0x318(%rdx)
    6637:	75 05                	jne    663e <sendm+0x6e>
    6639:	45 85 c0             	test   %r8d,%r8d
    663c:	74 09                	je     6647 <sendm+0x77>
        if (data->sending == 1) {
    663e:	83 b9 80 01 00 00 01 	cmpl   $0x1,0x180(%rcx)
    6645:	74 19                	je     6660 <sendm+0x90>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6647:	48 83 c0 01          	add    $0x1,%rax
    664b:	48 39 c7             	cmp    %rax,%rdi
    664e:	75 b0                	jne    6600 <sendm+0x30>
      asm volatile ("sfence" ::: "memory");
    6650:	0f ae f8             	sfence
}
    6653:	31 c0                	xor    %eax,%eax
    6655:	5b                   	pop    %rbx
    6656:	5d                   	pop    %rbp
    6657:	41 5c                	pop    %r12
    6659:	41 5d                	pop    %r13
    665b:	41 5e                	pop    %r14
    665d:	41 5f                	pop    %r15
    665f:	c3                   	ret
          for (; them->messages_count < min;) {
    6660:	48 63 aa 88 00 00 00 	movslq 0x88(%rdx),%rbp
    6667:	48 39 ee             	cmp    %rbp,%rsi
    666a:	0f 8d a5 00 00 00    	jge    6715 <sendm+0x145>
    6670:	48 8b 99 08 01 00 00 	mov    0x108(%rcx),%rbx
    6677:	4c 8b aa 08 03 00 00 	mov    0x308(%rdx),%r13
            them->messages[them->messages_count++] = data->message; 
    667e:	4c 8b 1a             	mov    (%rdx),%r11
    6681:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    6686:	48 89 eb             	mov    %rbp,%rbx
    6689:	48 29 f3             	sub    %rsi,%rbx
    668c:	4c 8d 43 ff          	lea    -0x1(%rbx),%r8
    6690:	49 83 f8 02          	cmp    $0x2,%r8
    6694:	0f 86 16 01 00 00    	jbe    67b0 <sendm+0x1e0>
    669a:	4c 8d 14 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r10
    66a2:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    66aa:	4f 8d 34 13          	lea    (%r11,%r10,1),%r14
    66ae:	4c 8d b9 88 01 00 00 	lea    0x188(%rcx),%r15
    66b5:	4f 8d 24 03          	lea    (%r11,%r8,1),%r12
    66b9:	4d 39 f7             	cmp    %r14,%r15
    66bc:	0f 83 7e 00 00 00    	jae    6740 <sendm+0x170>
    66c2:	4c 8d b1 90 01 00 00 	lea    0x190(%rcx),%r14
    66c9:	4d 39 f4             	cmp    %r14,%r12
    66cc:	73 72                	jae    6740 <sendm+0x170>
    66ce:	4d 01 d8             	add    %r11,%r8
    66d1:	4b 8d 34 13          	lea    (%r11,%r10,1),%rsi
    66d5:	0f 1f 00             	nopl   (%rax)
    66d8:	4c 8b 91 88 01 00 00 	mov    0x188(%rcx),%r10
          for (; them->messages_count < min;) {
    66df:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    66e3:	4d 89 50 f8          	mov    %r10,-0x8(%r8)
          for (; them->messages_count < min;) {
    66e7:	4c 39 c6             	cmp    %r8,%rsi
    66ea:	75 ec                	jne    66d8 <sendm+0x108>
    66ec:	0f 1f 40 00          	nopl   0x0(%rax)
    66f0:	48 8b 74 24 f0       	mov    -0x10(%rsp),%rsi
    66f5:	48 01 de             	add    %rbx,%rsi
    66f8:	4c 01 eb             	add    %r13,%rbx
    66fb:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
    6702:	48 89 9a 08 03 00 00 	mov    %rbx,0x308(%rdx)
    6709:	48 89 aa 80 00 00 00 	mov    %rbp,0x80(%rdx)
    6710:	4d 89 54 eb f8       	mov    %r10,-0x8(%r11,%rbp,8)
          them->available_sending = 0;
    6715:	c7 82 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdx)
          them->available_reading = 1;
    671f:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
          them->available_receiving = 1;
    6729:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
    6733:	e9 0f ff ff ff       	jmp    6647 <sendm+0x77>
    6738:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6740:	49 89 de             	mov    %rbx,%r14
    6743:	4c 8b 91 88 01 00 00 	mov    0x188(%rcx),%r10
    674a:	4d 89 e0             	mov    %r12,%r8
    674d:	49 d1 ee             	shr    %r14
    6750:	49 c1 e6 04          	shl    $0x4,%r14
    6754:	66 49 0f 6e c2       	movq   %r10,%xmm0
    6759:	4f 8d 3c 34          	lea    (%r12,%r14,1),%r15
    675d:	41 83 e6 10          	and    $0x10,%r14d
    6761:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    6765:	74 11                	je     6778 <sendm+0x1a8>
            them->messages[them->messages_count++] = data->message; 
    6767:	49 83 c0 10          	add    $0x10,%r8
    676b:	41 0f 11 04 24       	movups %xmm0,(%r12)
          for (; them->messages_count < min;) {
    6770:	4d 39 f8             	cmp    %r15,%r8
    6773:	74 15                	je     678a <sendm+0x1ba>
    6775:	0f 1f 00             	nopl   (%rax)
            them->messages[them->messages_count++] = data->message; 
    6778:	41 0f 11 00          	movups %xmm0,(%r8)
    677c:	49 83 c0 20          	add    $0x20,%r8
    6780:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    6785:	4d 39 f8             	cmp    %r15,%r8
    6788:	75 ee                	jne    6778 <sendm+0x1a8>
    678a:	49 89 d8             	mov    %rbx,%r8
    678d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6791:	4c 01 c6             	add    %r8,%rsi
    6794:	f6 c3 01             	test   $0x1,%bl
    6797:	0f 84 53 ff ff ff    	je     66f0 <sendm+0x120>
            them->messages[them->messages_count++] = data->message; 
    679d:	4c 8b 91 88 01 00 00 	mov    0x188(%rcx),%r10
    67a4:	4d 89 14 f3          	mov    %r10,(%r11,%rsi,8)
          for (; them->messages_count < min;) {
    67a8:	e9 43 ff ff ff       	jmp    66f0 <sendm+0x120>
    67ad:	0f 1f 00             	nopl   (%rax)
    67b0:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    67b8:	4c 8d 14 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r10
    67c0:	e9 09 ff ff ff       	jmp    66ce <sendm+0xfe>
    67c5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000067d0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    67d0:	f3 0f 1e fa          	endbr64
    67d4:	41 57                	push   %r15
    67d6:	41 56                	push   %r14
    67d8:	41 55                	push   %r13
    67da:	41 54                	push   %r12
    67dc:	55                   	push   %rbp
    67dd:	53                   	push   %rbx
    67de:	48 89 fb             	mov    %rdi,%rbx
    67e1:	48 83 ec 48          	sub    $0x48,%rsp
        int t = data->task_index;
    67e5:	8b 6f 04             	mov    0x4(%rdi),%ebp
  if (data->thread_index == data->task_index) {
    67e8:	39 af 30 01 00 00    	cmp    %ebp,0x130(%rdi)
    67ee:	74 60                	je     6850 <barriered_work+0x80>
    receive(data);
    67f0:	e8 7b fc ff ff       	call   6470 <receive>
    while (data->scheduled == 1) {
    67f5:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    67fc:	75 16                	jne    6814 <barriered_work+0x44>
    67fe:	66 90                	xchg   %ax,%ax
      data->n++;
    6800:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    6808:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    680b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6812:	74 ec                	je     6800 <barriered_work+0x30>
    sendm(data);
    6814:	48 89 df             	mov    %rbx,%rdi
    6817:	e8 b4 fd ff ff       	call   65d0 <sendm>
  if (t == data->thread_count - 1) {
    681c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6822:	83 e8 01             	sub    $0x1,%eax
    6825:	39 e8                	cmp    %ebp,%eax
    6827:	0f 84 53 02 00 00    	je     6a80 <barriered_work+0x2b0>
  data->swap = 0;
    682d:	c7 83 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbx)
  asm volatile ("sfence" ::: "memory");
    6837:	0f ae f8             	sfence
}
    683a:	48 83 c4 48          	add    $0x48,%rsp
    683e:	31 c0                	xor    %eax,%eax
    6840:	5b                   	pop    %rbx
    6841:	5d                   	pop    %rbp
    6842:	41 5c                	pop    %r12
    6844:	41 5d                	pop    %r13
    6846:	41 5e                	pop    %r14
    6848:	41 5f                	pop    %r15
    684a:	c3                   	ret
    684b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    receive(data);
    6850:	e8 1b fc ff ff       	call   6470 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6855:	8b 8b 40 01 00 00    	mov    0x140(%rbx),%ecx
    685b:	85 c9                	test   %ecx,%ecx
    685d:	0f 8e a4 04 00 00    	jle    6d07 <barriered_work+0x537>
              int next_task = abs((t + 1) % (data->thread_count));
    6863:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6869:	4c 63 cd             	movslq %ebp,%r9
    686c:	4c 63 f1             	movslq %ecx,%r14
    686f:	89 6c 24 0c          	mov    %ebp,0xc(%rsp)
        int b = data->thread->real_thread_index;
    6873:	4c 8b bb 28 01 00 00 	mov    0x128(%rbx),%r15
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    687a:	49 c1 e1 09          	shl    $0x9,%r9
    687e:	31 c9                	xor    %ecx,%ecx
    6880:	49 89 dc             	mov    %rbx,%r12
              int next_task = abs((t + 1) % (data->thread_count));
    6883:	89 44 24 20          	mov    %eax,0x20(%rsp)
        int b = data->thread->real_thread_index;
    6887:	49 63 47 08          	movslq 0x8(%r15),%rax
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    688b:	48 8d 34 40          	lea    (%rax,%rax,2),%rsi
        int b = data->thread->real_thread_index;
    688f:	48 89 c2             	mov    %rax,%rdx
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6892:	48 c1 e0 06          	shl    $0x6,%rax
    6896:	48 8d 34 f6          	lea    (%rsi,%rsi,8),%rsi
    689a:	48 89 04 24          	mov    %rax,(%rsp)
    689e:	41 89 d3             	mov    %edx,%r11d
    68a1:	4c 8d 2c f5 00 00 00 00 	lea    0x0(,%rsi,8),%r13
    68a9:	31 f6                	xor    %esi,%esi
    68ab:	eb 17                	jmp    68c4 <barriered_work+0xf4>
    68ad:	0f 1f 00             	nopl   (%rax)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    68b0:	48 83 c1 01          	add    $0x1,%rcx
    68b4:	48 81 c6 d8 00 00 00 	add    $0xd8,%rsi
    68bb:	4c 39 f1             	cmp    %r14,%rcx
    68be:	0f 84 3c 02 00 00    	je     6b00 <barriered_work+0x330>
              if (y == b) { continue; }
    68c4:	41 39 cb             	cmp    %ecx,%r11d
    68c7:	74 e7                	je     68b0 <barriered_work+0xe0>
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    68c9:	49 8b 57 20          	mov    0x20(%r15),%rdx
    68cd:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    68d2:	4a 8d 04 0f          	lea    (%rdi,%r9,1),%rax
    68d6:	44 8b 80 98 01 00 00 	mov    0x198(%rax),%r8d
    68dd:	45 85 c0             	test   %r8d,%r8d
    68e0:	75 ce                	jne    68b0 <barriered_work+0xe0>
    68e2:	4e 8b 44 2a 38       	mov    0x38(%rdx,%r13,1),%r8
    68e7:	4b 8d 14 08          	lea    (%r8,%r9,1),%rdx
    68eb:	44 8b 92 98 01 00 00 	mov    0x198(%rdx),%r10d
    68f2:	45 85 d2             	test   %r10d,%r10d
    68f5:	75 b9                	jne    68b0 <barriered_work+0xe0>
    68f7:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    68fe:	48 89 cd             	mov    %rcx,%rbp
    6901:	48 c1 e5 06          	shl    $0x6,%rbp
    6905:	83 7c 2a 38 02       	cmpl   $0x2,0x38(%rdx,%rbp,1)
    690a:	75 a4                	jne    68b0 <barriered_work+0xe0>
    690c:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6913:	48 8b 1c 24          	mov    (%rsp),%rbx
    6917:	83 7c 18 38 02       	cmpl   $0x2,0x38(%rax,%rbx,1)
    691c:	75 92                	jne    68b0 <barriered_work+0xe0>
                    for (int nn = 0; nn < data->thread_count; nn++) {
    691e:	48 63 44 24 20       	movslq 0x20(%rsp),%rax
    6923:	85 c0                	test   %eax,%eax
    6925:	7e 89                	jle    68b0 <barriered_work+0xe0>
    6927:	48 89 c2             	mov    %rax,%rdx
    692a:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    692f:	b8 70 01 00 00       	mov    $0x170,%eax
    6934:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    6939:	48 c1 e2 09          	shl    $0x9,%rdx
    693d:	44 89 5c 24 24       	mov    %r11d,0x24(%rsp)
    6942:	4c 8b 1c 24          	mov    (%rsp),%r11
    6946:	48 8d 9a 98 01 00 00 	lea    0x198(%rdx),%rbx
    694d:	48 89 74 24 28       	mov    %rsi,0x28(%rsp)
    6952:	8b 74 24 20          	mov    0x20(%rsp),%esi
    6956:	48 89 4c 24 30       	mov    %rcx,0x30(%rsp)
    695b:	48 89 c1             	mov    %rax,%rcx
    695e:	4c 89 74 24 38       	mov    %r14,0x38(%rsp)
    6963:	49 89 d6             	mov    %rdx,%r14
    6966:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
                      int next_task = abs((nn + 1) % data->thread_count);
    6970:	41 83 c2 01          	add    $0x1,%r10d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6974:	4d 8b 0c 08          	mov    (%r8,%rcx,1),%r9
                      int next_task = abs((nn + 1) % data->thread_count);
    6978:	44 89 d0             	mov    %r10d,%eax
    697b:	99                   	cltd
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    697c:	49 01 e9             	add    %rbp,%r9
                      int next_task = abs((nn + 1) % data->thread_count);
    697f:	f7 fe                	idiv   %esi
    return mailbox->lower;
    6981:	f3 41 0f 6f 09       	movdqu (%r9),%xmm1
    6986:	66 0f c6 c9 01       	shufpd $0x1,%xmm1,%xmm1
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    698b:	48 63 d2             	movslq %edx,%rdx
    698e:	48 c1 e2 09          	shl    $0x9,%rdx
    6992:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    699a:	4c 01 d8             	add    %r11,%rax
    return mailbox->higher;
    699d:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    69a1:	0f 11 08             	movups %xmm1,(%rax)
    69a4:	0f 12 d8             	movhlps %xmm0,%xmm3
    69a7:	66 49 0f 7e c7       	movq   %xmm0,%r15
    return mailbox->lower;
    69ac:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
    mailbox->lower = data;
    69b1:	41 0f 11 01          	movups %xmm0,(%r9)
    69b5:	66 48 0f 7e da       	movq   %xmm3,%rdx
    69ba:	41 b9 98 01 00 00    	mov    $0x198,%r9d
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
    69c0:	43 c7 04 08 01 00 00 00 	movl   $0x1,(%r8,%r9,1)
                        data->thread->all_threads[t2].tasks[jj].swap = 1;
    69c8:	42 c7 04 0f 01 00 00 00 	movl   $0x1,(%rdi,%r9,1)
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
    69d0:	49 81 c1 00 02 00 00 	add    $0x200,%r9
    69d7:	4c 39 cb             	cmp    %r9,%rbx
    69da:	75 e4                	jne    69c0 <barriered_work+0x1f0>
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    69dc:	4c 8b 0c 0f          	mov    (%rdi,%rcx,1),%r9
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    69e0:	48 8b 00             	mov    (%rax),%rax
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    69e3:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    69ee:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    69f5:	4f 8b 4c 19 08       	mov    0x8(%r9,%r11,1),%r9
    69fa:	41 c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r9)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6a05:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6a0f:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6a19:	44 39 d6             	cmp    %r10d,%esi
    6a1c:	0f 85 4e ff ff ff    	jne    6970 <barriered_work+0x1a0>
    6a22:	4c 89 f2             	mov    %r14,%rdx
    6a25:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6a2a:	44 8b 5c 24 24       	mov    0x24(%rsp),%r11d
    6a2f:	b8 70 01 00 00       	mov    $0x170,%eax
    6a34:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6a39:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    6a3e:	48 8d 9a 70 01 00 00 	lea    0x170(%rdx),%rbx
    6a45:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    6a4a:	4c 8b 3c 24          	mov    (%rsp),%r15
    6a4e:	66 90                	xchg   %ax,%ax
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6a50:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    6a54:	4d 8b 14 00          	mov    (%r8,%rax,1),%r10
    6a58:	4a 8b 14 3a          	mov    (%rdx,%r15,1),%rdx
    6a5c:	49 39 14 2a          	cmp    %rdx,(%r10,%rbp,1)
    6a60:	0f 84 ad 02 00 00    	je     6d13 <barriered_work+0x543>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6a66:	48 05 00 02 00 00    	add    $0x200,%rax
    6a6c:	48 39 c3             	cmp    %rax,%rbx
    6a6f:	75 df                	jne    6a50 <barriered_work+0x280>
    6a71:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    6a76:	e9 35 fe ff ff       	jmp    68b0 <barriered_work+0xe0>
    6a7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6a80:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    6a87:	85 d2                	test   %edx,%edx
    6a89:	0f 8e 9e fd ff ff    	jle    682d <barriered_work+0x5d>
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6a8f:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    6a96:	48 c1 e2 09          	shl    $0x9,%rdx
    6a9a:	48 63 41 08          	movslq 0x8(%rcx),%rax
    6a9e:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    6aa2:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    6aa6:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    6aaa:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    6aae:	48 8b 40 38          	mov    0x38(%rax),%rax
    6ab2:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    6ab6:	80 e6 02             	and    $0x2,%dh
    6ab9:	74 1d                	je     6ad8 <barriered_work+0x308>
    6abb:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6ac2:	48 05 00 02 00 00    	add    $0x200,%rax
    6ac8:	48 39 c8             	cmp    %rcx,%rax
    6acb:	0f 84 5c fd ff ff    	je     682d <barriered_work+0x5d>
    6ad1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6ad8:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
    6adf:	83 80 9c 03 00 00 01 	addl   $0x1,0x39c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6ae6:	48 05 00 04 00 00    	add    $0x400,%rax
    6aec:	48 39 c8             	cmp    %rcx,%rax
    6aef:	75 e7                	jne    6ad8 <barriered_work+0x308>
    6af1:	e9 37 fd ff ff       	jmp    682d <barriered_work+0x5d>
    6af6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6b00:	8b 6c 24 0c          	mov    0xc(%rsp),%ebp
    6b04:	4c 89 e3             	mov    %r12,%rbx
            int y = (k * data->thread->threads_per_group) + data->thread_index;
    6b07:	41 8b 87 c4 00 00 00 	mov    0xc4(%r15),%eax
    6b0e:	8b 93 94 01 00 00    	mov    0x194(%rbx),%edx
    6b14:	44 8b 93 30 01 00 00 	mov    0x130(%rbx),%r10d
    6b1b:	0f af d0             	imul   %eax,%edx
    6b1e:	41 01 d2             	add    %edx,%r10d
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6b21:	85 c0                	test   %eax,%eax
    6b23:	0f 8e 07 01 00 00    	jle    6c30 <barriered_work+0x460>
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6b29:	4d 63 d2             	movslq %r10d,%r10
    6b2c:	49 8b 7f 20          	mov    0x20(%r15),%rdi
    6b30:	48 63 d2             	movslq %edx,%rdx
    6b33:	4c 63 d8             	movslq %eax,%r11
    6b36:	4b 8d 0c 52          	lea    (%r10,%r10,2),%rcx
    6b3a:	48 89 d6             	mov    %rdx,%rsi
    6b3d:	49 01 d3             	add    %rdx,%r11
              int next_task = abs((t + 1) % (data->thread_count));
    6b40:	44 8b 83 34 01 00 00 	mov    0x134(%rbx),%r8d
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6b47:	48 8d 0c c9          	lea    (%rcx,%rcx,8),%rcx
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6b4b:	49 c1 e2 06          	shl    $0x6,%r10
    6b4f:	48 c1 e6 06          	shl    $0x6,%rsi
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6b53:	4c 8b 74 cf 38       	mov    0x38(%rdi,%rcx,8),%r14
    6b58:	48 63 cd             	movslq %ebp,%rcx
    6b5b:	49 c1 e3 06          	shl    $0x6,%r11
    6b5f:	48 c1 e1 09          	shl    $0x9,%rcx
    6b63:	4d 8b a4 0e 70 01 00 00 	mov    0x170(%r14,%rcx,1),%r12
    6b6b:	48 8d 0c 52          	lea    (%rdx,%rdx,2),%rcx
    6b6f:	48 8d 0c c9          	lea    (%rcx,%rcx,8),%rcx
    6b73:	4c 8d 0c cf          	lea    (%rdi,%rcx,8),%r9
    6b77:	eb 1b                	jmp    6b94 <barriered_work+0x3c4>
    6b79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6b80:	48 83 c6 40          	add    $0x40,%rsi
    6b84:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    6b8b:	4c 39 de             	cmp    %r11,%rsi
    6b8e:	0f 84 9c 00 00 00    	je     6c30 <barriered_work+0x460>
              if (kind == MAILBOX_FRIEND) {
    6b94:	41 83 7c 34 38 01    	cmpl   $0x1,0x38(%r12,%rsi,1)
    6b9a:	75 e4                	jne    6b80 <barriered_work+0x3b0>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6b9c:	49 8b 79 38          	mov    0x38(%r9),%rdi
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6ba0:	45 85 c0             	test   %r8d,%r8d
    6ba3:	7e db                	jle    6b80 <barriered_work+0x3b0>
    6ba5:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    6bac:	31 c9                	xor    %ecx,%ecx
    6bae:	eb 4a                	jmp    6bfa <barriered_work+0x42a>
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6bb0:	48 63 d2             	movslq %edx,%rdx
    6bb3:	48 c1 e2 09          	shl    $0x9,%rdx
    6bb7:	4d 8b bc 16 70 01 00 00 	mov    0x170(%r14,%rdx,1),%r15
    6bbf:	49 01 f7             	add    %rsi,%r15
    6bc2:	4c 89 fa             	mov    %r15,%rdx
    return mailbox->lower;
    6bc5:	4d 8b 3f             	mov    (%r15),%r15
                      if (dest->messages_count != 0) { 
    6bc8:	49 83 bf 80 00 00 00 00 	cmpq   $0x0,0x80(%r15)
    6bd0:	75 1c                	jne    6bee <barriered_work+0x41e>
    return mailbox->higher;
    6bd2:	f3 0f 7e 42 08       	movq   0x8(%rdx),%xmm0
    6bd7:	66 49 0f 6e d7       	movq   %r15,%xmm2
    mailbox->lower = data;
    6bdc:	4c 8b 78 08          	mov    0x8(%rax),%r15
    6be0:	66 0f 6c c2          	punpcklqdq %xmm2,%xmm0
    6be4:	4c 89 3a             	mov    %r15,(%rdx)
    6be7:	0f 11 00             	movups %xmm0,(%rax)
    mailbox->higher = data;
    6bea:	4c 89 6a 08          	mov    %r13,0x8(%rdx)
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6bee:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    6bf5:	41 39 c8             	cmp    %ecx,%r8d
    6bf8:	74 86                	je     6b80 <barriered_work+0x3b0>
                    int next_task = abs((nn + 1) % (data->thread_count));
    6bfa:	83 c1 01             	add    $0x1,%ecx
    6bfd:	89 c8                	mov    %ecx,%eax
    6bff:	99                   	cltd
    6c00:	41 f7 f8             	idiv   %r8d
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6c03:	48 8b 07             	mov    (%rdi),%rax
    6c06:	4c 01 d0             	add    %r10,%rax
    return mailbox->lower;
    6c09:	4c 8b 28             	mov    (%rax),%r13
                      if (source2->messages_count != 0) { 
    6c0c:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    6c14:	74 9a                	je     6bb0 <barriered_work+0x3e0>
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6c16:	48 83 c6 40          	add    $0x40,%rsi
    6c1a:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    6c21:	4c 39 de             	cmp    %r11,%rsi
    6c24:	0f 85 6a ff ff ff    	jne    6b94 <barriered_work+0x3c4>
    6c2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      receive(data);
    6c30:	48 89 df             	mov    %rbx,%rdi
    6c33:	e8 38 f8 ff ff       	call   6470 <receive>
      asm volatile ("sfence" ::: "memory");
    6c38:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6c3b:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6c42:	31 ff                	xor    %edi,%edi
    6c44:	48 c1 e6 05          	shl    $0x5,%rsi
    6c48:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6c4f:	e8 fc b6 ff ff       	call   2350 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6c54:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    6c5b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    6c62:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6c66:	8b 72 10             	mov    0x10(%rdx),%esi
    6c69:	44 8d 66 01          	lea    0x1(%rsi),%r12d
    6c6d:	44 89 62 10          	mov    %r12d,0x10(%rdx)
    while (data->scheduled == 1) {
    6c71:	75 57                	jne    6cca <barriered_work+0x4fa>
    6c73:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6c78:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    6c7f:	48 8b 40 18          	mov    0x18(%rax),%rax
    6c83:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
      data->n++;
    6c87:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6c8f:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6c93:	48 c1 e7 09          	shl    $0x9,%rdi
    6c97:	48 03 78 38          	add    0x38(%rax),%rdi
    6c9b:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    6ca1:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6ca4:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    6cab:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    6cb2:	74 c4                	je     6c78 <barriered_work+0x4a8>
    if (modcount != data->thread->protected_state->modcount) {
    6cb4:	48 8b 40 48          	mov    0x48(%rax),%rax
    6cb8:	44 3b 60 10          	cmp    0x10(%rax),%r12d
    6cbc:	74 0c                	je     6cca <barriered_work+0x4fa>
    6cbe:	48 8d 3d 81 15 00 00 	lea    0x1581(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6cc5:	e8 66 b6 ff ff       	call   2330 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6cca:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6cd1:	31 ff                	xor    %edi,%edi
    6cd3:	48 c1 e6 05          	shl    $0x5,%rsi
    6cd7:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6cde:	48 83 c6 10          	add    $0x10,%rsi
    6ce2:	e8 69 b6 ff ff       	call   2350 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6ce7:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6cee:	48 83 c0 01          	add    $0x1,%rax
    6cf2:	48 99                	cqto
    6cf4:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6cfb:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    6d02:	e9 15 fb ff ff       	jmp    681c <barriered_work+0x4c>
            int y = (k * data->thread->threads_per_group) + data->thread_index;
    6d07:	4c 8b bb 28 01 00 00 	mov    0x128(%rbx),%r15
    6d0e:	e9 f4 fd ff ff       	jmp    6b07 <barriered_work+0x337>
    6d13:	bf 01 00 00 00       	mov    $0x1,%edi
    6d18:	48 8d 35 0c 15 00 00 	lea    0x150c(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6d1f:	31 c0                	xor    %eax,%eax
    6d21:	e8 8a b7 ff ff       	call   24b0 <__printf_chk@plt>
                          exit(1);
    6d26:	bf 01 00 00 00       	mov    $0x1,%edi
    6d2b:	e8 e0 b7 ff ff       	call   2510 <exit@plt>

0000000000006d30 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6d30:	f3 0f 1e fa          	endbr64
    6d34:	53                   	push   %rbx
    6d35:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6d38:	e8 43 f3 ff ff       	call   6080 <barriered_work_ingest>
  barriered_work(data);
    6d3d:	48 89 df             	mov    %rbx,%rdi
}
    6d40:	5b                   	pop    %rbx
  barriered_work(data);
    6d41:	e9 8a fa ff ff       	jmp    67d0 <barriered_work>
    6d46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006d50 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6d50:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6d54:	85 f6                	test   %esi,%esi
    6d56:	74 10                	je     6d68 <mailboxkind+0x18>
  return NULL;
    6d58:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    6d5a:	83 fe 01             	cmp    $0x1,%esi
    6d5d:	74 01                	je     6d60 <mailboxkind+0x10>
}
    6d5f:	c3                   	ret
    return mailbox->higher;
    6d60:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    6d64:	c3                   	ret
    6d65:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
    6d68:	48 8b 07             	mov    (%rdi),%rax
    6d6b:	c3                   	ret
    6d6c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006d70 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    6d70:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6d74:	85 d2                	test   %edx,%edx
    6d76:	75 08                	jne    6d80 <setmailboxkind+0x10>
    mailbox->lower = data;
    6d78:	48 89 37             	mov    %rsi,(%rdi)
}
    6d7b:	31 c0                	xor    %eax,%eax
    6d7d:	c3                   	ret
    6d7e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    6d80:	83 fa 01             	cmp    $0x1,%edx
    6d83:	74 13                	je     6d98 <setmailboxkind+0x28>
  if (kind == 2) {
    6d85:	83 fa 02             	cmp    $0x2,%edx
    6d88:	75 16                	jne    6da0 <setmailboxkind+0x30>
    mailbox->pending_lower = data;
    6d8a:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
    6d8e:	31 c0                	xor    %eax,%eax
    6d90:	c3                   	ret
    6d91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    mailbox->higher = data;
    6d98:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    6d9c:	31 c0                	xor    %eax,%eax
    6d9e:	c3                   	ret
    6d9f:	90                   	nop
  if (kind == 3) {
    6da0:	83 fa 03             	cmp    $0x3,%edx
    6da3:	75 d6                	jne    6d7b <setmailboxkind+0xb>
    mailbox->pending_higher = data;
    6da5:	48 89 77 18          	mov    %rsi,0x18(%rdi)
}
    6da9:	31 c0                	xor    %eax,%eax
    6dab:	c3                   	ret
    6dac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006db0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6db0:	f3 0f 1e fa          	endbr64
}
    6db4:	31 c0                	xor    %eax,%eax
    6db6:	c3                   	ret
    6db7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006dc0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6dc0:	f3 0f 1e fa          	endbr64
    6dc4:	31 c0                	xor    %eax,%eax
    6dc6:	c3                   	ret
    6dc7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006dd0 <after>:
int after(struct timespec left, struct timespec right) {
    6dd0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6dd4:	31 c0                	xor    %eax,%eax
    6dd6:	48 39 d7             	cmp    %rdx,%rdi
    6dd9:	7e 08                	jle    6de3 <after+0x13>
    6ddb:	31 c0                	xor    %eax,%eax
    6ddd:	48 39 ce             	cmp    %rcx,%rsi
    6de0:	0f 9f c0             	setg   %al
}
    6de3:	c3                   	ret
    6de4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6def:	90                   	nop

0000000000006df0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6df0:	f3 0f 1e fa          	endbr64
    6df4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6df9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    6dfe:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6e00:	48 39 d7             	cmp    %rdx,%rdi
    6e03:	7f 18                	jg     6e1d <within+0x2d>
    6e05:	4d 39 d8             	cmp    %r11,%r8
    6e08:	0f 9e c2             	setle  %dl
    6e0b:	48 39 ce             	cmp    %rcx,%rsi
    6e0e:	0f 9e c0             	setle  %al
    6e11:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6e13:	31 c0                	xor    %eax,%eax
    6e15:	4d 39 d1             	cmp    %r10,%r9
    6e18:	0f 9e c0             	setle  %al
    6e1b:	21 d0                	and    %edx,%eax
}
    6e1d:	c3                   	ret
    6e1e:	66 90                	xchg   %ax,%ax

0000000000006e20 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6e20:	f3 0f 1e fa          	endbr64
    6e24:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6e29:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6e2e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6e33:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6e38:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6e3d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6e42:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6e47:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6e4c:	48 39 fe             	cmp    %rdi,%rsi
    6e4f:	7d 2f                	jge    6e80 <overlap+0x60>
    6e51:	48 39 ca             	cmp    %rcx,%rdx
    6e54:	7d 62                	jge    6eb8 <overlap+0x98>
    6e56:	4d 39 da             	cmp    %r11,%r10
    6e59:	7d 0e                	jge    6e69 <overlap+0x49>
    return 1;
    6e5b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6e60:	4d 39 c1             	cmp    %r8,%r9
    6e63:	0f 8c 7f 00 00 00    	jl     6ee8 <overlap+0xc8>
  return 0;
    6e69:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6e6b:	4d 39 c1             	cmp    %r8,%r9
    6e6e:	7f 4c                	jg     6ebc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6e70:	31 c0                	xor    %eax,%eax
    6e72:	4d 39 da             	cmp    %r11,%r10
    6e75:	0f 9e c0             	setle  %al
    6e78:	c3                   	ret
    6e79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6e80:	7e 4e                	jle    6ed0 <overlap+0xb0>
    6e82:	48 39 ca             	cmp    %rcx,%rdx
    6e85:	7f 39                	jg     6ec0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6e87:	75 31                	jne    6eba <overlap+0x9a>
    6e89:	4d 39 c1             	cmp    %r8,%r9
    6e8c:	7c 2c                	jl     6eba <overlap+0x9a>
    return 1;
    6e8e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6e93:	4d 39 da             	cmp    %r11,%r10
    6e96:	7d 24                	jge    6ebc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6e98:	48 39 ca             	cmp    %rcx,%rdx
    6e9b:	0f 94 c2             	sete   %dl
    6e9e:	48 39 fe             	cmp    %rdi,%rsi
    6ea1:	0f 94 c0             	sete   %al
    6ea4:	21 c2                	and    %eax,%edx
    6ea6:	31 c0                	xor    %eax,%eax
    6ea8:	4d 39 c1             	cmp    %r8,%r9
    6eab:	0f 94 c0             	sete   %al
    6eae:	21 d0                	and    %edx,%eax
    6eb0:	c3                   	ret
    6eb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6eb8:	74 af                	je     6e69 <overlap+0x49>
  return 0;
    6eba:	31 c0                	xor    %eax,%eax
}
    6ebc:	c3                   	ret
    6ebd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6ec0:	4d 39 da             	cmp    %r11,%r10
    6ec3:	7e c4                	jle    6e89 <overlap+0x69>
    return 1;
    6ec5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6eca:	4d 39 c1             	cmp    %r8,%r9
    6ecd:	7e ba                	jle    6e89 <overlap+0x69>
    6ecf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6ed0:	48 39 ca             	cmp    %rcx,%rdx
    6ed3:	7c 94                	jl     6e69 <overlap+0x49>
    6ed5:	4d 39 c1             	cmp    %r8,%r9
    6ed8:	7d b4                	jge    6e8e <overlap+0x6e>
    6eda:	48 39 ca             	cmp    %rcx,%rdx
    6edd:	74 91                	je     6e70 <overlap+0x50>
    6edf:	eb d9                	jmp    6eba <overlap+0x9a>
    6ee1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6ee8:	c3                   	ret
    6ee9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006ef0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6ef0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6ef4:	85 f6                	test   %esi,%esi
    6ef6:	0f 8e 44 03 00 00    	jle    7240 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    6efc:	41 57                	push   %r15
    6efe:	41 89 f7             	mov    %esi,%r15d
    6f01:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6f03:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6f06:	41 55                	push   %r13
    6f08:	41 54                	push   %r12
    6f0a:	55                   	push   %rbp
    6f0b:	53                   	push   %rbx
    6f0c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6f10:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6f14:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6f19:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6f1e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6f21:	45 39 e6             	cmp    %r12d,%r14d
    6f24:	0f 84 4e 02 00 00    	je     7178 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6f2a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6f2f:	8b 50 08             	mov    0x8(%rax),%edx
    6f32:	85 d2                	test   %edx,%edx
    6f34:	0f 8e 3e 02 00 00    	jle    7178 <verify+0x288>
    6f3a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    6f3f:	31 c9                	xor    %ecx,%ecx
    6f41:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6f46:	31 c0                	xor    %eax,%eax
    6f48:	44 89 f2             	mov    %r14d,%edx
    6f4b:	bf 01 00 00 00       	mov    $0x1,%edi
    6f50:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6f55:	48 8d 35 fa 12 00 00 	lea    0x12fa(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    6f5c:	e8 4f b5 ff ff       	call   24b0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6f61:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6f66:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    6f6b:	8b 40 08             	mov    0x8(%rax),%eax
    6f6e:	85 c0                	test   %eax,%eax
    6f70:	0f 8e e6 01 00 00    	jle    715c <verify+0x26c>
    6f76:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6f79:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    6f7e:	31 db                	xor    %ebx,%ebx
    6f80:	48 c1 e0 09          	shl    $0x9,%rax
    6f84:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6f89:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6f8e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6f93:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6f98:	4c 8b 20             	mov    (%rax),%r12
    6f9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6fa0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6fa5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    6faa:	49 89 de             	mov    %rbx,%r14
    6fad:	48 8d 35 b7 12 00 00 	lea    0x12b7(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    6fb4:	49 c1 e6 09          	shl    $0x9,%r14
    6fb8:	bf 01 00 00 00       	mov    $0x1,%edi
    6fbd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6fc1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6fc9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    6fce:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6fd6:	31 c0                	xor    %eax,%eax
    6fd8:	e8 d3 b4 ff ff       	call   24b0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6fdd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6fe2:	4c 8b 20             	mov    (%rax),%r12
    6fe5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    6fee:	0f 8e 47 01 00 00    	jle    713b <verify+0x24b>
    6ff4:	4c 03 75 00          	add    0x0(%rbp),%r14
    6ff8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    6ffd:	ba 01 00 00 00       	mov    $0x1,%edx
    7002:	4d 89 f5             	mov    %r14,%r13
    7005:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    700c:	4d 85 f6             	test   %r14,%r14
    700f:	0f 8e 21 01 00 00    	jle    7136 <verify+0x246>
    7015:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    7018:	48 89 d5             	mov    %rdx,%rbp
    701b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7020:	31 db                	xor    %ebx,%ebx
    7022:	4d 89 f2             	mov    %r14,%r10
    7025:	48 c1 e5 05          	shl    $0x5,%rbp
    7029:	48 83 ed 20          	sub    $0x20,%rbp
    702d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    7031:	49 89 ee             	mov    %rbp,%r14
    7034:	48 89 dd             	mov    %rbx,%rbp
    7037:	48 89 d3             	mov    %rdx,%rbx
    703a:	eb 31                	jmp    706d <verify+0x17d>
    703c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    7040:	4c 39 c2             	cmp    %r8,%rdx
    7043:	0f 8d 57 01 00 00    	jge    71a0 <verify+0x2b0>
    7049:	4c 39 df             	cmp    %r11,%rdi
    704c:	7e 05                	jle    7053 <verify+0x163>
    704e:	49 39 c1             	cmp    %rax,%r9
    7051:	7c 75                	jl     70c8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7053:	4c 39 df             	cmp    %r11,%rdi
    7056:	0f 8d ab 01 00 00    	jge    7207 <verify+0x317>
    705c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7060:	48 83 c5 01          	add    $0x1,%rbp
    7064:	49 39 ea             	cmp    %rbp,%r10
    7067:	0f 8e a9 00 00 00    	jle    7116 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    706d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    7074:	48 89 e8             	mov    %rbp,%rax
    7077:	48 c1 e0 05          	shl    $0x5,%rax
    707b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    7082:	4c 01 f2             	add    %r14,%rdx
    7085:	48 8b 08             	mov    (%rax),%rcx
    7088:	48 8b 78 10          	mov    0x10(%rax),%rdi
    708c:	48 8b 32             	mov    (%rdx),%rsi
    708f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    7093:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    7097:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    709b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    709f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    70a3:	48 39 f1             	cmp    %rsi,%rcx
    70a6:	7c 98                	jl     7040 <verify+0x150>
    70a8:	0f 8e 42 01 00 00    	jle    71f0 <verify+0x300>
    70ae:	4c 39 c2             	cmp    %r8,%rdx
    70b1:	0f 8f f9 00 00 00    	jg     71b0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    70b7:	75 a7                	jne    7060 <verify+0x170>
    70b9:	4c 39 df             	cmp    %r11,%rdi
    70bc:	7f a2                	jg     7060 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    70be:	49 39 c1             	cmp    %rax,%r9
    70c1:	7c 9d                	jl     7060 <verify+0x170>
    70c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    70c8:	49 89 c1             	mov    %rax,%r9
    70cb:	48 89 f9             	mov    %rdi,%rcx
    70ce:	48 89 f2             	mov    %rsi,%rdx
    70d1:	bf 01 00 00 00       	mov    $0x1,%edi
    70d6:	48 8d 35 5b 15 00 00 	lea    0x155b(%rip),%rsi        # 8638 <_IO_stdin_used+0x638>
    70dd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    70df:	48 83 c5 01          	add    $0x1,%rbp
    70e3:	e8 c8 b3 ff ff       	call   24b0 <__printf_chk@plt>
    70e8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    70ed:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    70f2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    70f5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    70fa:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7101:	4c 8b 20             	mov    (%rax),%r12
    7104:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7109:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    710d:	49 39 ea             	cmp    %rbp,%r10
    7110:	0f 8f 57 ff ff ff    	jg     706d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7116:	48 89 da             	mov    %rbx,%rdx
    7119:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7120:	7d 14                	jge    7136 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7122:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7129:	48 83 c2 01          	add    $0x1,%rdx
    712d:	4d 85 f6             	test   %r14,%r14
    7130:	0f 8f e2 fe ff ff    	jg     7018 <verify+0x128>
    7136:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    713b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7140:	48 83 c3 01          	add    $0x1,%rbx
    7144:	39 58 08             	cmp    %ebx,0x8(%rax)
    7147:	0f 8f 53 fe ff ff    	jg     6fa0 <verify+0xb0>
    714d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    7152:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    7157:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    715c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7161:	48 83 c1 01          	add    $0x1,%rcx
    7165:	39 48 08             	cmp    %ecx,0x8(%rax)
    7168:	0f 8f d8 fd ff ff    	jg     6f46 <verify+0x56>
    716e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    7173:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    7178:	48 81 44 24 10 d8 00 00 00 	addq   $0xd8,0x10(%rsp)
    7181:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    7186:	41 39 c7             	cmp    %eax,%r15d
    7189:	0f 84 86 00 00 00    	je     7215 <verify+0x325>
    718f:	41 89 c4             	mov    %eax,%r12d
    7192:	e9 8a fd ff ff       	jmp    6f21 <verify+0x31>
    7197:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71a0:	0f 85 ba fe ff ff    	jne    7060 <verify+0x170>
    71a6:	e9 a8 fe ff ff       	jmp    7053 <verify+0x163>
    71ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    71b0:	49 39 c1             	cmp    %rax,%r9
    71b3:	7e 09                	jle    71be <verify+0x2ce>
    71b5:	4c 39 df             	cmp    %r11,%rdi
    71b8:	0f 8c 0a ff ff ff    	jl     70c8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71be:	4c 39 df             	cmp    %r11,%rdi
    71c1:	0f 8f 99 fe ff ff    	jg     7060 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    71c7:	49 39 c1             	cmp    %rax,%r9
    71ca:	0f 8d f8 fe ff ff    	jge    70c8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71d0:	48 39 f1             	cmp    %rsi,%rcx
    71d3:	0f 85 87 fe ff ff    	jne    7060 <verify+0x170>
    71d9:	4c 39 c2             	cmp    %r8,%rdx
    71dc:	0f 85 7e fe ff ff    	jne    7060 <verify+0x170>
    71e2:	4c 39 df             	cmp    %r11,%rdi
    71e5:	0f 84 dd fe ff ff    	je     70c8 <verify+0x1d8>
    71eb:	e9 70 fe ff ff       	jmp    7060 <verify+0x170>
    71f0:	4c 39 c2             	cmp    %r8,%rdx
    71f3:	0f 8c 5a fe ff ff    	jl     7053 <verify+0x163>
    71f9:	4c 39 df             	cmp    %r11,%rdi
    71fc:	7e c9                	jle    71c7 <verify+0x2d7>
    71fe:	4c 39 c2             	cmp    %r8,%rdx
    7201:	0f 85 59 fe ff ff    	jne    7060 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7207:	49 39 c1             	cmp    %rax,%r9
    720a:	0f 8f 50 fe ff ff    	jg     7060 <verify+0x170>
    7210:	e9 b3 fe ff ff       	jmp    70c8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    7215:	48 81 44 24 18 d8 00 00 00 	addq   $0xd8,0x18(%rsp)
    721e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7222:	45 39 e6             	cmp    %r12d,%r14d
    7225:	74 08                	je     722f <verify+0x33f>
    7227:	41 89 c6             	mov    %eax,%r14d
    722a:	e9 ea fc ff ff       	jmp    6f19 <verify+0x29>
}
    722f:	48 83 c4 58          	add    $0x58,%rsp
    7233:	31 c0                	xor    %eax,%eax
    7235:	5b                   	pop    %rbx
    7236:	5d                   	pop    %rbp
    7237:	41 5c                	pop    %r12
    7239:	41 5d                	pop    %r13
    723b:	41 5e                	pop    %r14
    723d:	41 5f                	pop    %r15
    723f:	c3                   	ret
    7240:	31 c0                	xor    %eax,%eax
    7242:	c3                   	ret

Disassembly of section .fini:

0000000000007244 <_fini>:
    7244:	f3 0f 1e fa          	endbr64
    7248:	48 83 ec 08          	sub    $0x8,%rsp
    724c:	48 83 c4 08          	add    $0x8,%rsp
    7250:	c3                   	ret
