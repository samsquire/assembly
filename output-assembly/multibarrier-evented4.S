
multibarrier-evented4:     file format elf64-x86-64


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
    26a4:	48 8d 05 45 1e 00 00 	lea    0x1e45(%rip),%rax        # 44f0 <barriered_reset>
    26ab:	66 48 0f 6e f8       	movq   %rax,%xmm7
    26b0:	0f 16 3d a1 85 00 00 	movhps 0x85a1(%rip),%xmm7        # ac58 <__do_global_dtors_aux_fini_array_entry+0x8>
    26b7:	0f 29 bc 24 b0 00 00 00 	movaps %xmm7,0xb0(%rsp)
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
    2a0b:	48 8d 35 0e 5d 00 00 	lea    0x5d0e(%rip),%rsi        # 8720 <_IO_stdin_used+0x720>
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
    2a5f:	0f 84 13 11 00 00    	je     3b78 <main+0x1508>
        other = abs(x - 1) % total_threads;
    2a65:	45 89 f5             	mov    %r14d,%r13d
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    2a68:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
        other = abs(x - 1) % total_threads;
    2a6d:	41 8d 55 fe          	lea    -0x2(%r13),%edx
        my_thread_data[0] = &thread_data[other]; 
    2a71:	48 8d 04 d5 00 00 00 00 	lea    0x0(,%rdx,8),%rax
        other = abs(x - 1) % total_threads;
    2a79:	49 89 d6             	mov    %rdx,%r14
        my_thread_data[0] = &thread_data[other]; 
    2a7c:	48 29 d0             	sub    %rdx,%rax
        my_thread_data[1] = &thread_data[x]; 
    2a7f:	4c 89 ca             	mov    %r9,%rdx
        my_thread_data[0] = &thread_data[other]; 
    2a82:	48 c1 e0 05          	shl    $0x5,%rax
    2a86:	48 01 f0             	add    %rsi,%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2a89:	48 8d 73 08          	lea    0x8(%rbx),%rsi
    2a8d:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    2a92:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
    2a9a:	48 89 03             	mov    %rax,(%rbx)
    2a9d:	44 89 f1             	mov    %r14d,%ecx
    2aa0:	48 8d 35 a9 5c 00 00 	lea    0x5ca9(%rip),%rsi        # 8750 <_IO_stdin_used+0x750>
        thread_data[x].thread_index = 1;
    2aa7:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2aab:	31 c0                	xor    %eax,%eax
        thread_data[x].protected_state = &protected_state[k];
    2aad:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2ab1:	bf 01 00 00 00       	mov    $0x1,%edi
    2ab6:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    2aba:	44 89 fa             	mov    %r15d,%edx
    2abd:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2ac2:	e8 e9 f9 ff ff       	call   24b0 <__printf_chk@plt>
      thread_data[x].other = other;
    2ac7:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2acc:	8b 4c 24 7c          	mov    0x7c(%rsp),%ecx
    2ad0:	31 c0                	xor    %eax,%eax
    2ad2:	44 89 fa             	mov    %r15d,%edx
    2ad5:	48 8d 35 a4 5c 00 00 	lea    0x5ca4(%rip),%rsi        # 8780 <_IO_stdin_used+0x780>
    2adc:	bf 01 00 00 00       	mov    $0x1,%edi
    2ae1:	45 89 b1 b8 00 00 00 	mov    %r14d,0xb8(%r9)
    2ae8:	e8 c3 f9 ff ff       	call   24b0 <__printf_chk@plt>
        if (x < thread_count) {
    2aed:	41 83 ff 01          	cmp    $0x1,%r15d
    2af1:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2af6:	0f 87 ab 10 00 00    	ja     3ba7 <main+0x1537>
          CPU_SET(curcpu, sendercpu);
    2afc:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2b01:	48 89 c7             	mov    %rax,%rdi
    2b04:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2b0a:	77 13                	ja     2b1f <main+0x4af>
    2b0c:	48 c1 e8 06          	shr    $0x6,%rax
    2b10:	ba 01 00 00 00       	mov    $0x1,%edx
    2b15:	89 f9                	mov    %edi,%ecx
    2b17:	48 d3 e2             	shl    %cl,%rdx
    2b1a:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
          curcpu += 2;
    2b1f:	83 44 24 7c 02       	addl   $0x2,0x7c(%rsp)
      thread_data[x].real_thread_index = x;
    2b24:	45 89 79 08          	mov    %r15d,0x8(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b28:	be 10 00 00 00       	mov    $0x10,%esi
    2b2d:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].swapmutex = swapmutex;
    2b32:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    2b3a:	49 89 a9 b0 00 00 00 	mov    %rbp,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2b41:	31 ed                	xor    %ebp,%ebp
      thread_data[x].swapmutex = swapmutex;
    2b43:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2b4a:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2b52:	49 89 59 18          	mov    %rbx,0x18(%r9)
            data[0].messages_count = 0;
    2b56:	44 89 fb             	mov    %r15d,%ebx
      thread_data[x].mswapmutex = mswapmutex;
    2b59:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].all_threads = thread_data;
    2b60:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].kind = KERNEL_THREAD;
    2b65:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].all_threads = thread_data;
    2b6c:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2b70:	48 8b 05 69 61 00 00 	mov    0x6169(%rip),%rax        # 8ce0 <_IO_stdin_used+0xce0>
      thread_data[x].task_count = total_barrier_count;
    2b77:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].group_count = group_count;
    2b7f:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2b86:	48 8b 05 5b 61 00 00 	mov    0x615b(%rip),%rax        # 8ce8 <_IO_stdin_used+0xce8>
      thread_data[x].task_count = total_barrier_count;
    2b8d:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].thread_count = 2;
    2b92:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b96:	e8 65 f8 ff ff       	call   2400 <calloc@plt>
    2b9b:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2ba0:	be 10 00 00 00       	mov    $0x10,%esi
    2ba5:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2baa:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2bae:	e8 4d f8 ff ff       	call   2400 <calloc@plt>
    2bb3:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bb8:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2bbd:	66 0f 6f 3d eb 60 00 00 	movdqa 0x60eb(%rip),%xmm7        # 8cb0 <_IO_stdin_used+0xcb0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bc5:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2bca:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2bce:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bd6:	e8 25 f8 ff ff       	call   2400 <calloc@plt>
    2bdb:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2be0:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2be5:	66 0f 6f 35 c3 60 00 00 	movdqa 0x60c3(%rip),%xmm6        # 8cb0 <_IO_stdin_used+0xcb0>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2bed:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bf2:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2bf9:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c01:	e8 fa f7 ff ff       	call   2400 <calloc@plt>
        thread_data[x].tasks = barriers;
    2c06:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c0b:	4c 89 ef             	mov    %r13,%rdi
            data[0].messages_count = 0;
    2c0e:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c16:	49 89 c6             	mov    %rax,%r14
        thread_data[x].tasks = barriers;
    2c19:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c1d:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
            data[0].messages_count = 0;
    2c22:	4c 89 f1             	mov    %r14,%rcx
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c25:	48 0f af f8          	imul   %rax,%rdi
            data[0].messages_count = 0;
    2c29:	4c 89 4c 24 50       	mov    %r9,0x50(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c2e:	48 c1 ef 22          	shr    $0x22,%rdi
    2c32:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2c35:	8b 7c 24 20          	mov    0x20(%rsp),%edi
    2c39:	01 c0                	add    %eax,%eax
    2c3b:	29 c7                	sub    %eax,%edi
            data[0].messages_count = 0;
    2c3d:	89 bc 24 98 00 00 00 	mov    %edi,0x98(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c44:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c47:	be 48 00 00 00       	mov    $0x48,%esi
    2c4c:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c51:	45 31 f6             	xor    %r14d,%r14d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c54:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2c59:	48 c1 e0 09          	shl    $0x9,%rax
    2c5d:	4c 8d 2c 01          	lea    (%rcx,%rax,1),%r13
    2c61:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2c66:	48 8d 05 43 18 00 00 	lea    0x1843(%rip),%rax        # 44b0 <do_protected_write>
    2c6d:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c74:	e8 87 f7 ff ff       	call   2400 <calloc@plt>
    2c79:	8b 74 24 58          	mov    0x58(%rsp),%esi
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2c7d:	49 89 85 70 01 00 00 	mov    %rax,0x170(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c84:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c87:	85 f6                	test   %esi,%esi
    2c89:	0f 84 7e 06 00 00    	je     330d <main+0xc9d>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2c8f:	8b 44 24 20          	mov    0x20(%rsp),%eax
    2c93:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    2c97:	49 89 cd             	mov    %rcx,%r13
    2c9a:	48 89 8c 24 88 00 00 00 	mov    %rcx,0x88(%rsp)
    2ca2:	83 e8 02             	sub    $0x2,%eax
    2ca5:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2ca9:	eb 17                	jmp    2cc2 <main+0x652>
    2cab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cb0:	41 83 c6 01          	add    $0x1,%r14d
    2cb4:	49 83 c5 48          	add    $0x48,%r13
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
    2cee:	49 83 c5 48          	add    $0x48,%r13
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
    2d2d:	41 0f 11 7d c8       	movups %xmm7,-0x38(%r13)
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
    2d6e:	49 89 45 c0          	mov    %rax,-0x40(%r13)
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
    2d8e:	4d 89 4d b8          	mov    %r9,-0x48(%r13)
    2d92:	41 89 45 f4          	mov    %eax,-0xc(%r13)
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
    2dc7:	41 c7 45 f0 01 00 00 00 	movl   $0x1,-0x10(%r13)
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
    2ec4:	66 0f ef f6          	pxor   %xmm6,%xmm6
            data[0].messages_count = 0;
    2ec8:	66 0f 6f 3d f0 5d 00 00 	movdqa 0x5df0(%rip),%xmm7        # 8cc0 <_IO_stdin_used+0xcc0>
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
    2f8a:	41 0f 11 75 10       	movups %xmm6,0x10(%r13)
            data[0].messages_count = 0;
    2f8f:	41 0f 29 be 80 00 00 00 	movaps %xmm7,0x80(%r14)
            data[1].messages_count = 0;
    2f97:	41 0f 29 be 00 04 00 00 	movaps %xmm7,0x400(%r14)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2f9f:	83 c3 01             	add    $0x1,%ebx
    2fa2:	49 83 c5 48          	add    $0x48,%r13
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
    30c9:	0f 85 dd 12 00 00    	jne    43ac <main+0x1d3c>
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
    3106:	0f 84 a1 03 00 00    	je     34ad <main+0xe3d>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    310c:	85 ed                	test   %ebp,%ebp
    310e:	0f 84 81 03 00 00    	je     3495 <main+0xe25>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    3114:	4c 8b 4c 24 50       	mov    0x50(%rsp),%r9
    3119:	48 8d 05 a0 37 00 00 	lea    0x37a0(%rip),%rax        # 68c0 <barriered_work>
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
    3153:	66 0f 6f b4 24 b0 00 00 00 	movdqa 0xb0(%rsp),%xmm6
    for (int d = 0 ; d < threads_per_group ; d++) {
    315c:	83 44 24 20 01       	addl   $0x1,0x20(%rsp)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3161:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3164:	48 83 c3 10          	add    $0x10,%rbx
    3168:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    316f:	49 89 81 70 ff ff ff 	mov    %rax,-0x90(%r9)
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
    31b3:	41 8b 81 24 ff ff ff 	mov    -0xdc(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    31ba:	41 0f 11 b6 18 05 00 00 	movups %xmm6,0x518(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    31c2:	41 89 86 30 05 00 00 	mov    %eax,0x530(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    31c9:	8b 44 24 20          	mov    0x20(%rsp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    31cd:	41 c7 86 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r14)
        thread_data[x].tasks[barrier_count].available = 1; 
    31d8:	4d 89 ae 44 05 00 00 	mov    %r13,0x544(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    31df:	39 84 24 9c 00 00 00 	cmp    %eax,0x9c(%rsp)
    31e6:	0f 85 13 f8 ff ff    	jne    29ff <main+0x38f>
    31ec:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
    31f4:	48 8b 9c 24 e0 00 00 00 	mov    0xe0(%rsp),%rbx
    31fc:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    3204:	48 8b ac 24 e8 00 00 00 	mov    0xe8(%rsp),%rbp
  for (int k = 0 ; k < group_count ; k++) {
    320c:	41 83 c7 01          	add    $0x1,%r15d
    3210:	48 81 c3 c0 01 00 00 	add    $0x1c0,%rbx
    3217:	48 83 c6 18          	add    $0x18,%rsi
    321b:	41 83 ff 03          	cmp    $0x3,%r15d
    321f:	0f 85 8e f7 ff ff    	jne    29b3 <main+0x343>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3225:	be 08 00 00 00       	mov    $0x8,%esi
    322a:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    322f:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3232:	e8 c9 f1 ff ff       	call   2400 <calloc@plt>
    3237:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    323c:	48 89 c5             	mov    %rax,%rbp
    323f:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3241:	49 89 d1             	mov    %rdx,%r9
    3244:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3246:	45 8b 51 40          	mov    0x40(%r9),%r10d
    324a:	45 85 d2             	test   %r10d,%r10d
    324d:	0f 8e a1 00 00 00    	jle    32f4 <main+0xc84>
    3253:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3257:	4d 63 c2             	movslq %r10d,%r8
    325a:	49 63 cc             	movslq %r12d,%rcx
    325d:	49 c1 e0 09          	shl    $0x9,%r8
    3261:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    3266:	49 01 f8             	add    %rdi,%r8
    3269:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3270:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3277:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    327e:	48 83 c6 60          	add    $0x60,%rsi
    3282:	f3 0f 7e 61 48       	movq   0x48(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3287:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    328b:	f3 0f 7e 99 90 00 00 00 	movq   0x90(%rcx),%xmm3
    3293:	f3 0f 7e 91 d8 00 00 00 	movq   0xd8(%rcx),%xmm2
    329b:	f3 0f 7e 89 20 01 00 00 	movq   0x120(%rcx),%xmm1
    32a3:	0f 16 61 50          	movhps 0x50(%rcx),%xmm4
    32a7:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    32ab:	f3 0f 7e 81 68 01 00 00 	movq   0x168(%rcx),%xmm0
    32b3:	0f 16 99 98 00 00 00 	movhps 0x98(%rcx),%xmm3
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    32ba:	0f 16 91 e0 00 00 00 	movhps 0xe0(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32c1:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    32c5:	0f 16 89 28 01 00 00 	movhps 0x128(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    32cc:	0f 16 81 70 01 00 00 	movhps 0x170(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32d3:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    32d7:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    32db:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    32df:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    32e3:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    32e7:	49 39 f8             	cmp    %rdi,%r8
    32ea:	75 84                	jne    3270 <main+0xc00>
    32ec:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    32f0:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    32f4:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    32fb:	85 db                	test   %ebx,%ebx
    32fd:	0f 85 b8 01 00 00    	jne    34bb <main+0xe4b>
    3303:	bb 01 00 00 00       	mov    $0x1,%ebx
    3308:	e9 39 ff ff ff       	jmp    3246 <main+0xbd6>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    330d:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    3311:	49 89 c5             	mov    %rax,%r13
    3314:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
    3319:	eb 17                	jmp    3332 <main+0xcc2>
    331b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3320:	41 83 c6 01          	add    $0x1,%r14d
    3324:	49 83 c5 48          	add    $0x48,%r13
    3328:	41 83 fe 06          	cmp    $0x6,%r14d
    332c:	0f 84 55 01 00 00    	je     3487 <main+0xe17>
            int group_of = b / threads_per_group;
    3332:	44 89 f3             	mov    %r14d,%ebx
    3335:	31 c0                	xor    %eax,%eax
    3337:	44 89 f2             	mov    %r14d,%edx
    333a:	bf 01 00 00 00       	mov    $0x1,%edi
    333f:	d1 fb                	sar    %ebx
    3341:	48 8d 35 74 50 00 00 	lea    0x5074(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    3348:	89 d9                	mov    %ebx,%ecx
    334a:	e8 61 f1 ff ff       	call   24b0 <__printf_chk@plt>
            if (k == group_of) {
    334f:	41 39 df             	cmp    %ebx,%r15d
    3352:	75 cc                	jne    3320 <main+0xcb0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3354:	be 08 00 00 00       	mov    $0x8,%esi
    3359:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    335e:	49 83 c5 48          	add    $0x48,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3362:	e8 99 f0 ff ff       	call   2400 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3367:	be 08 00 00 00       	mov    $0x8,%esi
    336c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3371:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3376:	e8 85 f0 ff ff       	call   2400 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    337b:	be 80 03 00 00       	mov    $0x380,%esi
    3380:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3385:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    338a:	e8 71 f0 ff ff       	call   2400 <calloc@plt>
              data[0].a = x;
    338f:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
              mailboxes[b].pending_lower = NULL;
    3393:	66 0f ef ff          	pxor   %xmm7,%xmm7
    3397:	44 89 f2             	mov    %r14d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    339a:	49 89 c1             	mov    %rax,%r9
              mailboxes[b].pending_lower = NULL;
    339d:	41 0f 11 7d c8       	movups %xmm7,-0x38(%r13)
    33a2:	bf 01 00 00 00       	mov    $0x1,%edi
    33a7:	48 8d 35 f2 53 00 00 	lea    0x53f2(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
              data[0].c = b;
    33ae:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
              data[0].kind = MAILBOX_LOWER;
    33b5:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].a = x;
    33bf:	89 98 1c 03 00 00    	mov    %ebx,0x31c(%rax)
              data[0].b = y;
    33c5:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    33cb:	41 8d 44 24 01       	lea    0x1(%r12),%eax
              data[1].id = dataid++;
    33d0:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    33d7:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    33de:	49 89 45 c0          	mov    %rax,-0x40(%r13)
    33e2:	8b 84 24 98 00 00 00 	mov    0x98(%rsp),%eax
              data[0].id = dataid++;
    33e9:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
              data[1].id = dataid++;
    33f0:	41 83 c4 02          	add    $0x2,%r12d
              data[1].c = b;
    33f4:	45 89 b1 a4 06 00 00 	mov    %r14d,0x6a4(%r9)
    33fb:	89 c1                	mov    %eax,%ecx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    33fd:	41 83 c6 01          	add    $0x1,%r14d
              mailboxes[b].lower = &data[0];
    3401:	4d 89 4d b8          	mov    %r9,-0x48(%r13)
    3405:	41 89 45 f4          	mov    %eax,-0xc(%r13)
    3409:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    340b:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].a = x;
    3416:	41 89 99 9c 06 00 00 	mov    %ebx,0x69c(%r9)
              data[1].b = y;
    341d:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    3424:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    342f:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    343a:	41 c7 45 f0 01 00 00 00 	movl   $0x1,-0x10(%r13)
              data[1].finished_reading = 1;
    3442:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    3447:	e8 64 f0 ff ff       	call   24b0 <__printf_chk@plt>
              data[0].messages = messages;
    344c:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3451:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
              data[0].messages_count = 0;
    3456:	66 0f 6f 3d 62 58 00 00 	movdqa 0x5862(%rip),%xmm7        # 8cc0 <_IO_stdin_used+0xcc0>
              data[1].messages = messages2;
    345e:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
              data[0].messages = messages;
    3463:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    3466:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    346d:	41 0f 29 b9 80 00 00 00 	movaps %xmm7,0x80(%r9)
              data[1].messages_count = 0;
    3475:	41 0f 29 b9 00 04 00 00 	movaps %xmm7,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    347d:	41 83 fe 06          	cmp    $0x6,%r14d
    3481:	0f 85 ab fe ff ff    	jne    3332 <main+0xcc2>
    3487:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    348b:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    3490:	e9 8b f9 ff ff       	jmp    2e20 <main+0x7b0>
    3495:	48 8d 05 e4 39 00 00 	lea    0x39e4(%rip),%rax        # 6e80 <barriered_work_ingest_andwork>
    349c:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    34a1:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    34a8:	e9 97 f7 ff ff       	jmp    2c44 <main+0x5d4>
    34ad:	48 8d 05 0c 34 00 00 	lea    0x340c(%rip),%rax        # 68c0 <barriered_work>
    34b4:	bd 02 00 00 00       	mov    $0x2,%ebp
    34b9:	eb e6                	jmp    34a1 <main+0xe31>
  for (int k = 0 ; k < group_count ; k++) {
    34bb:	83 c0 02             	add    $0x2,%eax
    34be:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    34c5:	83 f8 06             	cmp    $0x6,%eax
    34c8:	0f 85 73 fd ff ff    	jne    3241 <main+0xbd1>
    34ce:	48 8d 3d 15 4f 00 00 	lea    0x4f15(%rip),%rdi        # 83ea <_IO_stdin_used+0x3ea>
    34d5:	e8 56 ee ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    34da:	48 8d 35 1e 4f 00 00 	lea    0x4f1e(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    34e1:	48 8d 3d 19 4f 00 00 	lea    0x4f19(%rip),%rdi        # 8401 <_IO_stdin_used+0x401>
    34e8:	e8 03 f0 ff ff       	call   24f0 <fopen@plt>
    34ed:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas_size; x++) {
    34f0:	45 85 e4             	test   %r12d,%r12d
    34f3:	7e 77                	jle    356c <main+0xefc>
    34f5:	4d 63 e4             	movslq %r12d,%r12
    34f8:	4c 8d 35 df 4e 00 00 	lea    0x4edf(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    34ff:	4c 8d 2d 1c 4f 00 00 	lea    0x4f1c(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    3506:	4a 8d 44 e5 00       	lea    0x0(%rbp,%r12,8),%rax
    350b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    char * c = calloc(250, sizeof(char));
    3510:	be 01 00 00 00       	mov    $0x1,%esi
    3515:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    351a:	48 83 c5 08          	add    $0x8,%rbp
    char * c = calloc(250, sizeof(char));
    351e:	e8 dd ee ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3523:	4c 89 f1             	mov    %r14,%rcx
    3526:	ba fa 00 00 00       	mov    $0xfa,%edx
    352b:	be 01 00 00 00       	mov    $0x1,%esi
    3530:	49 89 c4             	mov    %rax,%r12
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    3533:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    3537:	4c 89 e7             	mov    %r12,%rdi
    353a:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3541:	31 c0                	xor    %eax,%eax
    3543:	e8 58 f0 ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3548:	4c 89 e2             	mov    %r12,%rdx
    354b:	4c 89 ee             	mov    %r13,%rsi
    354e:	bf 01 00 00 00       	mov    $0x1,%edi
    3553:	31 c0                	xor    %eax,%eax
    3555:	e8 56 ef ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    355a:	4c 89 fe             	mov    %r15,%rsi
    355d:	4c 89 e7             	mov    %r12,%rdi
    3560:	e8 5b ee ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    3565:	48 39 6c 24 08       	cmp    %rbp,0x8(%rsp)
    356a:	75 a4                	jne    3510 <main+0xea0>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    356c:	4c 89 ff             	mov    %r15,%rdi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    356f:	45 31 f6             	xor    %r14d,%r14d
    3572:	4c 8d 25 d3 4e 00 00 	lea    0x4ed3(%rip),%r12        # 844c <_IO_stdin_used+0x44c>
    3579:	e8 e2 ed ff ff       	call   2360 <fclose@plt>
    357e:	48 8d 3d 85 4e 00 00 	lea    0x4e85(%rip),%rdi        # 840a <_IO_stdin_used+0x40a>
    3585:	4c 89 f5             	mov    %r14,%rbp
    3588:	e8 a3 ed ff ff       	call   2330 <puts@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    358d:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    3591:	89 ea                	mov    %ebp,%edx
    3593:	48 8d 35 8b 4e 00 00 	lea    0x4e8b(%rip),%rsi        # 8425 <_IO_stdin_used+0x425>
    359a:	bf 01 00 00 00       	mov    $0x1,%edi
    359f:	31 c0                	xor    %eax,%eax
    35a1:	48 8d 1c ed 00 00 00 00 	lea    0x0(,%rbp,8),%rbx
    35a9:	44 8d 6c 2d 00       	lea    0x0(%rbp,%rbp,1),%r13d
    35ae:	45 31 ff             	xor    %r15d,%r15d
    35b1:	e8 fa ee ff ff       	call   24b0 <__printf_chk@plt>
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    35b6:	48 29 eb             	sub    %rbp,%rbx
    35b9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    35be:	48 c1 e3 06          	shl    $0x6,%rbx
    35c2:	48 01 c3             	add    %rax,%rbx
      int x = (k * threads_per_group) + d;
    35c5:	43 8d 0c 2f          	lea    (%r15,%r13,1),%ecx
    35c9:	44 89 fa             	mov    %r15d,%edx
    35cc:	48 8d 35 5c 4e 00 00 	lea    0x4e5c(%rip),%rsi        # 842f <_IO_stdin_used+0x42f>
    35d3:	31 c0                	xor    %eax,%eax
    35d5:	bf 01 00 00 00       	mov    $0x1,%edi
    35da:	45 31 f6             	xor    %r14d,%r14d
    35dd:	e8 ce ee ff ff       	call   24b0 <__printf_chk@plt>
    35e2:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
    35e7:	4c 89 f1             	mov    %r14,%rcx
    35ea:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    35ef:	48 89 dd             	mov    %rbx,%rbp
    35f2:	89 ca                	mov    %ecx,%edx
    35f4:	48 8d 35 46 4e 00 00 	lea    0x4e46(%rip),%rsi        # 8441 <_IO_stdin_used+0x441>
    35fb:	bf 01 00 00 00       	mov    $0x1,%edi
    3600:	31 c0                	xor    %eax,%eax
    3602:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    3607:	45 31 ed             	xor    %r13d,%r13d
    360a:	e8 a1 ee ff ff       	call   24b0 <__printf_chk@plt>
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    360f:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    3614:	48 c1 e3 09          	shl    $0x9,%rbx
    3618:	eb 2f                	jmp    3649 <main+0xfd9>
    361a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    3620:	83 ff 01             	cmp    $0x1,%edi
    3623:	0f 84 a5 00 00 00    	je     36ce <main+0x105e>
    3629:	44 8b 46 3c          	mov    0x3c(%rsi),%r8d
    362d:	44 89 f2             	mov    %r14d,%edx
    3630:	4c 89 e6             	mov    %r12,%rsi
    3633:	bf 01 00 00 00       	mov    $0x1,%edi
    3638:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    363a:	49 83 c5 01          	add    $0x1,%r13
    363e:	e8 6d ee ff ff       	call   24b0 <__printf_chk@plt>
    3643:	49 83 fd 06          	cmp    $0x6,%r13
    3647:	74 4f                	je     3698 <main+0x1028>
          char * mailbox_kind = calloc(100, sizeof(char));
    3649:	be 01 00 00 00       	mov    $0x1,%esi
    364e:	bf 64 00 00 00       	mov    $0x64,%edi
    3653:	45 89 ee             	mov    %r13d,%r14d
    3656:	e8 a5 ed ff ff       	call   2400 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    365b:	4c 8b 45 38          	mov    0x38(%rbp),%r8
          char * mailbox_kind = calloc(100, sizeof(char));
    365f:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3662:	4b 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%rax
    3667:	49 8b b4 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rsi
    366f:	48 c1 e0 03          	shl    $0x3,%rax
    3673:	48 01 c6             	add    %rax,%rsi
    3676:	8b 7e 38             	mov    0x38(%rsi),%edi
    3679:	83 ff 02             	cmp    $0x2,%edi
    367c:	75 a2                	jne    3620 <main+0xfb0>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    367e:	48 bf 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rdi
    3688:	48 89 39             	mov    %rdi,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    368b:	49 03 84 18 70 01 00 00 	add    0x170(%r8,%rbx,1),%rax
    3693:	48 89 c6             	mov    %rax,%rsi
    3696:	eb 91                	jmp    3629 <main+0xfb9>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3698:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    369d:	48 83 c1 01          	add    $0x1,%rcx
    36a1:	48 83 f9 03          	cmp    $0x3,%rcx
    36a5:	0f 85 47 ff ff ff    	jne    35f2 <main+0xf82>
    for (int d = 0 ; d < threads_per_group ; d++) {
    36ab:	48 89 eb             	mov    %rbp,%rbx
    36ae:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    36b3:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    36b8:	48 81 c3 e0 00 00 00 	add    $0xe0,%rbx
    36bf:	45 85 ff             	test   %r15d,%r15d
    36c2:	75 27                	jne    36eb <main+0x107b>
    36c4:	44 8b 7c 24 10       	mov    0x10(%rsp),%r15d
    36c9:	e9 f7 fe ff ff       	jmp    35c5 <main+0xf55>
    36ce:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    36d4:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    36db:	49 03 84 18 70 01 00 00 	add    0x170(%r8,%rbx,1),%rax
    36e3:	48 89 c6             	mov    %rax,%rsi
    36e6:	e9 3e ff ff ff       	jmp    3629 <main+0xfb9>
  for (int k = 0 ; k < group_count ; k++) {
    36eb:	48 83 c5 01          	add    $0x1,%rbp
    36ef:	48 83 fd 03          	cmp    $0x3,%rbp
    36f3:	0f 85 98 fe ff ff    	jne    3591 <main+0xf21>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    36f9:	ba 07 00 00 00       	mov    $0x7,%edx
    36fe:	48 8d 35 62 4d 00 00 	lea    0x4d62(%rip),%rsi        # 8467 <_IO_stdin_used+0x467>
    3705:	bf 01 00 00 00       	mov    $0x1,%edi
    370a:	31 c0                	xor    %eax,%eax
    370c:	e8 9f ed ff ff       	call   24b0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    3711:	be 08 00 00 00       	mov    $0x8,%esi
    3716:	bf 02 00 00 00       	mov    $0x2,%edi
    371b:	e8 e0 ec ff ff       	call   2400 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    3720:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3725:	be 38 00 00 00       	mov    $0x38,%esi
    372a:	bf 0a 00 00 00       	mov    $0xa,%edi
    my_thread_data[0] = &thread_data[x]; 
    372f:	4c 8d ad 20 06 00 00 	lea    0x620(%rbp),%r13
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3736:	48 89 68 08          	mov    %rbp,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    373a:	4c 8d a5 e0 00 00 00 	lea    0xe0(%rbp),%r12
    thread_data[x].threads = my_thread_data;
    3741:	48 89 85 38 06 00 00 	mov    %rax,0x638(%rbp)
    my_thread_data[0] = &thread_data[x]; 
    3748:	4c 89 28             	mov    %r13,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    374b:	48 8b 45 38          	mov    0x38(%rbp),%rax
    thread_data[x].thread_count = 2;
    374f:	c7 85 48 06 00 00 02 00 00 00 	movl   $0x2,0x648(%rbp)
    thread_data[x].thread_index = 0;
    3759:	c7 85 24 06 00 00 00 00 00 00 	movl   $0x0,0x624(%rbp)
    thread_data[x].task_count = total_barrier_count;
    3763:	c7 85 60 06 00 00 03 00 00 00 	movl   $0x3,0x660(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    376d:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3777:	48 8b 85 18 01 00 00 	mov    0x118(%rbp),%rax
    377e:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3788:	e8 73 ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    378d:	be 38 00 00 00       	mov    $0x38,%esi
    3792:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3797:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    379c:	e8 5f ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37a1:	be 38 00 00 00       	mov    $0x38,%esi
    37a6:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37ab:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37ae:	e8 4d ec ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37b3:	be 38 00 00 00       	mov    $0x38,%esi
    37b8:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37bd:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37c2:	e8 39 ec ff ff       	call   2400 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37c7:	be 08 00 00 00       	mov    $0x8,%esi
    37cc:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37d1:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37d6:	e8 25 ec ff ff       	call   2400 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    37db:	be 08 00 00 00       	mov    $0x8,%esi
    37e0:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
    37e5:	c7 85 4c 05 00 00 00 00 00 00 	movl   $0x0,0x54c(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37ef:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    37f2:	48 8b 05 ff 54 00 00 	mov    0x54ff(%rip),%rax        # 8cf8 <_IO_stdin_used+0xcf8>
    37f9:	48 89 85 80 05 00 00 	mov    %rax,0x580(%rbp)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3800:	e8 fb eb ff ff       	call   2400 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3805:	48 8d 95 c0 01 00 00 	lea    0x1c0(%rbp),%rdx
    380c:	48 89 ef             	mov    %rbp,%rdi
    380f:	48 8d 8d 40 05 00 00 	lea    0x540(%rbp),%rcx
    3816:	48 89 50 10          	mov    %rdx,0x10(%rax)
    381a:	48 8d 95 a0 02 00 00 	lea    0x2a0(%rbp),%rdx
    3821:	48 8d 35 4e 4c 00 00 	lea    0x4c4e(%rip),%rsi        # 8476 <_IO_stdin_used+0x476>
    3828:	48 89 50 18          	mov    %rdx,0x18(%rax)
    382c:	48 8d 95 80 03 00 00 	lea    0x380(%rbp),%rdx
    3833:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3837:	48 8d 95 60 04 00 00 	lea    0x460(%rbp),%rdx
    383e:	48 89 28             	mov    %rbp,(%rax)
    3841:	48 8d ad 00 07 00 00 	lea    0x700(%rbp),%rbp
    3848:	48 89 50 28          	mov    %rdx,0x28(%rax)
    384c:	48 8d 97 e0 07 00 00 	lea    0x7e0(%rdi),%rdx
    3853:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3857:	4c 89 68 38          	mov    %r13,0x38(%rax)
    385b:	48 89 50 48          	mov    %rdx,0x48(%rax)
    385f:	ba 06 00 00 00       	mov    $0x6,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3864:	48 89 87 58 05 00 00 	mov    %rax,0x558(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    386b:	4c 89 60 08          	mov    %r12,0x8(%rax)
    386f:	48 89 68 40          	mov    %rbp,0x40(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3873:	48 8b 05 86 54 00 00 	mov    0x5486(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    387a:	c7 87 70 05 00 00 06 00 00 00 	movl   $0x6,0x570(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3884:	48 89 87 68 05 00 00 	mov    %rax,0x568(%rdi)
    388b:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    388d:	c7 87 44 05 00 00 00 00 00 00 	movl   $0x0,0x544(%rdi)
    3897:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
    389c:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    38a1:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    38a6:	e8 05 ec ff ff       	call   24b0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38ab:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    38b0:	49 8d b6 50 01 00 00 	lea    0x150(%r14),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    38b7:	45 31 f6             	xor    %r14d,%r14d
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38ba:	48 8d 15 af 0d 00 00 	lea    0xdaf(%rip),%rdx        # 4670 <timer_thread>
    38c1:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    38c5:	e8 06 ec ff ff       	call   24d0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    38ca:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    38cf:	4c 89 ee             	mov    %r13,%rsi
    38d2:	48 89 d9             	mov    %rbx,%rcx
    38d5:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38da:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    38df:	4c 89 64 24 30       	mov    %r12,0x30(%rsp)
    38e4:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    38ea:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    38ef:	45 89 d5             	mov    %r10d,%r13d
    38f2:	44 89 7c 24 20       	mov    %r15d,0x20(%rsp)
    38f7:	49 89 c7             	mov    %rax,%r15
    for (int d = 0 ; d < threads_per_group ; d++) {
    38fa:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    38ff:	47 8d 24 36          	lea    (%r14,%r14,1),%r12d
    3903:	48 89 cd             	mov    %rcx,%rbp
    3906:	48 89 d3             	mov    %rdx,%rbx
    3909:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
    390e:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    3913:	4c 89 7c 24 48       	mov    %r15,0x48(%rsp)
    3918:	49 89 f7             	mov    %rsi,%r15
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    391b:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    3922:	44 89 e2             	mov    %r12d,%edx
    3925:	44 89 f1             	mov    %r14d,%ecx
    3928:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    392a:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    3931:	48 8d 35 c0 4e 00 00 	lea    0x4ec0(%rip),%rsi        # 87f8 <_IO_stdin_used+0x7f8>
    3938:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    393d:	41 83 c4 01          	add    $0x1,%r12d
    3941:	e8 6a eb ff ff       	call   24b0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3946:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    394b:	48 89 d9             	mov    %rbx,%rcx
    394e:	48 89 ef             	mov    %rbp,%rdi
    3951:	48 8d 15 b8 28 00 00 	lea    0x28b8(%rip),%rdx        # 6210 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3958:	48 81 c3 e0 00 00 00 	add    $0xe0,%rbx
    395f:	48 83 c5 08          	add    $0x8,%rbp
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3963:	e8 68 eb ff ff       	call   24d0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3968:	48 8b 53 d0          	mov    -0x30(%rbx),%rdx
    396c:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
    3970:	be 08 00 00 00       	mov    $0x8,%esi
    3975:	e8 a6 e9 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    397a:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3980:	45 39 e5             	cmp    %r12d,%r13d
    3983:	75 96                	jne    391b <main+0x12ab>
  for (int k = 0 ; k < group_count ; k++) {
    3985:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    398a:	4c 89 fe             	mov    %r15,%rsi
    398d:	41 83 c6 01          	add    $0x1,%r14d
    3991:	41 83 c5 02          	add    $0x2,%r13d
    3995:	4c 8b 7c 24 48       	mov    0x48(%rsp),%r15
    399a:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    399f:	48 83 c1 10          	add    $0x10,%rcx
    39a3:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    39aa:	49 83 c7 70          	add    $0x70,%r15
    39ae:	41 83 fe 03          	cmp    $0x3,%r14d
    39b2:	0f 85 42 ff ff ff    	jne    38fa <main+0x128a>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    39b8:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    39bd:	48 8b 05 44 53 00 00 	mov    0x5344(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    thread_data[x].type = IO;
    39c4:	49 89 f5             	mov    %rsi,%r13

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39c7:	bf 01 00 00 00       	mov    $0x1,%edi
    39cc:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    39d1:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    39d6:	4c 8b 64 24 30       	mov    0x30(%rsp),%r12
    39db:	41 c7 86 2c 06 00 00 02 00 00 00 	movl   $0x2,0x62c(%r14)
    39e6:	44 8b 7c 24 20       	mov    0x20(%rsp),%r15d
    thread_data[x].task_count = 0;
    39eb:	49 89 86 60 06 00 00 	mov    %rax,0x660(%r14)
    thread_data[x].type = IO;
    39f2:	48 8b 6c 24 40       	mov    0x40(%rsp),%rbp
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39f7:	e8 04 ea ff ff       	call   2400 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    39fc:	be 00 08 00 00       	mov    $0x800,%esi
    3a01:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a03:	49 89 86 78 06 00 00 	mov    %rax,0x678(%r14)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a0a:	e8 11 eb ff ff       	call   2520 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a0f:	be 08 00 00 00       	mov    $0x8,%esi
    3a14:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a19:	41 89 86 80 06 00 00 	mov    %eax,0x680(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a20:	e8 db e9 ff ff       	call   2400 <calloc@plt>
    3a25:	ba 07 00 00 00       	mov    $0x7,%edx
    3a2a:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3a2f:	41 c7 86 48 06 00 00 02 00 00 00 	movl   $0x2,0x648(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3a3a:	4c 89 30             	mov    %r14,(%rax)
    3a3d:	48 8d 35 50 4a 00 00 	lea    0x4a50(%rip),%rsi        # 8494 <_IO_stdin_used+0x494>
    thread_data[x].threads = my_thread_data;
    3a44:	49 89 86 38 06 00 00 	mov    %rax,0x638(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3a4b:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3a4f:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3a51:	41 c7 86 24 06 00 00 07 00 00 00 	movl   $0x7,0x624(%r14)
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a5c:	41 be 08 00 00 00    	mov    $0x8,%r14d
    3a62:	e8 49 ea ff ff       	call   24b0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3a67:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3a6c:	4c 89 e9             	mov    %r13,%rcx
    3a6f:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3a73:	48 8d 15 a6 1f 00 00 	lea    0x1fa6(%rip),%rdx        # 5a20 <io_thread>
    3a7a:	4c 8d 6b 40          	lea    0x40(%rbx),%r13
    3a7e:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3a85:	e8 46 ea ff ff       	call   24d0 <pthread_create@plt>
    3a8a:	ba 08 00 00 00       	mov    $0x8,%edx
    3a8f:	48 8d 35 15 4a 00 00 	lea    0x4a15(%rip),%rsi        # 84ab <_IO_stdin_used+0x4ab>
    3a96:	31 c0                	xor    %eax,%eax
    3a98:	bf 01 00 00 00       	mov    $0x1,%edi
    3a9d:	e8 0e ea ff ff       	call   24b0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3aa2:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3aa7:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    3aad:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3ab2:	44 89 f2             	mov    %r14d,%edx
    3ab5:	48 8d 35 05 4a 00 00 	lea    0x4a05(%rip),%rsi        # 84c1 <_IO_stdin_used+0x4c1>
    3abc:	bf 01 00 00 00       	mov    $0x1,%edi
    3ac1:	31 c0                	xor    %eax,%eax
    3ac3:	e8 e8 e9 ff ff       	call   24b0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3ac8:	be 08 00 00 00       	mov    $0x8,%esi
    3acd:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3ad2:	48 8b 05 2f 52 00 00 	mov    0x522f(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    thread_data[x].type = EXTERNAL;
    3ad9:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    thread_data[x].task_count = 0;
    3ae0:	48 89 45 40          	mov    %rax,0x40(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3ae4:	e8 17 e9 ff ff       	call   2400 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3ae9:	48 8b bc 24 c0 00 00 00 	mov    0xc0(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3af1:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3af6:	c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3b00:	48 89 45 50          	mov    %rax,0x50(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3b04:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3b07:	bf 02 00 00 00       	mov    $0x2,%edi
    3b0c:	e8 ef e8 ff ff       	call   2400 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3b11:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b16:	48 89 e9             	mov    %rbp,%rcx
    3b19:	4c 89 ef             	mov    %r13,%rdi
    thread_data[x].threads = my_thread_data;
    3b1c:	48 89 45 18          	mov    %rax,0x18(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b20:	48 8d 15 39 0a 00 00 	lea    0xa39(%rip),%rdx        # 4560 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b27:	49 83 c5 08          	add    $0x8,%r13
    3b2b:	48 81 c5 e0 00 00 00 	add    $0xe0,%rbp
      my_thread_data[n] = &thread_data[n]; 
    3b32:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b35:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3b3a:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3b3e:	48 8b 05 a3 51 00 00 	mov    0x51a3(%rip),%rax        # 8ce8 <_IO_stdin_used+0xce8>
    thread_data[x].thread_index = x;
    3b45:	44 89 b5 24 ff ff ff 	mov    %r14d,-0xdc(%rbp)
    thread_data[x].thread_count = thread_count;
    3b4c:	48 89 85 48 ff ff ff 	mov    %rax,-0xb8(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b53:	e8 78 e9 ff ff       	call   24d0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b58:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3b5e:	48 83 84 24 c0 00 00 00 10 	addq   $0x10,0xc0(%rsp)
    3b67:	41 83 fe 08          	cmp    $0x8,%r14d
    3b6b:	75 47                	jne    3bb4 <main+0x1544>
    3b6d:	41 be 09 00 00 00    	mov    $0x9,%r14d
    3b73:	e9 3a ff ff ff       	jmp    3ab2 <main+0x1442>
        other = (x + 1) % total_threads;
    3b78:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
        my_thread_data[1] = &thread_data[other]; 
    3b7d:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3b82:	48 89 5c 24 48       	mov    %rbx,0x48(%rsp)
    3b87:	45 31 c0             	xor    %r8d,%r8d
    3b8a:	4a 8d 14 ed 00 00 00 00 	lea    0x0(,%r13,8),%rdx
        other = (x + 1) % total_threads;
    3b92:	45 89 ee             	mov    %r13d,%r14d
        my_thread_data[1] = &thread_data[other]; 
    3b95:	4c 29 ea             	sub    %r13,%rdx
    3b98:	48 c1 e2 05          	shl    $0x5,%rdx
    3b9c:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    3b9f:	4c 89 c8             	mov    %r9,%rax
    3ba2:	e9 eb ee ff ff       	jmp    2a92 <main+0x422>
            CPU_SET(j, sendercpu);
    3ba7:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
    3baf:	e9 70 ef ff ff       	jmp    2b24 <main+0x4b4>
    3bb4:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3bb9:	48 8d 2d 1e 49 00 00 	lea    0x491e(%rip),%rbp        # 84de <_IO_stdin_used+0x4de>
    3bc0:	4c 8d 68 04          	lea    0x4(%rax),%r13
    3bc4:	4c 8d a0 c4 08 00 00 	lea    0x8c4(%rax),%r12
    3bcb:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    3bcf:	41 8b 55 00          	mov    0x0(%r13),%edx
    3bd3:	48 89 ee             	mov    %rbp,%rsi
    3bd6:	bf 01 00 00 00       	mov    $0x1,%edi
    3bdb:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3bdd:	49 81 c5 e0 00 00 00 	add    $0xe0,%r13
    3be4:	e8 c7 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3be9:	4d 39 ec             	cmp    %r13,%r12
    3bec:	75 dd                	jne    3bcb <main+0x155b>
    3bee:	48 8d 3d fc 48 00 00 	lea    0x48fc(%rip),%rdi        # 84f1 <_IO_stdin_used+0x4f1>
    3bf5:	45 31 ed             	xor    %r13d,%r13d
    3bf8:	4c 8d a4 24 f0 00 00 00 	lea    0xf0(%rsp),%r12
    3c00:	e8 2b e7 ff ff       	call   2330 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3c05:	48 8d 2d 03 49 00 00 	lea    0x4903(%rip),%rbp        # 850f <_IO_stdin_used+0x50f>
    void * result; 
    pthread_join(thread[x], &result);
    3c0c:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    3c10:	4c 89 e6             	mov    %r12,%rsi
    3c13:	e8 48 e9 ff ff       	call   2560 <pthread_join@plt>
    3c18:	44 89 ea             	mov    %r13d,%edx
    3c1b:	48 89 ee             	mov    %rbp,%rsi
    3c1e:	bf 01 00 00 00       	mov    $0x1,%edi
    3c23:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3c25:	49 83 c5 01          	add    $0x1,%r13
    3c29:	e8 82 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c2e:	49 83 fd 0a          	cmp    $0xa,%r13
    3c32:	75 d8                	jne    3c0c <main+0x159c>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c34:	be 08 00 00 00       	mov    $0x8,%esi
    3c39:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3c3e:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c40:	e8 bb e7 ff ff       	call   2400 <calloc@plt>
    3c45:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3c4a:	48 89 c5             	mov    %rax,%rbp
    3c4d:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c4f:	49 89 d1             	mov    %rdx,%r9
    3c52:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c55:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3c59:	45 85 d2             	test   %r10d,%r10d
    3c5c:	0f 8e a1 00 00 00    	jle    3d03 <main+0x1693>
    3c62:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3c66:	4d 63 c2             	movslq %r10d,%r8
    3c69:	48 63 cb             	movslq %ebx,%rcx
    3c6c:	49 c1 e0 09          	shl    $0x9,%r8
    3c70:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    3c75:	49 01 f8             	add    %rdi,%r8
    3c78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c80:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c87:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3c8e:	48 83 c6 60          	add    $0x60,%rsi
    3c92:	f3 0f 7e 61 48       	movq   0x48(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c97:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3c9b:	f3 0f 7e 99 90 00 00 00 	movq   0x90(%rcx),%xmm3
    3ca3:	f3 0f 7e 91 d8 00 00 00 	movq   0xd8(%rcx),%xmm2
    3cab:	f3 0f 7e 89 20 01 00 00 	movq   0x120(%rcx),%xmm1
    3cb3:	0f 16 61 50          	movhps 0x50(%rcx),%xmm4
    3cb7:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    3cbb:	f3 0f 7e 81 68 01 00 00 	movq   0x168(%rcx),%xmm0
    3cc3:	0f 16 99 98 00 00 00 	movhps 0x98(%rcx),%xmm3
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3cca:	0f 16 91 e0 00 00 00 	movhps 0xe0(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3cd1:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3cd5:	0f 16 89 28 01 00 00 	movhps 0x128(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3cdc:	0f 16 81 70 01 00 00 	movhps 0x170(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3ce3:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3ce7:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3ceb:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3cef:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3cf3:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3cf7:	4c 39 c7             	cmp    %r8,%rdi
    3cfa:	75 84                	jne    3c80 <main+0x1610>
    3cfc:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3d00:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3d03:	49 81 c1 e0 00 00 00 	add    $0xe0,%r9
    3d0a:	45 85 db             	test   %r11d,%r11d
    3d0d:	75 08                	jne    3d17 <main+0x16a7>
    3d0f:	45 89 fb             	mov    %r15d,%r11d
    3d12:	e9 3e ff ff ff       	jmp    3c55 <main+0x15e5>
  for (int k = 0 ; k < group_count ; k++) {
    3d17:	83 c0 02             	add    $0x2,%eax
    3d1a:	48 81 c2 c0 01 00 00 	add    $0x1c0,%rdx
    3d21:	83 f8 06             	cmp    $0x6,%eax
    3d24:	0f 85 25 ff ff ff    	jne    3c4f <main+0x15df>
    3d2a:	48 8d 3d f2 47 00 00 	lea    0x47f2(%rip),%rdi        # 8523 <_IO_stdin_used+0x523>
    3d31:	e8 fa e5 ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3d36:	48 8d 35 c2 46 00 00 	lea    0x46c2(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3d3d:	48 8d 3d f7 47 00 00 	lea    0x47f7(%rip),%rdi        # 853b <_IO_stdin_used+0x53b>
    3d44:	e8 a7 e7 ff ff       	call   24f0 <fopen@plt>
    3d49:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas2_size; x++) {
    3d4c:	85 db                	test   %ebx,%ebx
    3d4e:	7e 73                	jle    3dc3 <main+0x1753>
    3d50:	48 63 db             	movslq %ebx,%rbx
    3d53:	49 89 ef             	mov    %rbp,%r15
    3d56:	4c 8d 35 81 46 00 00 	lea    0x4681(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    3d5d:	48 8d 6c dd 00       	lea    0x0(%rbp,%rbx,8),%rbp
    3d62:	4c 8d 2d b9 46 00 00 	lea    0x46b9(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    char * c = calloc(250, sizeof(char));
    3d69:	be 01 00 00 00       	mov    $0x1,%esi
    3d6e:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3d73:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    3d77:	e8 84 e6 ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3d7c:	4c 89 f1             	mov    %r14,%rcx
    3d7f:	ba fa 00 00 00       	mov    $0xfa,%edx
    3d84:	be 01 00 00 00       	mov    $0x1,%esi
    3d89:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3d8c:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3d90:	48 89 df             	mov    %rbx,%rdi
    3d93:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3d9a:	31 c0                	xor    %eax,%eax
    3d9c:	e8 ff e7 ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3da1:	48 89 da             	mov    %rbx,%rdx
    3da4:	4c 89 ee             	mov    %r13,%rsi
    3da7:	bf 01 00 00 00       	mov    $0x1,%edi
    3dac:	31 c0                	xor    %eax,%eax
    3dae:	e8 fd e6 ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3db3:	4c 89 e6             	mov    %r12,%rsi
    3db6:	48 89 df             	mov    %rbx,%rdi
    3db9:	e8 02 e6 ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3dbe:	49 39 ef             	cmp    %rbp,%r15
    3dc1:	75 a6                	jne    3d69 <main+0x16f9>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3dc3:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    3dcd:	4c 89 e7             	mov    %r12,%rdi
  long received = 0;
    3dd0:	31 db                	xor    %ebx,%ebx
  fclose(m2);
    3dd2:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
    3dd8:	e8 83 e5 ff ff       	call   2360 <fclose@plt>
  long sents = 0;
    3ddd:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long sends = 0;
    3de6:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long ingests = 0;
    3def:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long total = 0;
    3df8:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  int datas2_size = 0; 
    3e01:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
    3e09:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    3e0e:	4c 8b b4 24 a8 00 00 00 	mov    0xa8(%rsp),%r14
    3e16:	45 89 e5             	mov    %r12d,%r13d
    3e19:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    3e1e:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
      int x = (k * threads_per_group) + d;
    3e23:	44 89 e8             	mov    %r13d,%eax
    3e26:	41 83 c5 01          	add    $0x1,%r13d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3e2a:	bf 0a 00 00 00       	mov    $0xa,%edi
        other = abs(x - 1) % total_threads;
    3e2f:	41 f6 c5 01          	test   $0x1,%r13b
    3e33:	8d 50 02             	lea    0x2(%rax),%edx
    3e36:	0f 44 c2             	cmove  %edx,%eax
    3e39:	4c 63 e0             	movslq %eax,%r12
    3e3c:	e8 cf e4 ff ff       	call   2310 <putchar@plt>
    3e41:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3e46:	bf 01 00 00 00       	mov    $0x1,%edi
    3e4b:	48 8d 35 f2 46 00 00 	lea    0x46f2(%rip),%rsi        # 8544 <_IO_stdin_used+0x544>
    3e52:	48 8b 10             	mov    (%rax),%rdx
    3e55:	31 c0                	xor    %eax,%eax
    3e57:	e8 54 e6 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e5c:	41 8b 56 40          	mov    0x40(%r14),%edx
    3e60:	85 d2                	test   %edx,%edx
    3e62:	0f 8e 3d 05 00 00    	jle    43a5 <main+0x1d35>
    3e68:	48 63 ca             	movslq %edx,%rcx
    3e6b:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    3e6f:	31 d2                	xor    %edx,%edx
    3e71:	48 c1 e1 09          	shl    $0x9,%rcx
    3e75:	48 01 c1             	add    %rax,%rcx
    3e78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
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
    3eef:	48 8d 35 32 49 00 00 	lea    0x4932(%rip),%rsi        # 8828 <_IO_stdin_used+0x828>
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
    3f28:	0f 8e 45 01 00 00    	jle    4073 <main+0x1a03>
    3f2e:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    3f33:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    3f38:	31 d2                	xor    %edx,%edx
    3f3a:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3f3f:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3f44:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    3f49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        total += thread_data[x].tasks[n].n;
    3f50:	49 8b 46 38          	mov    0x38(%r14),%rax
    3f54:	49 89 d1             	mov    %rdx,%r9
        sends += thread_data[x].tasks[n].sends;
    3f57:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    3f5c:	41 89 d5             	mov    %edx,%r13d
        total += thread_data[x].tasks[n].n;
    3f5f:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    3f63:	45 31 e4             	xor    %r12d,%r12d
        total += thread_data[x].tasks[n].n;
    3f66:	4c 01 c8             	add    %r9,%rax
        sends += thread_data[x].tasks[n].sends;
    3f69:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
        total += thread_data[x].tasks[n].n;
    3f6e:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
        ingests += thread_data[x].tasks[n].ingest_count;
    3f75:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
        sends += thread_data[x].tasks[n].sends;
    3f7c:	48 03 b8 78 01 00 00 	add    0x178(%rax),%rdi
    3f83:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    3f88:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3f8d:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3f92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3f98:	8b 54 24 08          	mov    0x8(%rsp),%edx
    3f9c:	45 89 e0             	mov    %r12d,%r8d
    3f9f:	44 89 e9             	mov    %r13d,%ecx
    3fa2:	bf 01 00 00 00       	mov    $0x1,%edi
    3fa7:	48 8d 35 b8 45 00 00 	lea    0x45b8(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    3fae:	31 c0                	xor    %eax,%eax
    3fb0:	e8 fb e4 ff ff       	call   24b0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fb5:	49 8b 46 38          	mov    0x38(%r14),%rax
    3fb9:	4b 8d 14 e4          	lea    (%r12,%r12,8),%rdx
    3fbd:	45 89 e0             	mov    %r12d,%r8d
    3fc0:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    3fc5:	48 83 ec 08          	sub    $0x8,%rsp
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3fc9:	49 83 c4 01          	add    $0x1,%r12
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fcd:	48 8b 84 38 70 01 00 00 	mov    0x170(%rax,%rdi,1),%rax
    3fd5:	bf 01 00 00 00       	mov    $0x1,%edi
    3fda:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    3fde:	48 8b 02             	mov    (%rdx),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3fe1:	48 8b 72 08          	mov    0x8(%rdx),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fe5:	48 8b 88 08 03 00 00 	mov    0x308(%rax),%rcx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3fec:	48 8b 96 08 03 00 00 	mov    0x308(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3ff3:	48 8b 80 10 03 00 00 	mov    0x310(%rax),%rax
    3ffa:	48 8b b6 10 03 00 00 	mov    0x310(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4001:	49 01 cf             	add    %rcx,%r15
    4004:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
    4008:	44 89 e9             	mov    %r13d,%ecx
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    400b:	48 01 c3             	add    %rax,%rbx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    400e:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4011:	49 01 d7             	add    %rdx,%r15
    4014:	50                   	push   %rax
    4015:	8b 54 24 18          	mov    0x18(%rsp),%edx
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4019:	48 01 f3             	add    %rsi,%rbx
    401c:	31 c0                	xor    %eax,%eax
    401e:	48 8d 35 23 48 00 00 	lea    0x4823(%rip),%rsi        # 8848 <_IO_stdin_used+0x848>
    4025:	e8 86 e4 ff ff       	call   24b0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    402a:	41 5a                	pop    %r10
    402c:	41 5b                	pop    %r11
    402e:	49 83 fc 06          	cmp    $0x6,%r12
    4032:	0f 85 60 ff ff ff    	jne    3f98 <main+0x1928>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    4038:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    403d:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    4042:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    4047:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    404c:	48 83 c2 01          	add    $0x1,%rdx
    4050:	41 39 56 40          	cmp    %edx,0x40(%r14)
    4054:	0f 8f f6 fe ff ff    	jg     3f50 <main+0x18e0>
    405a:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    405f:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    4064:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    4069:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    406e:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    4073:	45 31 ff             	xor    %r15d,%r15d
    4076:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    407e:	4c 8d 25 e3 47 00 00 	lea    0x47e3(%rip),%r12        # 8868 <_IO_stdin_used+0x868>
    4085:	7e 61                	jle    40e8 <main+0x1a78>
    4087:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4090:	49 8b 86 90 00 00 00 	mov    0x90(%r14),%rax
    4097:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    409b:	48 83 ec 08          	sub    $0x8,%rsp
    409f:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    40a4:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    40a8:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    40ac:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    40b0:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    40b4:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    40b7:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    40bb:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    40be:	48 f7 e5             	mul    %rbp
    40c1:	8b 49 20             	mov    0x20(%rcx),%ecx
    40c4:	56                   	push   %rsi
    40c5:	31 c0                	xor    %eax,%eax
    40c7:	4c 89 e6             	mov    %r12,%rsi
    40ca:	48 c1 ea 12          	shr    $0x12,%rdx
    40ce:	49 89 d1             	mov    %rdx,%r9
    40d1:	ba 02 00 00 00       	mov    $0x2,%edx
    40d6:	e8 d5 e3 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    40db:	41 58                	pop    %r8
    40dd:	41 59                	pop    %r9
    40df:	4d 39 be a0 00 00 00 	cmp    %r15,0xa0(%r14)
    40e6:	7f a8                	jg     4090 <main+0x1a20>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    40e8:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    40ef:	85 d2                	test   %edx,%edx
    40f1:	0f 8e 0a 01 00 00    	jle    4201 <main+0x1b91>
    40f7:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    40fc:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4100:	45 31 ff             	xor    %r15d,%r15d
    4103:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    4108:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4110:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    4114:	44 89 fb             	mov    %r15d,%ebx
    4117:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    411f:	8b 30                	mov    (%rax),%esi
    4121:	85 f6                	test   %esi,%esi
    4123:	0f 8e c1 00 00 00    	jle    41ea <main+0x1b7a>
    4129:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    412e:	31 d2                	xor    %edx,%edx
    4130:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4134:	49 89 f8             	mov    %rdi,%r8
    4137:	48 89 d7             	mov    %rdx,%rdi
    413a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4140:	49 89 fc             	mov    %rdi,%r12
    4143:	45 31 ff             	xor    %r15d,%r15d
    4146:	49 c1 e4 08          	shl    $0x8,%r12
    414a:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    414e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4154:	85 d2                	test   %edx,%edx
    4156:	7e 77                	jle    41cf <main+0x1b5f>
    4158:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    415d:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4160:	4c 89 f9             	mov    %r15,%rcx
    4163:	48 83 ec 08          	sub    $0x8,%rsp
    4167:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    416c:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4170:	48 c1 e1 05          	shl    $0x5,%rcx
    4174:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    417b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    417f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    4183:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4186:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    418a:	4c 2b 01             	sub    (%rcx),%r8
    418d:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    418e:	48 f7 e5             	mul    %rbp
    4191:	89 d9                	mov    %ebx,%ecx
    4193:	48 8d 35 1e 47 00 00 	lea    0x471e(%rip),%rsi        # 88b8 <_IO_stdin_used+0x8b8>
    419a:	31 c0                	xor    %eax,%eax
    419c:	48 c1 ea 12          	shr    $0x12,%rdx
    41a0:	49 89 d1             	mov    %rdx,%r9
    41a3:	ba 02 00 00 00       	mov    $0x2,%edx
    41a8:	e8 03 e3 ff ff       	call   24b0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    41ad:	4d 8b 46 50          	mov    0x50(%r14),%r8
    41b1:	5e                   	pop    %rsi
    41b2:	5f                   	pop    %rdi
    41b3:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    41b7:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    41bb:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    41bf:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    41c6:	7f 98                	jg     4160 <main+0x1af0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    41c8:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    41cd:	8b 32                	mov    (%rdx),%esi
    41cf:	48 83 c7 01          	add    $0x1,%rdi
    41d3:	39 fe                	cmp    %edi,%esi
    41d5:	0f 8f 65 ff ff ff    	jg     4140 <main+0x1ad0>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    41db:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    41e0:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    41e7:	4c 89 c7             	mov    %r8,%rdi
    41ea:	49 83 c7 01          	add    $0x1,%r15
    41ee:	44 39 fa             	cmp    %r15d,%edx
    41f1:	0f 8f 19 ff ff ff    	jg     4110 <main+0x1aa0>
    41f7:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    41fc:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    4201:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    4207:	49 81 c6 e0 00 00 00 	add    $0xe0,%r14
    420e:	44 39 6c 24 48       	cmp    %r13d,0x48(%rsp)
    4213:	0f 85 0a fc ff ff    	jne    3e23 <main+0x17b3>
  for (int k = 0 ; k < group_count ; k++) {
    4219:	48 83 84 24 90 00 00 00 30 	addq   $0x30,0x90(%rsp)
    4222:	44 8b 44 24 48       	mov    0x48(%rsp),%r8d
    4227:	48 81 84 24 a8 00 00 00 c0 01 00 00 	addq   $0x1c0,0xa8(%rsp)
    4233:	41 83 f8 05          	cmp    $0x5,%r8d
    4237:	74 08                	je     4241 <main+0x1bd1>
    4239:	45 89 c4             	mov    %r8d,%r12d
    423c:	e9 c0 fb ff ff       	jmp    3e01 <main+0x1791>
    4241:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    4246:	bf 01 00 00 00       	mov    $0x1,%edi
    424b:	31 c0                	xor    %eax,%eax
    424d:	49 89 df             	mov    %rbx,%r15
    4250:	48 8d 35 1f 43 00 00 	lea    0x431f(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    4257:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4261:	4c 89 f2             	mov    %r14,%rdx
    4264:	e8 47 e2 ff ff       	call   24b0 <__printf_chk@plt>
    4269:	bf 0a 00 00 00       	mov    $0xa,%edi
    426e:	e8 9d e0 ff ff       	call   2310 <putchar@plt>
    4273:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
    427b:	48 8d 35 8e 46 00 00 	lea    0x468e(%rip),%rsi        # 8910 <_IO_stdin_used+0x910>
    4282:	31 c0                	xor    %eax,%eax
    4284:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    4288:	bf 01 00 00 00       	mov    $0x1,%edi
    428d:	e8 1e e2 ff ff       	call   24b0 <__printf_chk@plt>
    4292:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    4297:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    429c:	48 8d 35 95 46 00 00 	lea    0x4695(%rip),%rsi        # 8938 <_IO_stdin_used+0x938>
    42a3:	48 f7 eb             	imul   %rbx
    42a6:	48 c1 ff 3f          	sar    $0x3f,%rdi
    42aa:	31 c0                	xor    %eax,%eax
    42ac:	48 d1 fa             	sar    %rdx
    42af:	48 29 fa             	sub    %rdi,%rdx
    42b2:	bf 01 00 00 00       	mov    $0x1,%edi
    42b7:	e8 f4 e1 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    42bc:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    42c1:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    42c6:	48 8d 35 9b 46 00 00 	lea    0x469b(%rip),%rsi        # 8968 <_IO_stdin_used+0x968>
    42cd:	48 f7 eb             	imul   %rbx
    42d0:	48 c1 ff 3f          	sar    $0x3f,%rdi
    42d4:	31 c0                	xor    %eax,%eax
    42d6:	48 d1 fa             	sar    %rdx
    42d9:	48 29 fa             	sub    %rdi,%rdx
    42dc:	bf 01 00 00 00       	mov    $0x1,%edi
    42e1:	e8 ca e1 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    42e6:	4c 89 f0             	mov    %r14,%rax
    42e9:	bf 01 00 00 00       	mov    $0x1,%edi
    42ee:	48 8d 35 a3 46 00 00 	lea    0x46a3(%rip),%rsi        # 8998 <_IO_stdin_used+0x998>
    42f5:	48 f7 eb             	imul   %rbx
    42f8:	4c 89 f0             	mov    %r14,%rax
    42fb:	48 c1 f8 3f          	sar    $0x3f,%rax
    42ff:	48 d1 fa             	sar    %rdx
    4302:	48 29 c2             	sub    %rax,%rdx
    4305:	31 c0                	xor    %eax,%eax
    4307:	e8 a4 e1 ff ff       	call   24b0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    430c:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4311:	bf 01 00 00 00       	mov    $0x1,%edi
    4316:	48 8d 35 6d 42 00 00 	lea    0x426d(%rip),%rsi        # 858a <_IO_stdin_used+0x58a>
    431d:	48 f7 eb             	imul   %rbx
    4320:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4325:	48 c1 f8 3f          	sar    $0x3f,%rax
    4329:	48 d1 fa             	sar    %rdx
    432c:	48 29 c2             	sub    %rax,%rdx
    432f:	31 c0                	xor    %eax,%eax
    4331:	48 89 d5             	mov    %rdx,%rbp
    4334:	e8 77 e1 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
    4339:	4c 89 f8             	mov    %r15,%rax
    433c:	bf 01 00 00 00       	mov    $0x1,%edi
    4341:	48 8d 35 70 46 00 00 	lea    0x4670(%rip),%rsi        # 89b8 <_IO_stdin_used+0x9b8>
    4348:	48 f7 eb             	imul   %rbx
    434b:	4c 89 f8             	mov    %r15,%rax
    434e:	48 c1 f8 3f          	sar    $0x3f,%rax
    4352:	48 89 d3             	mov    %rdx,%rbx
    4355:	48 d1 fb             	sar    %rbx
    4358:	48 29 c3             	sub    %rax,%rbx
    435b:	31 c0                	xor    %eax,%eax
    435d:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    4360:	48 29 eb             	sub    %rbp,%rbx
    4363:	e8 48 e1 ff ff       	call   24b0 <__printf_chk@plt>
    4368:	31 c0                	xor    %eax,%eax
    436a:	48 89 da             	mov    %rbx,%rdx
    436d:	bf 01 00 00 00       	mov    $0x1,%edi
    4372:	48 8d 35 2d 42 00 00 	lea    0x422d(%rip),%rsi        # 85a6 <_IO_stdin_used+0x5a6>
    4379:	e8 32 e1 ff ff       	call   24b0 <__printf_chk@plt>
  return 0;

}
    437e:	48 8b 84 24 f8 00 00 00 	mov    0xf8(%rsp),%rax
    4386:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    438f:	75 25                	jne    43b6 <main+0x1d46>
    4391:	48 81 c4 08 01 00 00 	add    $0x108,%rsp
    4398:	31 c0                	xor    %eax,%eax
    439a:	5b                   	pop    %rbx
    439b:	5d                   	pop    %rbp
    439c:	41 5c                	pop    %r12
    439e:	41 5d                	pop    %r13
    43a0:	41 5e                	pop    %r14
    43a2:	41 5f                	pop    %r15
    43a4:	c3                   	ret
      long v = 0;
    43a5:	31 d2                	xor    %edx,%edx
    43a7:	e9 e6 fa ff ff       	jmp    3e92 <main+0x1822>
            exit(1);
    43ac:	bf 01 00 00 00       	mov    $0x1,%edi
    43b1:	e8 5a e1 ff ff       	call   2510 <exit@plt>
}
    43b6:	e8 c5 df ff ff       	call   2380 <__stack_chk_fail@plt>
    43bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

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
int do_protected_write(struct BarrierTask *data) {
    44b0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    44b4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    44bb:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    44bf:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    44c7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    44cb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    44cf:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    44d6:	48 85 c9             	test   %rcx,%rcx
    44d9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    44e0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    44e4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    44e8:	31 c0                	xor    %eax,%eax
    44ea:	c3                   	ret
    44eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000044f0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    44f0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    44f4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    44fb:	85 c9                	test   %ecx,%ecx
    44fd:	7e 4f                	jle    454e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    44ff:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4506:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    450d:	48 c1 e1 09          	shl    $0x9,%rcx
    4511:	48 8b 50 18          	mov    0x18(%rax),%rdx
    4515:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    4519:	48 8b 70 38          	mov    0x38(%rax),%rsi
    451d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    451f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4523:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4528:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4530:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4538:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    4543:	48 05 00 02 00 00    	add    $0x200,%rax
    4549:	48 39 c1             	cmp    %rax,%rcx
    454c:	75 da                	jne    4528 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    454e:	0f ae f8             	sfence
}
    4551:	31 c0                	xor    %eax,%eax
    4553:	c3                   	ret
    4554:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    455f:	90                   	nop

0000000000004560 <external_thread>:
void * external_thread(void *arg) {
    4560:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    4564:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4568:	0f 85 fb 00 00 00    	jne    4669 <external_thread+0x109>
void * external_thread(void *arg) {
    456e:	41 57                	push   %r15
    4570:	49 89 ff             	mov    %rdi,%r15
    4573:	41 56                	push   %r14
    4575:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    4577:	4c 8d 2d 86 3a 00 00 	lea    0x3a86(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    457e:	41 54                	push   %r12
    4580:	55                   	push   %rbp
    4581:	53                   	push   %rbx
    4582:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    4586:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    458c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    4590:	85 c9                	test   %ecx,%ecx
    4592:	7e 6e                	jle    4602 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
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
				if (data->buffers[b]->buffer[x].available == 0) {
    45bb:	48 89 dd             	mov    %rbx,%rbp
    45be:	48 c1 e5 08          	shl    $0x8,%rbp
    45c2:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    45c6:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    45cd:	45 85 c0             	test   %r8d,%r8d
    45d0:	74 36                	je     4608 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    45d2:	48 83 c3 01          	add    $0x1,%rbx
    45d6:	39 da                	cmp    %ebx,%edx
    45d8:	7f e1                	jg     45bb <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    45da:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    45e1:	49 83 c4 01          	add    $0x1,%r12
    45e5:	44 39 e1             	cmp    %r12d,%ecx
    45e8:	7f b6                	jg     45a0 <external_thread+0x40>
  while (data->running == 1) {
    45ea:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    45ef:	74 9f                	je     4590 <external_thread+0x30>
}
    45f1:	48 83 c4 08          	add    $0x8,%rsp
    45f5:	31 c0                	xor    %eax,%eax
    45f7:	5b                   	pop    %rbx
    45f8:	5d                   	pop    %rbp
    45f9:	41 5c                	pop    %r12
    45fb:	41 5d                	pop    %r13
    45fd:	41 5e                	pop    %r14
    45ff:	41 5f                	pop    %r15
    4601:	c3                   	ret
  while (data->running == 1) {
    4602:	eb fe                	jmp    4602 <external_thread+0xa2>
    4604:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    4608:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    460b:	48 8b 06             	mov    (%rsi),%rax
    460e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4612:	48 01 ef             	add    %rbp,%rdi
    4615:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    461c:	48 c1 e6 05          	shl    $0x5,%rsi
    4620:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4627:	bf 04 00 00 00       	mov    $0x4,%edi
    462c:	e8 1f dd ff ff       	call   2350 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4631:	49 8b 47 50          	mov    0x50(%r15),%rax
    4635:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    4639:	48 8b 40 08          	mov    0x8(%rax),%rax
    463d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    4648:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    464b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    464f:	48 83 c3 01          	add    $0x1,%rbx
    4653:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4657:	48 8b 06             	mov    (%rsi),%rax
    465a:	8b 10                	mov    (%rax),%edx
    465c:	39 da                	cmp    %ebx,%edx
    465e:	0f 8f 53 ff ff ff    	jg     45b7 <external_thread+0x57>
    4664:	e9 71 ff ff ff       	jmp    45da <external_thread+0x7a>
}
    4669:	31 c0                	xor    %eax,%eax
    466b:	c3                   	ret
    466c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004670 <timer_thread>:
void* timer_thread(void *arg) {
    4670:	f3 0f 1e fa          	endbr64
    4674:	41 57                	push   %r15
    4676:	48 8d 35 93 39 00 00 	lea    0x3993(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    467d:	41 56                	push   %r14
    467f:	49 89 fe             	mov    %rdi,%r14
    4682:	41 55                	push   %r13
    4684:	41 54                	push   %r12
    4686:	55                   	push   %rbp
    4687:	53                   	push   %rbx
    4688:	48 83 ec 68          	sub    $0x68,%rsp
    468c:	8b 57 04             	mov    0x4(%rdi),%edx
    468f:	bf 01 00 00 00       	mov    $0x1,%edi
    4694:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    469d:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    46a2:	31 c0                	xor    %eax,%eax
    46a4:	e8 07 de ff ff       	call   24b0 <__printf_chk@plt>
  struct timespec preempt = {
    46a9:	66 0f 6f 05 1f 45 00 00 	movdqa 0x451f(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    46b1:	ba 88 13 00 00       	mov    $0x1388,%edx
    46b6:	31 c0                	xor    %eax,%eax
    46b8:	48 8d 35 63 39 00 00 	lea    0x3963(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    46bf:	bf 01 00 00 00       	mov    $0x1,%edi
    46c4:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    46c9:	e8 e2 dd ff ff       	call   24b0 <__printf_chk@plt>
  while (data->running && n < times) {
    46ce:	41 8b 5e 44          	mov    0x44(%r14),%ebx
    46d2:	85 db                	test   %ebx,%ebx
    46d4:	0f 84 99 00 00 00    	je     4773 <timer_thread+0x103>
  int n = 0;
    46da:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    46dd:	31 db                	xor    %ebx,%ebx
    46df:	4c 8d 6c 24 10       	lea    0x10(%rsp),%r13
    y++;
    46e4:	31 ed                	xor    %ebp,%ebp
    46e6:	4c 8d 64 24 20       	lea    0x20(%rsp),%r12
    nanosleep(&preempt , &rem2);
    46eb:	4c 89 e7             	mov    %r12,%rdi
    46ee:	4c 89 ee             	mov    %r13,%rsi
    n++;
    46f1:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    46f5:	e8 a6 dc ff ff       	call   23a0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46fa:	49 63 46 30          	movslq 0x30(%r14),%rax
    y++;
    46fe:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4701:	85 c0                	test   %eax,%eax
    4703:	7e 47                	jle    474c <timer_thread+0xdc>
    4705:	49 8b 4e 18          	mov    0x18(%r14),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4709:	4c 63 c3             	movslq %ebx,%r8
    470c:	49 c1 e0 09          	shl    $0x9,%r8
    4710:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4714:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4718:	48 8b 19             	mov    (%rcx),%rbx
    471b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    471d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4721:	99                   	cltd
    4722:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4725:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4729:	48 63 d2             	movslq %edx,%rdx
    472c:	48 c1 e2 09          	shl    $0x9,%rdx
    4730:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    473b:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4747:	49 39 c9             	cmp    %rcx,%r9
    474a:	75 cc                	jne    4718 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    474c:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    474f:	49 8b 46 18          	mov    0x18(%r14),%rax
  while (data->running && n < times) {
    4753:	41 8b 4e 44          	mov    0x44(%r14),%ecx
    y++;
    4757:	89 fb                	mov    %edi,%ebx
    if (y >= data->threads[0]->task_count) {
    4759:	48 8b 00             	mov    (%rax),%rax
    y++;
    475c:	39 78 40             	cmp    %edi,0x40(%rax)
    475f:	0f 4e dd             	cmovle %ebp,%ebx
  while (data->running && n < times) {
    4762:	85 c9                	test   %ecx,%ecx
    4764:	74 0d                	je     4773 <timer_thread+0x103>
    4766:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    476d:	0f 85 78 ff ff ff    	jne    46eb <timer_thread+0x7b>
    4773:	48 8d 3d be 38 00 00 	lea    0x38be(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    477a:	e8 b1 db ff ff       	call   2330 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    477f:	49 63 56 30          	movslq 0x30(%r14),%rdx
    4783:	85 d2                	test   %edx,%edx
    4785:	7e 6e                	jle    47f5 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    4787:	49 63 46 40          	movslq 0x40(%r14),%rax
    478b:	85 c0                	test   %eax,%eax
    478d:	7e 66                	jle    47f5 <timer_thread+0x185>
    478f:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4793:	4d 8b 46 18          	mov    0x18(%r14),%r8
    4797:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    479f:	31 c9                	xor    %ecx,%ecx
    47a1:	48 89 c6             	mov    %rax,%rsi
    47a4:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    47a8:	48 8b 40 38          	mov    0x38(%rax),%rax
    47ac:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    47b0:	f7 c6 00 02 00 00    	test   $0x200,%esi
    47b6:	74 18                	je     47d0 <timer_thread+0x160>
    47b8:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    47c2:	48 05 00 02 00 00    	add    $0x200,%rax
    47c8:	48 39 c2             	cmp    %rax,%rdx
    47cb:	74 1f                	je     47ec <timer_thread+0x17c>
    47cd:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->tasks[y].sending = 0;
    47d0:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    47da:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    47e0:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    47e7:	48 39 c2             	cmp    %rax,%rdx
    47ea:	75 e4                	jne    47d0 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    47ec:	48 83 c1 08          	add    $0x8,%rcx
    47f0:	48 39 cf             	cmp    %rcx,%rdi
    47f3:	75 af                	jne    47a4 <timer_thread+0x134>
  asm volatile ("mfence" ::: "memory");
    47f5:	0f ae f0             	mfence
  struct timespec drain = {
    47f8:	66 0f 6f 05 e0 43 00 00 	movdqa 0x43e0(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4800:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4805:	49 63 46 28          	movslq 0x28(%r14),%rax
    y++;
    4809:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    480c:	85 c0                	test   %eax,%eax
    480e:	7e 44                	jle    4854 <timer_thread+0x1e4>
    4810:	49 8b 4e 18          	mov    0x18(%r14),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4814:	4c 63 c3             	movslq %ebx,%r8
    4817:	49 c1 e0 09          	shl    $0x9,%r8
    481b:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    481f:	90                   	nop
        int next = (y + 1) % data->threads[x]->task_count;
    4820:	48 8b 19             	mov    (%rcx),%rbx
    4823:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    4825:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4829:	99                   	cltd
    482a:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    482d:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4831:	48 63 d2             	movslq %edx,%rdx
    4834:	48 c1 e2 09          	shl    $0x9,%rdx
    4838:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4843:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    484f:	49 39 c9             	cmp    %rcx,%r9
    4852:	75 cc                	jne    4820 <timer_thread+0x1b0>
    asm volatile ("mfence" ::: "memory");
    4854:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4857:	49 8b 76 18          	mov    0x18(%r14),%rsi
    y++;
    485b:	31 db                	xor    %ebx,%ebx
    if (y >= data->threads[0]->task_count) {
    485d:	48 8b 06             	mov    (%rsi),%rax
    y++;
    4860:	39 78 40             	cmp    %edi,0x40(%rax)
    4863:	0f 4f df             	cmovg  %edi,%ebx
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4866:	41 8b 7e 30          	mov    0x30(%r14),%edi
    486a:	85 ff                	test   %edi,%edi
    486c:	0f 8e ca 01 00 00    	jle    4a3c <timer_thread+0x3cc>
    int all_empty = 1;
    4872:	89 5c 24 0c          	mov    %ebx,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4876:	45 31 ed             	xor    %r13d,%r13d
    int all_empty = 1;
    4879:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    487f:	90                   	nop
      for (int y = 0 ; y < 2 ; y++) {
    4880:	45 31 e4             	xor    %r12d,%r12d
    4883:	44 89 eb             	mov    %r13d,%ebx
    4886:	4a 8d 2c ed 00 00 00 00 	lea    0x0(,%r13,8),%rbp
    488e:	44 89 e6             	mov    %r12d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4891:	85 ff                	test   %edi,%edi
    4893:	0f 8e c7 00 00 00    	jle    4960 <timer_thread+0x2f0>
    4899:	4d 89 e2             	mov    %r12,%r10
      y = 0;
    489c:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    489e:	45 31 c0             	xor    %r8d,%r8d
    48a1:	49 c1 e2 09          	shl    $0x9,%r10
    48a5:	0f 1f 00             	nopl   (%rax)
          if (x == k) { continue; }
    48a8:	45 39 e8             	cmp    %r13d,%r8d
    48ab:	74 39                	je     48e6 <timer_thread+0x276>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    48ad:	49 8b 56 18          	mov    0x18(%r14),%rdx
    48b1:	48 8b 14 2a          	mov    (%rdx,%rbp,1),%rdx
    48b5:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    48b9:	4a 8b 8c 12 70 01 00 00 	mov    0x170(%rdx,%r10,1),%rcx
    48c1:	48 01 c1             	add    %rax,%rcx
    48c4:	48 89 ca             	mov    %rcx,%rdx
    48c7:	48 8b 09             	mov    (%rcx),%rcx
    48ca:	48 8b 52 08          	mov    0x8(%rdx),%rdx
    48ce:	4c 8b 89 80 00 00 00 	mov    0x80(%rcx),%r9
    48d5:	4c 8b 9a 80 00 00 00 	mov    0x80(%rdx),%r11
    48dc:	4d 85 c9             	test   %r9,%r9
    48df:	7f 27                	jg     4908 <timer_thread+0x298>
    48e1:	4d 85 db             	test   %r11,%r11
    48e4:	7f 22                	jg     4908 <timer_thread+0x298>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    48e6:	41 83 c0 01          	add    $0x1,%r8d
    48ea:	48 83 c0 48          	add    $0x48,%rax
    48ee:	44 39 c7             	cmp    %r8d,%edi
    48f1:	75 b5                	jne    48a8 <timer_thread+0x238>
      for (int y = 0 ; y < 2 ; y++) {
    48f3:	49 83 fc 01          	cmp    $0x1,%r12
    48f7:	74 67                	je     4960 <timer_thread+0x2f0>
    48f9:	49 83 c4 01          	add    $0x1,%r12
    48fd:	44 89 e6             	mov    %r12d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4900:	eb 97                	jmp    4899 <timer_thread+0x229>
    4902:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4908:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    490e:	48 83 ec 08          	sub    $0x8,%rsp
    4912:	bf 01 00 00 00       	mov    $0x1,%edi
    4917:	89 da                	mov    %ebx,%edx
    4919:	50                   	push   %rax
    491a:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    4920:	89 f1                	mov    %esi,%ecx
    4922:	48 8d 35 34 37 00 00 	lea    0x3734(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    4929:	50                   	push   %rax
    492a:	31 c0                	xor    %eax,%eax
    492c:	41 53                	push   %r11
    492e:	e8 7d db ff ff       	call   24b0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4933:	41 8b 7e 30          	mov    0x30(%r14),%edi
      for (int y = 0 ; y < 2 ; y++) {
    4937:	48 83 c4 20          	add    $0x20,%rsp
    493b:	49 83 fc 01          	cmp    $0x1,%r12
    493f:	0f 84 8b 00 00 00    	je     49d0 <timer_thread+0x360>
    4945:	49 83 c4 01          	add    $0x1,%r12
    4949:	45 31 ff             	xor    %r15d,%r15d
    494c:	44 89 e6             	mov    %r12d,%esi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    494f:	85 ff                	test   %edi,%edi
    4951:	0f 8f 42 ff ff ff    	jg     4899 <timer_thread+0x229>
    4957:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4960:	49 83 c5 01          	add    $0x1,%r13
    4964:	44 39 ef             	cmp    %r13d,%edi
    4967:	0f 8f 13 ff ff ff    	jg     4880 <timer_thread+0x210>
    496d:	8b 5c 24 0c          	mov    0xc(%rsp),%ebx
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4971:	85 ff                	test   %edi,%edi
    4973:	7e 38                	jle    49ad <timer_thread+0x33d>
    4975:	31 ed                	xor    %ebp,%ebp
    int all_waited = 1;
    4977:	bf 01 00 00 00       	mov    $0x1,%edi
    497c:	49 8b 76 18          	mov    0x18(%r14),%rsi
    4980:	41 8b 56 40          	mov    0x40(%r14),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4984:	48 8b 04 ee          	mov    (%rsi,%rbp,8),%rax
    4988:	48 8b 40 38          	mov    0x38(%rax),%rax
    498c:	8b 88 9c 01 00 00    	mov    0x19c(%rax),%ecx
    4992:	39 d1                	cmp    %edx,%ecx
    4994:	7c 7a                	jl     4a10 <timer_thread+0x3a0>
    4996:	8b 80 9c 03 00 00    	mov    0x39c(%rax),%eax
    499c:	39 d0                	cmp    %edx,%eax
    499e:	7c 48                	jl     49e8 <timer_thread+0x378>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    49a0:	48 83 c5 01          	add    $0x1,%rbp
    49a4:	41 39 6e 30          	cmp    %ebp,0x30(%r14)
    49a8:	7f da                	jg     4984 <timer_thread+0x314>
    49aa:	41 21 ff             	and    %edi,%r15d
    if (all_empty == 1 && all_waited == 1) {
    49ad:	45 85 ff             	test   %r15d,%r15d
    49b0:	0f 85 86 00 00 00    	jne    4a3c <timer_thread+0x3cc>
      nanosleep(&drain , &drainrem);
    49b6:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    49bb:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    49c0:	e8 db d9 ff ff       	call   23a0 <nanosleep@plt>
    49c5:	e9 3b fe ff ff       	jmp    4805 <timer_thread+0x195>
    49ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    49d0:	49 83 c5 01          	add    $0x1,%r13
    49d4:	45 31 ff             	xor    %r15d,%r15d
    49d7:	44 39 ef             	cmp    %r13d,%edi
    49da:	0f 8f a0 fe ff ff    	jg     4880 <timer_thread+0x210>
    49e0:	eb 8b                	jmp    496d <timer_thread+0x2fd>
    49e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    49e8:	89 c2                	mov    %eax,%edx
    49ea:	bf 01 00 00 00       	mov    $0x1,%edi
    49ef:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    49f1:	48 83 c5 01          	add    $0x1,%rbp
    49f5:	48 8d 35 09 39 00 00 	lea    0x3909(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    49fc:	e8 af da ff ff       	call   24b0 <__printf_chk@plt>
          all_waited = 0; 
    4a01:	31 ff                	xor    %edi,%edi
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4a03:	41 39 6e 30          	cmp    %ebp,0x30(%r14)
    4a07:	0f 8f 6f ff ff ff    	jg     497c <timer_thread+0x30c>
    4a0d:	eb 9b                	jmp    49aa <timer_thread+0x33a>
    4a0f:	90                   	nop
    4a10:	89 ca                	mov    %ecx,%edx
    4a12:	48 8d 35 ec 38 00 00 	lea    0x38ec(%rip),%rsi        # 8305 <_IO_stdin_used+0x305>
    4a19:	bf 01 00 00 00       	mov    $0x1,%edi
    4a1e:	31 c0                	xor    %eax,%eax
    4a20:	e8 8b da ff ff       	call   24b0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4a25:	49 8b 76 18          	mov    0x18(%r14),%rsi
    4a29:	41 8b 56 40          	mov    0x40(%r14),%edx
          all_waited = 0; 
    4a2d:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4a2f:	48 8b 04 ee          	mov    (%rsi,%rbp,8),%rax
    4a33:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a37:	e9 5a ff ff ff       	jmp    4996 <timer_thread+0x326>
    4a3c:	48 8d 3d 11 36 00 00 	lea    0x3611(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4a43:	e8 e8 d8 ff ff       	call   2330 <puts@plt>
  while (data->running) {
    4a48:	41 8b 56 44          	mov    0x44(%r14),%edx
    4a4c:	85 d2                	test   %edx,%edx
    4a4e:	0f 84 eb 00 00 00    	je     4b3f <timer_thread+0x4cf>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4a54:	41 8b 46 2c          	mov    0x2c(%r14),%eax
    4a58:	31 db                	xor    %ebx,%ebx
    4a5a:	48 8d 2d 19 36 00 00 	lea    0x3619(%rip),%rbp        # 807a <_IO_stdin_used+0x7a>
    4a61:	4c 8d 25 2d 36 00 00 	lea    0x362d(%rip),%r12        # 8095 <_IO_stdin_used+0x95>
    4a68:	85 c0                	test   %eax,%eax
    4a6a:	7e 38                	jle    4aa4 <timer_thread+0x434>
    4a6c:	0f 1f 40 00          	nopl   0x0(%rax)
    4a70:	31 c0                	xor    %eax,%eax
    4a72:	89 da                	mov    %ebx,%edx
    4a74:	48 89 ee             	mov    %rbp,%rsi
    4a77:	bf 01 00 00 00       	mov    $0x1,%edi
    4a7c:	e8 2f da ff ff       	call   24b0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4a81:	49 8b 46 18          	mov    0x18(%r14),%rax
    4a85:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4a89:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4a8d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4a94:	0f 84 d2 00 00 00    	je     4b6c <timer_thread+0x4fc>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4a9a:	48 83 c3 01          	add    $0x1,%rbx
    4a9e:	41 39 5e 2c          	cmp    %ebx,0x2c(%r14)
    4aa2:	7f cc                	jg     4a70 <timer_thread+0x400>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4aa4:	49 63 56 30          	movslq 0x30(%r14),%rdx
    4aa8:	85 d2                	test   %edx,%edx
    4aaa:	7e 7c                	jle    4b28 <timer_thread+0x4b8>
      for (int y = 0 ; y < data->task_count ; y++) {
    4aac:	41 8b 46 40          	mov    0x40(%r14),%eax
    4ab0:	85 c0                	test   %eax,%eax
    4ab2:	7e 74                	jle    4b28 <timer_thread+0x4b8>
    4ab4:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4ab7:	4d 8b 46 18          	mov    0x18(%r14),%r8
    4abb:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4ac3:	31 c9                	xor    %ecx,%ecx
    4ac5:	48 c1 e6 09          	shl    $0x9,%rsi
    4ac9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ad0:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4ad4:	48 8b 40 38          	mov    0x38(%rax),%rax
    4ad8:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4adc:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4ae2:	74 1c                	je     4b00 <timer_thread+0x490>
    4ae4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4aee:	48 05 00 02 00 00    	add    $0x200,%rax
    4af4:	48 39 d0             	cmp    %rdx,%rax
    4af7:	74 26                	je     4b1f <timer_thread+0x4af>
    4af9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4b00:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4b0a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4b10:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4b1a:	48 39 d0             	cmp    %rdx,%rax
    4b1d:	75 e1                	jne    4b00 <timer_thread+0x490>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4b1f:	48 83 c1 08          	add    $0x8,%rcx
    4b23:	48 39 cf             	cmp    %rcx,%rdi
    4b26:	75 a8                	jne    4ad0 <timer_thread+0x460>
    asm volatile ("mfence" ::: "memory");
    4b28:	0f ae f0             	mfence
    4b2b:	48 8d 3d 75 35 00 00 	lea    0x3575(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4b32:	e8 f9 d7 ff ff       	call   2330 <puts@plt>
    data->running = 0;
    4b37:	41 c7 46 44 00 00 00 00 	movl   $0x0,0x44(%r14)
    4b3f:	48 8d 3d 68 35 00 00 	lea    0x3568(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4b46:	e8 e5 d7 ff ff       	call   2330 <puts@plt>
}
    4b4b:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    4b50:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4b59:	75 41                	jne    4b9c <timer_thread+0x52c>
    4b5b:	48 83 c4 68          	add    $0x68,%rsp
    4b5f:	31 c0                	xor    %eax,%eax
    4b61:	5b                   	pop    %rbx
    4b62:	5d                   	pop    %rbp
    4b63:	41 5c                	pop    %r12
    4b65:	41 5d                	pop    %r13
    4b67:	41 5e                	pop    %r14
    4b69:	41 5f                	pop    %r15
    4b6b:	c3                   	ret
    4b6c:	4c 89 e7             	mov    %r12,%rdi
    4b6f:	e8 bc d7 ff ff       	call   2330 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4b74:	49 8b 46 18          	mov    0x18(%r14),%rax
    4b78:	be 01 00 00 00       	mov    $0x1,%esi
    4b7d:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4b81:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4b85:	8b 78 60             	mov    0x60(%rax),%edi
    4b88:	e8 d3 d8 ff ff       	call   2460 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4b8d:	41 39 5e 2c          	cmp    %ebx,0x2c(%r14)
    4b91:	0f 8f d9 fe ff ff    	jg     4a70 <timer_thread+0x400>
    4b97:	e9 08 ff ff ff       	jmp    4aa4 <timer_thread+0x434>
}
    4b9c:	e8 df d7 ff ff       	call   2380 <__stack_chk_fail@plt>
    4ba1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4bac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bb0 <minf>:
int minf(int a, int b) {
    4bb0:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    4bb4:	39 f7                	cmp    %esi,%edi
    4bb6:	89 f0                	mov    %esi,%eax
    4bb8:	0f 4e c7             	cmovle %edi,%eax
}
    4bbb:	c3                   	ret
    4bbc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bc0 <maxf>:
int maxf(int a, int b) {
    4bc0:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    4bc4:	39 f7                	cmp    %esi,%edi
    4bc6:	89 f0                	mov    %esi,%eax
    4bc8:	0f 4d c7             	cmovge %edi,%eax
}
    4bcb:	c3                   	ret
    4bcc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bd0 <strtolower>:
void strtolower(char *str) {
    4bd0:	f3 0f 1e fa          	endbr64
    4bd4:	55                   	push   %rbp
    4bd5:	53                   	push   %rbx
    4bd6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    4bda:	48 0f be 1f          	movsbq (%rdi),%rbx
    4bde:	84 db                	test   %bl,%bl
    4be0:	74 24                	je     4c06 <strtolower+0x36>
    4be2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4be5:	e8 a6 d9 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4bea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4bf0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4bf3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4bf7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4bfa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    4bfd:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4c02:	84 db                	test   %bl,%bl
    4c04:	75 ea                	jne    4bf0 <strtolower+0x20>
}
    4c06:	48 83 c4 08          	add    $0x8,%rsp
    4c0a:	5b                   	pop    %rbx
    4c0b:	5d                   	pop    %rbp
    4c0c:	c3                   	ret
    4c0d:	0f 1f 00             	nopl   (%rax)

0000000000004c10 <zh_malloc>:
void *zh_malloc(size_t size) {
    4c10:	f3 0f 1e fa          	endbr64
    4c14:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4c18:	e8 53 d8 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4c1d:	48 85 c0             	test   %rax,%rax
    4c20:	74 05                	je     4c27 <zh_malloc+0x17>
}
    4c22:	48 83 c4 08          	add    $0x8,%rsp
    4c26:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4c27:	48 8b 0d f2 63 00 00 	mov    0x63f2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4c2e:	ba 28 00 00 00       	mov    $0x28,%edx
    4c33:	be 01 00 00 00       	mov    $0x1,%esi
    4c38:	48 8d 3d 79 39 00 00 	lea    0x3979(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    4c3f:	e8 ec d8 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    4c44:	bf 01 00 00 00       	mov    $0x1,%edi
    4c49:	e8 c2 d8 ff ff       	call   2510 <exit@plt>
    4c4e:	66 90                	xchg   %ax,%ax

0000000000004c50 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4c50:	f3 0f 1e fa          	endbr64
    4c54:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4c55:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4c5a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4c5d:	e8 4e d7 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    4c62:	48 85 c0             	test   %rax,%rax
    4c65:	74 11                	je     4c78 <get_filename_ext+0x28>
    4c67:	48 39 c3             	cmp    %rax,%rbx
    4c6a:	74 0c                	je     4c78 <get_filename_ext+0x28>
    return dot + 1;
    4c6c:	48 83 c0 01          	add    $0x1,%rax
}
    4c70:	5b                   	pop    %rbx
    4c71:	c3                   	ret
    4c72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4c78:	48 8d 05 77 34 00 00 	lea    0x3477(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4c7f:	5b                   	pop    %rbx
    4c80:	c3                   	ret
    4c81:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4c8c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004c90 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4c90:	f3 0f 1e fa          	endbr64
    4c94:	41 55                	push   %r13
    4c96:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c99:	48 89 fe             	mov    %rdi,%rsi
    4c9c:	41 54                	push   %r12
    4c9e:	55                   	push   %rbp
    4c9f:	48 89 d5             	mov    %rdx,%rbp
    4ca2:	ba 00 04 00 00       	mov    $0x400,%edx
    4ca7:	53                   	push   %rbx
    4ca8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4caf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4cb8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4cc0:	31 c0                	xor    %eax,%eax
    4cc2:	49 89 e4             	mov    %rsp,%r12
    4cc5:	4c 89 e7             	mov    %r12,%rdi
    4cc8:	e8 c3 d7 ff ff       	call   2490 <__strcpy_chk@plt>
    for (; *str; ++str)
    4ccd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4cd2:	84 db                	test   %bl,%bl
    4cd4:	74 24                	je     4cfa <send_headers+0x6a>
        *str = (char)tolower(*str);
    4cd6:	e8 b5 d8 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4cdb:	48 8b 08             	mov    (%rax),%rcx
    4cde:	4c 89 e0             	mov    %r12,%rax
    4ce1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4ce8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4ceb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4cef:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4cf2:	48 0f be 18          	movsbq (%rax),%rbx
    4cf6:	84 db                	test   %bl,%bl
    4cf8:	75 ee                	jne    4ce8 <send_headers+0x58>
    void *buf = malloc(size);
    4cfa:	bf 11 00 00 00       	mov    $0x11,%edi
    4cff:	e8 6c d7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4d04:	48 85 c0             	test   %rax,%rax
    4d07:	0f 84 7e 04 00 00    	je     518b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4d0d:	66 0f 6f 05 db 3e 00 00 	movdqa 0x3edb(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    iov[0].iov_base = zh_malloc(slen);
    4d15:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4d19:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4d1e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4d26:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4d2a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4d2d:	e8 3e d7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4d32:	48 85 c0             	test   %rax,%rax
    4d35:	0f 84 50 04 00 00    	je     518b <send_headers+0x4fb>
    4d3b:	66 0f 6f 05 bd 3e 00 00 	movdqa 0x3ebd(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    iov[1].iov_base = zh_malloc(slen);
    4d43:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4d47:	4c 89 e7             	mov    %r12,%rdi
    4d4a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4d54:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4d5c:	0f 11 00             	movups %xmm0,(%rax)
    4d5f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4d63:	be 2e 00 00 00       	mov    $0x2e,%esi
    4d68:	e8 43 d6 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    4d6d:	48 85 c0             	test   %rax,%rax
    4d70:	0f 84 ea 02 00 00    	je     5060 <send_headers+0x3d0>
    4d76:	4c 39 e0             	cmp    %r12,%rax
    4d79:	0f 84 e1 02 00 00    	je     5060 <send_headers+0x3d0>
    return dot + 1;
    4d7f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4d83:	48 8d 3d 3a 33 00 00 	lea    0x333a(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4d8a:	48 89 de             	mov    %rbx,%rsi
    4d8d:	e8 7e d6 ff ff       	call   2410 <strcmp@plt>
    4d92:	85 c0                	test   %eax,%eax
    4d94:	75 20                	jne    4db6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d96:	66 0f 6f 05 72 3e 00 00 	movdqa 0x3e72(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4d9e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4da6:	66 0f 6f 05 72 3e 00 00 	movdqa 0x3e72(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4dae:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4db6:	48 89 de             	mov    %rbx,%rsi
    4db9:	48 8d 3d 08 33 00 00 	lea    0x3308(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4dc0:	e8 4b d6 ff ff       	call   2410 <strcmp@plt>
    4dc5:	85 c0                	test   %eax,%eax
    4dc7:	75 20                	jne    4de9 <send_headers+0x159>
    4dc9:	66 0f 6f 05 3f 3e 00 00 	movdqa 0x3e3f(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4dd1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4dd9:	66 0f 6f 05 3f 3e 00 00 	movdqa 0x3e3f(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4de1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4de9:	48 89 de             	mov    %rbx,%rsi
    4dec:	48 8d 3d da 32 00 00 	lea    0x32da(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4df3:	e8 18 d6 ff ff       	call   2410 <strcmp@plt>
    4df8:	85 c0                	test   %eax,%eax
    4dfa:	0f 84 10 02 00 00    	je     5010 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4e00:	48 89 de             	mov    %rbx,%rsi
    4e03:	48 8d 3d c7 32 00 00 	lea    0x32c7(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4e0a:	e8 01 d6 ff ff       	call   2410 <strcmp@plt>
    4e0f:	85 c0                	test   %eax,%eax
    4e11:	0f 84 a9 02 00 00    	je     50c0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4e17:	48 89 de             	mov    %rbx,%rsi
    4e1a:	48 8d 3d b4 32 00 00 	lea    0x32b4(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4e21:	e8 ea d5 ff ff       	call   2410 <strcmp@plt>
    4e26:	85 c0                	test   %eax,%eax
    4e28:	0f 84 6a 02 00 00    	je     5098 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4e2e:	48 89 de             	mov    %rbx,%rsi
    4e31:	48 8d 3d e0 32 00 00 	lea    0x32e0(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4e38:	e8 d3 d5 ff ff       	call   2410 <strcmp@plt>
    4e3d:	85 c0                	test   %eax,%eax
    4e3f:	0f 84 2b 02 00 00    	je     5070 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4e45:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4e48:	0f 84 52 01 00 00    	je     4fa0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4e4e:	48 89 de             	mov    %rbx,%rsi
    4e51:	48 8d 3d 81 32 00 00 	lea    0x3281(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4e58:	e8 b3 d5 ff ff       	call   2410 <strcmp@plt>
    4e5d:	85 c0                	test   %eax,%eax
    4e5f:	0f 84 ab 02 00 00    	je     5110 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4e65:	48 89 de             	mov    %rbx,%rsi
    4e68:	48 8d 3d 6e 32 00 00 	lea    0x326e(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4e6f:	e8 9c d5 ff ff       	call   2410 <strcmp@plt>
    4e74:	85 c0                	test   %eax,%eax
    4e76:	0f 84 6c 02 00 00    	je     50e8 <send_headers+0x458>
    slen = strlen(send_buffer);
    4e7c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4e84:	4c 89 e7             	mov    %r12,%rdi
    4e87:	e8 e4 d4 ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    4e8c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4e8f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4e92:	e8 d9 d5 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4e97:	48 85 c0             	test   %rax,%rax
    4e9a:	0f 84 eb 02 00 00    	je     518b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4ea0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4ea4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ea8:	83 fb 08             	cmp    $0x8,%ebx
    4eab:	0f 83 3f 01 00 00    	jae    4ff0 <send_headers+0x360>
    4eb1:	f6 c3 04             	test   $0x4,%bl
    4eb4:	0f 85 7b 02 00 00    	jne    5135 <send_headers+0x4a5>
    4eba:	85 db                	test   %ebx,%ebx
    4ebc:	74 13                	je     4ed1 <send_headers+0x241>
    4ebe:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4ec6:	88 10                	mov    %dl,(%rax)
    4ec8:	f6 c3 02             	test   $0x2,%bl
    4ecb:	0f 85 96 02 00 00    	jne    5167 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4ed1:	4d 89 e8             	mov    %r13,%r8
    4ed4:	48 8d 0d 06 32 00 00 	lea    0x3206(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4edb:	4c 89 e7             	mov    %r12,%rdi
    4ede:	31 c0                	xor    %eax,%eax
    4ee0:	ba 00 04 00 00       	mov    $0x400,%edx
    4ee5:	be 01 00 00 00       	mov    $0x1,%esi
    4eea:	e8 b1 d6 ff ff       	call   25a0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4eef:	4c 89 e7             	mov    %r12,%rdi
    4ef2:	e8 79 d4 ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    4ef7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4efa:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4efd:	e8 6e d5 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4f02:	48 85 c0             	test   %rax,%rax
    4f05:	0f 84 80 02 00 00    	je     518b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4f0b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4f0f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4f13:	83 fb 08             	cmp    $0x8,%ebx
    4f16:	0f 83 1c 01 00 00    	jae    5038 <send_headers+0x3a8>
    4f1c:	f6 c3 04             	test   $0x4,%bl
    4f1f:	0f 85 29 02 00 00    	jne    514e <send_headers+0x4be>
    4f25:	85 db                	test   %ebx,%ebx
    4f27:	74 13                	je     4f3c <send_headers+0x2ac>
    4f29:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4f31:	88 10                	mov    %dl,(%rax)
    4f33:	f6 c3 02             	test   $0x2,%bl
    4f36:	0f 85 3d 02 00 00    	jne    5179 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f3c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4f41:	bf 02 00 00 00       	mov    $0x2,%edi
    4f46:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4f4e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4f56:	e8 15 d5 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4f5b:	48 85 c0             	test   %rax,%rax
    4f5e:	0f 84 27 02 00 00    	je     518b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f64:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4f6c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4f70:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4f78:	66 89 10             	mov    %dx,(%rax)
}
    4f7b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4f83:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4f8c:	0f 85 20 02 00 00    	jne    51b2 <send_headers+0x522>
    4f92:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4f99:	5b                   	pop    %rbx
    4f9a:	5d                   	pop    %rbp
    4f9b:	41 5c                	pop    %r12
    4f9d:	41 5d                	pop    %r13
    4f9f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4fa0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4fa4:	0f 85 a4 fe ff ff    	jne    4e4e <send_headers+0x1be>
    4faa:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4fae:	0f 85 9a fe ff ff    	jne    4e4e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4fb4:	66 0f 6f 05 b4 3c 00 00 	movdqa 0x3cb4(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    4fbc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4fc6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fce:	66 0f 6f 05 aa 3c 00 00 	movdqa 0x3caa(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    4fd6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4fde:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4fe6:	e9 63 fe ff ff       	jmp    4e4e <send_headers+0x1be>
    4feb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ff0:	89 da                	mov    %ebx,%edx
    4ff2:	48 89 c7             	mov    %rax,%rdi
    4ff5:	4c 89 e6             	mov    %r12,%rsi
    4ff8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4ffd:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5002:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5005:	c1 e9 03             	shr    $0x3,%ecx
    5008:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    500b:	e9 c1 fe ff ff       	jmp    4ed1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5010:	66 0f 6f 05 f8 3b 00 00 	movdqa 0x3bf8(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    5018:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5020:	66 0f 6f 05 08 3c 00 00 	movdqa 0x3c08(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    5028:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5030:	e9 cb fd ff ff       	jmp    4e00 <send_headers+0x170>
    5035:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5038:	89 da                	mov    %ebx,%edx
    503a:	48 89 c7             	mov    %rax,%rdi
    503d:	4c 89 e6             	mov    %r12,%rsi
    5040:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    5045:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    504a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    504d:	c1 e9 03             	shr    $0x3,%ecx
    5050:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    5053:	e9 e4 fe ff ff       	jmp    4f3c <send_headers+0x2ac>
    5058:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    5060:	48 8d 1d 8f 30 00 00 	lea    0x308f(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    5067:	e9 94 fd ff ff       	jmp    4e00 <send_headers+0x170>
    506c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5070:	66 0f 6f 05 d8 3b 00 00 	movdqa 0x3bd8(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5078:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5080:	66 0f 6f 05 d8 3b 00 00 	movdqa 0x3bd8(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5088:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5090:	e9 b0 fd ff ff       	jmp    4e45 <send_headers+0x1b5>
    5095:	0f 1f 00             	nopl   (%rax)
    5098:	66 0f 6f 05 b0 3b 00 00 	movdqa 0x3bb0(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    50a0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50a8:	66 0f 6f 05 b0 3b 00 00 	movdqa 0x3bb0(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    50b0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    50b8:	e9 71 fd ff ff       	jmp    4e2e <send_headers+0x19e>
    50bd:	0f 1f 00             	nopl   (%rax)
    50c0:	66 0f 6f 05 48 3b 00 00 	movdqa 0x3b48(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    50c8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50d0:	66 0f 6f 05 68 3b 00 00 	movdqa 0x3b68(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    50d8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    50e0:	e9 32 fd ff ff       	jmp    4e17 <send_headers+0x187>
    50e5:	0f 1f 00             	nopl   (%rax)
    50e8:	66 0f 6f 05 60 3b 00 00 	movdqa 0x3b60(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    50f0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50f8:	66 0f 6f 05 a0 3b 00 00 	movdqa 0x3ba0(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    5100:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5108:	e9 6f fd ff ff       	jmp    4e7c <send_headers+0x1ec>
    510d:	0f 1f 00             	nopl   (%rax)
    5110:	66 0f 6f 05 38 3b 00 00 	movdqa 0x3b38(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5118:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5120:	66 0f 6f 05 68 3b 00 00 	movdqa 0x3b68(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    5128:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5130:	e9 30 fd ff ff       	jmp    4e65 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5135:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    513c:	89 db                	mov    %ebx,%ebx
    513e:	89 10                	mov    %edx,(%rax)
    5140:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5145:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5149:	e9 83 fd ff ff       	jmp    4ed1 <send_headers+0x241>
    514e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5155:	89 db                	mov    %ebx,%ebx
    5157:	89 10                	mov    %edx,(%rax)
    5159:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    515e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5162:	e9 d5 fd ff ff       	jmp    4f3c <send_headers+0x2ac>
    5167:	89 db                	mov    %ebx,%ebx
    5169:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    516f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5174:	e9 58 fd ff ff       	jmp    4ed1 <send_headers+0x241>
    5179:	89 db                	mov    %ebx,%ebx
    517b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    5181:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5186:	e9 b1 fd ff ff       	jmp    4f3c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    518b:	48 8b 0d 8e 5e 00 00 	mov    0x5e8e(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5192:	ba 28 00 00 00       	mov    $0x28,%edx
    5197:	be 01 00 00 00       	mov    $0x1,%esi
    519c:	48 8d 3d 15 34 00 00 	lea    0x3415(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    51a3:	e8 88 d3 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    51a8:	bf 01 00 00 00       	mov    $0x1,%edi
    51ad:	e8 5e d3 ff ff       	call   2510 <exit@plt>
}
    51b2:	e8 c9 d1 ff ff       	call   2380 <__stack_chk_fail@plt>
    51b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000051c0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    51c0:	f3 0f 1e fa          	endbr64
    51c4:	41 55                	push   %r13
    51c6:	49 89 d5             	mov    %rdx,%r13
    51c9:	41 54                	push   %r12
    51cb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    51ce:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    51d1:	55                   	push   %rbp
    51d2:	53                   	push   %rbx
    51d3:	48 89 f3             	mov    %rsi,%rbx
    51d6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    51da:	e8 91 d2 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    51df:	48 85 c0             	test   %rax,%rax
    51e2:	74 6b                	je     524f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    51e4:	4c 89 e7             	mov    %r12,%rdi
    51e7:	48 89 c5             	mov    %rax,%rbp
    51ea:	31 f6                	xor    %esi,%esi
    51ec:	31 c0                	xor    %eax,%eax
    51ee:	e8 ed d2 ff ff       	call   24e0 <open@plt>
    51f3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    51f6:	85 c0                	test   %eax,%eax
    51f8:	0f 88 d8 d3 ff ff    	js     25d6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    51fe:	48 89 da             	mov    %rbx,%rdx
    5201:	48 89 ee             	mov    %rbp,%rsi
    5204:	89 c7                	mov    %eax,%edi
    5206:	e8 e5 d1 ff ff       	call   23f0 <read@plt>
    if (ret < file_size) {
    520b:	48 98                	cltq
    520d:	48 39 d8             	cmp    %rbx,%rax
    5210:	7c 1e                	jl     5230 <copy_file_contents+0x70>
    close(fd);
    5212:	44 89 e7             	mov    %r12d,%edi
    5215:	e8 b6 d1 ff ff       	call   23d0 <close@plt>
    iov->iov_base = buf;
    521a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    521e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    5222:	48 83 c4 08          	add    $0x8,%rsp
    5226:	5b                   	pop    %rbx
    5227:	5d                   	pop    %rbp
    5228:	41 5c                	pop    %r12
    522a:	41 5d                	pop    %r13
    522c:	c3                   	ret
    522d:	0f 1f 00             	nopl   (%rax)
    5230:	48 8b 0d e9 5d 00 00 	mov    0x5de9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5237:	ba 1a 00 00 00       	mov    $0x1a,%edx
    523c:	be 01 00 00 00       	mov    $0x1,%esi
    5241:	48 8d 3d af 2e 00 00 	lea    0x2eaf(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    5248:	e8 e3 d2 ff ff       	call   2530 <fwrite@plt>
    524d:	eb c3                	jmp    5212 <copy_file_contents+0x52>
    524f:	48 8b 0d ca 5d 00 00 	mov    0x5dca(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5256:	ba 28 00 00 00       	mov    $0x28,%edx
    525b:	be 01 00 00 00       	mov    $0x1,%esi
    5260:	48 8d 3d 51 33 00 00 	lea    0x3351(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    5267:	e8 c4 d2 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    526c:	bf 01 00 00 00       	mov    $0x1,%edi
    5271:	e8 9a d2 ff ff       	call   2510 <exit@plt>
    5276:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005280 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    5280:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    5284:	8b 46 44             	mov    0x44(%rsi),%eax
    5287:	48 89 fa             	mov    %rdi,%rdx
    528a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    528d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5293:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5296:	48 8b 07             	mov    (%rdi),%rax
    5299:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    529c:	f6 c1 02             	test   $0x2,%cl
    529f:	74 00                	je     52a1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    52a1:	89 f0                	mov    %esi,%eax
    52a3:	44 29 c0             	sub    %r8d,%eax
    52a6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    52a9:	0f 82 33 d3 ff ff    	jb     25e2 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    52af:	c1 e9 0a             	shr    $0xa,%ecx
    52b2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52b6:	8b 47 44             	mov    0x44(%rdi),%eax
    52b9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    52bc:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    52bf:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    52c2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    52c5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    52c9:	d3 e0                	shl    %cl,%eax
    52cb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    52ce:	48 c1 e0 06          	shl    $0x6,%rax
    52d2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    52d6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    52dc:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    52df:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    52e3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    52e9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    52f1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    52f5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    52f8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    52ff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5307:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    530b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    530f:	e8 7c d0 ff ff       	call   2390 <io_uring_submit@plt>
}
    5314:	31 c0                	xor    %eax,%eax
    5316:	48 83 c4 08          	add    $0x8,%rsp
    531a:	c3                   	ret
    531b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005320 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    5320:	f3 0f 1e fa          	endbr64
    5324:	41 55                	push   %r13
    5326:	41 89 fd             	mov    %edi,%r13d
    5329:	41 54                	push   %r12
    532b:	55                   	push   %rbp
    532c:	53                   	push   %rbx
    532d:	48 89 f3             	mov    %rsi,%rbx
    5330:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    5334:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5337:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    533d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    5340:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5343:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5345:	f6 c1 02             	test   $0x2,%cl
    5348:	74 00                	je     534a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    534a:	89 c2                	mov    %eax,%edx
    534c:	29 f2                	sub    %esi,%edx
    534e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5351:	0f 82 9b d2 ff ff    	jb     25f2 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5357:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    535a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    535d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5360:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    5365:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5368:	23 6b 58             	and    0x58(%rbx),%ebp
    536b:	d3 e5                	shl    %cl,%ebp
    536d:	48 c1 e5 06          	shl    $0x6,%rbp
    5371:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5375:	e8 f6 d0 ff ff       	call   2470 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    537a:	be 01 00 00 00       	mov    $0x1,%esi
    537f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5384:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    5387:	e8 74 d0 ff ff       	call   2400 <calloc@plt>
    req->client_socket = client_socket;
    538c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5391:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5395:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5398:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    539d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    53a2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    53ab:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    53b3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    53b7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    53bb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    53c2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    53ca:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    53ce:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    53d6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    53de:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    53e2:	e8 a9 cf ff ff       	call   2390 <io_uring_submit@plt>
}
    53e7:	48 83 c4 08          	add    $0x8,%rsp
    53eb:	31 c0                	xor    %eax,%eax
    53ed:	5b                   	pop    %rbx
    53ee:	5d                   	pop    %rbp
    53ef:	41 5c                	pop    %r12
    53f1:	41 5d                	pop    %r13
    53f3:	c3                   	ret
    53f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    53ff:	90                   	nop

0000000000005400 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5400:	f3 0f 1e fa          	endbr64
    5404:	41 56                	push   %r14
    5406:	41 89 f6             	mov    %esi,%r14d
    5409:	41 55                	push   %r13
    540b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    540e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5413:	41 54                	push   %r12
    5415:	55                   	push   %rbp
    5416:	48 89 d5             	mov    %rdx,%rbp
    5419:	53                   	push   %rbx
    void *buf = malloc(size);
    541a:	e8 51 d0 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    541f:	48 85 c0             	test   %rax,%rax
    5422:	0f 84 dd 00 00 00    	je     5505 <_send_static_string_content+0x105>
    5428:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    542b:	4c 89 ef             	mov    %r13,%rdi
    542e:	e8 3d cf ff ff       	call   2370 <strlen@plt>
    req->iovec_count = 1;
    5433:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    543a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    543e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    5441:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    5444:	e8 27 d0 ff ff       	call   2470 <malloc@plt>
    5449:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    544c:	48 85 c0             	test   %rax,%rax
    544f:	0f 84 b0 00 00 00    	je     5505 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    5455:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5459:	4c 89 e2             	mov    %r12,%rdx
    545c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    545f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5463:	e8 d8 cf ff ff       	call   2440 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5468:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    546b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5471:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5474:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5478:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    547a:	f6 c1 02             	test   $0x2,%cl
    547d:	0f 85 7d 00 00 00    	jne    5500 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    5483:	89 d0                	mov    %edx,%eax
    5485:	29 f0                	sub    %esi,%eax
    5487:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    548a:	0f 82 6c d1 ff ff    	jb     25fc <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5490:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5493:	8b 45 44             	mov    0x44(%rbp),%eax
    5496:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    5499:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    549c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    549f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    54a2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    54a8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    54ac:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    54ae:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    54b1:	48 89 ef             	mov    %rbp,%rdi
    54b4:	48 c1 e0 06          	shl    $0x6,%rax
    54b8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    54bc:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    54bf:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    54c3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    54c9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    54d1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    54d5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    54d8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    54df:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    54e7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    54eb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    54ef:	5b                   	pop    %rbx
    54f0:	5d                   	pop    %rbp
    54f1:	41 5c                	pop    %r12
    54f3:	41 5d                	pop    %r13
    54f5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    54f7:	e9 94 ce ff ff       	jmp    2390 <io_uring_submit@plt>
    54fc:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    5500:	e9 7e ff ff ff       	jmp    5483 <_send_static_string_content+0x83>
    5505:	48 8b 0d 14 5b 00 00 	mov    0x5b14(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    550c:	ba 28 00 00 00       	mov    $0x28,%edx
    5511:	be 01 00 00 00       	mov    $0x1,%esi
    5516:	48 8d 3d 9b 30 00 00 	lea    0x309b(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    551d:	e8 0e d0 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5522:	bf 01 00 00 00       	mov    $0x1,%edi
    5527:	e8 e4 cf ff ff       	call   2510 <exit@plt>
    552c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005530 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    5530:	f3 0f 1e fa          	endbr64
    5534:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5537:	89 fe                	mov    %edi,%esi
    5539:	48 8b 3d d8 5a 00 00 	mov    0x5ad8(%rip),%rdi        # b018 <unimplemented_content>
    5540:	e9 bb fe ff ff       	jmp    5400 <_send_static_string_content>
    5545:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005550 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5550:	f3 0f 1e fa          	endbr64
    5554:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5557:	89 fe                	mov    %edi,%esi
    5559:	48 8b 3d b0 5a 00 00 	mov    0x5ab0(%rip),%rdi        # b010 <http_404_content>
    5560:	e9 9b fe ff ff       	jmp    5400 <_send_static_string_content>
    5565:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005570 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    5570:	f3 0f 1e fa          	endbr64
    5574:	41 56                	push   %r14
    5576:	41 55                	push   %r13
    5578:	49 89 d5             	mov    %rdx,%r13
    557b:	41 54                	push   %r12
    557d:	41 89 f4             	mov    %esi,%r12d
    5580:	55                   	push   %rbp
    5581:	48 89 fd             	mov    %rdi,%rbp
    5584:	53                   	push   %rbx
    5585:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    558c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5595:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    559d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    559f:	e8 cc cd ff ff       	call   2370 <strlen@plt>
    55a4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    55a9:	48 89 c3             	mov    %rax,%rbx
    55ac:	0f 84 b6 00 00 00    	je     5668 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55b2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55b7:	48 89 ee             	mov    %rbp,%rsi
    55ba:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    55be:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    55c3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    55cb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55d3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    55de:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55e6:	e8 35 ce ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    55eb:	48 89 e6             	mov    %rsp,%rsi
    55ee:	4c 89 f7             	mov    %r14,%rdi
    55f1:	e8 3a ce ff ff       	call   2430 <stat@plt>
    55f6:	83 f8 ff             	cmp    $0xffffffff,%eax
    55f9:	0f 84 d3 00 00 00    	je     56d2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    55ff:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5603:	25 00 f0 00 00       	and    $0xf000,%eax
    5608:	3d 00 80 00 00       	cmp    $0x8000,%eax
    560d:	0f 84 f5 00 00 00    	je     5708 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    5613:	48 8b 3d f6 59 00 00 	mov    0x59f6(%rip),%rdi        # b010 <http_404_content>
    561a:	4c 89 ea             	mov    %r13,%rdx
    561d:	44 89 e6             	mov    %r12d,%esi
    5620:	e8 db fd ff ff       	call   5400 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5625:	4c 89 f2             	mov    %r14,%rdx
    5628:	bf 01 00 00 00       	mov    $0x1,%edi
    562d:	31 c0                	xor    %eax,%eax
    562f:	48 8d 35 11 2b 00 00 	lea    0x2b11(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5636:	e8 75 ce ff ff       	call   24b0 <__printf_chk@plt>
}
    563b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5643:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    564c:	0f 85 20 01 00 00    	jne    5772 <handle_get_method+0x202>
    5652:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5659:	5b                   	pop    %rbx
    565a:	5d                   	pop    %rbp
    565b:	41 5c                	pop    %r12
    565d:	41 5d                	pop    %r13
    565f:	41 5e                	pop    %r14
    5661:	c3                   	ret
    5662:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5668:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    566d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5675:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    567a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    567d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5685:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5688:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5690:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    569b:	e8 80 cd ff ff       	call   2420 <__memcpy_chk@plt>
    56a0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    56a5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    56aa:	48 8d 35 61 2a 00 00 	lea    0x2a61(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    56b1:	48 29 d9             	sub    %rbx,%rcx
    56b4:	ba 0b 00 00 00       	mov    $0xb,%edx
    56b9:	e8 62 cd ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    56be:	48 89 e6             	mov    %rsp,%rsi
    56c1:	4c 89 f7             	mov    %r14,%rdi
    56c4:	e8 67 cd ff ff       	call   2430 <stat@plt>
    56c9:	83 f8 ff             	cmp    $0xffffffff,%eax
    56cc:	0f 85 2d ff ff ff    	jne    55ff <handle_get_method+0x8f>
    56d2:	4c 89 f2             	mov    %r14,%rdx
    56d5:	48 89 e9             	mov    %rbp,%rcx
    56d8:	48 8d 35 3e 2a 00 00 	lea    0x2a3e(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    56df:	31 c0                	xor    %eax,%eax
    56e1:	bf 01 00 00 00       	mov    $0x1,%edi
    56e6:	e8 c5 cd ff ff       	call   24b0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    56eb:	48 8b 3d 1e 59 00 00 	mov    0x591e(%rip),%rdi        # b010 <http_404_content>
    56f2:	4c 89 ea             	mov    %r13,%rdx
    56f5:	44 89 e6             	mov    %r12d,%esi
    56f8:	e8 03 fd ff ff       	call   5400 <_send_static_string_content>
}
    56fd:	e9 39 ff ff ff       	jmp    563b <handle_get_method+0xcb>
    5702:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5708:	bf 70 00 00 00       	mov    $0x70,%edi
    570d:	e8 5e cd ff ff       	call   2470 <malloc@plt>
    5712:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5715:	48 85 c0             	test   %rax,%rax
    5718:	74 5d                	je     5777 <handle_get_method+0x207>
            req->client_socket = client_socket;
    571a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    571e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5723:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5727:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    572a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5731:	e8 5a f5 ff ff       	call   4c90 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5736:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    573b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    573f:	4c 89 f7             	mov    %r14,%rdi
    5742:	e8 79 fa ff ff       	call   51c0 <copy_file_contents>
    5747:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    574c:	4c 89 f2             	mov    %r14,%rdx
    574f:	31 c0                	xor    %eax,%eax
    5751:	48 8d 35 dd 29 00 00 	lea    0x29dd(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    5758:	bf 01 00 00 00       	mov    $0x1,%edi
    575d:	e8 4e cd ff ff       	call   24b0 <__printf_chk@plt>
            add_write_request(req, ring);
    5762:	4c 89 ee             	mov    %r13,%rsi
    5765:	48 89 df             	mov    %rbx,%rdi
    5768:	e8 13 fb ff ff       	call   5280 <add_write_request>
    576d:	e9 c9 fe ff ff       	jmp    563b <handle_get_method+0xcb>
}
    5772:	e8 09 cc ff ff       	call   2380 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5777:	48 8b 0d a2 58 00 00 	mov    0x58a2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    577e:	ba 28 00 00 00       	mov    $0x28,%edx
    5783:	be 01 00 00 00       	mov    $0x1,%esi
    5788:	48 8d 3d 29 2e 00 00 	lea    0x2e29(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    578f:	e8 9c cd ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5794:	bf 01 00 00 00       	mov    $0x1,%edi
    5799:	e8 72 cd ff ff       	call   2510 <exit@plt>
    579e:	66 90                	xchg   %ax,%ax

00000000000057a0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    57a0:	f3 0f 1e fa          	endbr64
    57a4:	41 57                	push   %r15
    57a6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    57a8:	4c 8d 35 fd 28 00 00 	lea    0x28fd(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    57af:	41 55                	push   %r13
    57b1:	49 89 d5             	mov    %rdx,%r13
    57b4:	41 54                	push   %r12
    57b6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    57b9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    57bc:	55                   	push   %rbp
    57bd:	53                   	push   %rbx
    57be:	48 83 ec 18          	sub    $0x18,%rsp
    57c2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    57cb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    57d0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    57d2:	49 89 e7             	mov    %rsp,%r15
    57d5:	4c 89 fa             	mov    %r15,%rdx
    57d8:	e8 03 cc ff ff       	call   23e0 <strtok_r@plt>
    for (; *str; ++str)
    57dd:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    57e1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    57e4:	84 db                	test   %bl,%bl
    57e6:	74 1d                	je     5805 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    57e8:	e8 a3 cd ff ff       	call   2590 <__ctype_tolower_loc@plt>
    57ed:	48 89 ea             	mov    %rbp,%rdx
    57f0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    57f3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    57f7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    57fa:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    57fd:	48 0f be 1a          	movsbq (%rdx),%rbx
    5801:	84 db                	test   %bl,%bl
    5803:	75 eb                	jne    57f0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5805:	4c 89 fa             	mov    %r15,%rdx
    5808:	4c 89 f6             	mov    %r14,%rsi
    580b:	31 ff                	xor    %edi,%edi
    580d:	e8 ce cb ff ff       	call   23e0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5812:	48 8d 35 41 29 00 00 	lea    0x2941(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    5819:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    581c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    581f:	e8 ec cb ff ff       	call   2410 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5824:	4c 89 ea             	mov    %r13,%rdx
    5827:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    582a:	85 c0                	test   %eax,%eax
    582c:	75 2a                	jne    5858 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    582e:	48 89 df             	mov    %rbx,%rdi
    5831:	e8 3a fd ff ff       	call   5570 <handle_get_method>
}
    5836:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    583b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5844:	75 20                	jne    5866 <handle_http_method+0xc6>
    5846:	48 83 c4 18          	add    $0x18,%rsp
    584a:	5b                   	pop    %rbx
    584b:	5d                   	pop    %rbp
    584c:	41 5c                	pop    %r12
    584e:	41 5d                	pop    %r13
    5850:	41 5e                	pop    %r14
    5852:	41 5f                	pop    %r15
    5854:	c3                   	ret
    5855:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5858:	48 8b 3d b9 57 00 00 	mov    0x57b9(%rip),%rdi        # b018 <unimplemented_content>
    585f:	e8 9c fb ff ff       	call   5400 <_send_static_string_content>
}
    5864:	eb d0                	jmp    5836 <handle_http_method+0x96>
    5866:	e8 15 cb ff ff       	call   2380 <__stack_chk_fail@plt>
    586b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005870 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5870:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5874:	85 d2                	test   %edx,%edx
    5876:	7e 38                	jle    58b0 <get_line+0x40>
    5878:	48 63 d2             	movslq %edx,%rdx
    587b:	48 83 c7 01          	add    $0x1,%rdi
    587f:	48 01 f2             	add    %rsi,%rdx
    5882:	eb 11                	jmp    5895 <get_line+0x25>
    5884:	0f 1f 40 00          	nopl   0x0(%rax)
    5888:	48 83 c6 01          	add    $0x1,%rsi
    588c:	48 83 c7 01          	add    $0x1,%rdi
    5890:	48 39 d6             	cmp    %rdx,%rsi
    5893:	74 1b                	je     58b0 <get_line+0x40>
        dest[i] = src[i];
    5895:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5899:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    589b:	3c 0d                	cmp    $0xd,%al
    589d:	75 e9                	jne    5888 <get_line+0x18>
    589f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    58a2:	75 e4                	jne    5888 <get_line+0x18>
            dest[i] = '\0';
    58a4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    58a7:	31 c0                	xor    %eax,%eax
    58a9:	c3                   	ret
    58aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    58b0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    58b5:	c3                   	ret
    58b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000058c0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    58c0:	f3 0f 1e fa          	endbr64
    58c4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    58cb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    58cf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    58d8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    58e0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    58e2:	49 89 e2             	mov    %rsp,%r10
    58e5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    58ed:	4c 89 d0             	mov    %r10,%rax
    58f0:	eb 13                	jmp    5905 <handle_client_request+0x45>
    58f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    58f8:	48 83 c0 01          	add    $0x1,%rax
    58fc:	48 83 c1 01          	add    $0x1,%rcx
    5900:	4c 39 c8             	cmp    %r9,%rax
    5903:	74 4b                	je     5950 <handle_client_request+0x90>
        dest[i] = src[i];
    5905:	44 0f b6 01          	movzbl (%rcx),%r8d
    5909:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    590c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5910:	75 e6                	jne    58f8 <handle_client_request+0x38>
    5912:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5916:	75 e0                	jne    58f8 <handle_client_request+0x38>
            dest[i] = '\0';
    5918:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    591b:	8b 47 08             	mov    0x8(%rdi),%eax
    591e:	48 89 f2             	mov    %rsi,%rdx
    5921:	4c 89 d7             	mov    %r10,%rdi
    5924:	89 c6                	mov    %eax,%esi
    5926:	e8 75 fe ff ff       	call   57a0 <handle_http_method>
}
    592b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5933:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    593c:	75 39                	jne    5977 <handle_client_request+0xb7>
    593e:	31 c0                	xor    %eax,%eax
    5940:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5947:	c3                   	ret
    5948:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5950:	48 8b 0d c9 56 00 00 	mov    0x56c9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5957:	ba 12 00 00 00       	mov    $0x12,%edx
    595c:	be 01 00 00 00       	mov    $0x1,%esi
    5961:	48 8d 3d f6 27 00 00 	lea    0x27f6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5968:	e8 c3 cb ff ff       	call   2530 <fwrite@plt>
        exit(1);
    596d:	bf 01 00 00 00       	mov    $0x1,%edi
    5972:	e8 99 cb ff ff       	call   2510 <exit@plt>
}
    5977:	e8 04 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    597c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005980 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5980:	f3 0f 1e fa          	endbr64
    5984:	55                   	push   %rbp
    5985:	53                   	push   %rbx
    5986:	48 89 cb             	mov    %rcx,%rbx
    5989:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    598d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5990:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5993:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5999:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    599c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    599f:	f6 c1 02             	test   $0x2,%cl
    59a2:	74 00                	je     59a4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    59a4:	41 89 c0             	mov    %eax,%r8d
    59a7:	45 29 c8             	sub    %r9d,%r8d
    59aa:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    59ae:	0f 82 58 cc ff ff    	jb     260c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    59b4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    59b7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    59ba:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    59bd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    59c0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    59c3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    59c7:	d3 e5                	shl    %cl,%ebp
    59c9:	48 c1 e5 06          	shl    $0x6,%rbp
    59cd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    59d1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    59d4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    59d9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    59e0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    59e4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    59e8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    59f0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    59f8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    59fc:	e8 6f ca ff ff       	call   2470 <malloc@plt>
  io_uring_submit(ring);
    5a01:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5a04:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    5a0a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    5a0e:	48 83 c4 08          	add    $0x8,%rsp
    5a12:	5b                   	pop    %rbx
    5a13:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5a14:	e9 77 c9 ff ff       	jmp    2390 <io_uring_submit@plt>
    5a19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005a20 <io_thread>:
void* io_thread(void *arg) {
    5a20:	f3 0f 1e fa          	endbr64
    5a24:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a26:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5a28:	41 56                	push   %r14
    5a2a:	41 55                	push   %r13
    5a2c:	41 54                	push   %r12
    5a2e:	55                   	push   %rbp
    5a2f:	48 89 fd             	mov    %rdi,%rbp
    5a32:	53                   	push   %rbx
    5a33:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    5a3a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5a43:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    5a4b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a4f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5a54:	bf 00 01 00 00       	mov    $0x100,%edi
    5a59:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    5a5c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5a60:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5a65:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5a6a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    5a6f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5a74:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    5a7c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5a81:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5a89:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5a8e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5a96:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5a9b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5aa3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5aa8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5ab0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5ab5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    5abd:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5ac5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5acd:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5ad5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5add:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5ae5:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5aed:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5af5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5afd:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5b05:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5b0d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5b14:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5b1c:	e8 2f c9 ff ff       	call   2450 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5b21:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5b25:	31 f6                	xor    %esi,%esi
    5b27:	e8 24 ca ff ff       	call   2550 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5b2c:	31 d2                	xor    %edx,%edx
    5b2e:	be 01 00 00 00       	mov    $0x1,%esi
    5b33:	bf 02 00 00 00       	mov    $0x2,%edi
    5b38:	e8 73 ca ff ff       	call   25b0 <socket@plt>
  if (sock == -1)
    5b3d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5b40:	0f 84 08 cb ff ff    	je     264e <io_thread.cold+0x38>
  if (setsockopt(sock,
    5b46:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5b4b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5b51:	89 c7                	mov    %eax,%edi
    5b53:	41 89 c4             	mov    %eax,%r12d
    5b56:	ba 02 00 00 00       	mov    $0x2,%edx
    5b5b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5b60:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5b68:	e8 d3 c7 ff ff       	call   2340 <setsockopt@plt>
    5b6d:	85 c0                	test   %eax,%eax
    5b6f:	0f 88 ad ca ff ff    	js     2622 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5b75:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    5b7a:	ba 10 00 00 00       	mov    $0x10,%edx
    5b7f:	44 89 e7             	mov    %r12d,%edi
    5b82:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5b8b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5b93:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    5b9b:	e8 20 c9 ff ff       	call   24c0 <bind@plt>
    5ba0:	85 c0                	test   %eax,%eax
    5ba2:	0f 88 b2 ca ff ff    	js     265a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5ba8:	be 0a 00 00 00       	mov    $0xa,%esi
    5bad:	44 89 e7             	mov    %r12d,%edi
    5bb0:	e8 cb c8 ff ff       	call   2480 <listen@plt>
    5bb5:	85 c0                	test   %eax,%eax
    5bb7:	0f 88 71 ca ff ff    	js     262e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5bbd:	ba db 18 00 00       	mov    $0x18db,%edx
    5bc2:	48 8d 35 da 25 00 00 	lea    0x25da(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5bc9:	bf 01 00 00 00       	mov    $0x1,%edi
    5bce:	31 c0                	xor    %eax,%eax
    5bd0:	e8 db c8 ff ff       	call   24b0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5bd5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5bda:	48 89 d9             	mov    %rbx,%rcx
    5bdd:	44 89 e7             	mov    %r12d,%edi
    5be0:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5be5:	48 89 c6             	mov    %rax,%rsi
    5be8:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5bed:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5bf2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5bfa:	e8 81 fd ff ff       	call   5980 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5bff:	bf 01 00 00 00       	mov    $0x1,%edi
    5c04:	be 10 00 00 00       	mov    $0x10,%esi
    5c09:	e8 f2 c7 ff ff       	call   2400 <calloc@plt>
    void *buf = malloc(size);
    5c0e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5c13:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5c16:	e8 55 c8 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5c1b:	48 85 c0             	test   %rax,%rax
    5c1e:	0f 84 ae 04 00 00    	je     60d2 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5c24:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5c28:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5c2f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5c36:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5c3e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5c41:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5c46:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5c48:	f6 c1 02             	test   $0x2,%cl
    5c4b:	0f 85 0f 04 00 00    	jne    6060 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5c51:	89 d0                	mov    %edx,%eax
    5c53:	29 f0                	sub    %esi,%eax
    5c55:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5c5c:	0f 82 e2 c9 ff ff    	jb     2644 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5c62:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5c65:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5c69:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5c6d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c70:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5c77:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c7a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5c81:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5c88:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5c8a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5c8d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5c92:	48 c1 e0 06          	shl    $0x6,%rax
    5c96:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5c9e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5ca4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5ca7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5caf:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5cb3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5cbb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5cc3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5cc7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5ccb:	e8 c0 c6 ff ff       	call   2390 <io_uring_submit@plt>
  while (data->running == 1) {
    5cd0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5cd4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5cd9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5ce1:	0f 85 d7 01 00 00    	jne    5ebe <io_thread+0x49e>
    5ce7:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5cec:	4d 89 ce             	mov    %r9,%r14
    5cef:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5cf4:	0f 1f 40 00          	nopl   0x0(%rax)
    5cf8:	48 8d 3d ba 24 00 00 	lea    0x24ba(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5cff:	e8 2c c6 ff ff       	call   2330 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5d04:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5d0b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5d12:	c1 e9 0b             	shr    $0xb,%ecx
    5d15:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5d18:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5d20:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5d22:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5d2a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5d2c:	39 d0                	cmp    %edx,%eax
    5d2e:	74 36                	je     5d66 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5d30:	89 f8                	mov    %edi,%eax
    5d32:	21 d0                	and    %edx,%eax
    5d34:	d3 e0                	shl    %cl,%eax
    5d36:	48 c1 e0 04          	shl    $0x4,%rax
    5d3a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5d42:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5d4a:	0f 85 a8 01 00 00    	jne    5ef8 <io_thread+0x4d8>
    5d50:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5d54:	0f 85 0e 03 00 00    	jne    6068 <io_thread+0x648>
			if (cqe->res < 0)
    5d5a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5d5d:	83 c2 01             	add    $0x1,%edx
    5d60:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5d62:	85 c0                	test   %eax,%eax
    5d64:	79 b2                	jns    5d18 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5d66:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5d6f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5d70:	45 31 c0             	xor    %r8d,%r8d
    5d73:	31 d2                	xor    %edx,%edx
    5d75:	b9 01 00 00 00       	mov    $0x1,%ecx
    5d7a:	4c 89 f6             	mov    %r14,%rsi
    5d7d:	48 89 df             	mov    %rbx,%rdi
    5d80:	e8 1b c7 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5d85:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5d88:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5d8d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5d91:	0f 84 e1 02 00 00    	je     6078 <io_thread+0x658>
    5d97:	48 8d 3d 41 24 00 00 	lea    0x2441(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5d9e:	e8 8d c5 ff ff       	call   2330 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5da3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5da8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5dab:	45 85 ff             	test   %r15d,%r15d
    5dae:	0f 88 62 c8 ff ff    	js     2616 <io_thread.cold>
      if (cqe->res < 0) {
    5db4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5db7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    5dbb:	85 c0                	test   %eax,%eax
    5dbd:	0f 88 d5 02 00 00    	js     6098 <io_thread+0x678>
      switch (req->event_type) {
    5dc3:	41 83 f8 01          	cmp    $0x1,%r8d
    5dc7:	0f 84 7b 01 00 00    	je     5f48 <io_thread+0x528>
    5dcd:	41 83 f8 02          	cmp    $0x2,%r8d
    5dd1:	0f 84 a1 01 00 00    	je     5f78 <io_thread+0x558>
    5dd7:	45 85 c0             	test   %r8d,%r8d
    5dda:	0f 85 50 01 00 00    	jne    5f30 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5de0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5de5:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5dea:	48 89 d9             	mov    %rbx,%rcx
    5ded:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5df1:	e8 8a fb ff ff       	call   5980 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5df6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5dfb:	48 89 de             	mov    %rbx,%rsi
    5dfe:	8b 78 08             	mov    0x8(%rax),%edi
    5e01:	e8 1a f5 ff ff       	call   5320 <add_read_request>
              free(req);
    5e06:	4c 89 e7             	mov    %r12,%rdi
    5e09:	e8 f2 c4 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5e0e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5e13:	48 85 c0             	test   %rax,%rax
    5e16:	0f 85 14 01 00 00    	jne    5f30 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    5e1c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5e23:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5e2a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5e2d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5e32:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5e34:	f6 c1 02             	test   $0x2,%cl
    5e37:	74 00                	je     5e39 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5e39:	89 d0                	mov    %edx,%eax
    5e3b:	29 f0                	sub    %esi,%eax
    5e3d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5e44:	0f 82 f0 c7 ff ff    	jb     263a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5e4a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5e4d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5e52:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5e56:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e59:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5e60:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e63:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5e6a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e71:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5e73:	8b 55 60             	mov    0x60(%rbp),%edx
    5e76:	48 c1 e0 06          	shl    $0x6,%rax
    5e7a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5e82:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5e88:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5e8b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5e93:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5e97:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5e9f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5ea7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5eab:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5eaf:	e8 dc c4 ff ff       	call   2390 <io_uring_submit@plt>
  while (data->running == 1) {
    5eb4:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5eb8:	0f 84 3a fe ff ff    	je     5cf8 <io_thread+0x2d8>
    5ebe:	48 8d 3d 53 23 00 00 	lea    0x2353(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5ec5:	e8 66 c4 ff ff       	call   2330 <puts@plt>
}
    5eca:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5ed2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5edb:	0f 85 18 02 00 00    	jne    60f9 <io_thread+0x6d9>
    5ee1:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5ee8:	31 c0                	xor    %eax,%eax
    5eea:	5b                   	pop    %rbx
    5eeb:	5d                   	pop    %rbp
    5eec:	41 5c                	pop    %r12
    5eee:	41 5d                	pop    %r13
    5ef0:	41 5e                	pop    %r14
    5ef2:	41 5f                	pop    %r15
    5ef4:	c3                   	ret
    5ef5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5ef8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5efd:	48 85 c0             	test   %rax,%rax
    5f00:	0f 84 6a fe ff ff    	je     5d70 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5f06:	48 83 38 01          	cmpq   $0x1,(%rax)
    5f0a:	0f 84 68 01 00 00    	je     6078 <io_thread+0x658>
    5f10:	48 8d 3d c8 22 00 00 	lea    0x22c8(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5f17:	e8 14 c4 ff ff       	call   2330 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5f1c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5f21:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5f24:	e9 8b fe ff ff       	jmp    5db4 <io_thread+0x394>
    5f29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5f30:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5f38:	8b 02                	mov    (%rdx),%eax
    5f3a:	83 c0 01             	add    $0x1,%eax
    5f3d:	89 02                	mov    %eax,(%rdx)
}
    5f3f:	e9 d8 fe ff ff       	jmp    5e1c <io_thread+0x3fc>
    5f44:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5f48:	85 c0                	test   %eax,%eax
    5f4a:	75 74                	jne    5fc0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5f4c:	48 8b 0d cd 50 00 00 	mov    0x50cd(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5f53:	ba 0f 00 00 00       	mov    $0xf,%edx
    5f58:	be 01 00 00 00       	mov    $0x1,%esi
    5f5d:	48 8d 3d a4 22 00 00 	lea    0x22a4(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5f64:	e8 c7 c5 ff ff       	call   2530 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5f69:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f6e:	e9 a0 fe ff ff       	jmp    5e13 <io_thread+0x3f3>
    5f73:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5f78:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5f7d:	45 31 ff             	xor    %r15d,%r15d
    5f80:	85 c0                	test   %eax,%eax
    5f82:	7e 20                	jle    5fa4 <io_thread+0x584>
    5f84:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5f88:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5f8b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5f8f:	48 c1 e0 04          	shl    $0x4,%rax
    5f93:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5f98:	e8 63 c3 ff ff       	call   2300 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5f9d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5fa2:	7f e4                	jg     5f88 <io_thread+0x568>
              close(req->client_socket);
    5fa4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5fa9:	e8 22 c4 ff ff       	call   23d0 <close@plt>
              free(req);
    5fae:	4c 89 e7             	mov    %r12,%rdi
    5fb1:	e8 4a c3 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5fb6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5fbb:	e9 53 fe ff ff       	jmp    5e13 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5fc0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5fc5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5fca:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5fd2:	eb 11                	jmp    5fe5 <io_thread+0x5c5>
    5fd4:	0f 1f 40 00          	nopl   0x0(%rax)
    5fd8:	48 83 c0 01          	add    $0x1,%rax
    5fdc:	48 83 c2 01          	add    $0x1,%rdx
    5fe0:	48 39 c6             	cmp    %rax,%rsi
    5fe3:	74 4b                	je     6030 <io_thread+0x610>
        dest[i] = src[i];
    5fe5:	0f b6 0a             	movzbl (%rdx),%ecx
    5fe8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5fea:	80 f9 0d             	cmp    $0xd,%cl
    5fed:	75 e9                	jne    5fd8 <io_thread+0x5b8>
    5fef:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5ff3:	75 e3                	jne    5fd8 <io_thread+0x5b8>
            dest[i] = '\0';
    5ff5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5ff8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5ffd:	48 89 da             	mov    %rbx,%rdx
    6000:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    6005:	e8 96 f7 ff ff       	call   57a0 <handle_http_method>
              free(req->iov[0].iov_base);
    600a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    600f:	e8 ec c2 ff ff       	call   2300 <free@plt>
              free(req);
    6014:	4c 89 e7             	mov    %r12,%rdi
    6017:	e8 e4 c2 ff ff       	call   2300 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    601c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    6021:	e9 ed fd ff ff       	jmp    5e13 <io_thread+0x3f3>
    6026:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6030:	48 8b 0d e9 4f 00 00 	mov    0x4fe9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6037:	ba 12 00 00 00       	mov    $0x12,%edx
    603c:	be 01 00 00 00       	mov    $0x1,%esi
    6041:	48 8d 3d 16 21 00 00 	lea    0x2116(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6048:	e8 e3 c4 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    604d:	bf 01 00 00 00       	mov    $0x1,%edi
    6052:	e8 b9 c4 ff ff       	call   2510 <exit@plt>
    6057:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    6060:	e9 ec fb ff ff       	jmp    5c51 <io_thread+0x231>
    6065:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    6068:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    606d:	e9 94 fe ff ff       	jmp    5f06 <io_thread+0x4e6>
    6072:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6078:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6080:	48 8d 3d 44 21 00 00 	lea    0x2144(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    6087:	8b 02                	mov    (%rdx),%eax
    6089:	83 c0 01             	add    $0x1,%eax
    608c:	89 02                	mov    %eax,(%rdx)
    608e:	e8 9d c2 ff ff       	call   2330 <puts@plt>
    6093:	e9 26 fe ff ff       	jmp    5ebe <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    6098:	f7 d8                	neg    %eax
    609a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    609f:	89 c7                	mov    %eax,%edi
    60a1:	e8 ca c4 ff ff       	call   2570 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    60a6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    60ab:	be 01 00 00 00       	mov    $0x1,%esi
    60b0:	48 8b 3d 69 4f 00 00 	mov    0x4f69(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    60b7:	48 89 c1             	mov    %rax,%rcx
    60ba:	48 8d 15 27 25 00 00 	lea    0x2527(%rip),%rdx        # 85e8 <_IO_stdin_used+0x5e8>
    60c1:	31 c0                	xor    %eax,%eax
    60c3:	e8 78 c4 ff ff       	call   2540 <__fprintf_chk@plt>
          exit(1);
    60c8:	bf 01 00 00 00       	mov    $0x1,%edi
    60cd:	e8 3e c4 ff ff       	call   2510 <exit@plt>
    60d2:	48 8b 0d 47 4f 00 00 	mov    0x4f47(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    60d9:	ba 28 00 00 00       	mov    $0x28,%edx
    60de:	be 01 00 00 00       	mov    $0x1,%esi
    60e3:	48 8d 3d ce 24 00 00 	lea    0x24ce(%rip),%rdi        # 85b8 <_IO_stdin_used+0x5b8>
    60ea:	e8 41 c4 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    60ef:	bf 01 00 00 00       	mov    $0x1,%edi
    60f4:	e8 17 c4 ff ff       	call   2510 <exit@plt>
}
    60f9:	e8 82 c2 ff ff       	call   2380 <__stack_chk_fail@plt>
    60fe:	66 90                	xchg   %ax,%ax

0000000000006100 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    6100:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6104:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    610b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    6111:	85 c9                	test   %ecx,%ecx
    6113:	0f 8e ea 00 00 00    	jle    6203 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    6119:	41 56                	push   %r14
    611b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    611d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    6120:	41 54                	push   %r12
    6122:	49 89 fc             	mov    %rdi,%r12
    6125:	55                   	push   %rbp
    6126:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6127:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    612b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6130:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    6134:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    613c:	31 db                	xor    %ebx,%ebx
    613e:	8b 10                	mov    (%rax),%edx
    6140:	85 d2                	test   %edx,%edx
    6142:	7e 26                	jle    616a <barriered_work_ingest+0x6a>
    6144:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    6148:	48 89 dd             	mov    %rbx,%rbp
    614b:	48 c1 e5 08          	shl    $0x8,%rbp
    614f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    6153:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    615a:	74 24                	je     6180 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    615c:	48 83 c3 01          	add    $0x1,%rbx
    6160:	39 da                	cmp    %ebx,%edx
    6162:	7f e4                	jg     6148 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6164:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    616a:	49 83 c5 01          	add    $0x1,%r13
    616e:	44 39 e9             	cmp    %r13d,%ecx
    6171:	7f bd                	jg     6130 <barriered_work_ingest+0x30>
}
    6173:	5b                   	pop    %rbx
    6174:	31 c0                	xor    %eax,%eax
    6176:	5d                   	pop    %rbp
    6177:	41 5c                	pop    %r12
    6179:	41 5d                	pop    %r13
    617b:	41 5e                	pop    %r14
    617d:	c3                   	ret
    617e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    6180:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    6189:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    6190:	bf 04 00 00 00       	mov    $0x4,%edi
    6195:	48 c1 e6 05          	shl    $0x5,%rsi
    6199:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    61a0:	48 83 c6 10          	add    $0x10,%rsi
    61a4:	e8 a7 c1 ff ff       	call   2350 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    61a9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    61b1:	48 8b 40 50          	mov    0x50(%rax),%rax
    61b5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    61b9:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    61bd:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    61c7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    61cd:	83 c0 01             	add    $0x1,%eax
    61d0:	99                   	cltd
    61d1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    61d7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    61dd:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    61e0:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    61e8:	48 83 c3 01          	add    $0x1,%rbx
    61ec:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    61f0:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    61f4:	8b 10                	mov    (%rax),%edx
    61f6:	39 da                	cmp    %ebx,%edx
    61f8:	0f 8f 46 ff ff ff    	jg     6144 <barriered_work_ingest+0x44>
    61fe:	e9 61 ff ff ff       	jmp    6164 <barriered_work_ingest+0x64>
}
    6203:	31 c0                	xor    %eax,%eax
    6205:	c3                   	ret
    6206:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006210 <barriered_thread>:
void* barriered_thread(void *arg) {
    6210:	f3 0f 1e fa          	endbr64
    6214:	41 56                	push   %r14
    6216:	41 55                	push   %r13
    6218:	41 54                	push   %r12
  int t = 0;
    621a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    621d:	55                   	push   %rbp
  int waiting = 0;
    621e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    6220:	53                   	push   %rbx
    6221:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    6224:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6228:	0f 85 74 02 00 00    	jne    64a2 <barriered_thread+0x292>
    if (t >= data->task_count) {
    622e:	8b 43 40             	mov    0x40(%rbx),%eax
    6231:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6238:	41 39 c4             	cmp    %eax,%r12d
    623b:	0f 8d 6f 01 00 00    	jge    63b0 <barriered_thread+0x1a0>
    6241:	49 63 fc             	movslq %r12d,%rdi
    6244:	48 c1 e7 09          	shl    $0x9,%rdi
    6248:	49 89 fd             	mov    %rdi,%r13
    624b:	eb 32                	jmp    627f <barriered_thread+0x6f>
    624d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    6250:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6254:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6258:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    625c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6260:	4c 01 ef             	add    %r13,%rdi
    6263:	e8 98 fe ff ff       	call   6100 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    6268:	8b 43 40             	mov    0x40(%rbx),%eax
    626b:	41 83 c4 01          	add    $0x1,%r12d
    626f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    6276:	44 39 e0             	cmp    %r12d,%eax
    6279:	0f 8e 19 02 00 00    	jle    6498 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    627f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6283:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    6287:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    628e:	75 c0                	jne    6250 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6290:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    6294:	83 e8 01             	sub    $0x1,%eax
    6297:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    629c:	45 85 e4             	test   %r12d,%r12d
    629f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    62a2:	45 85 c0             	test   %r8d,%r8d
    62a5:	0f 8e 2d 01 00 00    	jle    63d8 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    62ab:	48 63 c8             	movslq %eax,%rcx
    62ae:	48 8b 43 18          	mov    0x18(%rbx),%rax
    62b2:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    62b5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    62bb:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    62c2:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    62c6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    62c9:	45 31 f6             	xor    %r14d,%r14d
    62cc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    62d0:	48 8b 10             	mov    (%rax),%rdx
    62d3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    62d7:	49 01 cb             	add    %rcx,%r11
    62da:	4c 89 da             	mov    %r11,%rdx
    62dd:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    62e4:	75 04                	jne    62ea <barriered_thread+0xda>
            arrived++;
    62e6:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    62ea:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    62f0:	75 04                	jne    62f6 <barriered_thread+0xe6>
            prearrive++;
    62f2:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    62f6:	48 83 c0 08          	add    $0x8,%rax
    62fa:	48 39 c6             	cmp    %rax,%rsi
    62fd:	75 d1                	jne    62d0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    62ff:	45 85 d2             	test   %r10d,%r10d
    6302:	0f 84 c0 00 00 00    	je     63c8 <barriered_thread+0x1b8>
    6308:	45 39 d0             	cmp    %r10d,%r8d
    630b:	0f 84 b7 00 00 00    	je     63c8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    6311:	45 85 f6             	test   %r14d,%r14d
    6314:	74 0a                	je     6320 <barriered_thread+0x110>
    6316:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    631a:	0f 85 ae 01 00 00    	jne    64ce <barriered_thread+0x2be>
    6320:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    6324:	4c 01 ea             	add    %r13,%rdx
    6327:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    632e:	45 85 e4             	test   %r12d,%r12d
    6331:	75 14                	jne    6347 <barriered_thread+0x137>
    6333:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    633a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6341:	0f 8c 69 01 00 00    	jl     64b0 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6347:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    634b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    634f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6359:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    635d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6361:	4c 01 ef             	add    %r13,%rdi
    6364:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    636a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    636e:	4c 01 e8             	add    %r13,%rax
    6371:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6378:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    637b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6380:	83 e8 01             	sub    $0x1,%eax
    6383:	44 39 e0             	cmp    %r12d,%eax
    6386:	0f 84 a4 00 00 00    	je     6430 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    638c:	0f ae f8             	sfence
          if (waiting == 0) {
    638f:	85 ed                	test   %ebp,%ebp
    6391:	0f 84 d1 00 00 00    	je     6468 <barriered_thread+0x258>
        int arrived = 0; 
    6397:	bd 01 00 00 00       	mov    $0x1,%ebp
    639c:	e9 c7 fe ff ff       	jmp    6268 <barriered_thread+0x58>
  while (data->running == 1) {
    63a1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    63a5:	0f 85 f7 00 00 00    	jne    64a2 <barriered_thread+0x292>
    63ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    63b0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    63b8:	85 c0                	test   %eax,%eax
    63ba:	7e e5                	jle    63a1 <barriered_thread+0x191>
    63bc:	45 31 e4             	xor    %r12d,%r12d
    63bf:	e9 7d fe ff ff       	jmp    6241 <barriered_thread+0x31>
    63c4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    63c8:	83 fd 01             	cmp    $0x1,%ebp
    63cb:	74 1b                	je     63e8 <barriered_thread+0x1d8>
        int arrived = 0; 
    63cd:	31 ed                	xor    %ebp,%ebp
    63cf:	e9 3d ff ff ff       	jmp    6311 <barriered_thread+0x101>
    63d4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    63d8:	83 fd 01             	cmp    $0x1,%ebp
    63db:	0f 85 43 ff ff ff    	jne    6324 <barriered_thread+0x114>
        int arrived = 0; 
    63e1:	45 31 f6             	xor    %r14d,%r14d
    63e4:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    63e8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    63ef:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    63f4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    63f6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    63fa:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6401:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6406:	e8 45 bf ff ff       	call   2350 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    640b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6412:	48 83 c0 01          	add    $0x1,%rax
    6416:	48 99                	cqto
    6418:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    641f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    6426:	e9 e6 fe ff ff       	jmp    6311 <barriered_thread+0x101>
    642b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6430:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6437:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    643e:	0f 8d 48 ff ff ff    	jge    638c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    6444:	48 c1 e6 04          	shl    $0x4,%rsi
    6448:	bf 04 00 00 00       	mov    $0x4,%edi
    644d:	48 03 73 70          	add    0x70(%rbx),%rsi
    6451:	e8 fa be ff ff       	call   2350 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6456:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    645e:	e9 29 ff ff ff       	jmp    638c <barriered_thread+0x17c>
    6463:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    6468:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    646f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    6474:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6478:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    647f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6483:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6487:	e8 c4 be ff ff       	call   2350 <clock_gettime@plt>
            waiting = 1;
    648c:	e9 06 ff ff ff       	jmp    6397 <barriered_thread+0x187>
    6491:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    6498:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    649c:	0f 84 96 fd ff ff    	je     6238 <barriered_thread+0x28>
}
    64a2:	5b                   	pop    %rbx
    64a3:	31 c0                	xor    %eax,%eax
    64a5:	5d                   	pop    %rbp
    64a6:	41 5c                	pop    %r12
    64a8:	41 5d                	pop    %r13
    64aa:	41 5e                	pop    %r14
    64ac:	c3                   	ret
    64ad:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    64b0:	48 c1 e6 04          	shl    $0x4,%rsi
    64b4:	bf 04 00 00 00       	mov    $0x4,%edi
    64b9:	48 03 73 68          	add    0x68(%rbx),%rsi
    64bd:	e8 8e be ff ff       	call   2350 <clock_gettime@plt>
          data->tasks[t].available = 0;
    64c2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    64c6:	4c 01 ea             	add    %r13,%rdx
    64c9:	e9 79 fe ff ff       	jmp    6347 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    64ce:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    64d2:	48 8b 43 18          	mov    0x18(%rbx),%rax
    64d6:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    64da:	48 8b 78 38          	mov    0x38(%rax),%rdi
    64de:	4c 01 ef             	add    %r13,%rdi
    64e1:	e8 1a fc ff ff       	call   6100 <barriered_work_ingest>
          break;
    64e6:	e9 39 fd ff ff       	jmp    6224 <barriered_thread+0x14>
    64eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000064f0 <receive>:
int receive(struct BarrierTask *data) {
    64f0:	f3 0f 1e fa          	endbr64
    64f4:	41 57                	push   %r15
    64f6:	41 56                	push   %r14
    64f8:	41 55                	push   %r13
    64fa:	41 54                	push   %r12
    64fc:	55                   	push   %rbp
    64fd:	53                   	push   %rbx
    64fe:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6502:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    6509:	45 85 f6             	test   %r14d,%r14d
    650c:	0f 8e 34 01 00 00    	jle    6646 <receive+0x156>
    if (n == data->thread->real_thread_index) { continue; }
    6512:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    6519:	48 89 fe             	mov    %rdi,%rsi
    651c:	45 31 e4             	xor    %r12d,%r12d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    651f:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    6521:	49 63 6f 08          	movslq 0x8(%r15),%rbp
    6525:	49 89 ed             	mov    %rbp,%r13
    6528:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6530:	41 39 dd             	cmp    %ebx,%r13d
    6533:	0f 84 fd 00 00 00    	je     6636 <receive+0x146>
    struct Data *me = data->mailboxes[n].lower;
    6539:	48 8b 86 70 01 00 00 	mov    0x170(%rsi),%rax
    6540:	4a 8b 14 20          	mov    (%rax,%r12,1),%rdx
    if (me->available_reading == 1) {
    6544:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    654a:	83 f8 01             	cmp    $0x1,%eax
    654d:	74 11                	je     6560 <receive+0x70>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    654f:	83 ba 18 03 00 00 02 	cmpl   $0x2,0x318(%rdx)
    6556:	75 08                	jne    6560 <receive+0x70>
    6558:	85 c0                	test   %eax,%eax
    655a:	0f 84 d6 00 00 00    	je     6636 <receive+0x146>
    for (; me->messages_count > 0 ; ) {
    6560:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    6567:	48 85 ff             	test   %rdi,%rdi
    656a:	0f 8e a8 00 00 00    	jle    6618 <receive+0x128>
    6570:	4c 8b 8e 78 01 00 00 	mov    0x178(%rsi),%r9
    6577:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    657e:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
    6582:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    6585:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    6589:	49 01 f9             	add    %rdi,%r9
    658c:	49 01 f8             	add    %rdi,%r8
    658f:	48 03 ba 10 03 00 00 	add    0x310(%rdx),%rdi
    6596:	eb 0e                	jmp    65a6 <receive+0xb6>
    6598:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    for (; me->messages_count > 0 ; ) {
    65a0:	48 83 e8 01          	sub    $0x1,%rax
    65a4:	72 72                	jb     6618 <receive+0x128>
      data->sends++;
    65a6:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
    65a9:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
    65b0:	48 29 c1             	sub    %rax,%rcx
    65b3:	48 89 8e 78 01 00 00 	mov    %rcx,0x178(%rsi)
      data->n++;
    65ba:	4c 89 c1             	mov    %r8,%rcx
    65bd:	48 29 c1             	sub    %rax,%rcx
    65c0:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
    65c7:	48 89 f9             	mov    %rdi,%rcx
    65ca:	48 29 c1             	sub    %rax,%rcx
    65cd:	48 89 8a 10 03 00 00 	mov    %rcx,0x310(%rdx)
      if (me->messages[x]->group == data->group) {
    65d4:	48 63 c8             	movslq %eax,%rcx
    65d7:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    65db:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    65df:	75 bf                	jne    65a0 <receive+0xb0>
    65e1:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    65e5:	75 b9                	jne    65a0 <receive+0xb0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    65e7:	49 63 47 04          	movslq 0x4(%r15),%rax
    65eb:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    65ed:	bf 01 00 00 00       	mov    $0x1,%edi
    65f2:	ba 01 00 00 00       	mov    $0x1,%edx
    65f7:	48 8d 35 12 20 00 00 	lea    0x2012(%rip),%rsi        # 8610 <_IO_stdin_used+0x610>
    65fe:	48 39 e8             	cmp    %rbp,%rax
    6601:	0f 94 c1             	sete   %cl
    6604:	31 c0                	xor    %eax,%eax
    6606:	e8 a5 be ff ff       	call   24b0 <__printf_chk@plt>
        exit(1);
    660b:	bf 01 00 00 00       	mov    $0x1,%edi
    6610:	e8 fb be ff ff       	call   2510 <exit@plt>
    6615:	0f 1f 00             	nopl   (%rax)
      me->available_reading = 0;
    6618:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    6622:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
    662c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6636:	83 c3 01             	add    $0x1,%ebx
    6639:	49 83 c4 48          	add    $0x48,%r12
    663d:	44 39 f3             	cmp    %r14d,%ebx
    6640:	0f 85 ea fe ff ff    	jne    6530 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    6646:	0f ae f8             	sfence
}
    6649:	48 83 c4 08          	add    $0x8,%rsp
    664d:	31 c0                	xor    %eax,%eax
    664f:	5b                   	pop    %rbx
    6650:	5d                   	pop    %rbp
    6651:	41 5c                	pop    %r12
    6653:	41 5d                	pop    %r13
    6655:	41 5e                	pop    %r14
    6657:	41 5f                	pop    %r15
    6659:	c3                   	ret
    665a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000006660 <sendm>:
int sendm(struct BarrierTask *data) {
    6660:	f3 0f 1e fa          	endbr64
    6664:	41 57                	push   %r15
    6666:	41 56                	push   %r14
    6668:	41 55                	push   %r13
    666a:	41 54                	push   %r12
    666c:	55                   	push   %rbp
    666d:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    666e:	8b 8f 40 01 00 00    	mov    0x140(%rdi),%ecx
    6674:	85 c9                	test   %ecx,%ecx
    6676:	0f 8e b9 00 00 00    	jle    6735 <sendm+0xd5>
    667c:	48 89 fa             	mov    %rdi,%rdx
    667f:	31 f6                	xor    %esi,%esi
    6681:	31 c0                	xor    %eax,%eax
    6683:	eb 20                	jmp    66a5 <sendm+0x45>
    6685:	0f 1f 00             	nopl   (%rax)
    6688:	48 c7 41 40 00 00 00 00 	movq   $0x0,0x40(%rcx)
    6690:	8b 8a 40 01 00 00    	mov    0x140(%rdx),%ecx
    6696:	83 c0 01             	add    $0x1,%eax
    6699:	48 83 c6 48          	add    $0x48,%rsi
    669d:	39 c8                	cmp    %ecx,%eax
    669f:	0f 8d 90 00 00 00    	jge    6735 <sendm+0xd5>
        if (n == data->thread->real_thread_index) { continue; }
    66a5:	4c 8b 82 28 01 00 00 	mov    0x128(%rdx),%r8
    66ac:	41 39 40 08          	cmp    %eax,0x8(%r8)
    66b0:	74 e4                	je     6696 <sendm+0x36>
        struct Data *them = data->mailboxes[n].higher;
    66b2:	48 8b 8a 70 01 00 00 	mov    0x170(%rdx),%rcx
    66b9:	48 01 f1             	add    %rsi,%rcx
        data->mailboxes[n].counter++;
    66bc:	48 8b 59 40          	mov    0x40(%rcx),%rbx
        struct Data *them = data->mailboxes[n].higher;
    66c0:	48 8b 79 08          	mov    0x8(%rcx),%rdi
        data->mailboxes[n].counter++;
    66c4:	4c 8d 4b 01          	lea    0x1(%rbx),%r9
        if (data->mailboxes[n].counter > limit) {
    66c8:	49 83 f9 64          	cmp    $0x64,%r9
    66cc:	7f ba                	jg     6688 <sendm+0x28>
    66ce:	4c 89 49 40          	mov    %r9,0x40(%rcx)
        if (data->mailboxes[n].counter < limit) {
    66d2:	75 4c                	jne    6720 <sendm+0xc0>
        if (them->messages_count > 0) {
    66d4:	4c 8b 8f 80 00 00 00 	mov    0x80(%rdi),%r9
    66db:	4d 85 c9             	test   %r9,%r9
    66de:	7f 40                	jg     6720 <sendm+0xc0>
        if (them->available_sending == 1) {
    66e0:	44 8b 97 00 01 00 00 	mov    0x100(%rdi),%r10d
    66e7:	41 83 fa 01          	cmp    $0x1,%r10d
    66eb:	74 0e                	je     66fb <sendm+0x9b>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    66ed:	83 bf 18 03 00 00 02 	cmpl   $0x2,0x318(%rdi)
    66f4:	75 05                	jne    66fb <sendm+0x9b>
    66f6:	45 85 d2             	test   %r10d,%r10d
    66f9:	74 25                	je     6720 <sendm+0xc0>
        if (data->sending == 1) {
    66fb:	83 ba 80 01 00 00 01 	cmpl   $0x1,0x180(%rdx)
    6702:	74 44                	je     6748 <sendm+0xe8>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter >= limit) {
    6704:	83 79 38 02          	cmpl   $0x2,0x38(%rcx)
    6708:	75 16                	jne    6720 <sendm+0xc0>
          data->mailboxes[n].counter = 0;
    670a:	48 c7 41 40 00 00 00 00 	movq   $0x0,0x40(%rcx)
          data->thread->have_foreign = 1;
    6712:	41 c7 80 d8 00 00 00 01 00 00 00 	movl   $0x1,0xd8(%r8)
    671d:	0f 1f 00             	nopl   (%rax)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6720:	8b 8a 40 01 00 00    	mov    0x140(%rdx),%ecx
    6726:	83 c0 01             	add    $0x1,%eax
    6729:	48 83 c6 48          	add    $0x48,%rsi
    672d:	39 c8                	cmp    %ecx,%eax
    672f:	0f 8c 70 ff ff ff    	jl     66a5 <sendm+0x45>
      asm volatile ("sfence" ::: "memory");
    6735:	0f ae f8             	sfence
}
    6738:	31 c0                	xor    %eax,%eax
    673a:	5b                   	pop    %rbx
    673b:	5d                   	pop    %rbp
    673c:	41 5c                	pop    %r12
    673e:	41 5d                	pop    %r13
    6740:	41 5e                	pop    %r14
    6742:	41 5f                	pop    %r15
    6744:	c3                   	ret
    6745:	0f 1f 00             	nopl   (%rax)
          for (; them->messages_count < min;) {
    6748:	4c 63 a7 88 00 00 00 	movslq 0x88(%rdi),%r12
    674f:	4d 39 e1             	cmp    %r12,%r9
    6752:	0f 8d aa 00 00 00    	jge    6802 <sendm+0x1a2>
    6758:	48 8b 9a 08 01 00 00 	mov    0x108(%rdx),%rbx
    675f:	4c 89 e5             	mov    %r12,%rbp
    6762:	4c 29 cd             	sub    %r9,%rbp
    6765:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    676a:	48 8b 9f 08 03 00 00 	mov    0x308(%rdi),%rbx
    6771:	4c 8d 55 ff          	lea    -0x1(%rbp),%r10
    6775:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
            them->messages[them->messages_count++] = data->message; 
    677a:	48 8b 1f             	mov    (%rdi),%rbx
    677d:	49 83 fa 02          	cmp    $0x2,%r10
    6781:	0f 86 19 01 00 00    	jbe    68a0 <sendm+0x240>
    6787:	4e 8d 1c e5 00 00 00 00 	lea    0x0(,%r12,8),%r11
    678f:	4e 8d 14 cd 00 00 00 00 	lea    0x0(,%r9,8),%r10
    6797:	4e 8d 34 1b          	lea    (%rbx,%r11,1),%r14
    679b:	4c 8d ba 88 01 00 00 	lea    0x188(%rdx),%r15
    67a2:	4e 8d 2c 13          	lea    (%rbx,%r10,1),%r13
    67a6:	4d 39 f7             	cmp    %r14,%r15
    67a9:	73 7d                	jae    6828 <sendm+0x1c8>
    67ab:	4c 8d b2 90 01 00 00 	lea    0x190(%rdx),%r14
    67b2:	4d 39 f5             	cmp    %r14,%r13
    67b5:	73 71                	jae    6828 <sendm+0x1c8>
    67b7:	49 01 da             	add    %rbx,%r10
    67ba:	4e 8d 0c 1b          	lea    (%rbx,%r11,1),%r9
    67be:	66 90                	xchg   %ax,%ax
    67c0:	4c 8b 9a 88 01 00 00 	mov    0x188(%rdx),%r11
          for (; them->messages_count < min;) {
    67c7:	49 83 c2 08          	add    $0x8,%r10
            them->messages[them->messages_count++] = data->message; 
    67cb:	4d 89 5a f8          	mov    %r11,-0x8(%r10)
          for (; them->messages_count < min;) {
    67cf:	4d 39 d1             	cmp    %r10,%r9
    67d2:	75 ec                	jne    67c0 <sendm+0x160>
    67d4:	0f 1f 40 00          	nopl   0x0(%rax)
    67d8:	4c 8b 4c 24 f0       	mov    -0x10(%rsp),%r9
    67dd:	4c 8b 7c 24 e8       	mov    -0x18(%rsp),%r15
    67e2:	49 01 e9             	add    %rbp,%r9
    67e5:	49 01 ef             	add    %rbp,%r15
    67e8:	4c 89 8a 08 01 00 00 	mov    %r9,0x108(%rdx)
    67ef:	4c 89 bf 08 03 00 00 	mov    %r15,0x308(%rdi)
    67f6:	4c 89 a7 80 00 00 00 	mov    %r12,0x80(%rdi)
    67fd:	4e 89 5c e3 f8       	mov    %r11,-0x8(%rbx,%r12,8)
          them->available_sending = 0;
    6802:	c7 87 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdi)
          them->available_reading = 1;
    680c:	c7 87 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdi)
          them->available_receiving = 1;
    6816:	c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdi)
    6820:	e9 df fe ff ff       	jmp    6704 <sendm+0xa4>
    6825:	0f 1f 00             	nopl   (%rax)
    6828:	49 89 ee             	mov    %rbp,%r14
    682b:	4c 8b 9a 88 01 00 00 	mov    0x188(%rdx),%r11
    6832:	4d 89 ea             	mov    %r13,%r10
    6835:	49 d1 ee             	shr    %r14
    6838:	49 c1 e6 04          	shl    $0x4,%r14
    683c:	66 49 0f 6e c3       	movq   %r11,%xmm0
    6841:	4f 8d 7c 35 00       	lea    0x0(%r13,%r14,1),%r15
    6846:	41 83 e6 10          	and    $0x10,%r14d
    684a:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    684e:	74 10                	je     6860 <sendm+0x200>
            them->messages[them->messages_count++] = data->message; 
    6850:	49 83 c2 10          	add    $0x10,%r10
    6854:	41 0f 11 45 00       	movups %xmm0,0x0(%r13)
          for (; them->messages_count < min;) {
    6859:	4d 39 fa             	cmp    %r15,%r10
    685c:	74 14                	je     6872 <sendm+0x212>
    685e:	66 90                	xchg   %ax,%ax
            them->messages[them->messages_count++] = data->message; 
    6860:	41 0f 11 02          	movups %xmm0,(%r10)
    6864:	49 83 c2 20          	add    $0x20,%r10
    6868:	41 0f 11 42 f0       	movups %xmm0,-0x10(%r10)
          for (; them->messages_count < min;) {
    686d:	4d 39 fa             	cmp    %r15,%r10
    6870:	75 ee                	jne    6860 <sendm+0x200>
    6872:	49 89 ea             	mov    %rbp,%r10
    6875:	49 83 e2 fe          	and    $0xfffffffffffffffe,%r10
    6879:	4d 01 d1             	add    %r10,%r9
    687c:	40 f6 c5 01          	test   $0x1,%bpl
    6880:	0f 84 52 ff ff ff    	je     67d8 <sendm+0x178>
            them->messages[them->messages_count++] = data->message; 
    6886:	4c 8b 9a 88 01 00 00 	mov    0x188(%rdx),%r11
    688d:	4e 89 1c cb          	mov    %r11,(%rbx,%r9,8)
          for (; them->messages_count < min;) {
    6891:	e9 42 ff ff ff       	jmp    67d8 <sendm+0x178>
    6896:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    68a0:	4e 8d 14 cd 00 00 00 00 	lea    0x0(,%r9,8),%r10
    68a8:	4e 8d 1c e5 00 00 00 00 	lea    0x0(,%r12,8),%r11
    68b0:	e9 02 ff ff ff       	jmp    67b7 <sendm+0x157>
    68b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000068c0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    68c0:	f3 0f 1e fa          	endbr64
    68c4:	41 57                	push   %r15
    68c6:	41 56                	push   %r14
    68c8:	41 55                	push   %r13
    68ca:	41 54                	push   %r12
    68cc:	55                   	push   %rbp
    68cd:	53                   	push   %rbx
    68ce:	48 89 fb             	mov    %rdi,%rbx
    68d1:	48 83 ec 48          	sub    $0x48,%rsp
        int t = data->task_index;
    68d5:	8b 6f 04             	mov    0x4(%rdi),%ebp
  if (data->thread_index == data->task_index) {
    68d8:	39 af 30 01 00 00    	cmp    %ebp,0x130(%rdi)
    68de:	74 60                	je     6940 <barriered_work+0x80>
    receive(data);
    68e0:	e8 0b fc ff ff       	call   64f0 <receive>
    while (data->scheduled == 1) {
    68e5:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    68ec:	75 16                	jne    6904 <barriered_work+0x44>
    68ee:	66 90                	xchg   %ax,%ax
      data->n++;
    68f0:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      asm volatile ("sfence" ::: "memory");
    68f8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    68fb:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6902:	74 ec                	je     68f0 <barriered_work+0x30>
    sendm(data);
    6904:	48 89 df             	mov    %rbx,%rdi
    6907:	e8 54 fd ff ff       	call   6660 <sendm>
  if (t == data->thread_count - 1) {
    690c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6912:	83 e8 01             	sub    $0x1,%eax
    6915:	39 e8                	cmp    %ebp,%eax
    6917:	0f 84 9e 02 00 00    	je     6bbb <barriered_work+0x2fb>
  data->swap = 0;
    691d:	c7 83 98 01 00 00 00 00 00 00 	movl   $0x0,0x198(%rbx)
  asm volatile ("sfence" ::: "memory");
    6927:	0f ae f8             	sfence
}
    692a:	48 83 c4 48          	add    $0x48,%rsp
    692e:	31 c0                	xor    %eax,%eax
    6930:	5b                   	pop    %rbx
    6931:	5d                   	pop    %rbp
    6932:	41 5c                	pop    %r12
    6934:	41 5d                	pop    %r13
    6936:	41 5e                	pop    %r14
    6938:	41 5f                	pop    %r15
    693a:	c3                   	ret
    693b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    receive(data);
    6940:	e8 ab fb ff ff       	call   64f0 <receive>
        if (data->thread->have_foreign == 1) {
    6945:	4c 8b 93 28 01 00 00 	mov    0x128(%rbx),%r10
    694c:	41 83 ba d8 00 00 00 01 	cmpl   $0x1,0xd8(%r10)
    6954:	0f 84 d4 02 00 00    	je     6c2e <barriered_work+0x36e>
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    695a:	49 63 82 c4 00 00 00 	movslq 0xc4(%r10),%rax
          int k = data->group;
    6961:	8b 93 94 01 00 00    	mov    0x194(%rbx),%edx
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6967:	85 c0                	test   %eax,%eax
    6969:	0f 8e 64 01 00 00    	jle    6ad3 <barriered_work+0x213>
            int y = (k * data->thread->threads_per_group) + d;
    696f:	0f af d0             	imul   %eax,%edx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6972:	48 63 cd             	movslq %ebp,%rcx
    6975:	89 6c 24 20          	mov    %ebp,0x20(%rsp)
              int next_task = abs((t + 1) % (data->thread_count));
    6979:	44 8b 8b 34 01 00 00 	mov    0x134(%rbx),%r9d
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6980:	48 c1 e1 09          	shl    $0x9,%rcx
    6984:	49 89 ce             	mov    %rcx,%r14
    6987:	48 63 d2             	movslq %edx,%rdx
    698a:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    698f:	48 8d 0c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rcx
    6997:	48 01 d0             	add    %rdx,%rax
    699a:	48 89 ce             	mov    %rcx,%rsi
    699d:	48 01 d1             	add    %rdx,%rcx
    69a0:	48 29 d6             	sub    %rdx,%rsi
    69a3:	4c 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r8
    69ab:	48 c1 e6 05          	shl    $0x5,%rsi
    69af:	49 03 72 20          	add    0x20(%r10),%rsi
    69b3:	4c 8d 14 c0          	lea    (%rax,%rax,8),%r10
    69b7:	4d 89 c3             	mov    %r8,%r11
    69ba:	4d 89 c4             	mov    %r8,%r12
    69bd:	49 89 f7             	mov    %rsi,%r15
    69c0:	49 c1 e2 03          	shl    $0x3,%r10
    69c4:	49 89 f5             	mov    %rsi,%r13
    69c7:	49 89 d8             	mov    %rbx,%r8
    69ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    69d0:	49 8b 6d 38          	mov    0x38(%r13),%rbp
    69d4:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    69d9:	4c 89 ff             	mov    %r15,%rdi
    69dc:	4c 89 e6             	mov    %r12,%rsi
    69df:	48 8b 9c 05 70 01 00 00 	mov    0x170(%rbp,%rax,1),%rbx
    69e7:	eb 1b                	jmp    6a04 <barriered_work+0x144>
    69e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    69f0:	48 83 c6 48          	add    $0x48,%rsi
    69f4:	48 81 c7 e0 00 00 00 	add    $0xe0,%rdi
    69fb:	49 39 f2             	cmp    %rsi,%r10
    69fe:	0f 84 b4 00 00 00    	je     6ab8 <barriered_work+0x1f8>
              if (kind == MAILBOX_FRIEND) {
    6a04:	83 7c 33 38 01       	cmpl   $0x1,0x38(%rbx,%rsi,1)
    6a09:	75 e5                	jne    69f0 <barriered_work+0x130>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6a0b:	4c 8b 77 38          	mov    0x38(%rdi),%r14
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6a0f:	45 85 c9             	test   %r9d,%r9d
    6a12:	7e dc                	jle    69f0 <barriered_work+0x130>
    6a14:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    6a19:	49 81 c6 70 01 00 00 	add    $0x170,%r14
    6a20:	31 c9                	xor    %ecx,%ecx
    6a22:	48 89 7c 24 10       	mov    %rdi,0x10(%rsp)
    6a27:	eb 4e                	jmp    6a77 <barriered_work+0x1b7>
    6a29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6a30:	48 63 d2             	movslq %edx,%rdx
    6a33:	48 c1 e2 09          	shl    $0x9,%rdx
    6a37:	48 8b 84 15 70 01 00 00 	mov    0x170(%rbp,%rdx,1),%rax
    6a3f:	48 01 f0             	add    %rsi,%rax
    return mailbox->lower;
    6a42:	48 8b 10             	mov    (%rax),%rdx
                      if (dest->messages_count != 0) { 
    6a45:	48 83 ba 80 00 00 00 00 	cmpq   $0x0,0x80(%rdx)
    6a4d:	75 1c                	jne    6a6b <barriered_work+0x1ab>
    return mailbox->higher;
    6a4f:	f3 0f 7e 40 08       	movq   0x8(%rax),%xmm0
    6a54:	66 48 0f 6e d2       	movq   %rdx,%xmm2
    mailbox->lower = data;
    6a59:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    6a5d:	66 0f 6c c2          	punpcklqdq %xmm2,%xmm0
    6a61:	48 89 10             	mov    %rdx,(%rax)
    6a64:	0f 11 07             	movups %xmm0,(%rdi)
    mailbox->higher = data;
    6a67:	48 89 58 08          	mov    %rbx,0x8(%rax)
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6a6b:	49 81 c6 00 02 00 00 	add    $0x200,%r14
    6a72:	41 39 c9             	cmp    %ecx,%r9d
    6a75:	74 1c                	je     6a93 <barriered_work+0x1d3>
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6a77:	49 8b 3e             	mov    (%r14),%rdi
                    int next_task = abs((nn + 1) % (data->thread_count));
    6a7a:	83 c1 01             	add    $0x1,%ecx
    6a7d:	89 c8                	mov    %ecx,%eax
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6a7f:	4c 01 df             	add    %r11,%rdi
                    int next_task = abs((nn + 1) % (data->thread_count));
    6a82:	99                   	cltd
    6a83:	41 f7 f9             	idiv   %r9d
    return mailbox->lower;
    6a86:	48 8b 1f             	mov    (%rdi),%rbx
                      if (source2->messages_count != 0) { 
    6a89:	48 83 bb 80 00 00 00 00 	cmpq   $0x0,0x80(%rbx)
    6a91:	74 9d                	je     6a30 <barriered_work+0x170>
    6a93:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6a98:	48 83 c6 48          	add    $0x48,%rsi
    6a9c:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    6aa1:	48 81 c7 e0 00 00 00 	add    $0xe0,%rdi
    6aa8:	49 39 f2             	cmp    %rsi,%r10
    6aab:	0f 85 53 ff ff ff    	jne    6a04 <barriered_work+0x144>
    6ab1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6ab8:	49 83 c3 48          	add    $0x48,%r11
    6abc:	49 81 c5 e0 00 00 00 	add    $0xe0,%r13
    6ac3:	4d 39 da             	cmp    %r11,%r10
    6ac6:	0f 85 04 ff ff ff    	jne    69d0 <barriered_work+0x110>
    6acc:	8b 6c 24 20          	mov    0x20(%rsp),%ebp
    6ad0:	4c 89 c3             	mov    %r8,%rbx
      receive(data);
    6ad3:	48 89 df             	mov    %rbx,%rdi
    6ad6:	e8 15 fa ff ff       	call   64f0 <receive>
      asm volatile ("sfence" ::: "memory");
    6adb:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6ade:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6ae5:	31 ff                	xor    %edi,%edi
    6ae7:	48 c1 e6 05          	shl    $0x5,%rsi
    6aeb:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6af2:	e8 59 b8 ff ff       	call   2350 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6af7:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    6afe:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    int modcount = ++data->thread->protected_state->modcount;
    6b05:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6b09:	8b 4a 10             	mov    0x10(%rdx),%ecx
    6b0c:	44 8d 61 01          	lea    0x1(%rcx),%r12d
    6b10:	44 89 62 10          	mov    %r12d,0x10(%rdx)
    while (data->scheduled == 1) {
    6b14:	75 5c                	jne    6b72 <barriered_work+0x2b2>
    6b16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6b20:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    6b27:	48 8b 40 18          	mov    0x18(%rax),%rax
    6b2b:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
      data->n++;
    6b2f:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6b37:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6b3b:	48 c1 e7 09          	shl    $0x9,%rdi
    6b3f:	48 03 78 38          	add    0x38(%rax),%rdi
    6b43:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      asm volatile ("sfence" ::: "memory");
    6b49:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6b4c:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    if (modcount != data->thread->protected_state->modcount) {
    6b53:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    while (data->scheduled == 1) {
    6b5a:	74 c4                	je     6b20 <barriered_work+0x260>
    if (modcount != data->thread->protected_state->modcount) {
    6b5c:	48 8b 40 48          	mov    0x48(%rax),%rax
    6b60:	44 3b 60 10          	cmp    0x10(%rax),%r12d
    6b64:	74 0c                	je     6b72 <barriered_work+0x2b2>
    6b66:	48 8d 3d d9 16 00 00 	lea    0x16d9(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6b6d:	e8 be b7 ff ff       	call   2330 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6b72:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6b79:	31 ff                	xor    %edi,%edi
    6b7b:	48 c1 e6 05          	shl    $0x5,%rsi
    6b7f:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6b86:	48 83 c6 10          	add    $0x10,%rsi
    6b8a:	e8 c1 b7 ff ff       	call   2350 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6b8f:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6b96:	48 83 c0 01          	add    $0x1,%rax
    6b9a:	48 99                	cqto
    6b9c:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
  if (t == data->thread_count - 1) {
    6ba3:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6ba9:	83 e8 01             	sub    $0x1,%eax
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6bac:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
  if (t == data->thread_count - 1) {
    6bb3:	39 e8                	cmp    %ebp,%eax
    6bb5:	0f 85 62 fd ff ff    	jne    691d <barriered_work+0x5d>
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6bbb:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    6bc2:	85 d2                	test   %edx,%edx
    6bc4:	0f 8e 53 fd ff ff    	jle    691d <barriered_work+0x5d>
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6bca:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    6bd1:	48 c1 e2 09          	shl    $0x9,%rdx
    6bd5:	48 63 71 08          	movslq 0x8(%rcx),%rsi
    6bd9:	48 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rax
    6be1:	48 29 f0             	sub    %rsi,%rax
    6be4:	48 c1 e0 05          	shl    $0x5,%rax
    6be8:	48 03 41 20          	add    0x20(%rcx),%rax
    6bec:	48 8b 40 38          	mov    0x38(%rax),%rax
    6bf0:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    6bf4:	80 e6 02             	and    $0x2,%dh
    6bf7:	74 17                	je     6c10 <barriered_work+0x350>
    6bf9:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6c00:	48 05 00 02 00 00    	add    $0x200,%rax
    6c06:	48 39 c8             	cmp    %rcx,%rax
    6c09:	0f 84 0e fd ff ff    	je     691d <barriered_work+0x5d>
    6c0f:	90                   	nop
        data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    6c10:	83 80 9c 01 00 00 01 	addl   $0x1,0x19c(%rax)
    6c17:	83 80 9c 03 00 00 01 	addl   $0x1,0x39c(%rax)
      for (int tt = 0 ; tt < data->task_count ; tt++) {
    6c1e:	48 05 00 04 00 00    	add    $0x400,%rax
    6c24:	48 39 c8             	cmp    %rcx,%rax
    6c27:	75 e7                	jne    6c10 <barriered_work+0x350>
    6c29:	e9 ef fc ff ff       	jmp    691d <barriered_work+0x5d>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6c2e:	44 8b bb 40 01 00 00 	mov    0x140(%rbx),%r15d
          data->thread->have_foreign = 0;
    6c35:	41 c7 82 d8 00 00 00 00 00 00 00 	movl   $0x0,0xd8(%r10)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6c40:	45 85 ff             	test   %r15d,%r15d
    6c43:	0f 8e 11 fd ff ff    	jle    695a <barriered_work+0x9a>
              int next_task = abs((t + 1) % (data->thread_count));
    6c49:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
        int b = data->thread->real_thread_index;
    6c4f:	49 63 4a 08          	movslq 0x8(%r10),%rcx
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6c53:	89 6c 24 18          	mov    %ebp,0x18(%rsp)
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6c57:	45 31 c0             	xor    %r8d,%r8d
              int next_task = abs((t + 1) % (data->thread_count));
    6c5a:	89 44 24 10          	mov    %eax,0x10(%rsp)
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6c5e:	48 63 c5             	movslq %ebp,%rax
        int b = data->thread->real_thread_index;
    6c61:	48 89 ca             	mov    %rcx,%rdx
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6c64:	48 c1 e0 09          	shl    $0x9,%rax
    6c68:	49 89 c6             	mov    %rax,%r14
    6c6b:	48 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%rax
    6c73:	48 89 c6             	mov    %rax,%rsi
    6c76:	48 01 c8             	add    %rcx,%rax
    6c79:	48 29 ce             	sub    %rcx,%rsi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6c7c:	31 c9                	xor    %ecx,%ecx
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6c7e:	4c 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%r13
    6c86:	48 c1 e6 05          	shl    $0x5,%rsi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6c8a:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    6c8e:	48 89 d9             	mov    %rbx,%rcx
    6c91:	89 d3                	mov    %edx,%ebx
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6c93:	49 89 f4             	mov    %rsi,%r12
    6c96:	31 f6                	xor    %esi,%esi
    6c98:	eb 23                	jmp    6cbd <barriered_work+0x3fd>
    6c9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6ca0:	83 44 24 08 01       	addl   $0x1,0x8(%rsp)
    6ca5:	8b 44 24 08          	mov    0x8(%rsp),%eax
    6ca9:	49 83 c0 48          	add    $0x48,%r8
    6cad:	48 81 c6 e0 00 00 00 	add    $0xe0,%rsi
    6cb4:	44 39 f8             	cmp    %r15d,%eax
    6cb7:	0f 84 b3 01 00 00    	je     6e70 <barriered_work+0x5b0>
              if (y == b) { continue; }
    6cbd:	8b 44 24 08          	mov    0x8(%rsp),%eax
    6cc1:	39 c3                	cmp    %eax,%ebx
    6cc3:	74 db                	je     6ca0 <barriered_work+0x3e0>
                  if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    6cc5:	49 8b 52 20          	mov    0x20(%r10),%rdx
    6cc9:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    6cce:	4a 8d 04 37          	lea    (%rdi,%r14,1),%rax
    6cd2:	44 8b 88 98 01 00 00 	mov    0x198(%rax),%r9d
    6cd9:	45 85 c9             	test   %r9d,%r9d
    6cdc:	75 c2                	jne    6ca0 <barriered_work+0x3e0>
    6cde:	4e 8b 4c 22 38       	mov    0x38(%rdx,%r12,1),%r9
    6ce3:	4b 8d 14 31          	lea    (%r9,%r14,1),%rdx
    6ce7:	44 8b 9a 98 01 00 00 	mov    0x198(%rdx),%r11d
    6cee:	45 85 db             	test   %r11d,%r11d
    6cf1:	75 ad                	jne    6ca0 <barriered_work+0x3e0>
    6cf3:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    6cfa:	42 83 7c 02 38 02    	cmpl   $0x2,0x38(%rdx,%r8,1)
    6d00:	75 9e                	jne    6ca0 <barriered_work+0x3e0>
    6d02:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6d09:	42 83 7c 28 38 02    	cmpl   $0x2,0x38(%rax,%r13,1)
    6d0f:	75 8f                	jne    6ca0 <barriered_work+0x3e0>
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6d11:	48 63 44 24 10       	movslq 0x10(%rsp),%rax
    6d16:	85 c0                	test   %eax,%eax
    6d18:	7e 86                	jle    6ca0 <barriered_work+0x3e0>
    6d1a:	48 89 c2             	mov    %rax,%rdx
    6d1d:	89 5c 24 30          	mov    %ebx,0x30(%rsp)
    6d21:	b8 70 01 00 00       	mov    $0x170,%eax
    6d26:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    6d2b:	48 c1 e2 09          	shl    $0x9,%rdx
    6d2f:	4c 89 54 24 20       	mov    %r10,0x20(%rsp)
    6d34:	44 8b 54 24 10       	mov    0x10(%rsp),%r10d
    6d39:	48 8d aa 98 01 00 00 	lea    0x198(%rdx),%rbp
    6d40:	4c 89 74 24 28       	mov    %r14,0x28(%rsp)
    6d45:	49 89 d6             	mov    %rdx,%r14
    6d48:	48 89 74 24 38       	mov    %rsi,0x38(%rsp)
    6d4d:	48 89 c6             	mov    %rax,%rsi
                      int next_task = abs((nn + 1) % data->thread_count);
    6d50:	41 83 c3 01          	add    $0x1,%r11d
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6d54:	49 8b 1c 31          	mov    (%r9,%rsi,1),%rbx
                      int next_task = abs((nn + 1) % data->thread_count);
    6d58:	44 89 d8             	mov    %r11d,%eax
    6d5b:	99                   	cltd
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6d5c:	4c 01 c3             	add    %r8,%rbx
                      int next_task = abs((nn + 1) % data->thread_count);
    6d5f:	41 f7 fa             	idiv   %r10d
    return mailbox->lower;
    6d62:	f3 0f 6f 0b          	movdqu (%rbx),%xmm1
    6d66:	66 0f c6 c9 01       	shufpd $0x1,%xmm1,%xmm1
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6d6b:	48 63 d2             	movslq %edx,%rdx
    6d6e:	48 c1 e2 09          	shl    $0x9,%rdx
    6d72:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    6d7a:	4c 01 e8             	add    %r13,%rax
    return mailbox->higher;
    6d7d:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    6d81:	0f 11 08             	movups %xmm1,(%rax)
    6d84:	0f 12 d8             	movhlps %xmm0,%xmm3
    6d87:	66 49 0f 7e c7       	movq   %xmm0,%r15
    return mailbox->lower;
    6d8c:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
    mailbox->lower = data;
    6d91:	0f 11 03             	movups %xmm0,(%rbx)
    6d94:	66 48 0f 7e da       	movq   %xmm3,%rdx
    6d99:	bb 98 01 00 00       	mov    $0x198,%ebx
    6d9e:	66 90                	xchg   %ax,%ax
                        data->thread->all_threads[l2].tasks[jj].swap = 1;
    6da0:	41 c7 04 19 01 00 00 00 	movl   $0x1,(%r9,%rbx,1)
                        data->thread->all_threads[t2].tasks[jj].swap = 1;
    6da8:	c7 04 1f 01 00 00 00 	movl   $0x1,(%rdi,%rbx,1)
                      for (int jj = 0 ; jj < data->thread_count; jj++) {
    6daf:	48 81 c3 00 02 00 00 	add    $0x200,%rbx
    6db6:	48 39 dd             	cmp    %rbx,%rbp
    6db9:	75 e5                	jne    6da0 <barriered_work+0x4e0>
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6dbb:	48 8b 1c 37          	mov    (%rdi,%rsi,1),%rbx
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6dbf:	48 8b 00             	mov    (%rax),%rax
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    6dc2:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6dcd:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6dd4:	4a 8b 5c 2b 08       	mov    0x8(%rbx,%r13,1),%rbx
    6dd9:	c7 83 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rbx)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6de3:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6ded:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6df7:	45 39 da             	cmp    %r11d,%r10d
    6dfa:	0f 85 50 ff ff ff    	jne    6d50 <barriered_work+0x490>
    6e00:	4c 89 f2             	mov    %r14,%rdx
    6e03:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6e08:	8b 5c 24 30          	mov    0x30(%rsp),%ebx
    6e0c:	b8 70 01 00 00       	mov    $0x170,%eax
    6e11:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    6e16:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    6e1b:	48 8d aa 70 01 00 00 	lea    0x170(%rdx),%rbp
    6e22:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    6e27:	eb 16                	jmp    6e3f <barriered_work+0x57f>
    6e29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6e30:	48 05 00 02 00 00    	add    $0x200,%rax
    6e36:	48 39 e8             	cmp    %rbp,%rax
    6e39:	0f 84 61 fe ff ff    	je     6ca0 <barriered_work+0x3e0>
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6e3f:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    6e43:	4d 8b 1c 01          	mov    (%r9,%rax,1),%r11
    6e47:	4a 8b 14 2a          	mov    (%rdx,%r13,1),%rdx
    6e4b:	4b 39 14 03          	cmp    %rdx,(%r11,%r8,1)
    6e4f:	75 df                	jne    6e30 <barriered_work+0x570>
    6e51:	bf 01 00 00 00       	mov    $0x1,%edi
    6e56:	48 8d 35 ce 13 00 00 	lea    0x13ce(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6e5d:	31 c0                	xor    %eax,%eax
    6e5f:	e8 4c b6 ff ff       	call   24b0 <__printf_chk@plt>
                          exit(1);
    6e64:	bf 01 00 00 00       	mov    $0x1,%edi
    6e69:	e8 a2 b6 ff ff       	call   2510 <exit@plt>
    6e6e:	66 90                	xchg   %ax,%ax
    6e70:	8b 6c 24 18          	mov    0x18(%rsp),%ebp
    6e74:	48 89 cb             	mov    %rcx,%rbx
    6e77:	e9 de fa ff ff       	jmp    695a <barriered_work+0x9a>
    6e7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006e80 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6e80:	f3 0f 1e fa          	endbr64
    6e84:	53                   	push   %rbx
    6e85:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6e88:	e8 73 f2 ff ff       	call   6100 <barriered_work_ingest>
  barriered_work(data);
    6e8d:	48 89 df             	mov    %rbx,%rdi
}
    6e90:	5b                   	pop    %rbx
  barriered_work(data);
    6e91:	e9 2a fa ff ff       	jmp    68c0 <barriered_work>
    6e96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006ea0 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6ea0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6ea4:	85 f6                	test   %esi,%esi
    6ea6:	74 10                	je     6eb8 <mailboxkind+0x18>
  return NULL;
    6ea8:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    6eaa:	83 fe 01             	cmp    $0x1,%esi
    6ead:	74 01                	je     6eb0 <mailboxkind+0x10>
}
    6eaf:	c3                   	ret
    return mailbox->higher;
    6eb0:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    6eb4:	c3                   	ret
    6eb5:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
    6eb8:	48 8b 07             	mov    (%rdi),%rax
    6ebb:	c3                   	ret
    6ebc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006ec0 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    6ec0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6ec4:	85 d2                	test   %edx,%edx
    6ec6:	75 08                	jne    6ed0 <setmailboxkind+0x10>
    mailbox->lower = data;
    6ec8:	48 89 37             	mov    %rsi,(%rdi)
}
    6ecb:	31 c0                	xor    %eax,%eax
    6ecd:	c3                   	ret
    6ece:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    6ed0:	83 fa 01             	cmp    $0x1,%edx
    6ed3:	74 13                	je     6ee8 <setmailboxkind+0x28>
  if (kind == 2) {
    6ed5:	83 fa 02             	cmp    $0x2,%edx
    6ed8:	75 16                	jne    6ef0 <setmailboxkind+0x30>
    mailbox->pending_lower = data;
    6eda:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
    6ede:	31 c0                	xor    %eax,%eax
    6ee0:	c3                   	ret
    6ee1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    mailbox->higher = data;
    6ee8:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    6eec:	31 c0                	xor    %eax,%eax
    6eee:	c3                   	ret
    6eef:	90                   	nop
  if (kind == 3) {
    6ef0:	83 fa 03             	cmp    $0x3,%edx
    6ef3:	75 d6                	jne    6ecb <setmailboxkind+0xb>
    mailbox->pending_higher = data;
    6ef5:	48 89 77 18          	mov    %rsi,0x18(%rdi)
}
    6ef9:	31 c0                	xor    %eax,%eax
    6efb:	c3                   	ret
    6efc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006f00 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6f00:	f3 0f 1e fa          	endbr64
}
    6f04:	31 c0                	xor    %eax,%eax
    6f06:	c3                   	ret
    6f07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006f10 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6f10:	f3 0f 1e fa          	endbr64
    6f14:	31 c0                	xor    %eax,%eax
    6f16:	c3                   	ret
    6f17:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006f20 <after>:
int after(struct timespec left, struct timespec right) {
    6f20:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6f24:	31 c0                	xor    %eax,%eax
    6f26:	48 39 d7             	cmp    %rdx,%rdi
    6f29:	7e 08                	jle    6f33 <after+0x13>
    6f2b:	31 c0                	xor    %eax,%eax
    6f2d:	48 39 ce             	cmp    %rcx,%rsi
    6f30:	0f 9f c0             	setg   %al
}
    6f33:	c3                   	ret
    6f34:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6f3f:	90                   	nop

0000000000006f40 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6f40:	f3 0f 1e fa          	endbr64
    6f44:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6f49:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    6f4e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f50:	48 39 d7             	cmp    %rdx,%rdi
    6f53:	7f 18                	jg     6f6d <within+0x2d>
    6f55:	4d 39 d8             	cmp    %r11,%r8
    6f58:	0f 9e c2             	setle  %dl
    6f5b:	48 39 ce             	cmp    %rcx,%rsi
    6f5e:	0f 9e c0             	setle  %al
    6f61:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6f63:	31 c0                	xor    %eax,%eax
    6f65:	4d 39 d1             	cmp    %r10,%r9
    6f68:	0f 9e c0             	setle  %al
    6f6b:	21 d0                	and    %edx,%eax
}
    6f6d:	c3                   	ret
    6f6e:	66 90                	xchg   %ax,%ax

0000000000006f70 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6f70:	f3 0f 1e fa          	endbr64
    6f74:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6f79:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6f7e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6f83:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6f88:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6f8d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6f92:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6f97:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6f9c:	48 39 fe             	cmp    %rdi,%rsi
    6f9f:	7d 2f                	jge    6fd0 <overlap+0x60>
    6fa1:	48 39 ca             	cmp    %rcx,%rdx
    6fa4:	7d 62                	jge    7008 <overlap+0x98>
    6fa6:	4d 39 da             	cmp    %r11,%r10
    6fa9:	7d 0e                	jge    6fb9 <overlap+0x49>
    return 1;
    6fab:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6fb0:	4d 39 c1             	cmp    %r8,%r9
    6fb3:	0f 8c 7f 00 00 00    	jl     7038 <overlap+0xc8>
  return 0;
    6fb9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6fbb:	4d 39 c1             	cmp    %r8,%r9
    6fbe:	7f 4c                	jg     700c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6fc0:	31 c0                	xor    %eax,%eax
    6fc2:	4d 39 da             	cmp    %r11,%r10
    6fc5:	0f 9e c0             	setle  %al
    6fc8:	c3                   	ret
    6fc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6fd0:	7e 4e                	jle    7020 <overlap+0xb0>
    6fd2:	48 39 ca             	cmp    %rcx,%rdx
    6fd5:	7f 39                	jg     7010 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6fd7:	75 31                	jne    700a <overlap+0x9a>
    6fd9:	4d 39 c1             	cmp    %r8,%r9
    6fdc:	7c 2c                	jl     700a <overlap+0x9a>
    return 1;
    6fde:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6fe3:	4d 39 da             	cmp    %r11,%r10
    6fe6:	7d 24                	jge    700c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6fe8:	48 39 ca             	cmp    %rcx,%rdx
    6feb:	0f 94 c2             	sete   %dl
    6fee:	48 39 fe             	cmp    %rdi,%rsi
    6ff1:	0f 94 c0             	sete   %al
    6ff4:	21 c2                	and    %eax,%edx
    6ff6:	31 c0                	xor    %eax,%eax
    6ff8:	4d 39 c1             	cmp    %r8,%r9
    6ffb:	0f 94 c0             	sete   %al
    6ffe:	21 d0                	and    %edx,%eax
    7000:	c3                   	ret
    7001:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7008:	74 af                	je     6fb9 <overlap+0x49>
  return 0;
    700a:	31 c0                	xor    %eax,%eax
}
    700c:	c3                   	ret
    700d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    7010:	4d 39 da             	cmp    %r11,%r10
    7013:	7e c4                	jle    6fd9 <overlap+0x69>
    return 1;
    7015:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    701a:	4d 39 c1             	cmp    %r8,%r9
    701d:	7e ba                	jle    6fd9 <overlap+0x69>
    701f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7020:	48 39 ca             	cmp    %rcx,%rdx
    7023:	7c 94                	jl     6fb9 <overlap+0x49>
    7025:	4d 39 c1             	cmp    %r8,%r9
    7028:	7d b4                	jge    6fde <overlap+0x6e>
    702a:	48 39 ca             	cmp    %rcx,%rdx
    702d:	74 91                	je     6fc0 <overlap+0x50>
    702f:	eb d9                	jmp    700a <overlap+0x9a>
    7031:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7038:	c3                   	ret
    7039:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007040 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    7040:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    7044:	85 f6                	test   %esi,%esi
    7046:	0f 8e 44 03 00 00    	jle    7390 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    704c:	41 57                	push   %r15
    704e:	41 89 f7             	mov    %esi,%r15d
    7051:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    7053:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    7056:	41 55                	push   %r13
    7058:	41 54                	push   %r12
    705a:	55                   	push   %rbp
    705b:	53                   	push   %rbx
    705c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    7060:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    7064:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    7069:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    706e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    7071:	45 39 e6             	cmp    %r12d,%r14d
    7074:	0f 84 4e 02 00 00    	je     72c8 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    707a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    707f:	8b 50 08             	mov    0x8(%rax),%edx
    7082:	85 d2                	test   %edx,%edx
    7084:	0f 8e 3e 02 00 00    	jle    72c8 <verify+0x288>
    708a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    708f:	31 c9                	xor    %ecx,%ecx
    7091:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    7096:	31 c0                	xor    %eax,%eax
    7098:	44 89 f2             	mov    %r14d,%edx
    709b:	bf 01 00 00 00       	mov    $0x1,%edi
    70a0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    70a5:	48 8d 35 aa 11 00 00 	lea    0x11aa(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    70ac:	e8 ff b3 ff ff       	call   24b0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    70b1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    70b6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    70bb:	8b 40 08             	mov    0x8(%rax),%eax
    70be:	85 c0                	test   %eax,%eax
    70c0:	0f 8e e6 01 00 00    	jle    72ac <verify+0x26c>
    70c6:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    70c9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    70ce:	31 db                	xor    %ebx,%ebx
    70d0:	48 c1 e0 09          	shl    $0x9,%rax
    70d4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    70d9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    70de:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    70e3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    70e8:	4c 8b 20             	mov    (%rax),%r12
    70eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    70f0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    70f5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    70fa:	49 89 de             	mov    %rbx,%r14
    70fd:	48 8d 35 67 11 00 00 	lea    0x1167(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    7104:	49 c1 e6 09          	shl    $0x9,%r14
    7108:	bf 01 00 00 00       	mov    $0x1,%edi
    710d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    7111:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    7119:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    711e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    7126:	31 c0                	xor    %eax,%eax
    7128:	e8 83 b3 ff ff       	call   24b0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    712d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7132:	4c 8b 20             	mov    (%rax),%r12
    7135:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    713e:	0f 8e 47 01 00 00    	jle    728b <verify+0x24b>
    7144:	4c 03 75 00          	add    0x0(%rbp),%r14
    7148:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    714d:	ba 01 00 00 00       	mov    $0x1,%edx
    7152:	4d 89 f5             	mov    %r14,%r13
    7155:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    715c:	4d 85 f6             	test   %r14,%r14
    715f:	0f 8e 21 01 00 00    	jle    7286 <verify+0x246>
    7165:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    7168:	48 89 d5             	mov    %rdx,%rbp
    716b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7170:	31 db                	xor    %ebx,%ebx
    7172:	4d 89 f2             	mov    %r14,%r10
    7175:	48 c1 e5 05          	shl    $0x5,%rbp
    7179:	48 83 ed 20          	sub    $0x20,%rbp
    717d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    7181:	49 89 ee             	mov    %rbp,%r14
    7184:	48 89 dd             	mov    %rbx,%rbp
    7187:	48 89 d3             	mov    %rdx,%rbx
    718a:	eb 31                	jmp    71bd <verify+0x17d>
    718c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    7190:	4c 39 c2             	cmp    %r8,%rdx
    7193:	0f 8d 57 01 00 00    	jge    72f0 <verify+0x2b0>
    7199:	4c 39 df             	cmp    %r11,%rdi
    719c:	7e 05                	jle    71a3 <verify+0x163>
    719e:	49 39 c1             	cmp    %rax,%r9
    71a1:	7c 75                	jl     7218 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71a3:	4c 39 df             	cmp    %r11,%rdi
    71a6:	0f 8d ab 01 00 00    	jge    7357 <verify+0x317>
    71ac:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    71b0:	48 83 c5 01          	add    $0x1,%rbp
    71b4:	49 39 ea             	cmp    %rbp,%r10
    71b7:	0f 8e a9 00 00 00    	jle    7266 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    71bd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    71c4:	48 89 e8             	mov    %rbp,%rax
    71c7:	48 c1 e0 05          	shl    $0x5,%rax
    71cb:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    71d2:	4c 01 f2             	add    %r14,%rdx
    71d5:	48 8b 08             	mov    (%rax),%rcx
    71d8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    71dc:	48 8b 32             	mov    (%rdx),%rsi
    71df:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    71e3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    71e7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    71eb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    71ef:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    71f3:	48 39 f1             	cmp    %rsi,%rcx
    71f6:	7c 98                	jl     7190 <verify+0x150>
    71f8:	0f 8e 42 01 00 00    	jle    7340 <verify+0x300>
    71fe:	4c 39 c2             	cmp    %r8,%rdx
    7201:	0f 8f f9 00 00 00    	jg     7300 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7207:	75 a7                	jne    71b0 <verify+0x170>
    7209:	4c 39 df             	cmp    %r11,%rdi
    720c:	7f a2                	jg     71b0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    720e:	49 39 c1             	cmp    %rax,%r9
    7211:	7c 9d                	jl     71b0 <verify+0x170>
    7213:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7218:	49 89 c1             	mov    %rax,%r9
    721b:	48 89 f9             	mov    %rdi,%rcx
    721e:	48 89 f2             	mov    %rsi,%rdx
    7221:	bf 01 00 00 00       	mov    $0x1,%edi
    7226:	48 8d 35 0b 14 00 00 	lea    0x140b(%rip),%rsi        # 8638 <_IO_stdin_used+0x638>
    722d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    722f:	48 83 c5 01          	add    $0x1,%rbp
    7233:	e8 78 b2 ff ff       	call   24b0 <__printf_chk@plt>
    7238:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    723d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    7242:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7245:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    724a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7251:	4c 8b 20             	mov    (%rax),%r12
    7254:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7259:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    725d:	49 39 ea             	cmp    %rbp,%r10
    7260:	0f 8f 57 ff ff ff    	jg     71bd <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7266:	48 89 da             	mov    %rbx,%rdx
    7269:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7270:	7d 14                	jge    7286 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7272:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7279:	48 83 c2 01          	add    $0x1,%rdx
    727d:	4d 85 f6             	test   %r14,%r14
    7280:	0f 8f e2 fe ff ff    	jg     7168 <verify+0x128>
    7286:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    728b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7290:	48 83 c3 01          	add    $0x1,%rbx
    7294:	39 58 08             	cmp    %ebx,0x8(%rax)
    7297:	0f 8f 53 fe ff ff    	jg     70f0 <verify+0xb0>
    729d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    72a2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    72a7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    72ac:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    72b1:	48 83 c1 01          	add    $0x1,%rcx
    72b5:	39 48 08             	cmp    %ecx,0x8(%rax)
    72b8:	0f 8f d8 fd ff ff    	jg     7096 <verify+0x56>
    72be:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    72c3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    72c8:	48 81 44 24 10 e0 00 00 00 	addq   $0xe0,0x10(%rsp)
    72d1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    72d6:	41 39 c7             	cmp    %eax,%r15d
    72d9:	0f 84 86 00 00 00    	je     7365 <verify+0x325>
    72df:	41 89 c4             	mov    %eax,%r12d
    72e2:	e9 8a fd ff ff       	jmp    7071 <verify+0x31>
    72e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    72f0:	0f 85 ba fe ff ff    	jne    71b0 <verify+0x170>
    72f6:	e9 a8 fe ff ff       	jmp    71a3 <verify+0x163>
    72fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7300:	49 39 c1             	cmp    %rax,%r9
    7303:	7e 09                	jle    730e <verify+0x2ce>
    7305:	4c 39 df             	cmp    %r11,%rdi
    7308:	0f 8c 0a ff ff ff    	jl     7218 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    730e:	4c 39 df             	cmp    %r11,%rdi
    7311:	0f 8f 99 fe ff ff    	jg     71b0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7317:	49 39 c1             	cmp    %rax,%r9
    731a:	0f 8d f8 fe ff ff    	jge    7218 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7320:	48 39 f1             	cmp    %rsi,%rcx
    7323:	0f 85 87 fe ff ff    	jne    71b0 <verify+0x170>
    7329:	4c 39 c2             	cmp    %r8,%rdx
    732c:	0f 85 7e fe ff ff    	jne    71b0 <verify+0x170>
    7332:	4c 39 df             	cmp    %r11,%rdi
    7335:	0f 84 dd fe ff ff    	je     7218 <verify+0x1d8>
    733b:	e9 70 fe ff ff       	jmp    71b0 <verify+0x170>
    7340:	4c 39 c2             	cmp    %r8,%rdx
    7343:	0f 8c 5a fe ff ff    	jl     71a3 <verify+0x163>
    7349:	4c 39 df             	cmp    %r11,%rdi
    734c:	7e c9                	jle    7317 <verify+0x2d7>
    734e:	4c 39 c2             	cmp    %r8,%rdx
    7351:	0f 85 59 fe ff ff    	jne    71b0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7357:	49 39 c1             	cmp    %rax,%r9
    735a:	0f 8f 50 fe ff ff    	jg     71b0 <verify+0x170>
    7360:	e9 b3 fe ff ff       	jmp    7218 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    7365:	48 81 44 24 18 e0 00 00 00 	addq   $0xe0,0x18(%rsp)
    736e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7372:	45 39 e6             	cmp    %r12d,%r14d
    7375:	74 08                	je     737f <verify+0x33f>
    7377:	41 89 c6             	mov    %eax,%r14d
    737a:	e9 ea fc ff ff       	jmp    7069 <verify+0x29>
}
    737f:	48 83 c4 58          	add    $0x58,%rsp
    7383:	31 c0                	xor    %eax,%eax
    7385:	5b                   	pop    %rbx
    7386:	5d                   	pop    %rbp
    7387:	41 5c                	pop    %r12
    7389:	41 5d                	pop    %r13
    738b:	41 5e                	pop    %r14
    738d:	41 5f                	pop    %r15
    738f:	c3                   	ret
    7390:	31 c0                	xor    %eax,%eax
    7392:	c3                   	ret

Disassembly of section .fini:

0000000000007394 <_fini>:
    7394:	f3 0f 1e fa          	endbr64
    7398:	48 83 ec 08          	sub    $0x8,%rsp
    739c:	48 83 c4 08          	add    $0x8,%rsp
    73a0:	c3                   	ret
