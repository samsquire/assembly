
multibarrier-topo:     file format elf64-x86-64


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
    2676:	48 8d 3d 1b 60 00 00 	lea    0x601b(%rip),%rdi        # 8698 <_IO_stdin_used+0x698>
    267d:	41 56                	push   %r14
    267f:	41 55                	push   %r13
    2681:	41 54                	push   %r12
    2683:	55                   	push   %rbp
    2684:	48 8d 2d 0b 5d 00 00 	lea    0x5d0b(%rip),%rbp        # 8396 <_IO_stdin_used+0x396>
    268b:	53                   	push   %rbx
    268c:	48 81 ec 28 01 00 00 	sub    $0x128,%rsp
    2693:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    269c:	48 89 84 24 18 01 00 00 	mov    %rax,0x118(%rsp)
    26a4:	48 8d 05 65 1f 00 00 	lea    0x1f65(%rip),%rax        # 4610 <barriered_reset>
    26ab:	66 48 0f 6e f0       	movq   %rax,%xmm6
    26b0:	0f 16 35 a1 85 00 00 	movhps 0x85a1(%rip),%xmm6        # ac58 <__do_global_dtors_aux_fini_array_entry+0x8>
    26b7:	0f 29 b4 24 c0 00 00 00 	movaps %xmm6,0xc0(%rsp)
    26bf:	e8 6c fc ff ff       	call   2330 <puts@plt>
    26c4:	bf 0a 00 00 00       	mov    $0xa,%edi
    26c9:	e8 42 fc ff ff       	call   2310 <putchar@plt>
    26ce:	ba 01 00 00 00       	mov    $0x1,%edx
    26d3:	48 8d 35 b4 5b 00 00 	lea    0x5bb4(%rip),%rsi        # 828e <_IO_stdin_used+0x28e>
    26da:	31 c0                	xor    %eax,%eax
    26dc:	bf 01 00 00 00       	mov    $0x1,%edi
    26e1:	e8 ca fd ff ff       	call   24b0 <__printf_chk@plt>
    26e6:	ba 06 00 00 00       	mov    $0x6,%edx
    26eb:	48 8d 35 ac 5b 00 00 	lea    0x5bac(%rip),%rsi        # 829e <_IO_stdin_used+0x29e>
    26f2:	31 c0                	xor    %eax,%eax
    26f4:	bf 01 00 00 00       	mov    $0x1,%edi
    26f9:	e8 b2 fd ff ff       	call   24b0 <__printf_chk@plt>
    26fe:	ba 03 00 00 00       	mov    $0x3,%edx
    2703:	48 8d 35 a9 5b 00 00 	lea    0x5ba9(%rip),%rsi        # 82b3 <_IO_stdin_used+0x2b3>
    270a:	31 c0                	xor    %eax,%eax
    270c:	bf 01 00 00 00       	mov    $0x1,%edi
    2711:	e8 9a fd ff ff       	call   24b0 <__printf_chk@plt>
    2716:	ba 02 00 00 00       	mov    $0x2,%edx
    271b:	48 8d 35 a1 5b 00 00 	lea    0x5ba1(%rip),%rsi        # 82c3 <_IO_stdin_used+0x2c3>
    2722:	31 c0                	xor    %eax,%eax
    2724:	bf 01 00 00 00       	mov    $0x1,%edi
    2729:	e8 82 fd ff ff       	call   24b0 <__printf_chk@plt>
    272e:	48 8d 3d a4 5b 00 00 	lea    0x5ba4(%rip),%rdi        # 82d9 <_IO_stdin_used+0x2d9>
    2735:	e8 f6 fb ff ff       	call   2330 <puts@plt>
    273a:	ba 02 00 00 00       	mov    $0x2,%edx
    273f:	48 8d 35 af 5b 00 00 	lea    0x5baf(%rip),%rsi        # 82f5 <_IO_stdin_used+0x2f5>
    2746:	31 c0                	xor    %eax,%eax
    2748:	bf 01 00 00 00       	mov    $0x1,%edi
    274d:	e8 5e fd ff ff       	call   24b0 <__printf_chk@plt>
    2752:	ba 0a 00 00 00       	mov    $0xa,%edx
    2757:	48 8d 35 b1 5b 00 00 	lea    0x5bb1(%rip),%rsi        # 830f <_IO_stdin_used+0x30f>
    275e:	31 c0                	xor    %eax,%eax
    2760:	bf 01 00 00 00       	mov    $0x1,%edi
    2765:	e8 46 fd ff ff       	call   24b0 <__printf_chk@plt>
    276a:	ba 01 00 00 00       	mov    $0x1,%edx
    276f:	48 8d 35 ad 5b 00 00 	lea    0x5bad(%rip),%rsi        # 8323 <_IO_stdin_used+0x323>
    2776:	31 c0                	xor    %eax,%eax
    2778:	bf 01 00 00 00       	mov    $0x1,%edi
    277d:	e8 2e fd ff ff       	call   24b0 <__printf_chk@plt>
    2782:	ba 01 00 00 00       	mov    $0x1,%edx
    2787:	48 8d 35 a6 5b 00 00 	lea    0x5ba6(%rip),%rsi        # 8334 <_IO_stdin_used+0x334>
    278e:	31 c0                	xor    %eax,%eax
    2790:	bf 01 00 00 00       	mov    $0x1,%edi
    2795:	e8 16 fd ff ff       	call   24b0 <__printf_chk@plt>
    279a:	ba 02 00 00 00       	mov    $0x2,%edx
    279f:	48 8d 35 a6 5b 00 00 	lea    0x5ba6(%rip),%rsi        # 834c <_IO_stdin_used+0x34c>
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
    27e7:	48 8d 35 7a 5b 00 00 	lea    0x5b7a(%rip),%rsi        # 8368 <_IO_stdin_used+0x368>
    27ee:	31 c0                	xor    %eax,%eax
    27f0:	bf 01 00 00 00       	mov    $0x1,%edi
    27f5:	e8 b6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27fa:	ba 05 00 00 00       	mov    $0x5,%edx
    27ff:	48 8d 35 7c 5b 00 00 	lea    0x5b7c(%rip),%rsi        # 8382 <_IO_stdin_used+0x382>
    2806:	31 c0                	xor    %eax,%eax
    2808:	bf 01 00 00 00       	mov    $0x1,%edi
    280d:	e8 9e fc ff ff       	call   24b0 <__printf_chk@plt>
    2812:	48 8d 3d dc 58 00 00 	lea    0x58dc(%rip),%rdi        # 80f5 <_IO_stdin_used+0xf5>
    2819:	e8 12 fb ff ff       	call   2330 <puts@plt>
    281e:	be 18 00 00 00       	mov    $0x18,%esi
    2823:	bf 03 00 00 00       	mov    $0x3,%edi
    2828:	e8 d3 fb ff ff       	call   2400 <calloc@plt>
    282d:	be f8 00 00 00       	mov    $0xf8,%esi
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
    2868:	48 89 84 24 d8 00 00 00 	mov    %rax,0xd8(%rsp)
    2870:	e8 8b fb ff ff       	call   2400 <calloc@plt>
    2875:	48 89 84 24 e0 00 00 00 	mov    %rax,0xe0(%rsp)
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
    28d2:	48 8d 35 cd 5a 00 00 	lea    0x5acd(%rip),%rsi        # 83a6 <_IO_stdin_used+0x3a6>
    28d9:	bf 01 00 00 00       	mov    $0x1,%edi
    28de:	31 c0                	xor    %eax,%eax
    28e0:	e8 cb fb ff ff       	call   24b0 <__printf_chk@plt>
    28e5:	ba 0c 00 00 00       	mov    $0xc,%edx
    28ea:	48 8d 35 cb 5a 00 00 	lea    0x5acb(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    28f1:	31 c0                	xor    %eax,%eax
    28f3:	bf 01 00 00 00       	mov    $0x1,%edi
    28f8:	e8 b3 fb ff ff       	call   24b0 <__printf_chk@plt>
    28fd:	be 10 00 00 00       	mov    $0x10,%esi
    2902:	bf 0c 00 00 00       	mov    $0xc,%edi
    2907:	e8 f4 fa ff ff       	call   2400 <calloc@plt>
    290c:	48 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%rsp)
    2914:	48 89 c5             	mov    %rax,%rbp
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
    294a:	49 89 c4             	mov    %rax,%r12
    294d:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    2957:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
    2961:	e8 9a fa ff ff       	call   2400 <calloc@plt>
    2966:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
    296e:	4c 39 eb             	cmp    %r13,%rbx
    2971:	75 ae                	jne    2921 <main+0x2b1>
    2973:	be 08 00 00 00       	mov    $0x8,%esi
    2978:	bf 64 00 00 00       	mov    $0x64,%edi
    297d:	31 db                	xor    %ebx,%ebx
    297f:	45 31 ff             	xor    %r15d,%r15d
    2982:	48 8b 05 97 63 00 00 	mov    0x6397(%rip),%rax        # 8d20 <_IO_stdin_used+0xd20>
    2989:	4c 8d b4 24 08 01 00 00 	lea    0x108(%rsp),%r14
    2991:	41 89 dd             	mov    %ebx,%r13d
    2994:	c7 84 24 10 01 00 00 06 00 00 00 	movl   $0x6,0x110(%rsp)
    299f:	48 89 84 24 08 01 00 00 	mov    %rax,0x108(%rsp)
    29a7:	e8 54 fa ff ff       	call   2400 <calloc@plt>
    29ac:	be 04 00 00 00       	mov    $0x4,%esi
    29b1:	bf 01 00 00 00       	mov    $0x1,%edi
    29b6:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    29be:	e8 3d fa ff ff       	call   2400 <calloc@plt>
    29c3:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    29cb:	48 89 84 24 b0 00 00 00 	mov    %rax,0xb0(%rsp)
    29d3:	c7 00 ff ff ff ff    	movl   $0xffffffff,(%rax)
    29d9:	48 8b 84 24 a0 00 00 00 	mov    0xa0(%rsp),%rax
    29e1:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
    29e9:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    29f1:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    29f9:	c7 44 24 78 00 00 00 00 	movl   $0x0,0x78(%rsp)
    2a01:	be 00 01 00 00       	mov    $0x100,%esi
    2a06:	bf 01 00 00 00       	mov    $0x1,%edi
    2a0b:	44 89 7c 24 50       	mov    %r15d,0x50(%rsp)
    2a10:	e8 eb f9 ff ff       	call   2400 <calloc@plt>
    2a15:	be 08 00 00 00       	mov    $0x8,%esi
    2a1a:	bf 64 00 00 00       	mov    $0x64,%edi
    2a1f:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a24:	e8 d7 f9 ff ff       	call   2400 <calloc@plt>
    2a29:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2a2e:	48 8b 9c 24 a8 00 00 00 	mov    0xa8(%rsp),%rbx
    2a36:	48 c7 44 24 68 00 00 00 00 	movq   $0x0,0x68(%rsp)
    2a3f:	48 89 ac 24 e8 00 00 00 	mov    %rbp,0xe8(%rsp)
    2a47:	48 89 82 88 00 00 00 	mov    %rax,0x88(%rdx)
    2a4e:	48 8b 84 24 b0 00 00 00 	mov    0xb0(%rsp),%rax
    2a56:	4a 89 14 fb          	mov    %rdx,(%rbx,%r15,8)
    2a5a:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    2a5f:	48 89 82 98 00 00 00 	mov    %rax,0x98(%rdx)
    2a66:	43 8b 04 be          	mov    (%r14,%r15,4),%eax
    2a6a:	c7 82 90 00 00 00 06 00 00 00 	movl   $0x6,0x90(%rdx)
    2a74:	89 82 a0 00 00 00    	mov    %eax,0xa0(%rdx)
    2a7a:	4c 89 f8             	mov    %r15,%rax
    2a7d:	48 c1 e0 05          	shl    $0x5,%rax
    2a81:	48 89 94 24 f0 00 00 00 	mov    %rdx,0xf0(%rsp)
    2a89:	4c 29 f8             	sub    %r15,%rax
    2a8c:	48 89 9c 24 d0 00 00 00 	mov    %rbx,0xd0(%rsp)
    2a94:	48 c1 e0 04          	shl    $0x4,%rax
    2a98:	4c 89 b4 24 f8 00 00 00 	mov    %r14,0xf8(%rsp)
    2aa0:	4d 89 fe             	mov    %r15,%r14
    2aa3:	4c 8d 0c 18          	lea    (%rax,%rbx,1),%r9
    2aa7:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2aac:	43 8d 1c 3f          	lea    (%r15,%r15,1),%ebx
    2ab0:	41 89 df             	mov    %ebx,%r15d
    2ab3:	48 c1 e0 04          	shl    $0x4,%rax
    2ab7:	48 01 e8             	add    %rbp,%rax
    2aba:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2abf:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    2ac7:	8b 54 24 50          	mov    0x50(%rsp),%edx
    2acb:	44 89 f9             	mov    %r15d,%ecx
    2ace:	bf 01 00 00 00       	mov    $0x1,%edi
    2ad3:	48 8b 9c 24 f0 00 00 00 	mov    0xf0(%rsp),%rbx
    2adb:	48 8d 35 76 5c 00 00 	lea    0x5c76(%rip),%rsi        # 8758 <_IO_stdin_used+0x758>
    2ae2:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2ae7:	49 89 81 e0 00 00 00 	mov    %rax,0xe0(%r9)
    2aee:	48 8b 84 24 b0 00 00 00 	mov    0xb0(%rsp),%rax
    2af6:	49 89 99 d8 00 00 00 	mov    %rbx,0xd8(%r9)
    2afd:	41 89 91 e8 00 00 00 	mov    %edx,0xe8(%r9)
    2b04:	49 89 81 f0 00 00 00 	mov    %rax,0xf0(%r9)
    2b0b:	31 c0                	xor    %eax,%eax
    2b0d:	e8 9e f9 ff ff       	call   24b0 <__printf_chk@plt>
    2b12:	be 08 00 00 00       	mov    $0x8,%esi
    2b17:	bf 02 00 00 00       	mov    $0x2,%edi
    2b1c:	e8 df f8 ff ff       	call   2400 <calloc@plt>
    2b21:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2b26:	be 80 00 00 00       	mov    $0x80,%esi
    2b2b:	bf 01 00 00 00       	mov    $0x1,%edi
    2b30:	48 89 c5             	mov    %rax,%rbp
    2b33:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    2b3a:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    2b3f:	4c 89 0c 18          	mov    %r9,(%rax,%rbx,1)
    2b43:	e8 b8 f8 ff ff       	call   2400 <calloc@plt>
    2b48:	45 89 f8             	mov    %r15d,%r8d
    2b4b:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2b50:	41 83 e0 01          	and    $0x1,%r8d
    2b54:	48 89 c3             	mov    %rax,%rbx
    2b57:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2b5c:	0f 84 84 0a 00 00    	je     35e6 <main+0xf76>
    2b62:	41 8d 57 ff          	lea    -0x1(%r15),%edx
    2b66:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2b6b:	48 89 d0             	mov    %rdx,%rax
    2b6e:	48 89 d1             	mov    %rdx,%rcx
    2b71:	48 c1 e0 05          	shl    $0x5,%rax
    2b75:	48 29 d0             	sub    %rdx,%rax
    2b78:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
    2b7c:	41 8d 7f 01          	lea    0x1(%r15),%edi
    2b80:	89 bc 24 80 00 00 00 	mov    %edi,0x80(%rsp)
    2b87:	48 8d 45 08          	lea    0x8(%rbp),%rax
    2b8b:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2b90:	4c 89 c8             	mov    %r9,%rax
    2b93:	48 89 45 08          	mov    %rax,0x8(%rbp)
    2b97:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    2b9f:	48 8d 35 e2 5b 00 00 	lea    0x5be2(%rip),%rsi        # 8788 <_IO_stdin_used+0x788>
    2ba6:	bf 01 00 00 00       	mov    $0x1,%edi
    2bab:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2baf:	49 89 41 48          	mov    %rax,0x48(%r9)
    2bb3:	31 c0                	xor    %eax,%eax
    2bb5:	48 89 55 00          	mov    %rdx,0x0(%rbp)
    2bb9:	44 89 fa             	mov    %r15d,%edx
    2bbc:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2bc1:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2bc5:	e8 e6 f8 ff ff       	call   24b0 <__printf_chk@plt>
    2bca:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2bce:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2bd3:	31 c0                	xor    %eax,%eax
    2bd5:	44 89 fa             	mov    %r15d,%edx
    2bd8:	48 8d 35 d9 5b 00 00 	lea    0x5bd9(%rip),%rsi        # 87b8 <_IO_stdin_used+0x7b8>
    2bdf:	bf 01 00 00 00       	mov    $0x1,%edi
    2be4:	41 89 89 b8 00 00 00 	mov    %ecx,0xb8(%r9)
    2beb:	8b 4c 24 78          	mov    0x78(%rsp),%ecx
    2bef:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2bf4:	e8 b7 f8 ff ff       	call   24b0 <__printf_chk@plt>
    2bf9:	41 83 ff 01          	cmp    $0x1,%r15d
    2bfd:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2c02:	0f 8f c1 10 00 00    	jg     3cc9 <main+0x1659>
    2c08:	48 63 44 24 78       	movslq 0x78(%rsp),%rax
    2c0d:	48 89 c7             	mov    %rax,%rdi
    2c10:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2c16:	77 12                	ja     2c2a <main+0x5ba>
    2c18:	48 c1 e8 06          	shr    $0x6,%rax
    2c1c:	ba 01 00 00 00       	mov    $0x1,%edx
    2c21:	89 f9                	mov    %edi,%ecx
    2c23:	48 d3 e2             	shl    %cl,%rdx
    2c26:	48 09 14 c3          	or     %rdx,(%rbx,%rax,8)
    2c2a:	83 44 24 78 02       	addl   $0x2,0x78(%rsp)
    2c2f:	45 89 79 08          	mov    %r15d,0x8(%r9)
    2c33:	be 10 00 00 00       	mov    $0x10,%esi
    2c38:	bf 64 00 00 00       	mov    $0x64,%edi
    2c3d:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
    2c45:	49 89 99 b0 00 00 00 	mov    %rbx,0xb0(%r9)
    2c4c:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
    2c53:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
    2c5b:	49 89 69 18          	mov    %rbp,0x18(%r9)
    2c5f:	31 ed                	xor    %ebp,%ebp
    2c61:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
    2c68:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2c6d:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
    2c74:	49 89 41 20          	mov    %rax,0x20(%r9)
    2c78:	48 8b 05 a9 60 00 00 	mov    0x60a9(%rip),%rax        # 8d28 <_IO_stdin_used+0xd28>
    2c7f:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
    2c87:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
    2c8e:	48 8b 05 9b 60 00 00 	mov    0x609b(%rip),%rax        # 8d30 <_IO_stdin_used+0xd30>
    2c95:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2c9a:	49 89 41 28          	mov    %rax,0x28(%r9)
    2c9e:	e8 5d f7 ff ff       	call   2400 <calloc@plt>
    2ca3:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2ca8:	be 10 00 00 00       	mov    $0x10,%esi
    2cad:	bf 64 00 00 00       	mov    $0x64,%edi
    2cb2:	49 89 41 68          	mov    %rax,0x68(%r9)
    2cb6:	e8 45 f7 ff ff       	call   2400 <calloc@plt>
    2cbb:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2cc0:	be 28 00 00 00       	mov    $0x28,%esi
    2cc5:	66 0f 6f 3d 23 60 00 00 	movdqa 0x6023(%rip),%xmm7        # 8cf0 <_IO_stdin_used+0xcf0>
    2ccd:	bf 64 00 00 00       	mov    $0x64,%edi
    2cd2:	49 89 41 70          	mov    %rax,0x70(%r9)
    2cd6:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
    2cde:	e8 1d f7 ff ff       	call   2400 <calloc@plt>
    2ce3:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2ce8:	bf 03 00 00 00       	mov    $0x3,%edi
    2ced:	66 0f 6f 35 fb 5f 00 00 	movdqa 0x5ffb(%rip),%xmm6        # 8cf0 <_IO_stdin_used+0xcf0>
    2cf5:	be 00 02 00 00       	mov    $0x200,%esi
    2cfa:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
    2d01:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
    2d09:	e8 f2 f6 ff ff       	call   2400 <calloc@plt>
    2d0e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2d13:	44 89 7c 24 18       	mov    %r15d,0x18(%rsp)
    2d18:	45 89 ef             	mov    %r13d,%r15d
    2d1b:	48 63 bc 24 80 00 00 00 	movslq 0x80(%rsp),%rdi
    2d23:	48 89 c2             	mov    %rax,%rdx
    2d26:	49 89 41 38          	mov    %rax,0x38(%r9)
    2d2a:	48 89 fb             	mov    %rdi,%rbx
    2d2d:	48 69 ff ab aa aa 2a 	imul   $0x2aaaaaab,%rdi,%rdi
    2d34:	4c 89 4c 24 48       	mov    %r9,0x48(%rsp)
    2d39:	89 d8                	mov    %ebx,%eax
    2d3b:	c1 f8 1f             	sar    $0x1f,%eax
    2d3e:	48 c1 ef 20          	shr    $0x20,%rdi
    2d42:	29 c7                	sub    %eax,%edi
    2d44:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2d47:	01 c0                	add    %eax,%eax
    2d49:	29 c3                	sub    %eax,%ebx
    2d4b:	89 9c 24 84 00 00 00 	mov    %ebx,0x84(%rsp)
    2d52:	48 63 c5             	movslq %ebp,%rax
    2d55:	be 00 01 00 00       	mov    $0x100,%esi
    2d5a:	bf 06 00 00 00       	mov    $0x6,%edi
    2d5f:	45 31 ed             	xor    %r13d,%r13d
    2d62:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2d67:	48 c1 e0 09          	shl    $0x9,%rax
    2d6b:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
    2d6f:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2d74:	48 8d 05 55 18 00 00 	lea    0x1855(%rip),%rax        # 45d0 <do_protected_write>
    2d7b:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
    2d82:	e8 79 f6 ff ff       	call   2400 <calloc@plt>
    2d87:	8b 74 24 58          	mov    0x58(%rsp),%esi
    2d8b:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
    2d92:	48 89 c1             	mov    %rax,%rcx
    2d95:	49 89 c4             	mov    %rax,%r12
    2d98:	85 f6                	test   %esi,%esi
    2d9a:	0f 84 85 01 00 00    	je     2f25 <main+0x8b5>
    2da0:	8b 44 24 18          	mov    0x18(%rsp),%eax
    2da4:	48 89 8c 24 88 00 00 00 	mov    %rcx,0x88(%rsp)
    2dac:	48 89 cb             	mov    %rcx,%rbx
    2daf:	45 89 ec             	mov    %r13d,%r12d
    2db2:	83 e8 01             	sub    $0x1,%eax
    2db5:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2db9:	eb 1a                	jmp    2dd5 <main+0x765>
    2dbb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    2dc0:	41 83 c4 01          	add    $0x1,%r12d
    2dc4:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    2dcb:	41 83 fc 06          	cmp    $0x6,%r12d
    2dcf:	0f 84 d0 02 00 00    	je     30a5 <main+0xa35>
    2dd5:	45 89 e5             	mov    %r12d,%r13d
    2dd8:	31 c0                	xor    %eax,%eax
    2dda:	44 89 e2             	mov    %r12d,%edx
    2ddd:	bf 01 00 00 00       	mov    $0x1,%edi
    2de2:	41 d1 fd             	sar    %r13d
    2de5:	48 8d 35 ea 55 00 00 	lea    0x55ea(%rip),%rsi        # 83d6 <_IO_stdin_used+0x3d6>
    2dec:	44 89 e9             	mov    %r13d,%ecx
    2def:	e8 bc f6 ff ff       	call   24b0 <__printf_chk@plt>
    2df4:	45 39 f5             	cmp    %r14d,%r13d
    2df7:	75 c7                	jne    2dc0 <main+0x750>
    2df9:	be 08 00 00 00       	mov    $0x8,%esi
    2dfe:	bf 01 00 00 00       	mov    $0x1,%edi
    2e03:	e8 f8 f5 ff ff       	call   2400 <calloc@plt>
    2e08:	be 08 00 00 00       	mov    $0x8,%esi
    2e0d:	bf 01 00 00 00       	mov    $0x1,%edi
    2e12:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2e17:	e8 e4 f5 ff ff       	call   2400 <calloc@plt>
    2e1c:	be 80 04 00 00       	mov    $0x480,%esi
    2e21:	bf 03 00 00 00       	mov    $0x3,%edi
    2e26:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2e2b:	e8 d0 f5 ff ff       	call   2400 <calloc@plt>
    2e30:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    2e34:	44 89 e2             	mov    %r12d,%edx
    2e37:	48 c7 83 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%rbx)
    2e42:	49 89 c5             	mov    %rax,%r13
    2e45:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    2e4b:	48 8d 35 86 59 00 00 	lea    0x5986(%rip),%rsi        # 87d8 <_IO_stdin_used+0x7d8>
    2e52:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
    2e58:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
    2e62:	44 89 a0 14 04 00 00 	mov    %r12d,0x414(%rax)
    2e69:	41 8d 47 01          	lea    0x1(%r15),%eax
    2e6d:	41 89 85 98 08 00 00 	mov    %eax,0x898(%r13)
    2e74:	49 8d 85 80 04 00 00 	lea    0x480(%r13),%rax
    2e7b:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
    2e82:	8b 44 24 70          	mov    0x70(%rsp),%eax
    2e86:	45 89 bd 18 04 00 00 	mov    %r15d,0x418(%r13)
    2e8d:	41 83 c7 02          	add    $0x2,%r15d
    2e91:	41 89 bd 8c 08 00 00 	mov    %edi,0x88c(%r13)
    2e98:	89 c1                	mov    %eax,%ecx
    2e9a:	bf 01 00 00 00       	mov    $0x1,%edi
    2e9f:	89 83 b4 00 00 00    	mov    %eax,0xb4(%rbx)
    2ea5:	31 c0                	xor    %eax,%eax
    2ea7:	41 c7 85 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r13)
    2eb2:	41 89 ad 90 08 00 00 	mov    %ebp,0x890(%r13)
    2eb9:	45 89 a5 94 08 00 00 	mov    %r12d,0x894(%r13)
    2ec0:	4c 89 2b             	mov    %r13,(%rbx)
    2ec3:	48 c7 83 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%rbx)
    2ece:	41 c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r13)
    2ed9:	41 c7 85 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r13)
    2ee4:	c7 83 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%rbx)
    2eee:	e8 bd f5 ff ff       	call   24b0 <__printf_chk@plt>
    2ef3:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2ef8:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2efd:	66 0f 6f 35 fb 5d 00 00 	movdqa 0x5dfb(%rip),%xmm6        # 8d00 <_IO_stdin_used+0xd00>
    2f05:	4d 89 5d 00          	mov    %r11,0x0(%r13)
    2f09:	4d 89 95 80 04 00 00 	mov    %r10,0x480(%r13)
    2f10:	41 0f 29 b5 80 00 00 00 	movaps %xmm6,0x80(%r13)
    2f18:	41 0f 29 b5 00 05 00 00 	movaps %xmm6,0x500(%r13)
    2f20:	e9 9b fe ff ff       	jmp    2dc0 <main+0x750>
    2f25:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
    2f2a:	44 89 eb             	mov    %r13d,%ebx
    2f2d:	eb 14                	jmp    2f43 <main+0x8d3>
    2f2f:	90                   	nop
    2f30:	83 c3 01             	add    $0x1,%ebx
    2f33:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    2f3a:	83 fb 06             	cmp    $0x6,%ebx
    2f3d:	0f 84 5b 01 00 00    	je     309e <main+0xa2e>
    2f43:	41 89 dd             	mov    %ebx,%r13d
    2f46:	31 c0                	xor    %eax,%eax
    2f48:	89 da                	mov    %ebx,%edx
    2f4a:	bf 01 00 00 00       	mov    $0x1,%edi
    2f4f:	41 d1 fd             	sar    %r13d
    2f52:	48 8d 35 7d 54 00 00 	lea    0x547d(%rip),%rsi        # 83d6 <_IO_stdin_used+0x3d6>
    2f59:	44 89 e9             	mov    %r13d,%ecx
    2f5c:	e8 4f f5 ff ff       	call   24b0 <__printf_chk@plt>
    2f61:	45 39 f5             	cmp    %r14d,%r13d
    2f64:	75 ca                	jne    2f30 <main+0x8c0>
    2f66:	be 08 00 00 00       	mov    $0x8,%esi
    2f6b:	bf 01 00 00 00       	mov    $0x1,%edi
    2f70:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    2f77:	e8 84 f4 ff ff       	call   2400 <calloc@plt>
    2f7c:	be 08 00 00 00       	mov    $0x8,%esi
    2f81:	bf 01 00 00 00       	mov    $0x1,%edi
    2f86:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2f8b:	e8 70 f4 ff ff       	call   2400 <calloc@plt>
    2f90:	be 80 04 00 00       	mov    $0x480,%esi
    2f95:	bf 03 00 00 00       	mov    $0x3,%edi
    2f9a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2f9f:	e8 5c f4 ff ff       	call   2400 <calloc@plt>
    2fa4:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    2fa8:	89 da                	mov    %ebx,%edx
    2faa:	49 c7 44 24 88 00 00 00 00 	movq   $0x0,-0x78(%r12)
    2fb3:	49 89 c5             	mov    %rax,%r13
    2fb6:	89 98 14 04 00 00    	mov    %ebx,0x414(%rax)
    2fbc:	48 8d 35 15 58 00 00 	lea    0x5815(%rip),%rsi        # 87d8 <_IO_stdin_used+0x7d8>
    2fc3:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
    2fc9:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
    2fd3:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    2fd9:	41 8d 47 01          	lea    0x1(%r15),%eax
    2fdd:	41 89 85 98 08 00 00 	mov    %eax,0x898(%r13)
    2fe4:	49 8d 85 80 04 00 00 	lea    0x480(%r13),%rax
    2feb:	49 89 44 24 80       	mov    %rax,-0x80(%r12)
    2ff0:	8b 84 24 84 00 00 00 	mov    0x84(%rsp),%eax
    2ff7:	45 89 bd 18 04 00 00 	mov    %r15d,0x418(%r13)
    2ffe:	41 83 c7 02          	add    $0x2,%r15d
    3002:	41 89 44 24 b4       	mov    %eax,-0x4c(%r12)
    3007:	89 c1                	mov    %eax,%ecx
    3009:	31 c0                	xor    %eax,%eax
    300b:	41 89 bd 8c 08 00 00 	mov    %edi,0x88c(%r13)
    3012:	bf 01 00 00 00       	mov    $0x1,%edi
    3017:	41 89 9d 94 08 00 00 	mov    %ebx,0x894(%r13)
    301e:	83 c3 01             	add    $0x1,%ebx
    3021:	4d 89 ac 24 00 ff ff ff 	mov    %r13,-0x100(%r12)
    3029:	49 c7 44 24 90 00 00 00 00 	movq   $0x0,-0x70(%r12)
    3032:	41 c7 44 24 b0 01 00 00 00 	movl   $0x1,-0x50(%r12)
    303b:	41 c7 85 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r13)
    3046:	41 89 ad 90 08 00 00 	mov    %ebp,0x890(%r13)
    304d:	41 c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r13)
    3058:	41 c7 85 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r13)
    3063:	e8 48 f4 ff ff       	call   24b0 <__printf_chk@plt>
    3068:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    306d:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    3072:	66 0f 6f 35 86 5c 00 00 	movdqa 0x5c86(%rip),%xmm6        # 8d00 <_IO_stdin_used+0xd00>
    307a:	4d 89 5d 00          	mov    %r11,0x0(%r13)
    307e:	4d 89 95 80 04 00 00 	mov    %r10,0x480(%r13)
    3085:	41 0f 29 b5 80 00 00 00 	movaps %xmm6,0x80(%r13)
    308d:	41 0f 29 b5 00 05 00 00 	movaps %xmm6,0x500(%r13)
    3095:	83 fb 06             	cmp    $0x6,%ebx
    3098:	0f 85 a5 fe ff ff    	jne    2f43 <main+0x8d3>
    309e:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    30a3:	eb 08                	jmp    30ad <main+0xa3d>
    30a5:	48 8b 8c 24 88 00 00 00 	mov    0x88(%rsp),%rcx
    30ad:	49 89 cd             	mov    %rcx,%r13
    30b0:	31 db                	xor    %ebx,%ebx
    30b2:	89 e9                	mov    %ebp,%ecx
    30b4:	4c 89 f5             	mov    %r14,%rbp
    30b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    30c0:	89 d8                	mov    %ebx,%eax
    30c2:	d1 f8                	sar    %eax
    30c4:	39 e8                	cmp    %ebp,%eax
    30c6:	0f 84 8b 01 00 00    	je     3257 <main+0xbe7>
    30cc:	89 da                	mov    %ebx,%edx
    30ce:	48 8d 35 11 53 00 00 	lea    0x5311(%rip),%rsi        # 83e6 <_IO_stdin_used+0x3e6>
    30d5:	bf 01 00 00 00       	mov    $0x1,%edi
    30da:	31 c0                	xor    %eax,%eax
    30dc:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    30e0:	e8 cb f3 ff ff       	call   24b0 <__printf_chk@plt>
    30e5:	be 08 00 00 00       	mov    $0x8,%esi
    30ea:	bf 01 00 00 00       	mov    $0x1,%edi
    30ef:	e8 0c f3 ff ff       	call   2400 <calloc@plt>
    30f4:	be 08 00 00 00       	mov    $0x8,%esi
    30f9:	bf 01 00 00 00       	mov    $0x1,%edi
    30fe:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3103:	e8 f8 f2 ff ff       	call   2400 <calloc@plt>
    3108:	be 80 04 00 00       	mov    $0x480,%esi
    310d:	bf 03 00 00 00       	mov    $0x3,%edi
    3112:	49 89 c6             	mov    %rax,%r14
    3115:	e8 e6 f2 ff ff       	call   2400 <calloc@plt>
    311a:	be 80 04 00 00       	mov    $0x480,%esi
    311f:	bf 03 00 00 00       	mov    $0x3,%edi
    3124:	49 89 c4             	mov    %rax,%r12
    3127:	e8 d4 f2 ff ff       	call   2400 <calloc@plt>
    312c:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    3130:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
    3134:	41 8d 77 01          	lea    0x1(%r15),%esi
    3138:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    313d:	66 0f 6f 35 bb 5b 00 00 	movdqa 0x5bbb(%rip),%xmm6        # 8d00 <_IO_stdin_used+0xd00>
    3145:	41 89 b4 24 98 08 00 00 	mov    %esi,0x898(%r12)
    314d:	49 8d b4 24 80 04 00 00 	lea    0x480(%r12),%rsi
    3155:	45 89 bc 24 18 04 00 00 	mov    %r15d,0x418(%r12)
    315d:	41 83 c7 02          	add    $0x2,%r15d
    3161:	41 c7 84 24 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%r12)
    316d:	41 89 bc 24 0c 04 00 00 	mov    %edi,0x40c(%r12)
    3175:	41 89 8c 24 10 04 00 00 	mov    %ecx,0x410(%r12)
    317d:	41 89 9c 24 14 04 00 00 	mov    %ebx,0x414(%r12)
    3185:	41 c7 84 24 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r12)
    3191:	41 89 bc 24 8c 08 00 00 	mov    %edi,0x88c(%r12)
    3199:	41 89 8c 24 90 08 00 00 	mov    %ecx,0x890(%r12)
    31a1:	41 89 9c 24 94 08 00 00 	mov    %ebx,0x894(%r12)
    31a9:	4d 89 65 00          	mov    %r12,0x0(%r13)
    31ad:	4d 89 a5 a0 00 00 00 	mov    %r12,0xa0(%r13)
    31b4:	49 89 b5 80 00 00 00 	mov    %rsi,0x80(%r13)
    31bb:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
    31c6:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
    31d1:	41 c7 84 24 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r12)
    31dd:	41 c7 84 24 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r12)
    31e9:	49 89 b5 a8 00 00 00 	mov    %rsi,0xa8(%r13)
    31f0:	41 c7 85 b0 00 00 00 02 00 00 00 	movl   $0x2,0xb0(%r13)
    31fb:	4c 89 20             	mov    %r12,(%rax)
    31fe:	48 89 70 08          	mov    %rsi,0x8(%rax)
    3202:	49 89 85 98 00 00 00 	mov    %rax,0x98(%r13)
    3209:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
    3215:	41 c7 84 24 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r12)
    3221:	49 89 14 24          	mov    %rdx,(%r12)
    3225:	4d 89 b4 24 80 04 00 00 	mov    %r14,0x480(%r12)
    322d:	41 c7 84 24 80 05 00 00 01 00 00 00 	movl   $0x1,0x580(%r12)
    3239:	41 c7 84 24 00 06 00 00 00 00 00 00 	movl   $0x0,0x600(%r12)
    3245:	41 0f 29 b4 24 80 00 00 00 	movaps %xmm6,0x80(%r12)
    324e:	41 0f 29 b4 24 00 05 00 00 	movaps %xmm6,0x500(%r12)
    3257:	83 c3 01             	add    $0x1,%ebx
    325a:	49 81 c5 00 01 00 00 	add    $0x100,%r13
    3261:	83 fb 06             	cmp    $0x6,%ebx
    3264:	0f 85 56 fe ff ff    	jne    30c0 <main+0xa50>
    326a:	be 01 00 00 00       	mov    $0x1,%esi
    326f:	bf 00 01 00 00       	mov    $0x100,%edi
    3274:	49 89 ee             	mov    %rbp,%r14
    3277:	89 cd                	mov    %ecx,%ebp
    3279:	e8 82 f1 ff ff       	call   2400 <calloc@plt>
    327e:	bf 20 00 00 00       	mov    $0x20,%edi
    3283:	48 89 c3             	mov    %rax,%rbx
    3286:	e8 e5 f1 ff ff       	call   2470 <malloc@plt>
    328b:	48 83 ec 08          	sub    $0x8,%rsp
    328f:	48 89 df             	mov    %rbx,%rdi
    3292:	41 89 e9             	mov    %ebp,%r9d
    3295:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    329a:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    329f:	ba 00 01 00 00       	mov    $0x100,%edx
    32a4:	31 c0                	xor    %eax,%eax
    32a6:	48 8d 0d 53 55 00 00 	lea    0x5553(%rip),%rcx        # 8800 <_IO_stdin_used+0x800>
    32ad:	be 01 00 00 00       	mov    $0x1,%esi
    32b2:	41 55                	push   %r13
    32b4:	44 8b 44 24 28       	mov    0x28(%rsp),%r8d
    32b9:	e8 e2 f2 ff ff       	call   25a0 <__sprintf_chk@plt>
    32be:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    32c3:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    32c8:	44 89 ef             	mov    %r13d,%edi
    32cb:	be 20 00 00 00       	mov    $0x20,%esi
    32d0:	45 89 6b 18          	mov    %r13d,0x18(%r11)
    32d4:	4c 8b 6c 24 58       	mov    0x58(%rsp),%r13
    32d9:	49 89 43 10          	mov    %rax,0x10(%r11)
    32dd:	49 63 45 08          	movslq 0x8(%r13),%rax
    32e1:	49 8b 55 38          	mov    0x38(%r13),%rdx
    32e5:	49 89 1b             	mov    %rbx,(%r11)
    32e8:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    32ed:	49 89 43 08          	mov    %rax,0x8(%r11)
    32f1:	8b 44 24 30          	mov    0x30(%rsp),%eax
    32f5:	48 01 d3             	add    %rdx,%rbx
    32f8:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    32fd:	89 83 a0 01 00 00    	mov    %eax,0x1a0(%rbx)
    3303:	83 c0 01             	add    $0x1,%eax
    3306:	89 44 24 30          	mov    %eax,0x30(%rsp)
    330a:	8d 45 01             	lea    0x1(%rbp),%eax
    330d:	83 e0 01             	and    $0x1,%eax
    3310:	89 bb 9c 01 00 00    	mov    %edi,0x19c(%rbx)
    3316:	bf 63 00 00 00       	mov    $0x63,%edi
    331b:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
    3321:	89 83 98 01 00 00    	mov    %eax,0x198(%rbx)
    3327:	4c 89 9b 90 01 00 00 	mov    %r11,0x190(%rbx)
    332e:	c7 83 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbx)
    3338:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
    3343:	e8 b8 f0 ff ff       	call   2400 <calloc@plt>
    3348:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
    3353:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
    335a:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    335f:	48 8b 00             	mov    (%rax),%rax
    3362:	8b 48 04             	mov    0x4(%rax),%ecx
    3365:	49 39 c5             	cmp    %rax,%r13
    3368:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
    336f:	89 8b 30 01 00 00    	mov    %ecx,0x130(%rbx)
    3375:	5a                   	pop    %rdx
    3376:	59                   	pop    %rcx
    3377:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    337c:	0f 85 4a 11 00 00    	jne    44cc <main+0x1e5c>
    3382:	66 0f 6f 05 86 59 00 00 	movdqa 0x5986(%rip),%xmm0        # 8d10 <_IO_stdin_used+0xd10>
    338a:	89 6b 04             	mov    %ebp,0x4(%rbx)
    338d:	48 8b 05 8c 59 00 00 	mov    0x598c(%rip),%rax        # 8d20 <_IO_stdin_used+0xd20>
    3394:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
    339e:	c7 83 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rbx)
    33a8:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
    33af:	0f 11 83 34 01 00 00 	movups %xmm0,0x134(%rbx)
    33b6:	83 fd 01             	cmp    $0x1,%ebp
    33b9:	0f 84 05 01 00 00    	je     34c4 <main+0xe54>
    33bf:	85 ed                	test   %ebp,%ebp
    33c1:	0f 84 e5 00 00 00    	je     34ac <main+0xe3c>
    33c7:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
    33cc:	48 8d 05 7d 37 00 00 	lea    0x377d(%rip),%rax        # 6b50 <barriered_work>
    33d3:	be 08 00 00 00       	mov    $0x8,%esi
    33d8:	45 89 fd             	mov    %r15d,%r13d
    33db:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
    33e2:	bf 01 00 00 00       	mov    $0x1,%edi
    33e7:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    33f2:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    33f7:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    33fc:	e8 ff ef ff ff       	call   2400 <calloc@plt>
    3401:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3406:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
    340b:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    3410:	83 44 24 7c 01       	addl   $0x1,0x7c(%rsp)
    3415:	49 89 41 50          	mov    %rax,0x50(%r9)
    3419:	49 81 c1 f8 00 00 00 	add    $0xf8,%r9
    3420:	66 0f 6f bc 24 c0 00 00 00 	movdqa 0xc0(%rsp),%xmm7
    3429:	48 89 18             	mov    %rbx,(%rax)
    342c:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3431:	48 83 c3 10          	add    $0x10,%rbx
    3435:	48 89 5c 24 60       	mov    %rbx,0x60(%rsp)
    343a:	48 8b 00             	mov    (%rax),%rax
    343d:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
    3444:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
    344e:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
    3455:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
    345f:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
    3469:	41 8b 81 0c ff ff ff 	mov    -0xf4(%r9),%eax
    3470:	c7 82 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rdx)
    347a:	48 83 7c 24 68 08    	cmpq   $0x8,0x68(%rsp)
    3480:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
    3486:	48 8b 05 93 58 00 00 	mov    0x5893(%rip),%rax        # 8d20 <_IO_stdin_used+0xd20>
    348d:	48 89 82 44 05 00 00 	mov    %rax,0x544(%rdx)
    3494:	74 3c                	je     34d2 <main+0xe62>
    3496:	48 c7 44 24 68 08 00 00 00 	movq   $0x8,0x68(%rsp)
    349f:	44 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%r15d
    34a7:	e9 13 f6 ff ff       	jmp    2abf <main+0x44f>
    34ac:	48 8d 05 cd 3b 00 00 	lea    0x3bcd(%rip),%rax        # 7080 <barriered_work_ingest_andwork>
    34b3:	bd 01 00 00 00       	mov    $0x1,%ebp
    34b8:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
    34bf:	e9 8e f8 ff ff       	jmp    2d52 <main+0x6e2>
    34c4:	48 8d 05 85 36 00 00 	lea    0x3685(%rip),%rax        # 6b50 <barriered_work>
    34cb:	bd 02 00 00 00       	mov    $0x2,%ebp
    34d0:	eb e6                	jmp    34b8 <main+0xe48>
    34d2:	4d 89 f7             	mov    %r14,%r15
    34d5:	48 8b ac 24 e8 00 00 00 	mov    0xe8(%rsp),%rbp
    34dd:	48 83 84 24 98 00 00 00 18 	addq   $0x18,0x98(%rsp)
    34e6:	49 83 c7 01          	add    $0x1,%r15
    34ea:	4c 8b b4 24 f8 00 00 00 	mov    0xf8(%rsp),%r14
    34f2:	49 83 ff 03          	cmp    $0x3,%r15
    34f6:	0f 85 05 f5 ff ff    	jne    2a01 <main+0x391>
    34fc:	be 08 00 00 00       	mov    $0x8,%esi
    3501:	bf 00 04 00 00       	mov    $0x400,%edi
    3506:	31 ed                	xor    %ebp,%ebp
    3508:	e8 f3 ee ff ff       	call   2400 <calloc@plt>
    350d:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3512:	49 89 c7             	mov    %rax,%r15
    3515:	31 c0                	xor    %eax,%eax
    3517:	49 89 d1             	mov    %rdx,%r9
    351a:	31 db                	xor    %ebx,%ebx
    351c:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3520:	45 85 d2             	test   %r10d,%r10d
    3523:	0f 8e a8 00 00 00    	jle    35d1 <main+0xf61>
    3529:	49 8b 79 38          	mov    0x38(%r9),%rdi
    352d:	4d 63 c2             	movslq %r10d,%r8
    3530:	48 63 cd             	movslq %ebp,%rcx
    3533:	49 c1 e0 09          	shl    $0x9,%r8
    3537:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    353b:	49 01 f8             	add    %rdi,%r8
    353e:	66 90                	xchg   %ax,%ax
    3540:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
    3547:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    354e:	48 83 c6 60          	add    $0x60,%rsi
    3552:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
    355a:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    355e:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    3566:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    356e:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    3576:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
    357d:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
    3585:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    358c:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
    3593:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
    359a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    359e:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
    35a5:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
    35ac:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    35b0:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    35b4:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    35b8:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    35bc:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    35c0:	49 39 f8             	cmp    %rdi,%r8
    35c3:	0f 85 77 ff ff ff    	jne    3540 <main+0xed0>
    35c9:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    35cd:	8d 6c 8d 00          	lea    0x0(%rbp,%rcx,4),%ebp
    35d1:	49 81 c1 f8 00 00 00 	add    $0xf8,%r9
    35d8:	85 db                	test   %ebx,%ebx
    35da:	75 3a                	jne    3616 <main+0xfa6>
    35dc:	bb 01 00 00 00       	mov    $0x1,%ebx
    35e1:	e9 36 ff ff ff       	jmp    351c <main+0xeac>
    35e6:	41 8d 57 01          	lea    0x1(%r15),%edx
    35ea:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    35ef:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    35f4:	45 31 c0             	xor    %r8d,%r8d
    35f7:	48 89 d0             	mov    %rdx,%rax
    35fa:	89 94 24 80 00 00 00 	mov    %edx,0x80(%rsp)
    3601:	89 d1                	mov    %edx,%ecx
    3603:	48 c1 e0 05          	shl    $0x5,%rax
    3607:	48 29 d0             	sub    %rdx,%rax
    360a:	4c 89 ca             	mov    %r9,%rdx
    360d:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3611:	e9 7d f5 ff ff       	jmp    2b93 <main+0x523>
    3616:	83 c0 02             	add    $0x2,%eax
    3619:	48 81 c2 f0 01 00 00 	add    $0x1f0,%rdx
    3620:	83 f8 06             	cmp    $0x6,%eax
    3623:	0f 85 ee fe ff ff    	jne    3517 <main+0xea7>
    3629:	48 8d 3d d4 4d 00 00 	lea    0x4dd4(%rip),%rdi        # 8404 <_IO_stdin_used+0x404>
    3630:	e8 fb ec ff ff       	call   2330 <puts@plt>
    3635:	48 8d 35 dd 4d 00 00 	lea    0x4ddd(%rip),%rsi        # 8419 <_IO_stdin_used+0x419>
    363c:	48 8d 3d d8 4d 00 00 	lea    0x4dd8(%rip),%rdi        # 841b <_IO_stdin_used+0x41b>
    3643:	e8 a8 ee ff ff       	call   24f0 <fopen@plt>
    3648:	49 89 c6             	mov    %rax,%r14
    364b:	85 ed                	test   %ebp,%ebp
    364d:	7e 76                	jle    36c5 <main+0x1055>
    364f:	48 63 ed             	movslq %ebp,%rbp
    3652:	4c 8d 2d 9f 4d 00 00 	lea    0x4d9f(%rip),%r13        # 83f8 <_IO_stdin_used+0x3f8>
    3659:	4c 8d 25 dc 4d 00 00 	lea    0x4ddc(%rip),%r12        # 843c <_IO_stdin_used+0x43c>
    3660:	49 8d 04 ef          	lea    (%r15,%rbp,8),%rax
    3664:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3669:	be 01 00 00 00       	mov    $0x1,%esi
    366e:	bf fa 00 00 00       	mov    $0xfa,%edi
    3673:	49 83 c7 08          	add    $0x8,%r15
    3677:	e8 84 ed ff ff       	call   2400 <calloc@plt>
    367c:	4c 89 e9             	mov    %r13,%rcx
    367f:	ba fa 00 00 00       	mov    $0xfa,%edx
    3684:	be 01 00 00 00       	mov    $0x1,%esi
    3689:	48 89 c5             	mov    %rax,%rbp
    368c:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3690:	48 89 ef             	mov    %rbp,%rdi
    3693:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    369a:	31 c0                	xor    %eax,%eax
    369c:	e8 ff ee ff ff       	call   25a0 <__sprintf_chk@plt>
    36a1:	48 89 ea             	mov    %rbp,%rdx
    36a4:	4c 89 e6             	mov    %r12,%rsi
    36a7:	bf 01 00 00 00       	mov    $0x1,%edi
    36ac:	31 c0                	xor    %eax,%eax
    36ae:	e8 fd ed ff ff       	call   24b0 <__printf_chk@plt>
    36b3:	4c 89 f6             	mov    %r14,%rsi
    36b6:	48 89 ef             	mov    %rbp,%rdi
    36b9:	e8 02 ed ff ff       	call   23c0 <fputs@plt>
    36be:	4c 39 7c 24 08       	cmp    %r15,0x8(%rsp)
    36c3:	75 a4                	jne    3669 <main+0xff9>
    36c5:	4c 89 f7             	mov    %r14,%rdi
    36c8:	45 31 f6             	xor    %r14d,%r14d
    36cb:	4c 8d 25 94 4d 00 00 	lea    0x4d94(%rip),%r12        # 8466 <_IO_stdin_used+0x466>
    36d2:	e8 89 ec ff ff       	call   2360 <fclose@plt>
    36d7:	48 8d 3d 46 4d 00 00 	lea    0x4d46(%rip),%rdi        # 8424 <_IO_stdin_used+0x424>
    36de:	4c 89 f5             	mov    %r14,%rbp
    36e1:	e8 4a ec ff ff       	call   2330 <puts@plt>
    36e6:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    36ea:	48 89 eb             	mov    %rbp,%rbx
    36ed:	89 ea                	mov    %ebp,%edx
    36ef:	48 8d 35 49 4d 00 00 	lea    0x4d49(%rip),%rsi        # 843f <_IO_stdin_used+0x43f>
    36f6:	31 c0                	xor    %eax,%eax
    36f8:	bf 01 00 00 00       	mov    $0x1,%edi
    36fd:	48 c1 e3 05          	shl    $0x5,%rbx
    3701:	44 8d 6c 2d 00       	lea    0x0(%rbp,%rbp,1),%r13d
    3706:	45 31 ff             	xor    %r15d,%r15d
    3709:	e8 a2 ed ff ff       	call   24b0 <__printf_chk@plt>
    370e:	48 29 eb             	sub    %rbp,%rbx
    3711:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3716:	48 c1 e3 04          	shl    $0x4,%rbx
    371a:	48 01 c3             	add    %rax,%rbx
    371d:	43 8d 0c 2f          	lea    (%r15,%r13,1),%ecx
    3721:	44 89 fa             	mov    %r15d,%edx
    3724:	48 8d 35 1e 4d 00 00 	lea    0x4d1e(%rip),%rsi        # 8449 <_IO_stdin_used+0x449>
    372b:	31 c0                	xor    %eax,%eax
    372d:	bf 01 00 00 00       	mov    $0x1,%edi
    3732:	45 31 f6             	xor    %r14d,%r14d
    3735:	e8 76 ed ff ff       	call   24b0 <__printf_chk@plt>
    373a:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
    373f:	4c 89 f1             	mov    %r14,%rcx
    3742:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    3747:	48 89 dd             	mov    %rbx,%rbp
    374a:	89 ca                	mov    %ecx,%edx
    374c:	48 8d 35 08 4d 00 00 	lea    0x4d08(%rip),%rsi        # 845b <_IO_stdin_used+0x45b>
    3753:	bf 01 00 00 00       	mov    $0x1,%edi
    3758:	31 c0                	xor    %eax,%eax
    375a:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    375f:	45 31 ed             	xor    %r13d,%r13d
    3762:	e8 49 ed ff ff       	call   24b0 <__printf_chk@plt>
    3767:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    376c:	48 c1 e3 09          	shl    $0x9,%rbx
    3770:	eb 32                	jmp    37a4 <main+0x1134>
    3772:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3778:	83 fe 01             	cmp    $0x1,%esi
    377b:	0f 84 a9 00 00 00    	je     382a <main+0x11ba>
    3781:	44 89 f2             	mov    %r14d,%edx
    3784:	4c 89 e6             	mov    %r12,%rsi
    3787:	bf 01 00 00 00       	mov    $0x1,%edi
    378c:	49 83 c5 01          	add    $0x1,%r13
    3790:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    3797:	31 c0                	xor    %eax,%eax
    3799:	e8 12 ed ff ff       	call   24b0 <__printf_chk@plt>
    379e:	49 83 fd 06          	cmp    $0x6,%r13
    37a2:	74 50                	je     37f4 <main+0x1184>
    37a4:	be 01 00 00 00       	mov    $0x1,%esi
    37a9:	bf 64 00 00 00       	mov    $0x64,%edi
    37ae:	45 89 ee             	mov    %r13d,%r14d
    37b1:	e8 4a ec ff ff       	call   2400 <calloc@plt>
    37b6:	4c 8b 45 38          	mov    0x38(%rbp),%r8
    37ba:	4c 89 ef             	mov    %r13,%rdi
    37bd:	48 89 c1             	mov    %rax,%rcx
    37c0:	48 c1 e7 08          	shl    $0x8,%rdi
    37c4:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    37cc:	48 01 f8             	add    %rdi,%rax
    37cf:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    37d5:	83 fe 02             	cmp    $0x2,%esi
    37d8:	75 9e                	jne    3778 <main+0x1108>
    37da:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    37e4:	48 89 01             	mov    %rax,(%rcx)
    37e7:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    37ef:	48 01 f8             	add    %rdi,%rax
    37f2:	eb 8d                	jmp    3781 <main+0x1111>
    37f4:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    37f9:	48 83 c1 01          	add    $0x1,%rcx
    37fd:	48 83 f9 03          	cmp    $0x3,%rcx
    3801:	0f 85 43 ff ff ff    	jne    374a <main+0x10da>
    3807:	48 89 eb             	mov    %rbp,%rbx
    380a:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    380f:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    3814:	48 81 c3 f8 00 00 00 	add    $0xf8,%rbx
    381b:	45 85 ff             	test   %r15d,%r15d
    381e:	75 27                	jne    3847 <main+0x11d7>
    3820:	44 8b 7c 24 10       	mov    0x10(%rsp),%r15d
    3825:	e9 f3 fe ff ff       	jmp    371d <main+0x10ad>
    382a:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3830:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    3837:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    383f:	48 01 f8             	add    %rdi,%rax
    3842:	e9 3a ff ff ff       	jmp    3781 <main+0x1111>
    3847:	48 83 c5 01          	add    $0x1,%rbp
    384b:	48 83 fd 03          	cmp    $0x3,%rbp
    384f:	0f 85 95 fe ff ff    	jne    36ea <main+0x107a>
    3855:	ba 07 00 00 00       	mov    $0x7,%edx
    385a:	48 8d 35 20 4c 00 00 	lea    0x4c20(%rip),%rsi        # 8481 <_IO_stdin_used+0x481>
    3861:	bf 01 00 00 00       	mov    $0x1,%edi
    3866:	31 c0                	xor    %eax,%eax
    3868:	e8 43 ec ff ff       	call   24b0 <__printf_chk@plt>
    386d:	be 08 00 00 00       	mov    $0x8,%esi
    3872:	bf 02 00 00 00       	mov    $0x2,%edi
    3877:	e8 84 eb ff ff       	call   2400 <calloc@plt>
    387c:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3881:	be 38 00 00 00       	mov    $0x38,%esi
    3886:	4c 8d af c8 06 00 00 	lea    0x6c8(%rdi),%r13
    388d:	48 89 78 08          	mov    %rdi,0x8(%rax)
    3891:	4c 8d a7 f8 00 00 00 	lea    0xf8(%rdi),%r12
    3898:	48 89 87 e0 06 00 00 	mov    %rax,0x6e0(%rdi)
    389f:	4c 89 28             	mov    %r13,(%rax)
    38a2:	48 8b 47 38          	mov    0x38(%rdi),%rax
    38a6:	c7 87 f0 06 00 00 02 00 00 00 	movl   $0x2,0x6f0(%rdi)
    38b0:	c7 87 cc 06 00 00 00 00 00 00 	movl   $0x0,0x6cc(%rdi)
    38ba:	c7 87 08 07 00 00 03 00 00 00 	movl   $0x3,0x708(%rdi)
    38c4:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    38ce:	48 8b 87 30 01 00 00 	mov    0x130(%rdi),%rax
    38d5:	bf 0a 00 00 00       	mov    $0xa,%edi
    38da:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    38e4:	e8 17 eb ff ff       	call   2400 <calloc@plt>
    38e9:	be 38 00 00 00       	mov    $0x38,%esi
    38ee:	bf 0a 00 00 00       	mov    $0xa,%edi
    38f3:	49 89 c6             	mov    %rax,%r14
    38f6:	e8 05 eb ff ff       	call   2400 <calloc@plt>
    38fb:	be 38 00 00 00       	mov    $0x38,%esi
    3900:	bf 0a 00 00 00       	mov    $0xa,%edi
    3905:	48 89 c5             	mov    %rax,%rbp
    3908:	e8 f3 ea ff ff       	call   2400 <calloc@plt>
    390d:	be 38 00 00 00       	mov    $0x38,%esi
    3912:	bf 0a 00 00 00       	mov    $0xa,%edi
    3917:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    391c:	e8 df ea ff ff       	call   2400 <calloc@plt>
    3921:	be 08 00 00 00       	mov    $0x8,%esi
    3926:	bf 0a 00 00 00       	mov    $0xa,%edi
    392b:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3930:	e8 cb ea ff ff       	call   2400 <calloc@plt>
    3935:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    393a:	be 08 00 00 00       	mov    $0x8,%esi
    393f:	48 89 c3             	mov    %rax,%rbx
    3942:	48 8b 05 ef 53 00 00 	mov    0x53ef(%rip),%rax        # 8d38 <_IO_stdin_used+0xd38>
    3949:	c7 87 dc 05 00 00 00 00 00 00 	movl   $0x0,0x5dc(%rdi)
    3953:	48 89 87 10 06 00 00 	mov    %rax,0x610(%rdi)
    395a:	bf 0a 00 00 00       	mov    $0xa,%edi
    395f:	e8 9c ea ff ff       	call   2400 <calloc@plt>
    3964:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3969:	4c 89 60 08          	mov    %r12,0x8(%rax)
    396d:	48 8d 97 f0 01 00 00 	lea    0x1f0(%rdi),%rdx
    3974:	48 8d 8f d0 05 00 00 	lea    0x5d0(%rdi),%rcx
    397b:	48 89 38             	mov    %rdi,(%rax)
    397e:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3982:	48 8d 97 e8 02 00 00 	lea    0x2e8(%rdi),%rdx
    3989:	48 8d b7 c0 07 00 00 	lea    0x7c0(%rdi),%rsi
    3990:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3994:	48 8d 97 e0 03 00 00 	lea    0x3e0(%rdi),%rdx
    399b:	48 89 50 20          	mov    %rdx,0x20(%rax)
    399f:	48 8d 97 d8 04 00 00 	lea    0x4d8(%rdi),%rdx
    39a6:	48 89 50 28          	mov    %rdx,0x28(%rax)
    39aa:	48 8d 97 b8 08 00 00 	lea    0x8b8(%rdi),%rdx
    39b1:	48 89 48 30          	mov    %rcx,0x30(%rax)
    39b5:	48 89 70 40          	mov    %rsi,0x40(%rax)
    39b9:	48 89 50 48          	mov    %rdx,0x48(%rax)
    39bd:	ba 06 00 00 00       	mov    $0x6,%edx
    39c2:	48 89 87 e8 05 00 00 	mov    %rax,0x5e8(%rdi)
    39c9:	4c 89 68 38          	mov    %r13,0x38(%rax)
    39cd:	48 8b 05 6c 53 00 00 	mov    0x536c(%rip),%rax        # 8d40 <_IO_stdin_used+0xd40>
    39d4:	c7 87 00 06 00 00 06 00 00 00 	movl   $0x6,0x600(%rdi)
    39de:	48 89 87 f8 05 00 00 	mov    %rax,0x5f8(%rdi)
    39e5:	31 c0                	xor    %eax,%eax
    39e7:	c7 87 d4 05 00 00 00 00 00 00 	movl   $0x0,0x5d4(%rdi)
    39f1:	bf 01 00 00 00       	mov    $0x1,%edi
    39f6:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    39fb:	48 8d 35 8e 4a 00 00 	lea    0x4a8e(%rip),%rsi        # 8490 <_IO_stdin_used+0x490>
    3a02:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    3a07:	e8 a4 ea ff ff       	call   24b0 <__printf_chk@plt>
    3a0c:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    3a11:	48 8d 15 a8 0d 00 00 	lea    0xda8(%rip),%rdx        # 47c0 <timer_thread>
    3a18:	48 8d b5 50 01 00 00 	lea    0x150(%rbp),%rsi
    3a1f:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    3a23:	e8 a8 ea ff ff       	call   24d0 <pthread_create@plt>
    3a28:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    3a2d:	4c 89 f0             	mov    %r14,%rax
    3a30:	48 89 d9             	mov    %rbx,%rcx
    3a33:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    3a38:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3a3e:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3a43:	45 31 f6             	xor    %r14d,%r14d
    3a46:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
    3a4b:	44 89 7c 24 20       	mov    %r15d,0x20(%rsp)
    3a50:	45 89 d7             	mov    %r10d,%r15d
    3a53:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3a58:	47 8d 24 36          	lea    (%r14,%r14,1),%r12d
    3a5c:	49 89 c5             	mov    %rax,%r13
    3a5f:	48 89 cb             	mov    %rcx,%rbx
    3a62:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    3a67:	48 89 d5             	mov    %rdx,%rbp
    3a6a:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
    3a6f:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    3a76:	44 89 e2             	mov    %r12d,%edx
    3a79:	44 89 f1             	mov    %r14d,%ecx
    3a7c:	31 c0                	xor    %eax,%eax
    3a7e:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    3a85:	48 8d 35 a4 4d 00 00 	lea    0x4da4(%rip),%rsi        # 8830 <_IO_stdin_used+0x830>
    3a8c:	bf 01 00 00 00       	mov    $0x1,%edi
    3a91:	41 83 c4 01          	add    $0x1,%r12d
    3a95:	e8 16 ea ff ff       	call   24b0 <__printf_chk@plt>
    3a9a:	48 89 e9             	mov    %rbp,%rcx
    3a9d:	4c 89 ee             	mov    %r13,%rsi
    3aa0:	48 89 df             	mov    %rbx,%rdi
    3aa3:	48 8d 15 96 28 00 00 	lea    0x2896(%rip),%rdx        # 6340 <barriered_thread>
    3aaa:	48 81 c5 f8 00 00 00 	add    $0xf8,%rbp
    3ab1:	48 83 c3 08          	add    $0x8,%rbx
    3ab5:	49 83 c5 38          	add    $0x38,%r13
    3ab9:	e8 12 ea ff ff       	call   24d0 <pthread_create@plt>
    3abe:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    3ac2:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    3ac6:	be 08 00 00 00       	mov    $0x8,%esi
    3acb:	e8 50 e8 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    3ad0:	45 39 e7             	cmp    %r12d,%r15d
    3ad3:	75 9a                	jne    3a6f <main+0x13ff>
    3ad5:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3ada:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    3adf:	41 83 c6 01          	add    $0x1,%r14d
    3ae3:	41 83 c7 02          	add    $0x2,%r15d
    3ae7:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    3aec:	48 83 c1 10          	add    $0x10,%rcx
    3af0:	48 83 c0 70          	add    $0x70,%rax
    3af4:	48 81 c2 f0 01 00 00 	add    $0x1f0,%rdx
    3afb:	41 83 fe 03          	cmp    $0x3,%r14d
    3aff:	0f 85 4e ff ff ff    	jne    3a53 <main+0x13e3>
    3b05:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3b0a:	be d8 00 00 00       	mov    $0xd8,%esi
    3b0f:	bf 01 00 00 00       	mov    $0x1,%edi
    3b14:	48 8b 05 2d 52 00 00 	mov    0x522d(%rip),%rax        # 8d48 <_IO_stdin_used+0xd48>
    3b1b:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    3b20:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    3b25:	41 c7 86 d4 06 00 00 02 00 00 00 	movl   $0x2,0x6d4(%r14)
    3b30:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    3b35:	49 89 86 08 07 00 00 	mov    %rax,0x708(%r14)
    3b3c:	44 8b 7c 24 20       	mov    0x20(%rsp),%r15d
    3b41:	48 8d 6b 40          	lea    0x40(%rbx),%rbp
    3b45:	e8 b6 e8 ff ff       	call   2400 <calloc@plt>
    3b4a:	be 00 08 00 00       	mov    $0x800,%esi
    3b4f:	31 ff                	xor    %edi,%edi
    3b51:	49 89 86 20 07 00 00 	mov    %rax,0x720(%r14)
    3b58:	e8 c3 e9 ff ff       	call   2520 <eventfd@plt>
    3b5d:	be 08 00 00 00       	mov    $0x8,%esi
    3b62:	bf 02 00 00 00       	mov    $0x2,%edi
    3b67:	41 89 86 28 07 00 00 	mov    %eax,0x728(%r14)
    3b6e:	e8 8d e8 ff ff       	call   2400 <calloc@plt>
    3b73:	ba 07 00 00 00       	mov    $0x7,%edx
    3b78:	bf 01 00 00 00       	mov    $0x1,%edi
    3b7d:	41 c7 86 f0 06 00 00 02 00 00 00 	movl   $0x2,0x6f0(%r14)
    3b88:	4c 89 30             	mov    %r14,(%rax)
    3b8b:	48 8d 35 1c 49 00 00 	lea    0x491c(%rip),%rsi        # 84ae <_IO_stdin_used+0x4ae>
    3b92:	49 89 86 e0 06 00 00 	mov    %rax,0x6e0(%r14)
    3b99:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3b9d:	31 c0                	xor    %eax,%eax
    3b9f:	41 c7 86 cc 06 00 00 07 00 00 00 	movl   $0x7,0x6cc(%r14)
    3baa:	41 be 08 00 00 00    	mov    $0x8,%r14d
    3bb0:	e8 fb e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bb5:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3bba:	4c 89 e9             	mov    %r13,%rcx
    3bbd:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3bc1:	48 8d 15 88 1f 00 00 	lea    0x1f88(%rip),%rdx        # 5b50 <io_thread>
    3bc8:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3bcf:	e8 fc e8 ff ff       	call   24d0 <pthread_create@plt>
    3bd4:	ba 08 00 00 00       	mov    $0x8,%edx
    3bd9:	48 8d 35 e5 48 00 00 	lea    0x48e5(%rip),%rsi        # 84c5 <_IO_stdin_used+0x4c5>
    3be0:	31 c0                	xor    %eax,%eax
    3be2:	bf 01 00 00 00       	mov    $0x1,%edi
    3be7:	e8 c4 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bec:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3bf1:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    3bf6:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    3bfc:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3c01:	44 89 f2             	mov    %r14d,%edx
    3c04:	48 8d 35 d0 48 00 00 	lea    0x48d0(%rip),%rsi        # 84db <_IO_stdin_used+0x4db>
    3c0b:	bf 01 00 00 00       	mov    $0x1,%edi
    3c10:	31 c0                	xor    %eax,%eax
    3c12:	e8 99 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c17:	be 08 00 00 00       	mov    $0x8,%esi
    3c1c:	bf 01 00 00 00       	mov    $0x1,%edi
    3c21:	48 8b 05 20 51 00 00 	mov    0x5120(%rip),%rax        # 8d48 <_IO_stdin_used+0xd48>
    3c28:	41 c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%r13)
    3c30:	49 89 45 40          	mov    %rax,0x40(%r13)
    3c34:	e8 c7 e7 ff ff       	call   2400 <calloc@plt>
    3c39:	48 8b bc 24 b8 00 00 00 	mov    0xb8(%rsp),%rdi
    3c41:	be 08 00 00 00       	mov    $0x8,%esi
    3c46:	41 c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r13)
    3c51:	49 89 45 50          	mov    %rax,0x50(%r13)
    3c55:	48 89 38             	mov    %rdi,(%rax)
    3c58:	bf 02 00 00 00       	mov    $0x2,%edi
    3c5d:	e8 9e e7 ff ff       	call   2400 <calloc@plt>
    3c62:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    3c67:	4c 89 e9             	mov    %r13,%rcx
    3c6a:	48 89 ef             	mov    %rbp,%rdi
    3c6d:	49 89 45 18          	mov    %rax,0x18(%r13)
    3c71:	48 8d 15 38 0a 00 00 	lea    0xa38(%rip),%rdx        # 46b0 <external_thread>
    3c78:	48 83 c5 08          	add    $0x8,%rbp
    3c7c:	49 81 c5 f8 00 00 00 	add    $0xf8,%r13
    3c83:	48 89 30             	mov    %rsi,(%rax)
    3c86:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3c8b:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3c8f:	48 8b 05 9a 50 00 00 	mov    0x509a(%rip),%rax        # 8d30 <_IO_stdin_used+0xd30>
    3c96:	45 89 b5 0c ff ff ff 	mov    %r14d,-0xf4(%r13)
    3c9d:	49 89 85 30 ff ff ff 	mov    %rax,-0xd0(%r13)
    3ca4:	e8 27 e8 ff ff       	call   24d0 <pthread_create@plt>
    3ca9:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3caf:	48 83 84 24 b8 00 00 00 10 	addq   $0x10,0xb8(%rsp)
    3cb8:	41 83 fe 08          	cmp    $0x8,%r14d
    3cbc:	75 17                	jne    3cd5 <main+0x1665>
    3cbe:	41 be 09 00 00 00    	mov    $0x9,%r14d
    3cc4:	e9 38 ff ff ff       	jmp    3c01 <main+0x1591>
    3cc9:	48 81 0b ff 0f 00 00 	orq    $0xfff,(%rbx)
    3cd0:	e9 5a ef ff ff       	jmp    2c2f <main+0x5bf>
    3cd5:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3cda:	48 8d 2d 17 48 00 00 	lea    0x4817(%rip),%rbp        # 84f8 <_IO_stdin_used+0x4f8>
    3ce1:	4c 8d 68 04          	lea    0x4(%rax),%r13
    3ce5:	4c 8d a0 b4 09 00 00 	lea    0x9b4(%rax),%r12
    3cec:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    3cf0:	41 8b 55 00          	mov    0x0(%r13),%edx
    3cf4:	48 89 ee             	mov    %rbp,%rsi
    3cf7:	bf 01 00 00 00       	mov    $0x1,%edi
    3cfc:	31 c0                	xor    %eax,%eax
    3cfe:	49 81 c5 f8 00 00 00 	add    $0xf8,%r13
    3d05:	e8 a6 e7 ff ff       	call   24b0 <__printf_chk@plt>
    3d0a:	4d 39 ec             	cmp    %r13,%r12
    3d0d:	75 dd                	jne    3cec <main+0x167c>
    3d0f:	48 8d 3d f5 47 00 00 	lea    0x47f5(%rip),%rdi        # 850b <_IO_stdin_used+0x50b>
    3d16:	45 31 ed             	xor    %r13d,%r13d
    3d19:	4c 8d a4 24 00 01 00 00 	lea    0x100(%rsp),%r12
    3d21:	e8 0a e6 ff ff       	call   2330 <puts@plt>
    3d26:	48 8d 2d fc 47 00 00 	lea    0x47fc(%rip),%rbp        # 8529 <_IO_stdin_used+0x529>
    3d2d:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    3d31:	4c 89 e6             	mov    %r12,%rsi
    3d34:	e8 27 e8 ff ff       	call   2560 <pthread_join@plt>
    3d39:	44 89 ea             	mov    %r13d,%edx
    3d3c:	48 89 ee             	mov    %rbp,%rsi
    3d3f:	bf 01 00 00 00       	mov    $0x1,%edi
    3d44:	31 c0                	xor    %eax,%eax
    3d46:	49 83 c5 01          	add    $0x1,%r13
    3d4a:	e8 61 e7 ff ff       	call   24b0 <__printf_chk@plt>
    3d4f:	49 83 fd 0a          	cmp    $0xa,%r13
    3d53:	75 d8                	jne    3d2d <main+0x16bd>
    3d55:	be 08 00 00 00       	mov    $0x8,%esi
    3d5a:	bf 00 04 00 00       	mov    $0x400,%edi
    3d5f:	31 db                	xor    %ebx,%ebx
    3d61:	e8 9a e6 ff ff       	call   2400 <calloc@plt>
    3d66:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3d6b:	48 89 c5             	mov    %rax,%rbp
    3d6e:	31 c0                	xor    %eax,%eax
    3d70:	49 89 d1             	mov    %rdx,%r9
    3d73:	45 31 db             	xor    %r11d,%r11d
    3d76:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3d7a:	45 85 d2             	test   %r10d,%r10d
    3d7d:	0f 8e ad 00 00 00    	jle    3e30 <main+0x17c0>
    3d83:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3d87:	4d 63 c2             	movslq %r10d,%r8
    3d8a:	48 63 cb             	movslq %ebx,%rcx
    3d8d:	49 c1 e0 09          	shl    $0x9,%r8
    3d91:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    3d96:	49 01 f8             	add    %rdi,%r8
    3d99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3da0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
    3da7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3dae:	48 83 c6 60          	add    $0x60,%rsi
    3db2:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
    3dba:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3dbe:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    3dc6:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    3dce:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    3dd6:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
    3ddd:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
    3de5:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    3dec:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
    3df3:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
    3dfa:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3dfe:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
    3e05:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
    3e0c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3e10:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3e14:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3e18:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3e1c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    3e20:	4c 39 c7             	cmp    %r8,%rdi
    3e23:	0f 85 77 ff ff ff    	jne    3da0 <main+0x1730>
    3e29:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3e2d:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    3e30:	49 81 c1 f8 00 00 00 	add    $0xf8,%r9
    3e37:	45 85 db             	test   %r11d,%r11d
    3e3a:	75 08                	jne    3e44 <main+0x17d4>
    3e3c:	45 89 fb             	mov    %r15d,%r11d
    3e3f:	e9 32 ff ff ff       	jmp    3d76 <main+0x1706>
    3e44:	83 c0 02             	add    $0x2,%eax
    3e47:	48 81 c2 f0 01 00 00 	add    $0x1f0,%rdx
    3e4e:	83 f8 06             	cmp    $0x6,%eax
    3e51:	0f 85 19 ff ff ff    	jne    3d70 <main+0x1700>
    3e57:	48 8d 3d df 46 00 00 	lea    0x46df(%rip),%rdi        # 853d <_IO_stdin_used+0x53d>
    3e5e:	e8 cd e4 ff ff       	call   2330 <puts@plt>
    3e63:	48 8d 35 af 45 00 00 	lea    0x45af(%rip),%rsi        # 8419 <_IO_stdin_used+0x419>
    3e6a:	48 8d 3d e4 46 00 00 	lea    0x46e4(%rip),%rdi        # 8555 <_IO_stdin_used+0x555>
    3e71:	e8 7a e6 ff ff       	call   24f0 <fopen@plt>
    3e76:	49 89 c6             	mov    %rax,%r14
    3e79:	85 db                	test   %ebx,%ebx
    3e7b:	7e 73                	jle    3ef0 <main+0x1880>
    3e7d:	48 63 db             	movslq %ebx,%rbx
    3e80:	49 89 ef             	mov    %rbp,%r15
    3e83:	4c 8d 2d 6e 45 00 00 	lea    0x456e(%rip),%r13        # 83f8 <_IO_stdin_used+0x3f8>
    3e8a:	48 8d 6c dd 00       	lea    0x0(%rbp,%rbx,8),%rbp
    3e8f:	4c 8d 25 a6 45 00 00 	lea    0x45a6(%rip),%r12        # 843c <_IO_stdin_used+0x43c>
    3e96:	be 01 00 00 00       	mov    $0x1,%esi
    3e9b:	bf fa 00 00 00       	mov    $0xfa,%edi
    3ea0:	49 83 c7 08          	add    $0x8,%r15
    3ea4:	e8 57 e5 ff ff       	call   2400 <calloc@plt>
    3ea9:	4c 89 e9             	mov    %r13,%rcx
    3eac:	ba fa 00 00 00       	mov    $0xfa,%edx
    3eb1:	be 01 00 00 00       	mov    $0x1,%esi
    3eb6:	48 89 c3             	mov    %rax,%rbx
    3eb9:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3ebd:	48 89 df             	mov    %rbx,%rdi
    3ec0:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3ec7:	31 c0                	xor    %eax,%eax
    3ec9:	e8 d2 e6 ff ff       	call   25a0 <__sprintf_chk@plt>
    3ece:	48 89 da             	mov    %rbx,%rdx
    3ed1:	4c 89 e6             	mov    %r12,%rsi
    3ed4:	bf 01 00 00 00       	mov    $0x1,%edi
    3ed9:	31 c0                	xor    %eax,%eax
    3edb:	e8 d0 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3ee0:	4c 89 f6             	mov    %r14,%rsi
    3ee3:	48 89 df             	mov    %rbx,%rdi
    3ee6:	e8 d5 e4 ff ff       	call   23c0 <fputs@plt>
    3eeb:	49 39 ef             	cmp    %rbp,%r15
    3eee:	75 a6                	jne    3e96 <main+0x1826>
    3ef0:	4c 89 f7             	mov    %r14,%rdi
    3ef3:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
    3ef9:	31 db                	xor    %ebx,%ebx
    3efb:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
    3f05:	e8 56 e4 ff ff       	call   2360 <fclose@plt>
    3f0a:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
    3f13:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    3f1c:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3f25:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
    3f2e:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
    3f36:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    3f3b:	4c 8b b4 24 d0 00 00 00 	mov    0xd0(%rsp),%r14
    3f43:	45 89 e5             	mov    %r12d,%r13d
    3f46:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    3f4b:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3f50:	44 89 e8             	mov    %r13d,%eax
    3f53:	41 83 c5 01          	add    $0x1,%r13d
    3f57:	bf 0a 00 00 00       	mov    $0xa,%edi
    3f5c:	41 f6 c5 01          	test   $0x1,%r13b
    3f60:	8d 50 02             	lea    0x2(%rax),%edx
    3f63:	0f 44 c2             	cmove  %edx,%eax
    3f66:	4c 63 e0             	movslq %eax,%r12
    3f69:	e8 a2 e3 ff ff       	call   2310 <putchar@plt>
    3f6e:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3f73:	bf 01 00 00 00       	mov    $0x1,%edi
    3f78:	48 8d 35 df 45 00 00 	lea    0x45df(%rip),%rsi        # 855e <_IO_stdin_used+0x55e>
    3f7f:	48 8b 10             	mov    (%rax),%rdx
    3f82:	31 c0                	xor    %eax,%eax
    3f84:	e8 27 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3f89:	41 8b 56 40          	mov    0x40(%r14),%edx
    3f8d:	85 d2                	test   %edx,%edx
    3f8f:	0f 8e 30 05 00 00    	jle    44c5 <main+0x1e55>
    3f95:	48 63 ca             	movslq %edx,%rcx
    3f98:	49 8b 46 38          	mov    0x38(%r14),%rax
    3f9c:	31 d2                	xor    %edx,%edx
    3f9e:	48 c1 e1 09          	shl    $0x9,%rcx
    3fa2:	48 01 c1             	add    %rax,%rcx
    3fa5:	0f 1f 00             	nopl   (%rax)
    3fa8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3faf:	48 05 00 02 00 00    	add    $0x200,%rax
    3fb5:	48 39 c8             	cmp    %rcx,%rax
    3fb8:	75 ee                	jne    3fa8 <main+0x1938>
    3fba:	4c 89 e0             	mov    %r12,%rax
    3fbd:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3fc2:	48 c1 e0 05          	shl    $0x5,%rax
    3fc6:	4c 29 e0             	sub    %r12,%rax
    3fc9:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3fcd:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3fd1:	85 c9                	test   %ecx,%ecx
    3fd3:	7e 1d                	jle    3ff2 <main+0x1982>
    3fd5:	48 8b 40 38          	mov    0x38(%rax),%rax
    3fd9:	48 c1 e1 09          	shl    $0x9,%rcx
    3fdd:	48 01 c1             	add    %rax,%rcx
    3fe0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3fe7:	48 05 00 02 00 00    	add    $0x200,%rax
    3fed:	48 39 c8             	cmp    %rcx,%rax
    3ff0:	75 ee                	jne    3fe0 <main+0x1970>
    3ff2:	48 8d 35 7a 45 00 00 	lea    0x457a(%rip),%rsi        # 8573 <_IO_stdin_used+0x573>
    3ff9:	bf 01 00 00 00       	mov    $0x1,%edi
    3ffe:	31 c0                	xor    %eax,%eax
    4000:	e8 ab e4 ff ff       	call   24b0 <__printf_chk@plt>
    4005:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    400a:	bf 01 00 00 00       	mov    $0x1,%edi
    400f:	48 8d 35 4a 48 00 00 	lea    0x484a(%rip),%rsi        # 8860 <_IO_stdin_used+0x860>
    4016:	48 8b 08             	mov    (%rax),%rcx
    4019:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    4023:	48 f7 e9             	imul   %rcx
    4026:	48 c1 f9 3f          	sar    $0x3f,%rcx
    402a:	31 c0                	xor    %eax,%eax
    402c:	48 d1 fa             	sar    %rdx
    402f:	48 29 ca             	sub    %rcx,%rdx
    4032:	e8 79 e4 ff ff       	call   24b0 <__printf_chk@plt>
    4037:	bf 0a 00 00 00       	mov    $0xa,%edi
    403c:	e8 cf e2 ff ff       	call   2310 <putchar@plt>
    4041:	45 8b 66 40          	mov    0x40(%r14),%r12d
    4045:	45 85 e4             	test   %r12d,%r12d
    4048:	0f 8e 47 01 00 00    	jle    4195 <main+0x1b25>
    404e:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    4053:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    4058:	31 d2                	xor    %edx,%edx
    405a:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    405f:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    4064:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    4069:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4070:	49 8b 46 38          	mov    0x38(%r14),%rax
    4074:	49 89 d1             	mov    %rdx,%r9
    4077:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    407c:	41 89 d5             	mov    %edx,%r13d
    407f:	49 c1 e1 09          	shl    $0x9,%r9
    4083:	45 31 e4             	xor    %r12d,%r12d
    4086:	4c 01 c8             	add    %r9,%rax
    4089:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    408e:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
    4095:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
    409c:	48 03 b8 80 01 00 00 	add    0x180(%rax),%rdi
    40a3:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    40a8:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    40ad:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    40b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    40b8:	8b 54 24 08          	mov    0x8(%rsp),%edx
    40bc:	45 89 e0             	mov    %r12d,%r8d
    40bf:	44 89 e9             	mov    %r13d,%ecx
    40c2:	bf 01 00 00 00       	mov    $0x1,%edi
    40c7:	48 8d 35 b2 44 00 00 	lea    0x44b2(%rip),%rsi        # 8580 <_IO_stdin_used+0x580>
    40ce:	31 c0                	xor    %eax,%eax
    40d0:	e8 db e3 ff ff       	call   24b0 <__printf_chk@plt>
    40d5:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    40da:	4c 89 e0             	mov    %r12,%rax
    40dd:	45 89 e0             	mov    %r12d,%r8d
    40e0:	49 8b 56 38          	mov    0x38(%r14),%rdx
    40e4:	48 c1 e0 08          	shl    $0x8,%rax
    40e8:	48 83 ec 08          	sub    $0x8,%rsp
    40ec:	49 83 c4 01          	add    $0x1,%r12
    40f0:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    40f8:	48 8b 38             	mov    (%rax),%rdi
    40fb:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    4102:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
    4109:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
    4110:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
    4117:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    411e:	bf 01 00 00 00       	mov    $0x1,%edi
    4123:	48 01 c3             	add    %rax,%rbx
    4126:	48 01 f0             	add    %rsi,%rax
    4129:	49 01 cf             	add    %rcx,%r15
    412c:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
    4130:	48 01 f3             	add    %rsi,%rbx
    4133:	50                   	push   %rax
    4134:	49 01 d7             	add    %rdx,%r15
    4137:	8b 54 24 18          	mov    0x18(%rsp),%edx
    413b:	44 89 e9             	mov    %r13d,%ecx
    413e:	48 8d 35 3b 47 00 00 	lea    0x473b(%rip),%rsi        # 8880 <_IO_stdin_used+0x880>
    4145:	31 c0                	xor    %eax,%eax
    4147:	e8 64 e3 ff ff       	call   24b0 <__printf_chk@plt>
    414c:	41 5a                	pop    %r10
    414e:	41 5b                	pop    %r11
    4150:	49 83 fc 06          	cmp    $0x6,%r12
    4154:	0f 85 5e ff ff ff    	jne    40b8 <main+0x1a48>
    415a:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    415f:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    4164:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    4169:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    416e:	48 83 c2 01          	add    $0x1,%rdx
    4172:	41 39 56 40          	cmp    %edx,0x40(%r14)
    4176:	0f 8f f4 fe ff ff    	jg     4070 <main+0x1a00>
    417c:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    4181:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    4186:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    418b:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    4190:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    4195:	45 31 ff             	xor    %r15d,%r15d
    4198:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    41a0:	4c 8d 25 f9 46 00 00 	lea    0x46f9(%rip),%r12        # 88a0 <_IO_stdin_used+0x8a0>
    41a7:	7e 5f                	jle    4208 <main+0x1b98>
    41a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    41b0:	49 8b 86 90 00 00 00 	mov    0x90(%r14),%rax
    41b7:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    41bb:	48 83 ec 08          	sub    $0x8,%rsp
    41bf:	bf 01 00 00 00       	mov    $0x1,%edi
    41c4:	49 83 c7 01          	add    $0x1,%r15
    41c8:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    41cc:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    41d0:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    41d4:	48 89 f0             	mov    %rsi,%rax
    41d7:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    41db:	4c 2b 01             	sub    (%rcx),%r8
    41de:	48 f7 e5             	mul    %rbp
    41e1:	8b 49 20             	mov    0x20(%rcx),%ecx
    41e4:	56                   	push   %rsi
    41e5:	31 c0                	xor    %eax,%eax
    41e7:	4c 89 e6             	mov    %r12,%rsi
    41ea:	48 c1 ea 12          	shr    $0x12,%rdx
    41ee:	49 89 d1             	mov    %rdx,%r9
    41f1:	ba 02 00 00 00       	mov    $0x2,%edx
    41f6:	e8 b5 e2 ff ff       	call   24b0 <__printf_chk@plt>
    41fb:	41 58                	pop    %r8
    41fd:	41 59                	pop    %r9
    41ff:	4d 39 be a0 00 00 00 	cmp    %r15,0xa0(%r14)
    4206:	7f a8                	jg     41b0 <main+0x1b40>
    4208:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    420f:	85 d2                	test   %edx,%edx
    4211:	0f 8e 0a 01 00 00    	jle    4321 <main+0x1cb1>
    4217:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
    421c:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4220:	45 31 ff             	xor    %r15d,%r15d
    4223:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    4228:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4230:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    4234:	44 89 fb             	mov    %r15d,%ebx
    4237:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    423f:	8b 30                	mov    (%rax),%esi
    4241:	85 f6                	test   %esi,%esi
    4243:	0f 8e c1 00 00 00    	jle    430a <main+0x1c9a>
    4249:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    424e:	31 d2                	xor    %edx,%edx
    4250:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4254:	49 89 f8             	mov    %rdi,%r8
    4257:	48 89 d7             	mov    %rdx,%rdi
    425a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4260:	49 89 fc             	mov    %rdi,%r12
    4263:	45 31 ff             	xor    %r15d,%r15d
    4266:	49 c1 e4 08          	shl    $0x8,%r12
    426a:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    426e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4274:	85 d2                	test   %edx,%edx
    4276:	7e 77                	jle    42ef <main+0x1c7f>
    4278:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    427d:	0f 1f 00             	nopl   (%rax)
    4280:	4c 89 f9             	mov    %r15,%rcx
    4283:	48 83 ec 08          	sub    $0x8,%rsp
    4287:	bf 01 00 00 00       	mov    $0x1,%edi
    428c:	49 83 c7 01          	add    $0x1,%r15
    4290:	48 c1 e1 05          	shl    $0x5,%rcx
    4294:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
    429b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    429f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    42a3:	48 89 f0             	mov    %rsi,%rax
    42a6:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    42aa:	4c 2b 01             	sub    (%rcx),%r8
    42ad:	56                   	push   %rsi
    42ae:	48 f7 e5             	mul    %rbp
    42b1:	89 d9                	mov    %ebx,%ecx
    42b3:	48 8d 35 36 46 00 00 	lea    0x4636(%rip),%rsi        # 88f0 <_IO_stdin_used+0x8f0>
    42ba:	31 c0                	xor    %eax,%eax
    42bc:	48 c1 ea 12          	shr    $0x12,%rdx
    42c0:	49 89 d1             	mov    %rdx,%r9
    42c3:	ba 02 00 00 00       	mov    $0x2,%edx
    42c8:	e8 e3 e1 ff ff       	call   24b0 <__printf_chk@plt>
    42cd:	4d 8b 46 50          	mov    0x50(%r14),%r8
    42d1:	5e                   	pop    %rsi
    42d2:	5f                   	pop    %rdi
    42d3:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    42d7:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    42db:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    42df:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    42e6:	7f 98                	jg     4280 <main+0x1c10>
    42e8:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    42ed:	8b 32                	mov    (%rdx),%esi
    42ef:	48 83 c7 01          	add    $0x1,%rdi
    42f3:	39 fe                	cmp    %edi,%esi
    42f5:	0f 8f 65 ff ff ff    	jg     4260 <main+0x1bf0>
    42fb:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    4300:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    4307:	4c 89 c7             	mov    %r8,%rdi
    430a:	49 83 c7 01          	add    $0x1,%r15
    430e:	44 39 fa             	cmp    %r15d,%edx
    4311:	0f 8f 19 ff ff ff    	jg     4230 <main+0x1bc0>
    4317:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    431c:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    4321:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    4327:	49 81 c6 f8 00 00 00 	add    $0xf8,%r14
    432e:	44 39 6c 24 48       	cmp    %r13d,0x48(%rsp)
    4333:	0f 85 17 fc ff ff    	jne    3f50 <main+0x18e0>
    4339:	48 83 84 24 90 00 00 00 30 	addq   $0x30,0x90(%rsp)
    4342:	44 8b 44 24 48       	mov    0x48(%rsp),%r8d
    4347:	48 81 84 24 d0 00 00 00 f0 01 00 00 	addq   $0x1f0,0xd0(%rsp)
    4353:	41 83 f8 05          	cmp    $0x5,%r8d
    4357:	74 08                	je     4361 <main+0x1cf1>
    4359:	45 89 c4             	mov    %r8d,%r12d
    435c:	e9 cd fb ff ff       	jmp    3f2e <main+0x18be>
    4361:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    4366:	bf 01 00 00 00       	mov    $0x1,%edi
    436b:	31 c0                	xor    %eax,%eax
    436d:	49 89 df             	mov    %rbx,%r15
    4370:	48 8d 35 19 42 00 00 	lea    0x4219(%rip),%rsi        # 8590 <_IO_stdin_used+0x590>
    4377:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4381:	4c 89 f2             	mov    %r14,%rdx
    4384:	e8 27 e1 ff ff       	call   24b0 <__printf_chk@plt>
    4389:	bf 0a 00 00 00       	mov    $0xa,%edi
    438e:	e8 7d df ff ff       	call   2310 <putchar@plt>
    4393:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
    439b:	48 8d 35 a6 45 00 00 	lea    0x45a6(%rip),%rsi        # 8948 <_IO_stdin_used+0x948>
    43a2:	31 c0                	xor    %eax,%eax
    43a4:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    43a8:	bf 01 00 00 00       	mov    $0x1,%edi
    43ad:	e8 fe e0 ff ff       	call   24b0 <__printf_chk@plt>
    43b2:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    43b7:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    43bc:	48 8d 35 ad 45 00 00 	lea    0x45ad(%rip),%rsi        # 8970 <_IO_stdin_used+0x970>
    43c3:	48 f7 eb             	imul   %rbx
    43c6:	48 c1 ff 3f          	sar    $0x3f,%rdi
    43ca:	31 c0                	xor    %eax,%eax
    43cc:	48 d1 fa             	sar    %rdx
    43cf:	48 29 fa             	sub    %rdi,%rdx
    43d2:	bf 01 00 00 00       	mov    $0x1,%edi
    43d7:	e8 d4 e0 ff ff       	call   24b0 <__printf_chk@plt>
    43dc:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    43e1:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    43e6:	48 8d 35 b3 45 00 00 	lea    0x45b3(%rip),%rsi        # 89a0 <_IO_stdin_used+0x9a0>
    43ed:	48 f7 eb             	imul   %rbx
    43f0:	48 c1 ff 3f          	sar    $0x3f,%rdi
    43f4:	31 c0                	xor    %eax,%eax
    43f6:	48 d1 fa             	sar    %rdx
    43f9:	48 29 fa             	sub    %rdi,%rdx
    43fc:	bf 01 00 00 00       	mov    $0x1,%edi
    4401:	e8 aa e0 ff ff       	call   24b0 <__printf_chk@plt>
    4406:	4c 89 f0             	mov    %r14,%rax
    4409:	bf 01 00 00 00       	mov    $0x1,%edi
    440e:	48 8d 35 bb 45 00 00 	lea    0x45bb(%rip),%rsi        # 89d0 <_IO_stdin_used+0x9d0>
    4415:	48 f7 eb             	imul   %rbx
    4418:	4c 89 f0             	mov    %r14,%rax
    441b:	48 c1 f8 3f          	sar    $0x3f,%rax
    441f:	48 d1 fa             	sar    %rdx
    4422:	48 29 c2             	sub    %rax,%rdx
    4425:	31 c0                	xor    %eax,%eax
    4427:	e8 84 e0 ff ff       	call   24b0 <__printf_chk@plt>
    442c:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4431:	bf 01 00 00 00       	mov    $0x1,%edi
    4436:	48 8d 35 67 41 00 00 	lea    0x4167(%rip),%rsi        # 85a4 <_IO_stdin_used+0x5a4>
    443d:	48 f7 eb             	imul   %rbx
    4440:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4445:	48 c1 f8 3f          	sar    $0x3f,%rax
    4449:	48 d1 fa             	sar    %rdx
    444c:	48 29 c2             	sub    %rax,%rdx
    444f:	31 c0                	xor    %eax,%eax
    4451:	48 89 d5             	mov    %rdx,%rbp
    4454:	e8 57 e0 ff ff       	call   24b0 <__printf_chk@plt>
    4459:	4c 89 f8             	mov    %r15,%rax
    445c:	bf 01 00 00 00       	mov    $0x1,%edi
    4461:	48 8d 35 88 45 00 00 	lea    0x4588(%rip),%rsi        # 89f0 <_IO_stdin_used+0x9f0>
    4468:	48 f7 eb             	imul   %rbx
    446b:	4c 89 f8             	mov    %r15,%rax
    446e:	48 c1 f8 3f          	sar    $0x3f,%rax
    4472:	48 89 d3             	mov    %rdx,%rbx
    4475:	48 d1 fb             	sar    %rbx
    4478:	48 29 c3             	sub    %rax,%rbx
    447b:	31 c0                	xor    %eax,%eax
    447d:	48 89 da             	mov    %rbx,%rdx
    4480:	48 29 eb             	sub    %rbp,%rbx
    4483:	e8 28 e0 ff ff       	call   24b0 <__printf_chk@plt>
    4488:	31 c0                	xor    %eax,%eax
    448a:	48 89 da             	mov    %rbx,%rdx
    448d:	bf 01 00 00 00       	mov    $0x1,%edi
    4492:	48 8d 35 27 41 00 00 	lea    0x4127(%rip),%rsi        # 85c0 <_IO_stdin_used+0x5c0>
    4499:	e8 12 e0 ff ff       	call   24b0 <__printf_chk@plt>
    449e:	48 8b 84 24 18 01 00 00 	mov    0x118(%rsp),%rax
    44a6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    44af:	75 25                	jne    44d6 <main+0x1e66>
    44b1:	48 81 c4 28 01 00 00 	add    $0x128,%rsp
    44b8:	31 c0                	xor    %eax,%eax
    44ba:	5b                   	pop    %rbx
    44bb:	5d                   	pop    %rbp
    44bc:	41 5c                	pop    %r12
    44be:	41 5d                	pop    %r13
    44c0:	41 5e                	pop    %r14
    44c2:	41 5f                	pop    %r15
    44c4:	c3                   	ret
    44c5:	31 d2                	xor    %edx,%edx
    44c7:	e9 ee fa ff ff       	jmp    3fba <main+0x194a>
    44cc:	bf 01 00 00 00       	mov    $0x1,%edi
    44d1:	e8 3a e0 ff ff       	call   2510 <exit@plt>
    44d6:	e8 a5 de ff ff       	call   2380 <__stack_chk_fail@plt>
    44db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000044e0 <_start>:
    44e0:	f3 0f 1e fa          	endbr64
    44e4:	31 ed                	xor    %ebp,%ebp
    44e6:	49 89 d1             	mov    %rdx,%r9
    44e9:	5e                   	pop    %rsi
    44ea:	48 89 e2             	mov    %rsp,%rdx
    44ed:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    44f1:	50                   	push   %rax
    44f2:	54                   	push   %rsp
    44f3:	45 31 c0             	xor    %r8d,%r8d
    44f6:	31 c9                	xor    %ecx,%ecx
    44f8:	48 8d 3d 71 e1 ff ff 	lea    -0x1e8f(%rip),%rdi        # 2670 <main>
    44ff:	ff 15 d3 6a 00 00    	call   *0x6ad3(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    4505:	f4                   	hlt
    4506:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004510 <deregister_tm_clones>:
    4510:	48 8d 3d 09 6b 00 00 	lea    0x6b09(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4517:	48 8d 05 02 6b 00 00 	lea    0x6b02(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    451e:	48 39 f8             	cmp    %rdi,%rax
    4521:	74 15                	je     4538 <deregister_tm_clones+0x28>
    4523:	48 8b 05 b6 6a 00 00 	mov    0x6ab6(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    452a:	48 85 c0             	test   %rax,%rax
    452d:	74 09                	je     4538 <deregister_tm_clones+0x28>
    452f:	ff e0                	jmp    *%rax
    4531:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4538:	c3                   	ret
    4539:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004540 <register_tm_clones>:
    4540:	48 8d 3d d9 6a 00 00 	lea    0x6ad9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4547:	48 8d 35 d2 6a 00 00 	lea    0x6ad2(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    454e:	48 29 fe             	sub    %rdi,%rsi
    4551:	48 89 f0             	mov    %rsi,%rax
    4554:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4558:	48 c1 f8 03          	sar    $0x3,%rax
    455c:	48 01 c6             	add    %rax,%rsi
    455f:	48 d1 fe             	sar    %rsi
    4562:	74 14                	je     4578 <register_tm_clones+0x38>
    4564:	48 8b 05 85 6a 00 00 	mov    0x6a85(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    456b:	48 85 c0             	test   %rax,%rax
    456e:	74 08                	je     4578 <register_tm_clones+0x38>
    4570:	ff e0                	jmp    *%rax
    4572:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4578:	c3                   	ret
    4579:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004580 <__do_global_dtors_aux>:
    4580:	f3 0f 1e fa          	endbr64
    4584:	80 3d 9d 6a 00 00 00 	cmpb   $0x0,0x6a9d(%rip)        # b028 <completed.0>
    458b:	75 2b                	jne    45b8 <__do_global_dtors_aux+0x38>
    458d:	55                   	push   %rbp
    458e:	48 83 3d 62 6a 00 00 00 	cmpq   $0x0,0x6a62(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    4596:	48 89 e5             	mov    %rsp,%rbp
    4599:	74 0c                	je     45a7 <__do_global_dtors_aux+0x27>
    459b:	48 8b 3d 66 6a 00 00 	mov    0x6a66(%rip),%rdi        # b008 <__dso_handle>
    45a2:	e8 49 dd ff ff       	call   22f0 <__cxa_finalize@plt>
    45a7:	e8 64 ff ff ff       	call   4510 <deregister_tm_clones>
    45ac:	c6 05 75 6a 00 00 01 	movb   $0x1,0x6a75(%rip)        # b028 <completed.0>
    45b3:	5d                   	pop    %rbp
    45b4:	c3                   	ret
    45b5:	0f 1f 00             	nopl   (%rax)
    45b8:	c3                   	ret
    45b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000045c0 <frame_dummy>:
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	e9 77 ff ff ff       	jmp    4540 <register_tm_clones>
    45c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000045d0 <do_protected_write>:
    45d0:	f3 0f 1e fa          	endbr64
    45d4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    45db:	48 8b 40 48          	mov    0x48(%rax),%rax
    45df:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
    45e7:	48 8b 48 08          	mov    0x8(%rax),%rcx
    45eb:	48 83 00 01          	addq   $0x1,(%rax)
    45ef:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    45f6:	48 85 c9             	test   %rcx,%rcx
    45f9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4600:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4604:	48 89 50 08          	mov    %rdx,0x8(%rax)
    4608:	31 c0                	xor    %eax,%eax
    460a:	c3                   	ret
    460b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004610 <barriered_reset>:
    4610:	f3 0f 1e fa          	endbr64
    4614:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    461b:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    4622:	85 c9                	test   %ecx,%ecx
    4624:	7e 48                	jle    466e <barriered_reset+0x5e>
    4626:	48 63 97 30 01 00 00 	movslq 0x130(%rdi),%rdx
    462d:	49 8b 40 18          	mov    0x18(%r8),%rax
    4631:	48 c1 e1 09          	shl    $0x9,%rcx
    4635:	49 8b 70 38          	mov    0x38(%r8),%rsi
    4639:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    463d:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4641:	31 c0                	xor    %eax,%eax
    4643:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4648:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
    4650:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
    4658:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    4663:	48 05 00 02 00 00    	add    $0x200,%rax
    4669:	48 39 c1             	cmp    %rax,%rcx
    466c:	75 da                	jne    4648 <barriered_reset+0x38>
    466e:	49 8b 88 f0 00 00 00 	mov    0xf0(%r8),%rcx
    4675:	8b 01                	mov    (%rcx),%eax
    4677:	83 f8 ff             	cmp    $0xffffffff,%eax
    467a:	74 0e                	je     468a <barriered_reset+0x7a>
    467c:	41 8b b8 c0 00 00 00 	mov    0xc0(%r8),%edi
    4683:	8d 57 ff             	lea    -0x1(%rdi),%edx
    4686:	39 d0                	cmp    %edx,%eax
    4688:	74 06                	je     4690 <barriered_reset+0x80>
    468a:	0f ae f8             	sfence
    468d:	31 c0                	xor    %eax,%eax
    468f:	c3                   	ret
    4690:	41 83 78 04 01       	cmpl   $0x1,0x4(%r8)
    4695:	75 f3                	jne    468a <barriered_reset+0x7a>
    4697:	49 8b 80 d8 00 00 00 	mov    0xd8(%r8),%rax
    469e:	83 00 01             	addl   $0x1,(%rax)
    46a1:	c7 01 ff ff ff ff    	movl   $0xffffffff,(%rcx)
    46a7:	eb e1                	jmp    468a <barriered_reset+0x7a>
    46a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000046b0 <external_thread>:
    46b0:	f3 0f 1e fa          	endbr64
    46b4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    46b8:	0f 85 fb 00 00 00    	jne    47b9 <external_thread+0x109>
    46be:	41 57                	push   %r15
    46c0:	49 89 ff             	mov    %rdi,%r15
    46c3:	41 56                	push   %r14
    46c5:	41 55                	push   %r13
    46c7:	4c 8d 2d 36 39 00 00 	lea    0x3936(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
    46ce:	41 54                	push   %r12
    46d0:	55                   	push   %rbp
    46d1:	53                   	push   %rbx
    46d2:	48 83 ec 08          	sub    $0x8,%rsp
    46d6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    46dc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    46e0:	85 c9                	test   %ecx,%ecx
    46e2:	7e 6e                	jle    4752 <external_thread+0xa2>
    46e4:	45 31 e4             	xor    %r12d,%r12d
    46e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    46f0:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    46f8:	31 db                	xor    %ebx,%ebx
    46fa:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    46fe:	48 8b 06             	mov    (%rsi),%rax
    4701:	8b 10                	mov    (%rax),%edx
    4703:	85 d2                	test   %edx,%edx
    4705:	7e 2a                	jle    4731 <external_thread+0x81>
    4707:	48 8b 48 08          	mov    0x8(%rax),%rcx
    470b:	48 89 dd             	mov    %rbx,%rbp
    470e:	48 c1 e5 08          	shl    $0x8,%rbp
    4712:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4716:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    471d:	45 85 c0             	test   %r8d,%r8d
    4720:	74 36                	je     4758 <external_thread+0xa8>
    4722:	48 83 c3 01          	add    $0x1,%rbx
    4726:	39 da                	cmp    %ebx,%edx
    4728:	7f e1                	jg     470b <external_thread+0x5b>
    472a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4731:	49 83 c4 01          	add    $0x1,%r12
    4735:	44 39 e1             	cmp    %r12d,%ecx
    4738:	7f b6                	jg     46f0 <external_thread+0x40>
    473a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    473f:	74 9f                	je     46e0 <external_thread+0x30>
    4741:	48 83 c4 08          	add    $0x8,%rsp
    4745:	31 c0                	xor    %eax,%eax
    4747:	5b                   	pop    %rbx
    4748:	5d                   	pop    %rbp
    4749:	41 5c                	pop    %r12
    474b:	41 5d                	pop    %r13
    474d:	41 5e                	pop    %r14
    474f:	41 5f                	pop    %r15
    4751:	c3                   	ret
    4752:	eb fe                	jmp    4752 <external_thread+0xa2>
    4754:	0f 1f 40 00          	nopl   0x0(%rax)
    4758:	4c 89 28             	mov    %r13,(%rax)
    475b:	48 8b 06             	mov    (%rsi),%rax
    475e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4762:	48 01 ef             	add    %rbp,%rdi
    4765:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    476c:	48 c1 e6 05          	shl    $0x5,%rsi
    4770:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4777:	bf 04 00 00 00       	mov    $0x4,%edi
    477c:	e8 cf db ff ff       	call   2350 <clock_gettime@plt>
    4781:	49 8b 47 50          	mov    0x50(%r15),%rax
    4785:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    4789:	48 8b 40 08          	mov    0x8(%rax),%rax
    478d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
    4798:	0f ae f8             	sfence
    479b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    479f:	48 83 c3 01          	add    $0x1,%rbx
    47a3:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    47a7:	48 8b 06             	mov    (%rsi),%rax
    47aa:	8b 10                	mov    (%rax),%edx
    47ac:	39 da                	cmp    %ebx,%edx
    47ae:	0f 8f 53 ff ff ff    	jg     4707 <external_thread+0x57>
    47b4:	e9 71 ff ff ff       	jmp    472a <external_thread+0x7a>
    47b9:	31 c0                	xor    %eax,%eax
    47bb:	c3                   	ret
    47bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000047c0 <timer_thread>:
    47c0:	f3 0f 1e fa          	endbr64
    47c4:	41 57                	push   %r15
    47c6:	48 8d 35 43 38 00 00 	lea    0x3843(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    47cd:	49 89 ff             	mov    %rdi,%r15
    47d0:	41 56                	push   %r14
    47d2:	41 55                	push   %r13
    47d4:	41 54                	push   %r12
    47d6:	55                   	push   %rbp
    47d7:	53                   	push   %rbx
    47d8:	48 83 ec 58          	sub    $0x58,%rsp
    47dc:	8b 57 04             	mov    0x4(%rdi),%edx
    47df:	bf 01 00 00 00       	mov    $0x1,%edi
    47e4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    47ed:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    47f2:	31 c0                	xor    %eax,%eax
    47f4:	e8 b7 dc ff ff       	call   24b0 <__printf_chk@plt>
    47f9:	66 0f 6f 05 0f 44 00 00 	movdqa 0x440f(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4801:	ba 88 13 00 00       	mov    $0x1388,%edx
    4806:	31 c0                	xor    %eax,%eax
    4808:	48 8d 35 13 38 00 00 	lea    0x3813(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    480f:	bf 01 00 00 00       	mov    $0x1,%edi
    4814:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4819:	e8 92 dc ff ff       	call   24b0 <__printf_chk@plt>
    481e:	41 8b 47 44          	mov    0x44(%r15),%eax
    4822:	89 c3                	mov    %eax,%ebx
    4824:	85 c0                	test   %eax,%eax
    4826:	0f 84 9a 00 00 00    	je     48c6 <timer_thread+0x106>
    482c:	45 31 f6             	xor    %r14d,%r14d
    482f:	31 db                	xor    %ebx,%ebx
    4831:	49 89 e5             	mov    %rsp,%r13
    4834:	31 ed                	xor    %ebp,%ebp
    4836:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    483b:	4c 89 e7             	mov    %r12,%rdi
    483e:	4c 89 ee             	mov    %r13,%rsi
    4841:	41 83 c6 01          	add    $0x1,%r14d
    4845:	e8 56 db ff ff       	call   23a0 <nanosleep@plt>
    484a:	49 63 47 30          	movslq 0x30(%r15),%rax
    484e:	8d 7b 01             	lea    0x1(%rbx),%edi
    4851:	85 c0                	test   %eax,%eax
    4853:	7e 4a                	jle    489f <timer_thread+0xdf>
    4855:	49 8b 4f 18          	mov    0x18(%r15),%rcx
    4859:	4c 63 c3             	movslq %ebx,%r8
    485c:	49 c1 e0 09          	shl    $0x9,%r8
    4860:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4864:	0f 1f 40 00          	nopl   0x0(%rax)
    4868:	48 8b 19             	mov    (%rcx),%rbx
    486b:	89 f8                	mov    %edi,%eax
    486d:	48 83 c1 08          	add    $0x8,%rcx
    4871:	99                   	cltd
    4872:	f7 7b 40             	idivl  0x40(%rbx)
    4875:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4879:	83 ea 01             	sub    $0x1,%edx
    487c:	48 63 d2             	movslq %edx,%rdx
    487f:	48 c1 e2 09          	shl    $0x9,%rdx
    4883:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    488e:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    489a:	49 39 c9             	cmp    %rcx,%r9
    489d:	75 c9                	jne    4868 <timer_thread+0xa8>
    489f:	0f ae f0             	mfence
    48a2:	49 8b 47 18          	mov    0x18(%r15),%rax
    48a6:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    48aa:	89 fb                	mov    %edi,%ebx
    48ac:	48 8b 00             	mov    (%rax),%rax
    48af:	39 78 40             	cmp    %edi,0x40(%rax)
    48b2:	0f 4e dd             	cmovle %ebp,%ebx
    48b5:	85 c9                	test   %ecx,%ecx
    48b7:	74 0d                	je     48c6 <timer_thread+0x106>
    48b9:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    48c0:	0f 85 75 ff ff ff    	jne    483b <timer_thread+0x7b>
    48c6:	48 8d 3d 6b 37 00 00 	lea    0x376b(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    48cd:	e8 5e da ff ff       	call   2330 <puts@plt>
    48d2:	49 63 57 30          	movslq 0x30(%r15),%rdx
    48d6:	85 d2                	test   %edx,%edx
    48d8:	7e 6b                	jle    4945 <timer_thread+0x185>
    48da:	49 63 47 40          	movslq 0x40(%r15),%rax
    48de:	85 c0                	test   %eax,%eax
    48e0:	7e 63                	jle    4945 <timer_thread+0x185>
    48e2:	48 c1 e0 09          	shl    $0x9,%rax
    48e6:	4d 8b 47 18          	mov    0x18(%r15),%r8
    48ea:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    48f2:	31 c9                	xor    %ecx,%ecx
    48f4:	48 89 c6             	mov    %rax,%rsi
    48f7:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    48fb:	48 8b 40 38          	mov    0x38(%rax),%rax
    48ff:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4903:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4909:	74 15                	je     4920 <timer_thread+0x160>
    490b:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    4915:	48 05 00 02 00 00    	add    $0x200,%rax
    491b:	48 39 c2             	cmp    %rax,%rdx
    491e:	74 1c                	je     493c <timer_thread+0x17c>
    4920:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    492a:	48 05 00 04 00 00    	add    $0x400,%rax
    4930:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    4937:	48 39 c2             	cmp    %rax,%rdx
    493a:	75 e4                	jne    4920 <timer_thread+0x160>
    493c:	48 83 c1 08          	add    $0x8,%rcx
    4940:	48 39 cf             	cmp    %rcx,%rdi
    4943:	75 b2                	jne    48f7 <timer_thread+0x137>
    4945:	0f ae f0             	mfence
    4948:	66 0f 6f 05 d0 42 00 00 	movdqa 0x42d0(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4950:	41 89 dc             	mov    %ebx,%r12d
    4953:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    4958:	49 63 47 28          	movslq 0x28(%r15),%rax
    495c:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    4961:	85 c0                	test   %eax,%eax
    4963:	7e 46                	jle    49ab <timer_thread+0x1eb>
    4965:	49 8b 4f 18          	mov    0x18(%r15),%rcx
    4969:	49 63 ec             	movslq %r12d,%rbp
    496c:	48 c1 e5 09          	shl    $0x9,%rbp
    4970:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4974:	0f 1f 40 00          	nopl   0x0(%rax)
    4978:	48 8b 19             	mov    (%rcx),%rbx
    497b:	89 f8                	mov    %edi,%eax
    497d:	48 83 c1 08          	add    $0x8,%rcx
    4981:	99                   	cltd
    4982:	f7 7b 40             	idivl  0x40(%rbx)
    4985:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4989:	48 63 d2             	movslq %edx,%rdx
    498c:	48 c1 e2 09          	shl    $0x9,%rdx
    4990:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    499b:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    49a6:	49 39 c8             	cmp    %rcx,%r8
    49a9:	75 cd                	jne    4978 <timer_thread+0x1b8>
    49ab:	0f ae f0             	mfence
    49ae:	49 8b 77 18          	mov    0x18(%r15),%rsi
    49b2:	45 31 e4             	xor    %r12d,%r12d
    49b5:	48 8b 06             	mov    (%rsi),%rax
    49b8:	39 78 40             	cmp    %edi,0x40(%rax)
    49bb:	44 0f 4f e7          	cmovg  %edi,%r12d
    49bf:	41 8b 7f 30          	mov    0x30(%r15),%edi
    49c3:	85 ff                	test   %edi,%edi
    49c5:	0f 8e a9 01 00 00    	jle    4b74 <timer_thread+0x3b4>
    49cb:	45 31 f6             	xor    %r14d,%r14d
    49ce:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    49d4:	4c 89 f5             	mov    %r14,%rbp
    49d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    49e0:	89 eb                	mov    %ebp,%ebx
    49e2:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    49ea:	45 31 f6             	xor    %r14d,%r14d
    49ed:	85 ff                	test   %edi,%edi
    49ef:	7e 77                	jle    4a68 <timer_thread+0x2a8>
    49f1:	4c 89 f6             	mov    %r14,%rsi
    49f4:	48 63 cf             	movslq %edi,%rcx
    49f7:	45 31 c0             	xor    %r8d,%r8d
    49fa:	48 c1 e6 09          	shl    $0x9,%rsi
    49fe:	66 90                	xchg   %ax,%ax
    4a00:	41 39 e8             	cmp    %ebp,%r8d
    4a03:	74 45                	je     4a4a <timer_thread+0x28a>
    4a05:	49 8b 47 18          	mov    0x18(%r15),%rax
    4a09:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    4a0d:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4a11:	4c 89 c0             	mov    %r8,%rax
    4a14:	48 c1 e0 08          	shl    $0x8,%rax
    4a18:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4a20:	48 8b 10             	mov    (%rax),%rdx
    4a23:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    4a2a:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4a31:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4a38:	4d 85 c9             	test   %r9,%r9
    4a3b:	0f 8f 97 00 00 00    	jg     4ad8 <timer_thread+0x318>
    4a41:	4d 85 db             	test   %r11,%r11
    4a44:	0f 8f 8e 00 00 00    	jg     4ad8 <timer_thread+0x318>
    4a4a:	49 83 c0 01          	add    $0x1,%r8
    4a4e:	4c 39 c1             	cmp    %r8,%rcx
    4a51:	75 ad                	jne    4a00 <timer_thread+0x240>
    4a53:	49 83 fe 01          	cmp    $0x1,%r14
    4a57:	74 0f                	je     4a68 <timer_thread+0x2a8>
    4a59:	41 be 01 00 00 00    	mov    $0x1,%r14d
    4a5f:	85 ff                	test   %edi,%edi
    4a61:	7f 8e                	jg     49f1 <timer_thread+0x231>
    4a63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4a68:	48 83 c5 01          	add    $0x1,%rbp
    4a6c:	39 ef                	cmp    %ebp,%edi
    4a6e:	0f 8f 6c ff ff ff    	jg     49e0 <timer_thread+0x220>
    4a74:	44 89 d5             	mov    %r10d,%ebp
    4a77:	85 ff                	test   %edi,%edi
    4a79:	7e 3b                	jle    4ab6 <timer_thread+0x2f6>
    4a7b:	31 db                	xor    %ebx,%ebx
    4a7d:	bf 01 00 00 00       	mov    $0x1,%edi
    4a82:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4a86:	41 8b 57 40          	mov    0x40(%r15),%edx
    4a8a:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4a8e:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a92:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    4a98:	39 d1                	cmp    %edx,%ecx
    4a9a:	0f 8c a8 00 00 00    	jl     4b48 <timer_thread+0x388>
    4aa0:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    4aa6:	39 d0                	cmp    %edx,%eax
    4aa8:	7c 6e                	jl     4b18 <timer_thread+0x358>
    4aaa:	48 83 c3 01          	add    $0x1,%rbx
    4aae:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4ab2:	7f d6                	jg     4a8a <timer_thread+0x2ca>
    4ab4:	21 fd                	and    %edi,%ebp
    4ab6:	85 ed                	test   %ebp,%ebp
    4ab8:	0f 85 b6 00 00 00    	jne    4b74 <timer_thread+0x3b4>
    4abe:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4ac3:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4ac8:	e8 d3 d8 ff ff       	call   23a0 <nanosleep@plt>
    4acd:	e9 86 fe ff ff       	jmp    4958 <timer_thread+0x198>
    4ad2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4ad8:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    4ade:	48 83 ec 08          	sub    $0x8,%rsp
    4ae2:	bf 01 00 00 00       	mov    $0x1,%edi
    4ae7:	44 89 f1             	mov    %r14d,%ecx
    4aea:	48 8d 35 6c 35 00 00 	lea    0x356c(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    4af1:	50                   	push   %rax
    4af2:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    4af8:	89 da                	mov    %ebx,%edx
    4afa:	50                   	push   %rax
    4afb:	31 c0                	xor    %eax,%eax
    4afd:	41 53                	push   %r11
    4aff:	e8 ac d9 ff ff       	call   24b0 <__printf_chk@plt>
    4b04:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4b08:	48 83 c4 20          	add    $0x20,%rsp
    4b0c:	45 31 d2             	xor    %r10d,%r10d
    4b0f:	e9 3f ff ff ff       	jmp    4a53 <timer_thread+0x293>
    4b14:	0f 1f 40 00          	nopl   0x0(%rax)
    4b18:	89 c2                	mov    %eax,%edx
    4b1a:	bf 01 00 00 00       	mov    $0x1,%edi
    4b1f:	31 c0                	xor    %eax,%eax
    4b21:	48 83 c3 01          	add    $0x1,%rbx
    4b25:	48 8d 35 f3 37 00 00 	lea    0x37f3(%rip),%rsi        # 831f <_IO_stdin_used+0x31f>
    4b2c:	e8 7f d9 ff ff       	call   24b0 <__printf_chk@plt>
    4b31:	31 ff                	xor    %edi,%edi
    4b33:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4b37:	0f 8f 45 ff ff ff    	jg     4a82 <timer_thread+0x2c2>
    4b3d:	e9 72 ff ff ff       	jmp    4ab4 <timer_thread+0x2f4>
    4b42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b48:	89 ca                	mov    %ecx,%edx
    4b4a:	48 8d 35 ce 37 00 00 	lea    0x37ce(%rip),%rsi        # 831f <_IO_stdin_used+0x31f>
    4b51:	bf 01 00 00 00       	mov    $0x1,%edi
    4b56:	31 c0                	xor    %eax,%eax
    4b58:	e8 53 d9 ff ff       	call   24b0 <__printf_chk@plt>
    4b5d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4b61:	41 8b 57 40          	mov    0x40(%r15),%edx
    4b65:	31 ff                	xor    %edi,%edi
    4b67:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4b6b:	48 8b 40 38          	mov    0x38(%rax),%rax
    4b6f:	e9 2c ff ff ff       	jmp    4aa0 <timer_thread+0x2e0>
    4b74:	48 8d 3d d9 34 00 00 	lea    0x34d9(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4b7b:	e8 b0 d7 ff ff       	call   2330 <puts@plt>
    4b80:	41 8b 57 44          	mov    0x44(%r15),%edx
    4b84:	85 d2                	test   %edx,%edx
    4b86:	0f 84 eb 00 00 00    	je     4c77 <timer_thread+0x4b7>
    4b8c:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4b90:	31 db                	xor    %ebx,%ebx
    4b92:	48 8d 2d e1 34 00 00 	lea    0x34e1(%rip),%rbp        # 807a <_IO_stdin_used+0x7a>
    4b99:	4c 8d 25 f5 34 00 00 	lea    0x34f5(%rip),%r12        # 8095 <_IO_stdin_used+0x95>
    4ba0:	85 c0                	test   %eax,%eax
    4ba2:	7e 38                	jle    4bdc <timer_thread+0x41c>
    4ba4:	0f 1f 40 00          	nopl   0x0(%rax)
    4ba8:	31 c0                	xor    %eax,%eax
    4baa:	89 da                	mov    %ebx,%edx
    4bac:	48 89 ee             	mov    %rbp,%rsi
    4baf:	bf 01 00 00 00       	mov    $0x1,%edi
    4bb4:	e8 f7 d8 ff ff       	call   24b0 <__printf_chk@plt>
    4bb9:	49 8b 47 18          	mov    0x18(%r15),%rax
    4bbd:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4bc1:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
    4bc5:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
    4bcc:	0f 84 d2 00 00 00    	je     4ca4 <timer_thread+0x4e4>
    4bd2:	48 83 c3 01          	add    $0x1,%rbx
    4bd6:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4bda:	7f cc                	jg     4ba8 <timer_thread+0x3e8>
    4bdc:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4be0:	85 d2                	test   %edx,%edx
    4be2:	7e 7c                	jle    4c60 <timer_thread+0x4a0>
    4be4:	41 8b 47 40          	mov    0x40(%r15),%eax
    4be8:	85 c0                	test   %eax,%eax
    4bea:	7e 74                	jle    4c60 <timer_thread+0x4a0>
    4bec:	48 63 f0             	movslq %eax,%rsi
    4bef:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4bf3:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4bfb:	31 c9                	xor    %ecx,%ecx
    4bfd:	48 c1 e6 09          	shl    $0x9,%rsi
    4c01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c08:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4c0c:	48 8b 40 38          	mov    0x38(%rax),%rax
    4c10:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4c14:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4c1a:	74 1c                	je     4c38 <timer_thread+0x478>
    4c1c:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4c26:	48 05 00 02 00 00    	add    $0x200,%rax
    4c2c:	48 39 d0             	cmp    %rdx,%rax
    4c2f:	74 26                	je     4c57 <timer_thread+0x497>
    4c31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c38:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4c42:	48 05 00 04 00 00    	add    $0x400,%rax
    4c48:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
    4c52:	48 39 d0             	cmp    %rdx,%rax
    4c55:	75 e1                	jne    4c38 <timer_thread+0x478>
    4c57:	48 83 c1 08          	add    $0x8,%rcx
    4c5b:	48 39 cf             	cmp    %rcx,%rdi
    4c5e:	75 a8                	jne    4c08 <timer_thread+0x448>
    4c60:	0f ae f0             	mfence
    4c63:	48 8d 3d 3d 34 00 00 	lea    0x343d(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4c6a:	e8 c1 d6 ff ff       	call   2330 <puts@plt>
    4c6f:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4c77:	48 8d 3d 30 34 00 00 	lea    0x3430(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4c7e:	e8 ad d6 ff ff       	call   2330 <puts@plt>
    4c83:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4c88:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4c91:	75 41                	jne    4cd4 <timer_thread+0x514>
    4c93:	48 83 c4 58          	add    $0x58,%rsp
    4c97:	31 c0                	xor    %eax,%eax
    4c99:	5b                   	pop    %rbx
    4c9a:	5d                   	pop    %rbp
    4c9b:	41 5c                	pop    %r12
    4c9d:	41 5d                	pop    %r13
    4c9f:	41 5e                	pop    %r14
    4ca1:	41 5f                	pop    %r15
    4ca3:	c3                   	ret
    4ca4:	4c 89 e7             	mov    %r12,%rdi
    4ca7:	e8 84 d6 ff ff       	call   2330 <puts@plt>
    4cac:	49 8b 47 18          	mov    0x18(%r15),%rax
    4cb0:	be 01 00 00 00       	mov    $0x1,%esi
    4cb5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4cb9:	48 83 c3 01          	add    $0x1,%rbx
    4cbd:	8b 78 60             	mov    0x60(%rax),%edi
    4cc0:	e8 9b d7 ff ff       	call   2460 <eventfd_write@plt>
    4cc5:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4cc9:	0f 8f d9 fe ff ff    	jg     4ba8 <timer_thread+0x3e8>
    4ccf:	e9 08 ff ff ff       	jmp    4bdc <timer_thread+0x41c>
    4cd4:	e8 a7 d6 ff ff       	call   2380 <__stack_chk_fail@plt>
    4cd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004ce0 <minf>:
    4ce0:	f3 0f 1e fa          	endbr64
    4ce4:	39 f7                	cmp    %esi,%edi
    4ce6:	89 f0                	mov    %esi,%eax
    4ce8:	0f 4e c7             	cmovle %edi,%eax
    4ceb:	c3                   	ret
    4cec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004cf0 <maxf>:
    4cf0:	f3 0f 1e fa          	endbr64
    4cf4:	39 f7                	cmp    %esi,%edi
    4cf6:	89 f0                	mov    %esi,%eax
    4cf8:	0f 4d c7             	cmovge %edi,%eax
    4cfb:	c3                   	ret
    4cfc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004d00 <strtolower>:
    4d00:	f3 0f 1e fa          	endbr64
    4d04:	55                   	push   %rbp
    4d05:	53                   	push   %rbx
    4d06:	48 83 ec 08          	sub    $0x8,%rsp
    4d0a:	48 0f be 1f          	movsbq (%rdi),%rbx
    4d0e:	84 db                	test   %bl,%bl
    4d10:	74 24                	je     4d36 <strtolower+0x36>
    4d12:	48 89 fd             	mov    %rdi,%rbp
    4d15:	e8 76 d8 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4d1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d20:	48 8b 10             	mov    (%rax),%rdx
    4d23:	48 83 c5 01          	add    $0x1,%rbp
    4d27:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4d2a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    4d2d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4d32:	84 db                	test   %bl,%bl
    4d34:	75 ea                	jne    4d20 <strtolower+0x20>
    4d36:	48 83 c4 08          	add    $0x8,%rsp
    4d3a:	5b                   	pop    %rbx
    4d3b:	5d                   	pop    %rbp
    4d3c:	c3                   	ret
    4d3d:	0f 1f 00             	nopl   (%rax)

0000000000004d40 <zh_malloc>:
    4d40:	f3 0f 1e fa          	endbr64
    4d44:	48 83 ec 08          	sub    $0x8,%rsp
    4d48:	e8 23 d7 ff ff       	call   2470 <malloc@plt>
    4d4d:	48 85 c0             	test   %rax,%rax
    4d50:	74 05                	je     4d57 <zh_malloc+0x17>
    4d52:	48 83 c4 08          	add    $0x8,%rsp
    4d56:	c3                   	ret
    4d57:	48 8b 0d c2 62 00 00 	mov    0x62c2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4d5e:	ba 28 00 00 00       	mov    $0x28,%edx
    4d63:	be 01 00 00 00       	mov    $0x1,%esi
    4d68:	48 8d 3d 61 38 00 00 	lea    0x3861(%rip),%rdi        # 85d0 <_IO_stdin_used+0x5d0>
    4d6f:	e8 bc d7 ff ff       	call   2530 <fwrite@plt>
    4d74:	bf 01 00 00 00       	mov    $0x1,%edi
    4d79:	e8 92 d7 ff ff       	call   2510 <exit@plt>
    4d7e:	66 90                	xchg   %ax,%ax

0000000000004d80 <get_filename_ext>:
    4d80:	f3 0f 1e fa          	endbr64
    4d84:	53                   	push   %rbx
    4d85:	be 2e 00 00 00       	mov    $0x2e,%esi
    4d8a:	48 89 fb             	mov    %rdi,%rbx
    4d8d:	e8 1e d6 ff ff       	call   23b0 <strrchr@plt>
    4d92:	48 85 c0             	test   %rax,%rax
    4d95:	74 11                	je     4da8 <get_filename_ext+0x28>
    4d97:	48 39 c3             	cmp    %rax,%rbx
    4d9a:	74 0c                	je     4da8 <get_filename_ext+0x28>
    4d9c:	48 83 c0 01          	add    $0x1,%rax
    4da0:	5b                   	pop    %rbx
    4da1:	c3                   	ret
    4da2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4da8:	48 8d 05 47 33 00 00 	lea    0x3347(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
    4daf:	5b                   	pop    %rbx
    4db0:	c3                   	ret
    4db1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4dbc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004dc0 <send_headers>:
    4dc0:	f3 0f 1e fa          	endbr64
    4dc4:	41 55                	push   %r13
    4dc6:	49 89 f5             	mov    %rsi,%r13
    4dc9:	48 89 fe             	mov    %rdi,%rsi
    4dcc:	41 54                	push   %r12
    4dce:	55                   	push   %rbp
    4dcf:	48 89 d5             	mov    %rdx,%rbp
    4dd2:	ba 00 04 00 00       	mov    $0x400,%edx
    4dd7:	53                   	push   %rbx
    4dd8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4ddf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4de8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4df0:	31 c0                	xor    %eax,%eax
    4df2:	49 89 e4             	mov    %rsp,%r12
    4df5:	4c 89 e7             	mov    %r12,%rdi
    4df8:	e8 93 d6 ff ff       	call   2490 <__strcpy_chk@plt>
    4dfd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4e02:	84 db                	test   %bl,%bl
    4e04:	74 24                	je     4e2a <send_headers+0x6a>
    4e06:	e8 85 d7 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4e0b:	48 8b 08             	mov    (%rax),%rcx
    4e0e:	4c 89 e0             	mov    %r12,%rax
    4e11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4e18:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    4e1b:	48 83 c0 01          	add    $0x1,%rax
    4e1f:	88 50 ff             	mov    %dl,-0x1(%rax)
    4e22:	48 0f be 18          	movsbq (%rax),%rbx
    4e26:	84 db                	test   %bl,%bl
    4e28:	75 ee                	jne    4e18 <send_headers+0x58>
    4e2a:	bf 11 00 00 00       	mov    $0x11,%edi
    4e2f:	e8 3c d6 ff ff       	call   2470 <malloc@plt>
    4e34:	48 85 c0             	test   %rax,%rax
    4e37:	0f 84 7e 04 00 00    	je     52bb <send_headers+0x4fb>
    4e3d:	66 0f 6f 05 eb 3d 00 00 	movdqa 0x3deb(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4e45:	48 89 45 00          	mov    %rax,0x0(%rbp)
    4e49:	bf 17 00 00 00       	mov    $0x17,%edi
    4e4e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4e56:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4e5a:	0f 11 00             	movups %xmm0,(%rax)
    4e5d:	e8 0e d6 ff ff       	call   2470 <malloc@plt>
    4e62:	48 85 c0             	test   %rax,%rax
    4e65:	0f 84 50 04 00 00    	je     52bb <send_headers+0x4fb>
    4e6b:	66 0f 6f 05 cd 3d 00 00 	movdqa 0x3dcd(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4e73:	48 89 45 10          	mov    %rax,0x10(%rbp)
    4e77:	4c 89 e7             	mov    %r12,%rdi
    4e7a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    4e84:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4e8c:	0f 11 00             	movups %xmm0,(%rax)
    4e8f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    4e93:	be 2e 00 00 00       	mov    $0x2e,%esi
    4e98:	e8 13 d5 ff ff       	call   23b0 <strrchr@plt>
    4e9d:	48 85 c0             	test   %rax,%rax
    4ea0:	0f 84 ea 02 00 00    	je     5190 <send_headers+0x3d0>
    4ea6:	4c 39 e0             	cmp    %r12,%rax
    4ea9:	0f 84 e1 02 00 00    	je     5190 <send_headers+0x3d0>
    4eaf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    4eb3:	48 8d 3d 0a 32 00 00 	lea    0x320a(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4eba:	48 89 de             	mov    %rbx,%rsi
    4ebd:	e8 4e d5 ff ff       	call   2410 <strcmp@plt>
    4ec2:	85 c0                	test   %eax,%eax
    4ec4:	75 20                	jne    4ee6 <send_headers+0x126>
    4ec6:	66 0f 6f 05 82 3d 00 00 	movdqa 0x3d82(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4ece:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ed6:	66 0f 6f 05 82 3d 00 00 	movdqa 0x3d82(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    4ede:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4ee6:	48 89 de             	mov    %rbx,%rsi
    4ee9:	48 8d 3d d8 31 00 00 	lea    0x31d8(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4ef0:	e8 1b d5 ff ff       	call   2410 <strcmp@plt>
    4ef5:	85 c0                	test   %eax,%eax
    4ef7:	75 20                	jne    4f19 <send_headers+0x159>
    4ef9:	66 0f 6f 05 4f 3d 00 00 	movdqa 0x3d4f(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4f01:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f09:	66 0f 6f 05 4f 3d 00 00 	movdqa 0x3d4f(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    4f11:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4f19:	48 89 de             	mov    %rbx,%rsi
    4f1c:	48 8d 3d aa 31 00 00 	lea    0x31aa(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4f23:	e8 e8 d4 ff ff       	call   2410 <strcmp@plt>
    4f28:	85 c0                	test   %eax,%eax
    4f2a:	0f 84 10 02 00 00    	je     5140 <send_headers+0x380>
    4f30:	48 89 de             	mov    %rbx,%rsi
    4f33:	48 8d 3d 97 31 00 00 	lea    0x3197(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4f3a:	e8 d1 d4 ff ff       	call   2410 <strcmp@plt>
    4f3f:	85 c0                	test   %eax,%eax
    4f41:	0f 84 a9 02 00 00    	je     51f0 <send_headers+0x430>
    4f47:	48 89 de             	mov    %rbx,%rsi
    4f4a:	48 8d 3d 84 31 00 00 	lea    0x3184(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4f51:	e8 ba d4 ff ff       	call   2410 <strcmp@plt>
    4f56:	85 c0                	test   %eax,%eax
    4f58:	0f 84 6a 02 00 00    	je     51c8 <send_headers+0x408>
    4f5e:	48 89 de             	mov    %rbx,%rsi
    4f61:	48 8d 3d b0 31 00 00 	lea    0x31b0(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4f68:	e8 a3 d4 ff ff       	call   2410 <strcmp@plt>
    4f6d:	85 c0                	test   %eax,%eax
    4f6f:	0f 84 2b 02 00 00    	je     51a0 <send_headers+0x3e0>
    4f75:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4f78:	0f 84 52 01 00 00    	je     50d0 <send_headers+0x310>
    4f7e:	48 89 de             	mov    %rbx,%rsi
    4f81:	48 8d 3d 51 31 00 00 	lea    0x3151(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4f88:	e8 83 d4 ff ff       	call   2410 <strcmp@plt>
    4f8d:	85 c0                	test   %eax,%eax
    4f8f:	0f 84 ab 02 00 00    	je     5240 <send_headers+0x480>
    4f95:	48 89 de             	mov    %rbx,%rsi
    4f98:	48 8d 3d 3e 31 00 00 	lea    0x313e(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4f9f:	e8 6c d4 ff ff       	call   2410 <strcmp@plt>
    4fa4:	85 c0                	test   %eax,%eax
    4fa6:	0f 84 6c 02 00 00    	je     5218 <send_headers+0x458>
    4fac:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4fb4:	4c 89 e7             	mov    %r12,%rdi
    4fb7:	e8 b4 d3 ff ff       	call   2370 <strlen@plt>
    4fbc:	48 89 c7             	mov    %rax,%rdi
    4fbf:	48 89 c3             	mov    %rax,%rbx
    4fc2:	e8 a9 d4 ff ff       	call   2470 <malloc@plt>
    4fc7:	48 85 c0             	test   %rax,%rax
    4fca:	0f 84 eb 02 00 00    	je     52bb <send_headers+0x4fb>
    4fd0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4fd4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    4fd8:	83 fb 08             	cmp    $0x8,%ebx
    4fdb:	0f 83 3f 01 00 00    	jae    5120 <send_headers+0x360>
    4fe1:	f6 c3 04             	test   $0x4,%bl
    4fe4:	0f 85 7b 02 00 00    	jne    5265 <send_headers+0x4a5>
    4fea:	85 db                	test   %ebx,%ebx
    4fec:	74 13                	je     5001 <send_headers+0x241>
    4fee:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4ff6:	88 10                	mov    %dl,(%rax)
    4ff8:	f6 c3 02             	test   $0x2,%bl
    4ffb:	0f 85 96 02 00 00    	jne    5297 <send_headers+0x4d7>
    5001:	4d 89 e8             	mov    %r13,%r8
    5004:	48 8d 0d d6 30 00 00 	lea    0x30d6(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    500b:	4c 89 e7             	mov    %r12,%rdi
    500e:	31 c0                	xor    %eax,%eax
    5010:	ba 00 04 00 00       	mov    $0x400,%edx
    5015:	be 01 00 00 00       	mov    $0x1,%esi
    501a:	e8 81 d5 ff ff       	call   25a0 <__sprintf_chk@plt>
    501f:	4c 89 e7             	mov    %r12,%rdi
    5022:	e8 49 d3 ff ff       	call   2370 <strlen@plt>
    5027:	48 89 c7             	mov    %rax,%rdi
    502a:	48 89 c3             	mov    %rax,%rbx
    502d:	e8 3e d4 ff ff       	call   2470 <malloc@plt>
    5032:	48 85 c0             	test   %rax,%rax
    5035:	0f 84 80 02 00 00    	je     52bb <send_headers+0x4fb>
    503b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    503f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    5043:	83 fb 08             	cmp    $0x8,%ebx
    5046:	0f 83 1c 01 00 00    	jae    5168 <send_headers+0x3a8>
    504c:	f6 c3 04             	test   $0x4,%bl
    504f:	0f 85 29 02 00 00    	jne    527e <send_headers+0x4be>
    5055:	85 db                	test   %ebx,%ebx
    5057:	74 13                	je     506c <send_headers+0x2ac>
    5059:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    5061:	88 10                	mov    %dl,(%rax)
    5063:	f6 c3 02             	test   $0x2,%bl
    5066:	0f 85 3d 02 00 00    	jne    52a9 <send_headers+0x4e9>
    506c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    5071:	bf 02 00 00 00       	mov    $0x2,%edi
    5076:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    507e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    5086:	e8 e5 d3 ff ff       	call   2470 <malloc@plt>
    508b:	48 85 c0             	test   %rax,%rax
    508e:	0f 84 27 02 00 00    	je     52bb <send_headers+0x4fb>
    5094:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    509c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    50a0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    50a8:	66 89 10             	mov    %dx,(%rax)
    50ab:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    50b3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    50bc:	0f 85 20 02 00 00    	jne    52e2 <send_headers+0x522>
    50c2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    50c9:	5b                   	pop    %rbx
    50ca:	5d                   	pop    %rbp
    50cb:	41 5c                	pop    %r12
    50cd:	41 5d                	pop    %r13
    50cf:	c3                   	ret
    50d0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    50d4:	0f 85 a4 fe ff ff    	jne    4f7e <send_headers+0x1be>
    50da:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    50de:	0f 85 9a fe ff ff    	jne    4f7e <send_headers+0x1be>
    50e4:	66 0f 6f 05 c4 3b 00 00 	movdqa 0x3bc4(%rip),%xmm0        # 8cb0 <_IO_stdin_used+0xcb0>
    50ec:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    50f6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50fe:	66 0f 6f 05 ba 3b 00 00 	movdqa 0x3bba(%rip),%xmm0        # 8cc0 <_IO_stdin_used+0xcc0>
    5106:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    510e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    5116:	e9 63 fe ff ff       	jmp    4f7e <send_headers+0x1be>
    511b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5120:	89 da                	mov    %ebx,%edx
    5122:	48 89 c7             	mov    %rax,%rdi
    5125:	4c 89 e6             	mov    %r12,%rsi
    5128:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    512d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5132:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5135:	c1 e9 03             	shr    $0x3,%ecx
    5138:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    513b:	e9 c1 fe ff ff       	jmp    5001 <send_headers+0x241>
    5140:	66 0f 6f 05 08 3b 00 00 	movdqa 0x3b08(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5148:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5150:	66 0f 6f 05 18 3b 00 00 	movdqa 0x3b18(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    5158:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5160:	e9 cb fd ff ff       	jmp    4f30 <send_headers+0x170>
    5165:	0f 1f 00             	nopl   (%rax)
    5168:	89 da                	mov    %ebx,%edx
    516a:	48 89 c7             	mov    %rax,%rdi
    516d:	4c 89 e6             	mov    %r12,%rsi
    5170:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    5175:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    517a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    517d:	c1 e9 03             	shr    $0x3,%ecx
    5180:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    5183:	e9 e4 fe ff ff       	jmp    506c <send_headers+0x2ac>
    5188:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5190:	48 8d 1d 5f 2f 00 00 	lea    0x2f5f(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    5197:	e9 94 fd ff ff       	jmp    4f30 <send_headers+0x170>
    519c:	0f 1f 40 00          	nopl   0x0(%rax)
    51a0:	66 0f 6f 05 e8 3a 00 00 	movdqa 0x3ae8(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    51a8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    51b0:	66 0f 6f 05 e8 3a 00 00 	movdqa 0x3ae8(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    51b8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    51c0:	e9 b0 fd ff ff       	jmp    4f75 <send_headers+0x1b5>
    51c5:	0f 1f 00             	nopl   (%rax)
    51c8:	66 0f 6f 05 c0 3a 00 00 	movdqa 0x3ac0(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    51d0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    51d8:	66 0f 6f 05 c0 3a 00 00 	movdqa 0x3ac0(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    51e0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    51e8:	e9 71 fd ff ff       	jmp    4f5e <send_headers+0x19e>
    51ed:	0f 1f 00             	nopl   (%rax)
    51f0:	66 0f 6f 05 58 3a 00 00 	movdqa 0x3a58(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    51f8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5200:	66 0f 6f 05 78 3a 00 00 	movdqa 0x3a78(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    5208:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5210:	e9 32 fd ff ff       	jmp    4f47 <send_headers+0x187>
    5215:	0f 1f 00             	nopl   (%rax)
    5218:	66 0f 6f 05 70 3a 00 00 	movdqa 0x3a70(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    5220:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5228:	66 0f 6f 05 b0 3a 00 00 	movdqa 0x3ab0(%rip),%xmm0        # 8ce0 <_IO_stdin_used+0xce0>
    5230:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5238:	e9 6f fd ff ff       	jmp    4fac <send_headers+0x1ec>
    523d:	0f 1f 00             	nopl   (%rax)
    5240:	66 0f 6f 05 48 3a 00 00 	movdqa 0x3a48(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    5248:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5250:	66 0f 6f 05 78 3a 00 00 	movdqa 0x3a78(%rip),%xmm0        # 8cd0 <_IO_stdin_used+0xcd0>
    5258:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5260:	e9 30 fd ff ff       	jmp    4f95 <send_headers+0x1d5>
    5265:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    526c:	89 db                	mov    %ebx,%ebx
    526e:	89 10                	mov    %edx,(%rax)
    5270:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5275:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5279:	e9 83 fd ff ff       	jmp    5001 <send_headers+0x241>
    527e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5285:	89 db                	mov    %ebx,%ebx
    5287:	89 10                	mov    %edx,(%rax)
    5289:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    528e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5292:	e9 d5 fd ff ff       	jmp    506c <send_headers+0x2ac>
    5297:	89 db                	mov    %ebx,%ebx
    5299:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    529f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    52a4:	e9 58 fd ff ff       	jmp    5001 <send_headers+0x241>
    52a9:	89 db                	mov    %ebx,%ebx
    52ab:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    52b1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    52b6:	e9 b1 fd ff ff       	jmp    506c <send_headers+0x2ac>
    52bb:	48 8b 0d 5e 5d 00 00 	mov    0x5d5e(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    52c2:	ba 28 00 00 00       	mov    $0x28,%edx
    52c7:	be 01 00 00 00       	mov    $0x1,%esi
    52cc:	48 8d 3d fd 32 00 00 	lea    0x32fd(%rip),%rdi        # 85d0 <_IO_stdin_used+0x5d0>
    52d3:	e8 58 d2 ff ff       	call   2530 <fwrite@plt>
    52d8:	bf 01 00 00 00       	mov    $0x1,%edi
    52dd:	e8 2e d2 ff ff       	call   2510 <exit@plt>
    52e2:	e8 99 d0 ff ff       	call   2380 <__stack_chk_fail@plt>
    52e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000052f0 <copy_file_contents>:
    52f0:	f3 0f 1e fa          	endbr64
    52f4:	41 55                	push   %r13
    52f6:	49 89 d5             	mov    %rdx,%r13
    52f9:	41 54                	push   %r12
    52fb:	49 89 fc             	mov    %rdi,%r12
    52fe:	48 89 f7             	mov    %rsi,%rdi
    5301:	55                   	push   %rbp
    5302:	53                   	push   %rbx
    5303:	48 89 f3             	mov    %rsi,%rbx
    5306:	48 83 ec 08          	sub    $0x8,%rsp
    530a:	e8 61 d1 ff ff       	call   2470 <malloc@plt>
    530f:	48 85 c0             	test   %rax,%rax
    5312:	74 6b                	je     537f <copy_file_contents+0x8f>
    5314:	4c 89 e7             	mov    %r12,%rdi
    5317:	48 89 c5             	mov    %rax,%rbp
    531a:	31 f6                	xor    %esi,%esi
    531c:	31 c0                	xor    %eax,%eax
    531e:	e8 bd d1 ff ff       	call   24e0 <open@plt>
    5323:	41 89 c4             	mov    %eax,%r12d
    5326:	85 c0                	test   %eax,%eax
    5328:	0f 88 a8 d2 ff ff    	js     25d6 <copy_file_contents.cold>
    532e:	48 89 da             	mov    %rbx,%rdx
    5331:	48 89 ee             	mov    %rbp,%rsi
    5334:	89 c7                	mov    %eax,%edi
    5336:	e8 b5 d0 ff ff       	call   23f0 <read@plt>
    533b:	48 98                	cltq
    533d:	48 39 d8             	cmp    %rbx,%rax
    5340:	7c 1e                	jl     5360 <copy_file_contents+0x70>
    5342:	44 89 e7             	mov    %r12d,%edi
    5345:	e8 86 d0 ff ff       	call   23d0 <close@plt>
    534a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    534e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    5352:	48 83 c4 08          	add    $0x8,%rsp
    5356:	5b                   	pop    %rbx
    5357:	5d                   	pop    %rbp
    5358:	41 5c                	pop    %r12
    535a:	41 5d                	pop    %r13
    535c:	c3                   	ret
    535d:	0f 1f 00             	nopl   (%rax)
    5360:	48 8b 0d b9 5c 00 00 	mov    0x5cb9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5367:	ba 1a 00 00 00       	mov    $0x1a,%edx
    536c:	be 01 00 00 00       	mov    $0x1,%esi
    5371:	48 8d 3d 7f 2d 00 00 	lea    0x2d7f(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    5378:	e8 b3 d1 ff ff       	call   2530 <fwrite@plt>
    537d:	eb c3                	jmp    5342 <copy_file_contents+0x52>
    537f:	48 8b 0d 9a 5c 00 00 	mov    0x5c9a(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5386:	ba 28 00 00 00       	mov    $0x28,%edx
    538b:	be 01 00 00 00       	mov    $0x1,%esi
    5390:	48 8d 3d 39 32 00 00 	lea    0x3239(%rip),%rdi        # 85d0 <_IO_stdin_used+0x5d0>
    5397:	e8 94 d1 ff ff       	call   2530 <fwrite@plt>
    539c:	bf 01 00 00 00       	mov    $0x1,%edi
    53a1:	e8 6a d1 ff ff       	call   2510 <exit@plt>
    53a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000053b0 <add_write_request>:
    53b0:	f3 0f 1e fa          	endbr64
    53b4:	8b 46 44             	mov    0x44(%rsi),%eax
    53b7:	48 89 fa             	mov    %rdi,%rdx
    53ba:	48 89 f7             	mov    %rsi,%rdi
    53bd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    53c3:	8d 70 01             	lea    0x1(%rax),%esi
    53c6:	48 8b 07             	mov    (%rdi),%rax
    53c9:	44 8b 00             	mov    (%rax),%r8d
    53cc:	f6 c1 02             	test   $0x2,%cl
    53cf:	74 00                	je     53d1 <add_write_request+0x21>
    53d1:	89 f0                	mov    %esi,%eax
    53d3:	44 29 c0             	sub    %r8d,%eax
    53d6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    53d9:	0f 82 03 d2 ff ff    	jb     25e2 <add_write_request.cold>
    53df:	c1 e9 0a             	shr    $0xa,%ecx
    53e2:	48 83 ec 08          	sub    $0x8,%rsp
    53e6:	8b 47 44             	mov    0x44(%rdi),%eax
    53e9:	23 47 58             	and    0x58(%rdi),%eax
    53ec:	83 e1 01             	and    $0x1,%ecx
    53ef:	89 77 44             	mov    %esi,0x44(%rdi)
    53f2:	8b 72 08             	mov    0x8(%rdx),%esi
    53f5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    53f9:	d3 e0                	shl    %cl,%eax
    53fb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    53fe:	48 c1 e0 06          	shl    $0x6,%rax
    5402:	48 03 47 38          	add    0x38(%rdi),%rax
    5406:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    540c:	89 70 04             	mov    %esi,0x4(%rax)
    540f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    5413:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    5419:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5421:	48 89 70 10          	mov    %rsi,0x10(%rax)
    5425:	89 48 18             	mov    %ecx,0x18(%rax)
    5428:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    542f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5437:	48 89 50 20          	mov    %rdx,0x20(%rax)
    543b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    543f:	e8 4c cf ff ff       	call   2390 <io_uring_submit@plt>
    5444:	31 c0                	xor    %eax,%eax
    5446:	48 83 c4 08          	add    $0x8,%rsp
    544a:	c3                   	ret
    544b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005450 <add_read_request>:
    5450:	f3 0f 1e fa          	endbr64
    5454:	41 55                	push   %r13
    5456:	41 89 fd             	mov    %edi,%r13d
    5459:	41 54                	push   %r12
    545b:	55                   	push   %rbp
    545c:	53                   	push   %rbx
    545d:	48 89 f3             	mov    %rsi,%rbx
    5460:	48 83 ec 08          	sub    $0x8,%rsp
    5464:	8b 46 44             	mov    0x44(%rsi),%eax
    5467:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    546d:	48 8b 16             	mov    (%rsi),%rdx
    5470:	83 c0 01             	add    $0x1,%eax
    5473:	8b 32                	mov    (%rdx),%esi
    5475:	f6 c1 02             	test   $0x2,%cl
    5478:	74 00                	je     547a <add_read_request+0x2a>
    547a:	89 c2                	mov    %eax,%edx
    547c:	29 f2                	sub    %esi,%edx
    547e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5481:	0f 82 6b d1 ff ff    	jb     25f2 <add_read_request.cold>
    5487:	8b 6b 44             	mov    0x44(%rbx),%ebp
    548a:	c1 e9 0a             	shr    $0xa,%ecx
    548d:	89 43 44             	mov    %eax,0x44(%rbx)
    5490:	bf 20 00 00 00       	mov    $0x20,%edi
    5495:	83 e1 01             	and    $0x1,%ecx
    5498:	23 6b 58             	and    0x58(%rbx),%ebp
    549b:	d3 e5                	shl    %cl,%ebp
    549d:	48 c1 e5 06          	shl    $0x6,%rbp
    54a1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    54a5:	e8 c6 cf ff ff       	call   2470 <malloc@plt>
    54aa:	be 01 00 00 00       	mov    $0x1,%esi
    54af:	bf 00 20 00 00       	mov    $0x2000,%edi
    54b4:	49 89 c4             	mov    %rax,%r12
    54b7:	e8 44 cf ff ff       	call   2400 <calloc@plt>
    54bc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    54c1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    54c5:	48 89 df             	mov    %rbx,%rdi
    54c8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    54cd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    54d2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    54db:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    54e3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    54e7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    54eb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    54f2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    54fa:	48 89 45 10          	mov    %rax,0x10(%rbp)
    54fe:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    5506:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    550e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5512:	e8 79 ce ff ff       	call   2390 <io_uring_submit@plt>
    5517:	48 83 c4 08          	add    $0x8,%rsp
    551b:	31 c0                	xor    %eax,%eax
    551d:	5b                   	pop    %rbx
    551e:	5d                   	pop    %rbp
    551f:	41 5c                	pop    %r12
    5521:	41 5d                	pop    %r13
    5523:	c3                   	ret
    5524:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    552f:	90                   	nop

0000000000005530 <_send_static_string_content>:
    5530:	f3 0f 1e fa          	endbr64
    5534:	41 56                	push   %r14
    5536:	41 89 f6             	mov    %esi,%r14d
    5539:	41 55                	push   %r13
    553b:	49 89 fd             	mov    %rdi,%r13
    553e:	bf 20 00 00 00       	mov    $0x20,%edi
    5543:	41 54                	push   %r12
    5545:	55                   	push   %rbp
    5546:	48 89 d5             	mov    %rdx,%rbp
    5549:	53                   	push   %rbx
    554a:	e8 21 cf ff ff       	call   2470 <malloc@plt>
    554f:	48 85 c0             	test   %rax,%rax
    5552:	0f 84 dd 00 00 00    	je     5635 <_send_static_string_content+0x105>
    5558:	48 89 c3             	mov    %rax,%rbx
    555b:	4c 89 ef             	mov    %r13,%rdi
    555e:	e8 0d ce ff ff       	call   2370 <strlen@plt>
    5563:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    556a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    556e:	48 89 c7             	mov    %rax,%rdi
    5571:	49 89 c4             	mov    %rax,%r12
    5574:	e8 f7 ce ff ff       	call   2470 <malloc@plt>
    5579:	48 89 c7             	mov    %rax,%rdi
    557c:	48 85 c0             	test   %rax,%rax
    557f:	0f 84 b0 00 00 00    	je     5635 <_send_static_string_content+0x105>
    5585:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5589:	4c 89 e2             	mov    %r12,%rdx
    558c:	4c 89 ee             	mov    %r13,%rsi
    558f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5593:	e8 a8 ce ff ff       	call   2440 <memcpy@plt>
    5598:	8b 45 44             	mov    0x44(%rbp),%eax
    559b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    55a1:	8d 50 01             	lea    0x1(%rax),%edx
    55a4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    55a8:	8b 30                	mov    (%rax),%esi
    55aa:	f6 c1 02             	test   $0x2,%cl
    55ad:	0f 85 7d 00 00 00    	jne    5630 <_send_static_string_content+0x100>
    55b3:	89 d0                	mov    %edx,%eax
    55b5:	29 f0                	sub    %esi,%eax
    55b7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    55ba:	0f 82 3c d0 ff ff    	jb     25fc <_send_static_string_content.cold>
    55c0:	c1 e9 0a             	shr    $0xa,%ecx
    55c3:	8b 45 44             	mov    0x44(%rbp),%eax
    55c6:	23 45 58             	and    0x58(%rbp),%eax
    55c9:	89 55 44             	mov    %edx,0x44(%rbp)
    55cc:	83 e1 01             	and    $0x1,%ecx
    55cf:	8b 53 04             	mov    0x4(%rbx),%edx
    55d2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    55d8:	66 0f ef c0          	pxor   %xmm0,%xmm0
    55dc:	d3 e0                	shl    %cl,%eax
    55de:	8b 4b 08             	mov    0x8(%rbx),%ecx
    55e1:	48 89 ef             	mov    %rbp,%rdi
    55e4:	48 c1 e0 06          	shl    $0x6,%rax
    55e8:	48 03 45 38          	add    0x38(%rbp),%rax
    55ec:	89 48 04             	mov    %ecx,0x4(%rax)
    55ef:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    55f3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    55f9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5601:	48 89 48 10          	mov    %rcx,0x10(%rax)
    5605:	89 50 18             	mov    %edx,0x18(%rax)
    5608:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    560f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5617:	48 89 58 20          	mov    %rbx,0x20(%rax)
    561b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    561f:	5b                   	pop    %rbx
    5620:	5d                   	pop    %rbp
    5621:	41 5c                	pop    %r12
    5623:	41 5d                	pop    %r13
    5625:	41 5e                	pop    %r14
    5627:	e9 64 cd ff ff       	jmp    2390 <io_uring_submit@plt>
    562c:	0f 1f 40 00          	nopl   0x0(%rax)
    5630:	e9 7e ff ff ff       	jmp    55b3 <_send_static_string_content+0x83>
    5635:	48 8b 0d e4 59 00 00 	mov    0x59e4(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    563c:	ba 28 00 00 00       	mov    $0x28,%edx
    5641:	be 01 00 00 00       	mov    $0x1,%esi
    5646:	48 8d 3d 83 2f 00 00 	lea    0x2f83(%rip),%rdi        # 85d0 <_IO_stdin_used+0x5d0>
    564d:	e8 de ce ff ff       	call   2530 <fwrite@plt>
    5652:	bf 01 00 00 00       	mov    $0x1,%edi
    5657:	e8 b4 ce ff ff       	call   2510 <exit@plt>
    565c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005660 <handle_unimplemented_method>:
    5660:	f3 0f 1e fa          	endbr64
    5664:	48 89 f2             	mov    %rsi,%rdx
    5667:	89 fe                	mov    %edi,%esi
    5669:	48 8b 3d a8 59 00 00 	mov    0x59a8(%rip),%rdi        # b018 <unimplemented_content>
    5670:	e9 bb fe ff ff       	jmp    5530 <_send_static_string_content>
    5675:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005680 <handle_http_404>:
    5680:	f3 0f 1e fa          	endbr64
    5684:	48 89 f2             	mov    %rsi,%rdx
    5687:	89 fe                	mov    %edi,%esi
    5689:	48 8b 3d 80 59 00 00 	mov    0x5980(%rip),%rdi        # b010 <http_404_content>
    5690:	e9 9b fe ff ff       	jmp    5530 <_send_static_string_content>
    5695:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000056a0 <handle_get_method>:
    56a0:	f3 0f 1e fa          	endbr64
    56a4:	41 56                	push   %r14
    56a6:	41 55                	push   %r13
    56a8:	49 89 d5             	mov    %rdx,%r13
    56ab:	41 54                	push   %r12
    56ad:	41 89 f4             	mov    %esi,%r12d
    56b0:	55                   	push   %rbp
    56b1:	48 89 fd             	mov    %rdi,%rbp
    56b4:	53                   	push   %rbx
    56b5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    56bc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    56c5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    56cd:	31 c0                	xor    %eax,%eax
    56cf:	e8 9c cc ff ff       	call   2370 <strlen@plt>
    56d4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    56d9:	48 89 c3             	mov    %rax,%rbx
    56dc:	0f 84 b6 00 00 00    	je     5798 <handle_get_method+0xf8>
    56e2:	b8 69 63 00 00       	mov    $0x6369,%eax
    56e7:	48 89 ee             	mov    %rbp,%rsi
    56ea:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    56ee:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    56f3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    56fb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5703:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    570e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    5716:	e8 05 cd ff ff       	call   2420 <__memcpy_chk@plt>
    571b:	48 89 e6             	mov    %rsp,%rsi
    571e:	4c 89 f7             	mov    %r14,%rdi
    5721:	e8 0a cd ff ff       	call   2430 <stat@plt>
    5726:	83 f8 ff             	cmp    $0xffffffff,%eax
    5729:	0f 84 d3 00 00 00    	je     5802 <handle_get_method+0x162>
    572f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5733:	25 00 f0 00 00       	and    $0xf000,%eax
    5738:	3d 00 80 00 00       	cmp    $0x8000,%eax
    573d:	0f 84 f5 00 00 00    	je     5838 <handle_get_method+0x198>
    5743:	48 8b 3d c6 58 00 00 	mov    0x58c6(%rip),%rdi        # b010 <http_404_content>
    574a:	4c 89 ea             	mov    %r13,%rdx
    574d:	44 89 e6             	mov    %r12d,%esi
    5750:	e8 db fd ff ff       	call   5530 <_send_static_string_content>
    5755:	4c 89 f2             	mov    %r14,%rdx
    5758:	bf 01 00 00 00       	mov    $0x1,%edi
    575d:	31 c0                	xor    %eax,%eax
    575f:	48 8d 35 e1 29 00 00 	lea    0x29e1(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5766:	e8 45 cd ff ff       	call   24b0 <__printf_chk@plt>
    576b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5773:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    577c:	0f 85 20 01 00 00    	jne    58a2 <handle_get_method+0x202>
    5782:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5789:	5b                   	pop    %rbx
    578a:	5d                   	pop    %rbp
    578b:	41 5c                	pop    %r12
    578d:	41 5d                	pop    %r13
    578f:	41 5e                	pop    %r14
    5791:	c3                   	ret
    5792:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5798:	ba 69 63 00 00       	mov    $0x6369,%edx
    579d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    57a5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    57aa:	48 89 ee             	mov    %rbp,%rsi
    57ad:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    57b5:	48 89 c2             	mov    %rax,%rdx
    57b8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    57c0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    57cb:	e8 50 cc ff ff       	call   2420 <__memcpy_chk@plt>
    57d0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    57d5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    57da:	48 8d 35 31 29 00 00 	lea    0x2931(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    57e1:	48 29 d9             	sub    %rbx,%rcx
    57e4:	ba 0b 00 00 00       	mov    $0xb,%edx
    57e9:	e8 32 cc ff ff       	call   2420 <__memcpy_chk@plt>
    57ee:	48 89 e6             	mov    %rsp,%rsi
    57f1:	4c 89 f7             	mov    %r14,%rdi
    57f4:	e8 37 cc ff ff       	call   2430 <stat@plt>
    57f9:	83 f8 ff             	cmp    $0xffffffff,%eax
    57fc:	0f 85 2d ff ff ff    	jne    572f <handle_get_method+0x8f>
    5802:	4c 89 f2             	mov    %r14,%rdx
    5805:	48 89 e9             	mov    %rbp,%rcx
    5808:	48 8d 35 0e 29 00 00 	lea    0x290e(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    580f:	31 c0                	xor    %eax,%eax
    5811:	bf 01 00 00 00       	mov    $0x1,%edi
    5816:	e8 95 cc ff ff       	call   24b0 <__printf_chk@plt>
    581b:	48 8b 3d ee 57 00 00 	mov    0x57ee(%rip),%rdi        # b010 <http_404_content>
    5822:	4c 89 ea             	mov    %r13,%rdx
    5825:	44 89 e6             	mov    %r12d,%esi
    5828:	e8 03 fd ff ff       	call   5530 <_send_static_string_content>
    582d:	e9 39 ff ff ff       	jmp    576b <handle_get_method+0xcb>
    5832:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5838:	bf 70 00 00 00       	mov    $0x70,%edi
    583d:	e8 2e cc ff ff       	call   2470 <malloc@plt>
    5842:	48 89 c3             	mov    %rax,%rbx
    5845:	48 85 c0             	test   %rax,%rax
    5848:	74 5d                	je     58a7 <handle_get_method+0x207>
    584a:	44 89 60 08          	mov    %r12d,0x8(%rax)
    584e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5853:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5857:	4c 89 f7             	mov    %r14,%rdi
    585a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    5861:	e8 5a f5 ff ff       	call   4dc0 <send_headers>
    5866:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    586b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    586f:	4c 89 f7             	mov    %r14,%rdi
    5872:	e8 79 fa ff ff       	call   52f0 <copy_file_contents>
    5877:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    587c:	4c 89 f2             	mov    %r14,%rdx
    587f:	31 c0                	xor    %eax,%eax
    5881:	48 8d 35 ad 28 00 00 	lea    0x28ad(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    5888:	bf 01 00 00 00       	mov    $0x1,%edi
    588d:	e8 1e cc ff ff       	call   24b0 <__printf_chk@plt>
    5892:	4c 89 ee             	mov    %r13,%rsi
    5895:	48 89 df             	mov    %rbx,%rdi
    5898:	e8 13 fb ff ff       	call   53b0 <add_write_request>
    589d:	e9 c9 fe ff ff       	jmp    576b <handle_get_method+0xcb>
    58a2:	e8 d9 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    58a7:	48 8b 0d 72 57 00 00 	mov    0x5772(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    58ae:	ba 28 00 00 00       	mov    $0x28,%edx
    58b3:	be 01 00 00 00       	mov    $0x1,%esi
    58b8:	48 8d 3d 11 2d 00 00 	lea    0x2d11(%rip),%rdi        # 85d0 <_IO_stdin_used+0x5d0>
    58bf:	e8 6c cc ff ff       	call   2530 <fwrite@plt>
    58c4:	bf 01 00 00 00       	mov    $0x1,%edi
    58c9:	e8 42 cc ff ff       	call   2510 <exit@plt>
    58ce:	66 90                	xchg   %ax,%ax

00000000000058d0 <handle_http_method>:
    58d0:	f3 0f 1e fa          	endbr64
    58d4:	41 57                	push   %r15
    58d6:	41 56                	push   %r14
    58d8:	4c 8d 35 cd 27 00 00 	lea    0x27cd(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
    58df:	41 55                	push   %r13
    58e1:	49 89 d5             	mov    %rdx,%r13
    58e4:	41 54                	push   %r12
    58e6:	41 89 f4             	mov    %esi,%r12d
    58e9:	4c 89 f6             	mov    %r14,%rsi
    58ec:	55                   	push   %rbp
    58ed:	53                   	push   %rbx
    58ee:	48 83 ec 18          	sub    $0x18,%rsp
    58f2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    58fb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5900:	31 c0                	xor    %eax,%eax
    5902:	49 89 e7             	mov    %rsp,%r15
    5905:	4c 89 fa             	mov    %r15,%rdx
    5908:	e8 d3 ca ff ff       	call   23e0 <strtok_r@plt>
    590d:	48 0f be 18          	movsbq (%rax),%rbx
    5911:	48 89 c5             	mov    %rax,%rbp
    5914:	84 db                	test   %bl,%bl
    5916:	74 1d                	je     5935 <handle_http_method+0x65>
    5918:	e8 73 cc ff ff       	call   2590 <__ctype_tolower_loc@plt>
    591d:	48 89 ea             	mov    %rbp,%rdx
    5920:	48 8b 08             	mov    (%rax),%rcx
    5923:	48 83 c2 01          	add    $0x1,%rdx
    5927:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    592a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    592d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5931:	84 db                	test   %bl,%bl
    5933:	75 eb                	jne    5920 <handle_http_method+0x50>
    5935:	4c 89 fa             	mov    %r15,%rdx
    5938:	4c 89 f6             	mov    %r14,%rsi
    593b:	31 ff                	xor    %edi,%edi
    593d:	e8 9e ca ff ff       	call   23e0 <strtok_r@plt>
    5942:	48 8d 35 11 28 00 00 	lea    0x2811(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    5949:	48 89 ef             	mov    %rbp,%rdi
    594c:	48 89 c3             	mov    %rax,%rbx
    594f:	e8 bc ca ff ff       	call   2410 <strcmp@plt>
    5954:	4c 89 ea             	mov    %r13,%rdx
    5957:	44 89 e6             	mov    %r12d,%esi
    595a:	85 c0                	test   %eax,%eax
    595c:	75 2a                	jne    5988 <handle_http_method+0xb8>
    595e:	48 89 df             	mov    %rbx,%rdi
    5961:	e8 3a fd ff ff       	call   56a0 <handle_get_method>
    5966:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    596b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5974:	75 20                	jne    5996 <handle_http_method+0xc6>
    5976:	48 83 c4 18          	add    $0x18,%rsp
    597a:	5b                   	pop    %rbx
    597b:	5d                   	pop    %rbp
    597c:	41 5c                	pop    %r12
    597e:	41 5d                	pop    %r13
    5980:	41 5e                	pop    %r14
    5982:	41 5f                	pop    %r15
    5984:	c3                   	ret
    5985:	0f 1f 00             	nopl   (%rax)
    5988:	48 8b 3d 89 56 00 00 	mov    0x5689(%rip),%rdi        # b018 <unimplemented_content>
    598f:	e8 9c fb ff ff       	call   5530 <_send_static_string_content>
    5994:	eb d0                	jmp    5966 <handle_http_method+0x96>
    5996:	e8 e5 c9 ff ff       	call   2380 <__stack_chk_fail@plt>
    599b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000059a0 <get_line>:
    59a0:	f3 0f 1e fa          	endbr64
    59a4:	85 d2                	test   %edx,%edx
    59a6:	7e 38                	jle    59e0 <get_line+0x40>
    59a8:	48 63 d2             	movslq %edx,%rdx
    59ab:	48 83 c7 01          	add    $0x1,%rdi
    59af:	48 01 f2             	add    %rsi,%rdx
    59b2:	eb 11                	jmp    59c5 <get_line+0x25>
    59b4:	0f 1f 40 00          	nopl   0x0(%rax)
    59b8:	48 83 c6 01          	add    $0x1,%rsi
    59bc:	48 83 c7 01          	add    $0x1,%rdi
    59c0:	48 39 d6             	cmp    %rdx,%rsi
    59c3:	74 1b                	je     59e0 <get_line+0x40>
    59c5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    59c9:	88 06                	mov    %al,(%rsi)
    59cb:	3c 0d                	cmp    $0xd,%al
    59cd:	75 e9                	jne    59b8 <get_line+0x18>
    59cf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    59d2:	75 e4                	jne    59b8 <get_line+0x18>
    59d4:	c6 06 00             	movb   $0x0,(%rsi)
    59d7:	31 c0                	xor    %eax,%eax
    59d9:	c3                   	ret
    59da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    59e0:	b8 01 00 00 00       	mov    $0x1,%eax
    59e5:	c3                   	ret
    59e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000059f0 <handle_client_request>:
    59f0:	f3 0f 1e fa          	endbr64
    59f4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    59fb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    59ff:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5a08:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5a10:	31 c0                	xor    %eax,%eax
    5a12:	49 89 e2             	mov    %rsp,%r10
    5a15:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    5a1d:	4c 89 d0             	mov    %r10,%rax
    5a20:	eb 13                	jmp    5a35 <handle_client_request+0x45>
    5a22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5a28:	48 83 c0 01          	add    $0x1,%rax
    5a2c:	48 83 c1 01          	add    $0x1,%rcx
    5a30:	4c 39 c8             	cmp    %r9,%rax
    5a33:	74 4b                	je     5a80 <handle_client_request+0x90>
    5a35:	44 0f b6 01          	movzbl (%rcx),%r8d
    5a39:	44 88 00             	mov    %r8b,(%rax)
    5a3c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5a40:	75 e6                	jne    5a28 <handle_client_request+0x38>
    5a42:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5a46:	75 e0                	jne    5a28 <handle_client_request+0x38>
    5a48:	c6 00 00             	movb   $0x0,(%rax)
    5a4b:	8b 47 08             	mov    0x8(%rdi),%eax
    5a4e:	48 89 f2             	mov    %rsi,%rdx
    5a51:	4c 89 d7             	mov    %r10,%rdi
    5a54:	89 c6                	mov    %eax,%esi
    5a56:	e8 75 fe ff ff       	call   58d0 <handle_http_method>
    5a5b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5a63:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5a6c:	75 39                	jne    5aa7 <handle_client_request+0xb7>
    5a6e:	31 c0                	xor    %eax,%eax
    5a70:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5a77:	c3                   	ret
    5a78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5a80:	48 8b 0d 99 55 00 00 	mov    0x5599(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5a87:	ba 12 00 00 00       	mov    $0x12,%edx
    5a8c:	be 01 00 00 00       	mov    $0x1,%esi
    5a91:	48 8d 3d c6 26 00 00 	lea    0x26c6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5a98:	e8 93 ca ff ff       	call   2530 <fwrite@plt>
    5a9d:	bf 01 00 00 00       	mov    $0x1,%edi
    5aa2:	e8 69 ca ff ff       	call   2510 <exit@plt>
    5aa7:	e8 d4 c8 ff ff       	call   2380 <__stack_chk_fail@plt>
    5aac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005ab0 <add_accept_request>:
    5ab0:	f3 0f 1e fa          	endbr64
    5ab4:	55                   	push   %rbp
    5ab5:	53                   	push   %rbx
    5ab6:	48 89 cb             	mov    %rcx,%rbx
    5ab9:	48 83 ec 08          	sub    $0x8,%rsp
    5abd:	8b 41 44             	mov    0x44(%rcx),%eax
    5ac0:	4c 8b 03             	mov    (%rbx),%r8
    5ac3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    5ac9:	83 c0 01             	add    $0x1,%eax
    5acc:	45 8b 08             	mov    (%r8),%r9d
    5acf:	f6 c1 02             	test   $0x2,%cl
    5ad2:	74 00                	je     5ad4 <add_accept_request+0x24>
    5ad4:	41 89 c0             	mov    %eax,%r8d
    5ad7:	45 29 c8             	sub    %r9d,%r8d
    5ada:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    5ade:	0f 82 28 cb ff ff    	jb     260c <add_accept_request.cold>
    5ae4:	c1 e9 0a             	shr    $0xa,%ecx
    5ae7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    5aea:	23 6b 58             	and    0x58(%rbx),%ebp
    5aed:	89 43 44             	mov    %eax,0x44(%rbx)
    5af0:	83 e1 01             	and    $0x1,%ecx
    5af3:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5af7:	d3 e5                	shl    %cl,%ebp
    5af9:	48 c1 e5 06          	shl    $0x6,%rbp
    5afd:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5b01:	89 7d 04             	mov    %edi,0x4(%rbp)
    5b04:	bf 10 00 00 00       	mov    $0x10,%edi
    5b09:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    5b10:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    5b14:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    5b18:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    5b20:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    5b28:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5b2c:	e8 3f c9 ff ff       	call   2470 <malloc@plt>
    5b31:	48 89 df             	mov    %rbx,%rdi
    5b34:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    5b3a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    5b3e:	48 83 c4 08          	add    $0x8,%rsp
    5b42:	5b                   	pop    %rbx
    5b43:	5d                   	pop    %rbp
    5b44:	e9 47 c8 ff ff       	jmp    2390 <io_uring_submit@plt>
    5b49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005b50 <io_thread>:
    5b50:	f3 0f 1e fa          	endbr64
    5b54:	41 57                	push   %r15
    5b56:	31 d2                	xor    %edx,%edx
    5b58:	41 56                	push   %r14
    5b5a:	41 55                	push   %r13
    5b5c:	41 54                	push   %r12
    5b5e:	55                   	push   %rbp
    5b5f:	48 89 fd             	mov    %rdi,%rbp
    5b62:	53                   	push   %rbx
    5b63:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    5b6a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5b73:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    5b7b:	48 8b 47 58          	mov    0x58(%rdi),%rax
    5b7f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5b84:	bf 00 01 00 00       	mov    $0x100,%edi
    5b89:	48 89 de             	mov    %rbx,%rsi
    5b8c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5b90:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5b95:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5b9a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    5b9f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5ba4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    5bac:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5bb1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5bb9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5bbe:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5bc6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5bcb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5bd3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5bd8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5be0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5be5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    5bed:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5bf5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5bfd:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5c05:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5c0d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5c15:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5c1d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5c25:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5c2d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5c35:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5c3d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5c44:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    5c4c:	e8 ff c7 ff ff       	call   2450 <io_uring_queue_init@plt>
    5c51:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5c55:	31 f6                	xor    %esi,%esi
    5c57:	e8 f4 c8 ff ff       	call   2550 <io_uring_register_eventfd@plt>
    5c5c:	31 d2                	xor    %edx,%edx
    5c5e:	be 01 00 00 00       	mov    $0x1,%esi
    5c63:	bf 02 00 00 00       	mov    $0x2,%edi
    5c68:	e8 43 c9 ff ff       	call   25b0 <socket@plt>
    5c6d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5c70:	0f 84 d8 c9 ff ff    	je     264e <io_thread.cold+0x38>
    5c76:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5c7b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5c81:	89 c7                	mov    %eax,%edi
    5c83:	41 89 c4             	mov    %eax,%r12d
    5c86:	ba 02 00 00 00       	mov    $0x2,%edx
    5c8b:	be 01 00 00 00       	mov    $0x1,%esi
    5c90:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    5c98:	e8 a3 c6 ff ff       	call   2340 <setsockopt@plt>
    5c9d:	85 c0                	test   %eax,%eax
    5c9f:	0f 88 7d c9 ff ff    	js     2622 <io_thread.cold+0xc>
    5ca5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    5caa:	ba 10 00 00 00       	mov    $0x10,%edx
    5caf:	44 89 e7             	mov    %r12d,%edi
    5cb2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5cbb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    5cc3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
    5ccb:	e8 f0 c7 ff ff       	call   24c0 <bind@plt>
    5cd0:	85 c0                	test   %eax,%eax
    5cd2:	0f 88 82 c9 ff ff    	js     265a <io_thread.cold+0x44>
    5cd8:	be 0a 00 00 00       	mov    $0xa,%esi
    5cdd:	44 89 e7             	mov    %r12d,%edi
    5ce0:	e8 9b c7 ff ff       	call   2480 <listen@plt>
    5ce5:	85 c0                	test   %eax,%eax
    5ce7:	0f 88 41 c9 ff ff    	js     262e <io_thread.cold+0x18>
    5ced:	ba db 18 00 00       	mov    $0x18db,%edx
    5cf2:	48 8d 35 aa 24 00 00 	lea    0x24aa(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5cf9:	bf 01 00 00 00       	mov    $0x1,%edi
    5cfe:	31 c0                	xor    %eax,%eax
    5d00:	e8 ab c7 ff ff       	call   24b0 <__printf_chk@plt>
    5d05:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5d0a:	48 89 d9             	mov    %rbx,%rcx
    5d0d:	44 89 e7             	mov    %r12d,%edi
    5d10:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5d15:	48 89 c6             	mov    %rax,%rsi
    5d18:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5d1d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    5d22:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    5d2a:	e8 81 fd ff ff       	call   5ab0 <add_accept_request>
    5d2f:	bf 01 00 00 00       	mov    $0x1,%edi
    5d34:	be 10 00 00 00       	mov    $0x10,%esi
    5d39:	e8 c2 c6 ff ff       	call   2400 <calloc@plt>
    5d3e:	bf 0a 00 00 00       	mov    $0xa,%edi
    5d43:	49 89 c5             	mov    %rax,%r13
    5d46:	e8 25 c7 ff ff       	call   2470 <malloc@plt>
    5d4b:	48 85 c0             	test   %rax,%rax
    5d4e:	0f 84 ae 04 00 00    	je     6202 <io_thread+0x6b2>
    5d54:	49 89 45 00          	mov    %rax,0x0(%r13)
    5d58:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5d5f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5d66:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    5d6e:	8d 50 01             	lea    0x1(%rax),%edx
    5d71:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5d76:	8b 30                	mov    (%rax),%esi
    5d78:	f6 c1 02             	test   $0x2,%cl
    5d7b:	0f 85 0f 04 00 00    	jne    6190 <io_thread+0x640>
    5d81:	89 d0                	mov    %edx,%eax
    5d83:	29 f0                	sub    %esi,%eax
    5d85:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5d8c:	0f 82 b2 c8 ff ff    	jb     2644 <io_thread.cold+0x2e>
    5d92:	c1 e9 0a             	shr    $0xa,%ecx
    5d95:	48 8d 75 60          	lea    0x60(%rbp),%rsi
    5d99:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5d9d:	48 89 df             	mov    %rbx,%rdi
    5da0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5da7:	83 e1 01             	and    $0x1,%ecx
    5daa:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5db1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5db8:	d3 e0                	shl    %cl,%eax
    5dba:	8b 55 60             	mov    0x60(%rbp),%edx
    5dbd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5dc2:	48 c1 e0 06          	shl    $0x6,%rax
    5dc6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5dce:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5dd4:	89 50 04             	mov    %edx,0x4(%rax)
    5dd7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5ddf:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5de3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5deb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5df3:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5df7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5dfb:	e8 90 c5 ff ff       	call   2390 <io_uring_submit@plt>
    5e00:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5e04:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5e09:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5e11:	0f 85 d7 01 00 00    	jne    5fee <io_thread+0x49e>
    5e17:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5e1c:	4d 89 ce             	mov    %r9,%r14
    5e1f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5e24:	0f 1f 40 00          	nopl   0x0(%rax)
    5e28:	48 8d 3d 8a 23 00 00 	lea    0x238a(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5e2f:	e8 fc c4 ff ff       	call   2330 <puts@plt>
    5e34:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5e3b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    5e42:	c1 e9 0b             	shr    $0xb,%ecx
    5e45:	83 e1 01             	and    $0x1,%ecx
    5e48:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5e50:	8b 00                	mov    (%rax),%eax
    5e52:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5e5a:	8b 16                	mov    (%rsi),%edx
    5e5c:	39 d0                	cmp    %edx,%eax
    5e5e:	74 36                	je     5e96 <io_thread+0x346>
    5e60:	89 f8                	mov    %edi,%eax
    5e62:	21 d0                	and    %edx,%eax
    5e64:	d3 e0                	shl    %cl,%eax
    5e66:	48 c1 e0 04          	shl    $0x4,%rax
    5e6a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    5e72:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5e7a:	0f 85 a8 01 00 00    	jne    6028 <io_thread+0x4d8>
    5e80:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5e84:	0f 85 0e 03 00 00    	jne    6198 <io_thread+0x648>
    5e8a:	8b 40 08             	mov    0x8(%rax),%eax
    5e8d:	83 c2 01             	add    $0x1,%edx
    5e90:	89 16                	mov    %edx,(%rsi)
    5e92:	85 c0                	test   %eax,%eax
    5e94:	79 b2                	jns    5e48 <io_thread+0x2f8>
    5e96:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    5e9f:	90                   	nop
    5ea0:	45 31 c0             	xor    %r8d,%r8d
    5ea3:	31 d2                	xor    %edx,%edx
    5ea5:	b9 01 00 00 00       	mov    $0x1,%ecx
    5eaa:	4c 89 f6             	mov    %r14,%rsi
    5ead:	48 89 df             	mov    %rbx,%rdi
    5eb0:	e8 eb c5 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5eb5:	41 89 c7             	mov    %eax,%r15d
    5eb8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5ebd:	48 83 38 01          	cmpq   $0x1,(%rax)
    5ec1:	0f 84 e1 02 00 00    	je     61a8 <io_thread+0x658>
    5ec7:	48 8d 3d 11 23 00 00 	lea    0x2311(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5ece:	e8 5d c4 ff ff       	call   2330 <puts@plt>
    5ed3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5ed8:	4c 8b 22             	mov    (%rdx),%r12
    5edb:	45 85 ff             	test   %r15d,%r15d
    5ede:	0f 88 32 c7 ff ff    	js     2616 <io_thread.cold>
    5ee4:	8b 42 08             	mov    0x8(%rdx),%eax
    5ee7:	45 8b 04 24          	mov    (%r12),%r8d
    5eeb:	85 c0                	test   %eax,%eax
    5eed:	0f 88 d5 02 00 00    	js     61c8 <io_thread+0x678>
    5ef3:	41 83 f8 01          	cmp    $0x1,%r8d
    5ef7:	0f 84 7b 01 00 00    	je     6078 <io_thread+0x528>
    5efd:	41 83 f8 02          	cmp    $0x2,%r8d
    5f01:	0f 84 a1 01 00 00    	je     60a8 <io_thread+0x558>
    5f07:	45 85 c0             	test   %r8d,%r8d
    5f0a:	0f 85 50 01 00 00    	jne    6060 <io_thread+0x510>
    5f10:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5f15:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5f1a:	48 89 d9             	mov    %rbx,%rcx
    5f1d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5f21:	e8 8a fb ff ff       	call   5ab0 <add_accept_request>
    5f26:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f2b:	48 89 de             	mov    %rbx,%rsi
    5f2e:	8b 78 08             	mov    0x8(%rax),%edi
    5f31:	e8 1a f5 ff ff       	call   5450 <add_read_request>
    5f36:	4c 89 e7             	mov    %r12,%rdi
    5f39:	e8 c2 c3 ff ff       	call   2300 <free@plt>
    5f3e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f43:	48 85 c0             	test   %rax,%rax
    5f46:	0f 85 14 01 00 00    	jne    6060 <io_thread+0x510>
    5f4c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5f53:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5f5a:	8d 50 01             	lea    0x1(%rax),%edx
    5f5d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5f62:	8b 30                	mov    (%rax),%esi
    5f64:	f6 c1 02             	test   $0x2,%cl
    5f67:	74 00                	je     5f69 <io_thread+0x419>
    5f69:	89 d0                	mov    %edx,%eax
    5f6b:	29 f0                	sub    %esi,%eax
    5f6d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5f74:	0f 82 c0 c6 ff ff    	jb     263a <io_thread.cold+0x24>
    5f7a:	c1 e9 0a             	shr    $0xa,%ecx
    5f7d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5f82:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5f86:	48 89 df             	mov    %rbx,%rdi
    5f89:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5f90:	83 e1 01             	and    $0x1,%ecx
    5f93:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5f9a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5fa1:	d3 e0                	shl    %cl,%eax
    5fa3:	8b 55 60             	mov    0x60(%rbp),%edx
    5fa6:	48 c1 e0 06          	shl    $0x6,%rax
    5faa:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5fb2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5fb8:	89 50 04             	mov    %edx,0x4(%rax)
    5fbb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5fc3:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5fc7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5fcf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5fd7:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5fdb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5fdf:	e8 ac c3 ff ff       	call   2390 <io_uring_submit@plt>
    5fe4:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5fe8:	0f 84 3a fe ff ff    	je     5e28 <io_thread+0x2d8>
    5fee:	48 8d 3d 23 22 00 00 	lea    0x2223(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5ff5:	e8 36 c3 ff ff       	call   2330 <puts@plt>
    5ffa:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    6002:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    600b:	0f 85 18 02 00 00    	jne    6229 <io_thread+0x6d9>
    6011:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    6018:	31 c0                	xor    %eax,%eax
    601a:	5b                   	pop    %rbx
    601b:	5d                   	pop    %rbp
    601c:	41 5c                	pop    %r12
    601e:	41 5d                	pop    %r13
    6020:	41 5e                	pop    %r14
    6022:	41 5f                	pop    %r15
    6024:	c3                   	ret
    6025:	0f 1f 00             	nopl   (%rax)
    6028:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    602d:	48 85 c0             	test   %rax,%rax
    6030:	0f 84 6a fe ff ff    	je     5ea0 <io_thread+0x350>
    6036:	48 83 38 01          	cmpq   $0x1,(%rax)
    603a:	0f 84 68 01 00 00    	je     61a8 <io_thread+0x658>
    6040:	48 8d 3d 98 21 00 00 	lea    0x2198(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    6047:	e8 e4 c2 ff ff       	call   2330 <puts@plt>
    604c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    6051:	4c 8b 22             	mov    (%rdx),%r12
    6054:	e9 8b fe ff ff       	jmp    5ee4 <io_thread+0x394>
    6059:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6060:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    6068:	8b 02                	mov    (%rdx),%eax
    606a:	83 c0 01             	add    $0x1,%eax
    606d:	89 02                	mov    %eax,(%rdx)
    606f:	e9 d8 fe ff ff       	jmp    5f4c <io_thread+0x3fc>
    6074:	0f 1f 40 00          	nopl   0x0(%rax)
    6078:	85 c0                	test   %eax,%eax
    607a:	75 74                	jne    60f0 <io_thread+0x5a0>
    607c:	48 8b 0d 9d 4f 00 00 	mov    0x4f9d(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6083:	ba 0f 00 00 00       	mov    $0xf,%edx
    6088:	be 01 00 00 00       	mov    $0x1,%esi
    608d:	48 8d 3d 74 21 00 00 	lea    0x2174(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    6094:	e8 97 c4 ff ff       	call   2530 <fwrite@plt>
    6099:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    609e:	e9 a0 fe ff ff       	jmp    5f43 <io_thread+0x3f3>
    60a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60a8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    60ad:	45 31 ff             	xor    %r15d,%r15d
    60b0:	85 c0                	test   %eax,%eax
    60b2:	7e 20                	jle    60d4 <io_thread+0x584>
    60b4:	0f 1f 40 00          	nopl   0x0(%rax)
    60b8:	4c 89 f8             	mov    %r15,%rax
    60bb:	49 83 c7 01          	add    $0x1,%r15
    60bf:	48 c1 e0 04          	shl    $0x4,%rax
    60c3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    60c8:	e8 33 c2 ff ff       	call   2300 <free@plt>
    60cd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    60d2:	7f e4                	jg     60b8 <io_thread+0x568>
    60d4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    60d9:	e8 f2 c2 ff ff       	call   23d0 <close@plt>
    60de:	4c 89 e7             	mov    %r12,%rdi
    60e1:	e8 1a c2 ff ff       	call   2300 <free@plt>
    60e6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    60eb:	e9 53 fe ff ff       	jmp    5f43 <io_thread+0x3f3>
    60f0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    60f5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    60fa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    6102:	eb 11                	jmp    6115 <io_thread+0x5c5>
    6104:	0f 1f 40 00          	nopl   0x0(%rax)
    6108:	48 83 c0 01          	add    $0x1,%rax
    610c:	48 83 c2 01          	add    $0x1,%rdx
    6110:	48 39 c6             	cmp    %rax,%rsi
    6113:	74 4b                	je     6160 <io_thread+0x610>
    6115:	0f b6 0a             	movzbl (%rdx),%ecx
    6118:	88 08                	mov    %cl,(%rax)
    611a:	80 f9 0d             	cmp    $0xd,%cl
    611d:	75 e9                	jne    6108 <io_thread+0x5b8>
    611f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    6123:	75 e3                	jne    6108 <io_thread+0x5b8>
    6125:	c6 00 00             	movb   $0x0,(%rax)
    6128:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    612d:	48 89 da             	mov    %rbx,%rdx
    6130:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    6135:	e8 96 f7 ff ff       	call   58d0 <handle_http_method>
    613a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    613f:	e8 bc c1 ff ff       	call   2300 <free@plt>
    6144:	4c 89 e7             	mov    %r12,%rdi
    6147:	e8 b4 c1 ff ff       	call   2300 <free@plt>
    614c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    6151:	e9 ed fd ff ff       	jmp    5f43 <io_thread+0x3f3>
    6156:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6160:	48 8b 0d b9 4e 00 00 	mov    0x4eb9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6167:	ba 12 00 00 00       	mov    $0x12,%edx
    616c:	be 01 00 00 00       	mov    $0x1,%esi
    6171:	48 8d 3d e6 1f 00 00 	lea    0x1fe6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6178:	e8 b3 c3 ff ff       	call   2530 <fwrite@plt>
    617d:	bf 01 00 00 00       	mov    $0x1,%edi
    6182:	e8 89 c3 ff ff       	call   2510 <exit@plt>
    6187:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6190:	e9 ec fb ff ff       	jmp    5d81 <io_thread+0x231>
    6195:	0f 1f 00             	nopl   (%rax)
    6198:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    619d:	e9 94 fe ff ff       	jmp    6036 <io_thread+0x4e6>
    61a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    61a8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    61b0:	48 8d 3d 14 20 00 00 	lea    0x2014(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    61b7:	8b 02                	mov    (%rdx),%eax
    61b9:	83 c0 01             	add    $0x1,%eax
    61bc:	89 02                	mov    %eax,(%rdx)
    61be:	e8 6d c1 ff ff       	call   2330 <puts@plt>
    61c3:	e9 26 fe ff ff       	jmp    5fee <io_thread+0x49e>
    61c8:	f7 d8                	neg    %eax
    61ca:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    61cf:	89 c7                	mov    %eax,%edi
    61d1:	e8 9a c3 ff ff       	call   2570 <strerror@plt>
    61d6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    61db:	be 01 00 00 00       	mov    $0x1,%esi
    61e0:	48 8b 3d 39 4e 00 00 	mov    0x4e39(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    61e7:	48 89 c1             	mov    %rax,%rcx
    61ea:	48 8d 15 0f 24 00 00 	lea    0x240f(%rip),%rdx        # 8600 <_IO_stdin_used+0x600>
    61f1:	31 c0                	xor    %eax,%eax
    61f3:	e8 48 c3 ff ff       	call   2540 <__fprintf_chk@plt>
    61f8:	bf 01 00 00 00       	mov    $0x1,%edi
    61fd:	e8 0e c3 ff ff       	call   2510 <exit@plt>
    6202:	48 8b 0d 17 4e 00 00 	mov    0x4e17(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6209:	ba 28 00 00 00       	mov    $0x28,%edx
    620e:	be 01 00 00 00       	mov    $0x1,%esi
    6213:	48 8d 3d b6 23 00 00 	lea    0x23b6(%rip),%rdi        # 85d0 <_IO_stdin_used+0x5d0>
    621a:	e8 11 c3 ff ff       	call   2530 <fwrite@plt>
    621f:	bf 01 00 00 00       	mov    $0x1,%edi
    6224:	e8 e7 c2 ff ff       	call   2510 <exit@plt>
    6229:	e8 52 c1 ff ff       	call   2380 <__stack_chk_fail@plt>
    622e:	66 90                	xchg   %ax,%ax

0000000000006230 <barriered_work_ingest>:
    6230:	f3 0f 1e fa          	endbr64
    6234:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    623b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    6241:	85 c9                	test   %ecx,%ecx
    6243:	0f 8e ea 00 00 00    	jle    6333 <barriered_work_ingest+0x103>
    6249:	41 56                	push   %r14
    624b:	41 55                	push   %r13
    624d:	45 31 ed             	xor    %r13d,%r13d
    6250:	41 54                	push   %r12
    6252:	49 89 fc             	mov    %rdi,%r12
    6255:	55                   	push   %rbp
    6256:	53                   	push   %rbx
    6257:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    625b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6260:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    6264:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    626c:	31 db                	xor    %ebx,%ebx
    626e:	8b 10                	mov    (%rax),%edx
    6270:	85 d2                	test   %edx,%edx
    6272:	7e 26                	jle    629a <barriered_work_ingest+0x6a>
    6274:	48 8b 48 08          	mov    0x8(%rax),%rcx
    6278:	48 89 dd             	mov    %rbx,%rbp
    627b:	48 c1 e5 08          	shl    $0x8,%rbp
    627f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    6283:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    628a:	74 24                	je     62b0 <barriered_work_ingest+0x80>
    628c:	48 83 c3 01          	add    $0x1,%rbx
    6290:	39 da                	cmp    %ebx,%edx
    6292:	7f e4                	jg     6278 <barriered_work_ingest+0x48>
    6294:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    629a:	49 83 c5 01          	add    $0x1,%r13
    629e:	44 39 e9             	cmp    %r13d,%ecx
    62a1:	7f bd                	jg     6260 <barriered_work_ingest+0x30>
    62a3:	5b                   	pop    %rbx
    62a4:	31 c0                	xor    %eax,%eax
    62a6:	5d                   	pop    %rbp
    62a7:	41 5c                	pop    %r12
    62a9:	41 5d                	pop    %r13
    62ab:	41 5e                	pop    %r14
    62ad:	c3                   	ret
    62ae:	66 90                	xchg   %ax,%ax
    62b0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
    62b9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    62c0:	bf 04 00 00 00       	mov    $0x4,%edi
    62c5:	48 c1 e6 05          	shl    $0x5,%rsi
    62c9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    62d0:	48 83 c6 10          	add    $0x10,%rsi
    62d4:	e8 77 c0 ff ff       	call   2350 <clock_gettime@plt>
    62d9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    62e1:	48 8b 40 50          	mov    0x50(%rax),%rax
    62e5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    62e9:	48 03 68 08          	add    0x8(%rax),%rbp
    62ed:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    62f7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    62fd:	83 c0 01             	add    $0x1,%eax
    6300:	99                   	cltd
    6301:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    6307:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
    630d:	0f ae f8             	sfence
    6310:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    6318:	48 83 c3 01          	add    $0x1,%rbx
    631c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6320:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    6324:	8b 10                	mov    (%rax),%edx
    6326:	39 da                	cmp    %ebx,%edx
    6328:	0f 8f 46 ff ff ff    	jg     6274 <barriered_work_ingest+0x44>
    632e:	e9 61 ff ff ff       	jmp    6294 <barriered_work_ingest+0x64>
    6333:	31 c0                	xor    %eax,%eax
    6335:	c3                   	ret
    6336:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006340 <barriered_thread>:
    6340:	f3 0f 1e fa          	endbr64
    6344:	41 56                	push   %r14
    6346:	41 55                	push   %r13
    6348:	41 54                	push   %r12
    634a:	45 31 e4             	xor    %r12d,%r12d
    634d:	55                   	push   %rbp
    634e:	31 ed                	xor    %ebp,%ebp
    6350:	53                   	push   %rbx
    6351:	48 89 fb             	mov    %rdi,%rbx
    6354:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6358:	0f 85 74 02 00 00    	jne    65d2 <barriered_thread+0x292>
    635e:	8b 43 40             	mov    0x40(%rbx),%eax
    6361:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6368:	41 39 c4             	cmp    %eax,%r12d
    636b:	0f 8d 6f 01 00 00    	jge    64e0 <barriered_thread+0x1a0>
    6371:	49 63 fc             	movslq %r12d,%rdi
    6374:	48 c1 e7 09          	shl    $0x9,%rdi
    6378:	49 89 fd             	mov    %rdi,%r13
    637b:	eb 32                	jmp    63af <barriered_thread+0x6f>
    637d:	0f 1f 00             	nopl   (%rax)
    6380:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6384:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6388:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    638c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6390:	4c 01 ef             	add    %r13,%rdi
    6393:	e8 98 fe ff ff       	call   6230 <barriered_work_ingest>
    6398:	8b 43 40             	mov    0x40(%rbx),%eax
    639b:	41 83 c4 01          	add    $0x1,%r12d
    639f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    63a6:	44 39 e0             	cmp    %r12d,%eax
    63a9:	0f 8e 19 02 00 00    	jle    65c8 <barriered_thread+0x288>
    63af:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    63b3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    63b7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    63be:	75 c0                	jne    6380 <barriered_thread+0x40>
    63c0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
    63c4:	83 e8 01             	sub    $0x1,%eax
    63c7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    63cc:	45 85 e4             	test   %r12d,%r12d
    63cf:	0f 4f c1             	cmovg  %ecx,%eax
    63d2:	45 85 c0             	test   %r8d,%r8d
    63d5:	0f 8e 2d 01 00 00    	jle    6508 <barriered_thread+0x1c8>
    63db:	48 63 c8             	movslq %eax,%rcx
    63de:	48 8b 43 18          	mov    0x18(%rbx),%rax
    63e2:	49 63 d0             	movslq %r8d,%rdx
    63e5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
    63eb:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    63f2:	48 c1 e1 09          	shl    $0x9,%rcx
    63f6:	45 31 d2             	xor    %r10d,%r10d
    63f9:	45 31 f6             	xor    %r14d,%r14d
    63fc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6400:	48 8b 10             	mov    (%rax),%rdx
    6403:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6407:	49 01 cb             	add    %rcx,%r11
    640a:	4c 89 da             	mov    %r11,%rdx
    640d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6414:	75 04                	jne    641a <barriered_thread+0xda>
    6416:	41 83 c6 01          	add    $0x1,%r14d
    641a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6420:	75 04                	jne    6426 <barriered_thread+0xe6>
    6422:	41 83 c2 01          	add    $0x1,%r10d
    6426:	48 83 c0 08          	add    $0x8,%rax
    642a:	48 39 c6             	cmp    %rax,%rsi
    642d:	75 d1                	jne    6400 <barriered_thread+0xc0>
    642f:	45 85 d2             	test   %r10d,%r10d
    6432:	0f 84 c0 00 00 00    	je     64f8 <barriered_thread+0x1b8>
    6438:	45 39 d0             	cmp    %r10d,%r8d
    643b:	0f 84 b7 00 00 00    	je     64f8 <barriered_thread+0x1b8>
    6441:	45 85 f6             	test   %r14d,%r14d
    6444:	74 0a                	je     6450 <barriered_thread+0x110>
    6446:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    644a:	0f 85 ae 01 00 00    	jne    65fe <barriered_thread+0x2be>
    6450:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6454:	4c 01 ea             	add    %r13,%rdx
    6457:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
    645e:	45 85 e4             	test   %r12d,%r12d
    6461:	75 14                	jne    6477 <barriered_thread+0x137>
    6463:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    646a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6471:	0f 8c 69 01 00 00    	jl     65e0 <barriered_thread+0x2a0>
    6477:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    647b:	48 8b 43 18          	mov    0x18(%rbx),%rax
    647f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
    6489:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    648d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6491:	4c 01 ef             	add    %r13,%rdi
    6494:	ff 92 18 01 00 00    	call   *0x118(%rdx)
    649a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    649e:	4c 01 e8             	add    %r13,%rax
    64a1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    64a8:	8b 43 40             	mov    0x40(%rbx),%eax
    64ab:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
    64b0:	83 e8 01             	sub    $0x1,%eax
    64b3:	44 39 e0             	cmp    %r12d,%eax
    64b6:	0f 84 a4 00 00 00    	je     6560 <barriered_thread+0x220>
    64bc:	0f ae f8             	sfence
    64bf:	85 ed                	test   %ebp,%ebp
    64c1:	0f 84 d1 00 00 00    	je     6598 <barriered_thread+0x258>
    64c7:	bd 01 00 00 00       	mov    $0x1,%ebp
    64cc:	e9 c7 fe ff ff       	jmp    6398 <barriered_thread+0x58>
    64d1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    64d5:	0f 85 f7 00 00 00    	jne    65d2 <barriered_thread+0x292>
    64db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    64e0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    64e8:	85 c0                	test   %eax,%eax
    64ea:	7e e5                	jle    64d1 <barriered_thread+0x191>
    64ec:	45 31 e4             	xor    %r12d,%r12d
    64ef:	e9 7d fe ff ff       	jmp    6371 <barriered_thread+0x31>
    64f4:	0f 1f 40 00          	nopl   0x0(%rax)
    64f8:	83 fd 01             	cmp    $0x1,%ebp
    64fb:	74 1b                	je     6518 <barriered_thread+0x1d8>
    64fd:	31 ed                	xor    %ebp,%ebp
    64ff:	e9 3d ff ff ff       	jmp    6441 <barriered_thread+0x101>
    6504:	0f 1f 40 00          	nopl   0x0(%rax)
    6508:	83 fd 01             	cmp    $0x1,%ebp
    650b:	0f 85 43 ff ff ff    	jne    6454 <barriered_thread+0x114>
    6511:	45 31 f6             	xor    %r14d,%r14d
    6514:	0f 1f 40 00          	nopl   0x0(%rax)
    6518:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    651f:	bf 04 00 00 00       	mov    $0x4,%edi
    6524:	31 ed                	xor    %ebp,%ebp
    6526:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    652a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6531:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6536:	e8 15 be ff ff       	call   2350 <clock_gettime@plt>
    653b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6542:	48 83 c0 01          	add    $0x1,%rax
    6546:	48 99                	cqto
    6548:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    654f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
    6556:	e9 e6 fe ff ff       	jmp    6441 <barriered_thread+0x101>
    655b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6560:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6567:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    656e:	0f 8d 48 ff ff ff    	jge    64bc <barriered_thread+0x17c>
    6574:	48 c1 e6 04          	shl    $0x4,%rsi
    6578:	bf 04 00 00 00       	mov    $0x4,%edi
    657d:	48 03 73 70          	add    0x70(%rbx),%rsi
    6581:	e8 ca bd ff ff       	call   2350 <clock_gettime@plt>
    6586:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    658e:	e9 29 ff ff ff       	jmp    64bc <barriered_thread+0x17c>
    6593:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6598:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    659f:	bf 04 00 00 00       	mov    $0x4,%edi
    65a4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    65a8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    65af:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    65b3:	44 89 66 20          	mov    %r12d,0x20(%rsi)
    65b7:	e8 94 bd ff ff       	call   2350 <clock_gettime@plt>
    65bc:	e9 06 ff ff ff       	jmp    64c7 <barriered_thread+0x187>
    65c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    65c8:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    65cc:	0f 84 96 fd ff ff    	je     6368 <barriered_thread+0x28>
    65d2:	5b                   	pop    %rbx
    65d3:	31 c0                	xor    %eax,%eax
    65d5:	5d                   	pop    %rbp
    65d6:	41 5c                	pop    %r12
    65d8:	41 5d                	pop    %r13
    65da:	41 5e                	pop    %r14
    65dc:	c3                   	ret
    65dd:	0f 1f 00             	nopl   (%rax)
    65e0:	48 c1 e6 04          	shl    $0x4,%rsi
    65e4:	bf 04 00 00 00       	mov    $0x4,%edi
    65e9:	48 03 73 68          	add    0x68(%rbx),%rsi
    65ed:	e8 5e bd ff ff       	call   2350 <clock_gettime@plt>
    65f2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    65f6:	4c 01 ea             	add    %r13,%rdx
    65f9:	e9 79 fe ff ff       	jmp    6477 <barriered_thread+0x137>
    65fe:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6602:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6606:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    660a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    660e:	4c 01 ef             	add    %r13,%rdi
    6611:	e8 1a fc ff ff       	call   6230 <barriered_work_ingest>
    6616:	e9 39 fd ff ff       	jmp    6354 <barriered_thread+0x14>
    661b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006620 <receive>:
    6620:	f3 0f 1e fa          	endbr64
    6624:	41 56                	push   %r14
    6626:	41 55                	push   %r13
    6628:	41 54                	push   %r12
    662a:	55                   	push   %rbp
    662b:	53                   	push   %rbx
    662c:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    6633:	45 85 e4             	test   %r12d,%r12d
    6636:	0f 8e 27 01 00 00    	jle    6763 <receive+0x143>
    663c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    6643:	48 89 fe             	mov    %rdi,%rsi
    6646:	31 db                	xor    %ebx,%ebx
    6648:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    664c:	49 89 ed             	mov    %rbp,%r13
    664f:	90                   	nop
    6650:	41 39 dd             	cmp    %ebx,%r13d
    6653:	0f 84 fd 00 00 00    	je     6756 <receive+0x136>
    6659:	48 89 d8             	mov    %rbx,%rax
    665c:	48 c1 e0 08          	shl    $0x8,%rax
    6660:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    6667:	48 8b 10             	mov    (%rax),%rdx
    666a:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    6670:	83 f8 01             	cmp    $0x1,%eax
    6673:	74 11                	je     6686 <receive+0x66>
    6675:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    667c:	75 08                	jne    6686 <receive+0x66>
    667e:	85 c0                	test   %eax,%eax
    6680:	0f 84 d0 00 00 00    	je     6756 <receive+0x136>
    6686:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    668d:	48 85 ff             	test   %rdi,%rdi
    6690:	0f 8e a2 00 00 00    	jle    6738 <receive+0x118>
    6696:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    669d:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    66a4:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    66a8:	4c 8b 1a             	mov    (%rdx),%r11
    66ab:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    66af:	49 01 f9             	add    %rdi,%r9
    66b2:	49 01 f8             	add    %rdi,%r8
    66b5:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    66bc:	eb 08                	jmp    66c6 <receive+0xa6>
    66be:	66 90                	xchg   %ax,%ax
    66c0:	48 83 e8 01          	sub    $0x1,%rax
    66c4:	72 72                	jb     6738 <receive+0x118>
    66c6:	4c 89 c9             	mov    %r9,%rcx
    66c9:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
    66d0:	48 29 c1             	sub    %rax,%rcx
    66d3:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
    66da:	4c 89 c1             	mov    %r8,%rcx
    66dd:	48 29 c1             	sub    %rax,%rcx
    66e0:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
    66e7:	48 89 f9             	mov    %rdi,%rcx
    66ea:	48 29 c1             	sub    %rax,%rcx
    66ed:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
    66f4:	48 63 c8             	movslq %eax,%rcx
    66f7:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
    66fb:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    66ff:	75 bf                	jne    66c0 <receive+0xa0>
    6701:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    6705:	75 b9                	jne    66c0 <receive+0xa0>
    6707:	49 63 46 04          	movslq 0x4(%r14),%rax
    670b:	31 c9                	xor    %ecx,%ecx
    670d:	bf 01 00 00 00       	mov    $0x1,%edi
    6712:	ba 01 00 00 00       	mov    $0x1,%edx
    6717:	48 8d 35 0a 1f 00 00 	lea    0x1f0a(%rip),%rsi        # 8628 <_IO_stdin_used+0x628>
    671e:	48 39 e8             	cmp    %rbp,%rax
    6721:	0f 94 c1             	sete   %cl
    6724:	31 c0                	xor    %eax,%eax
    6726:	e8 85 bd ff ff       	call   24b0 <__printf_chk@plt>
    672b:	bf 01 00 00 00       	mov    $0x1,%edi
    6730:	e8 db bd ff ff       	call   2510 <exit@plt>
    6735:	0f 1f 00             	nopl   (%rax)
    6738:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
    6742:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
    674c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
    6756:	48 83 c3 01          	add    $0x1,%rbx
    675a:	49 39 dc             	cmp    %rbx,%r12
    675d:	0f 85 ed fe ff ff    	jne    6650 <receive+0x30>
    6763:	0f ae f8             	sfence
    6766:	31 c0                	xor    %eax,%eax
    6768:	5b                   	pop    %rbx
    6769:	5d                   	pop    %rbp
    676a:	41 5c                	pop    %r12
    676c:	41 5d                	pop    %r13
    676e:	41 5e                	pop    %r14
    6770:	c3                   	ret
    6771:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    677c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006780 <sendm>:
    6780:	f3 0f 1e fa          	endbr64
    6784:	41 57                	push   %r15
    6786:	48 89 f9             	mov    %rdi,%rcx
    6789:	41 56                	push   %r14
    678b:	41 55                	push   %r13
    678d:	41 54                	push   %r12
    678f:	55                   	push   %rbp
    6790:	53                   	push   %rbx
    6791:	48 63 bf 40 01 00 00 	movslq 0x140(%rdi),%rdi
    6798:	85 ff                	test   %edi,%edi
    679a:	7e 67                	jle    6803 <sendm+0x83>
    679c:	48 8b 81 28 01 00 00 	mov    0x128(%rcx),%rax
    67a3:	44 8b 48 08          	mov    0x8(%rax),%r9d
    67a7:	31 c0                	xor    %eax,%eax
    67a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    67b0:	41 39 c1             	cmp    %eax,%r9d
    67b3:	74 45                	je     67fa <sendm+0x7a>
    67b5:	48 89 c2             	mov    %rax,%rdx
    67b8:	48 c1 e2 08          	shl    $0x8,%rdx
    67bc:	48 03 91 70 01 00 00 	add    0x170(%rcx),%rdx
    67c3:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    67ca:	48 8b b2 80 00 00 00 	mov    0x80(%rdx),%rsi
    67d1:	48 85 f6             	test   %rsi,%rsi
    67d4:	7f 24                	jg     67fa <sendm+0x7a>
    67d6:	44 8b 82 00 01 00 00 	mov    0x100(%rdx),%r8d
    67dd:	41 83 f8 01          	cmp    $0x1,%r8d
    67e1:	74 0e                	je     67f1 <sendm+0x71>
    67e3:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    67ea:	75 05                	jne    67f1 <sendm+0x71>
    67ec:	45 85 c0             	test   %r8d,%r8d
    67ef:	74 09                	je     67fa <sendm+0x7a>
    67f1:	83 b9 88 01 00 00 01 	cmpl   $0x1,0x188(%rcx)
    67f8:	74 1e                	je     6818 <sendm+0x98>
    67fa:	48 83 c0 01          	add    $0x1,%rax
    67fe:	48 39 c7             	cmp    %rax,%rdi
    6801:	75 ad                	jne    67b0 <sendm+0x30>
    6803:	0f ae f8             	sfence
    6806:	31 c0                	xor    %eax,%eax
    6808:	5b                   	pop    %rbx
    6809:	5d                   	pop    %rbp
    680a:	41 5c                	pop    %r12
    680c:	41 5d                	pop    %r13
    680e:	41 5e                	pop    %r14
    6810:	41 5f                	pop    %r15
    6812:	c3                   	ret
    6813:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6818:	48 63 aa 88 00 00 00 	movslq 0x88(%rdx),%rbp
    681f:	48 39 ee             	cmp    %rbp,%rsi
    6822:	0f 8d a5 00 00 00    	jge    68cd <sendm+0x14d>
    6828:	48 8b 99 08 01 00 00 	mov    0x108(%rcx),%rbx
    682f:	4c 8b aa 80 03 00 00 	mov    0x380(%rdx),%r13
    6836:	4c 8b 1a             	mov    (%rdx),%r11
    6839:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    683e:	48 89 eb             	mov    %rbp,%rbx
    6841:	48 29 f3             	sub    %rsi,%rbx
    6844:	4c 8d 43 ff          	lea    -0x1(%rbx),%r8
    6848:	49 83 f8 02          	cmp    $0x2,%r8
    684c:	0f 86 0e 01 00 00    	jbe    6960 <sendm+0x1e0>
    6852:	4c 8d 14 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r10
    685a:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    6862:	4f 8d 34 13          	lea    (%r11,%r10,1),%r14
    6866:	4c 8d b9 90 01 00 00 	lea    0x190(%rcx),%r15
    686d:	4f 8d 24 03          	lea    (%r11,%r8,1),%r12
    6871:	4d 39 f7             	cmp    %r14,%r15
    6874:	73 7a                	jae    68f0 <sendm+0x170>
    6876:	4c 8d b1 98 01 00 00 	lea    0x198(%rcx),%r14
    687d:	4d 39 f4             	cmp    %r14,%r12
    6880:	73 6e                	jae    68f0 <sendm+0x170>
    6882:	4d 01 d8             	add    %r11,%r8
    6885:	4b 8d 34 13          	lea    (%r11,%r10,1),%rsi
    6889:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6890:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    6897:	49 83 c0 08          	add    $0x8,%r8
    689b:	4d 89 50 f8          	mov    %r10,-0x8(%r8)
    689f:	4c 39 c6             	cmp    %r8,%rsi
    68a2:	75 ec                	jne    6890 <sendm+0x110>
    68a4:	0f 1f 40 00          	nopl   0x0(%rax)
    68a8:	48 8b 74 24 f0       	mov    -0x10(%rsp),%rsi
    68ad:	48 01 de             	add    %rbx,%rsi
    68b0:	4c 01 eb             	add    %r13,%rbx
    68b3:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
    68ba:	48 89 9a 80 03 00 00 	mov    %rbx,0x380(%rdx)
    68c1:	48 89 aa 80 00 00 00 	mov    %rbp,0x80(%rdx)
    68c8:	4d 89 54 eb f8       	mov    %r10,-0x8(%r11,%rbp,8)
    68cd:	c7 82 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdx)
    68d7:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    68e1:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
    68eb:	e9 0a ff ff ff       	jmp    67fa <sendm+0x7a>
    68f0:	49 89 de             	mov    %rbx,%r14
    68f3:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    68fa:	4d 89 e0             	mov    %r12,%r8
    68fd:	49 d1 ee             	shr    %r14
    6900:	49 c1 e6 04          	shl    $0x4,%r14
    6904:	66 49 0f 6e c2       	movq   %r10,%xmm0
    6909:	4f 8d 3c 34          	lea    (%r12,%r14,1),%r15
    690d:	41 83 e6 10          	and    $0x10,%r14d
    6911:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    6915:	74 11                	je     6928 <sendm+0x1a8>
    6917:	49 83 c0 10          	add    $0x10,%r8
    691b:	41 0f 11 04 24       	movups %xmm0,(%r12)
    6920:	4d 39 f8             	cmp    %r15,%r8
    6923:	74 15                	je     693a <sendm+0x1ba>
    6925:	0f 1f 00             	nopl   (%rax)
    6928:	41 0f 11 00          	movups %xmm0,(%r8)
    692c:	49 83 c0 20          	add    $0x20,%r8
    6930:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
    6935:	4d 39 f8             	cmp    %r15,%r8
    6938:	75 ee                	jne    6928 <sendm+0x1a8>
    693a:	49 89 d8             	mov    %rbx,%r8
    693d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6941:	4c 01 c6             	add    %r8,%rsi
    6944:	f6 c3 01             	test   $0x1,%bl
    6947:	0f 84 5b ff ff ff    	je     68a8 <sendm+0x128>
    694d:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    6954:	4d 89 14 f3          	mov    %r10,(%r11,%rsi,8)
    6958:	e9 4b ff ff ff       	jmp    68a8 <sendm+0x128>
    695d:	0f 1f 00             	nopl   (%rax)
    6960:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    6968:	4c 8d 14 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r10
    6970:	e9 0d ff ff ff       	jmp    6882 <sendm+0x102>
    6975:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000006980 <mailboxkind>:
    6980:	f3 0f 1e fa          	endbr64
    6984:	85 f6                	test   %esi,%esi
    6986:	74 18                	je     69a0 <mailboxkind+0x20>
    6988:	31 c0                	xor    %eax,%eax
    698a:	83 fe 01             	cmp    $0x1,%esi
    698d:	74 01                	je     6990 <mailboxkind+0x10>
    698f:	c3                   	ret
    6990:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
    6997:	c3                   	ret
    6998:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    69a0:	48 8b 07             	mov    (%rdi),%rax
    69a3:	c3                   	ret
    69a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    69af:	90                   	nop

00000000000069b0 <setmailboxkind>:
    69b0:	f3 0f 1e fa          	endbr64
    69b4:	85 d2                	test   %edx,%edx
    69b6:	75 08                	jne    69c0 <setmailboxkind+0x10>
    69b8:	48 89 37             	mov    %rsi,(%rdi)
    69bb:	31 c0                	xor    %eax,%eax
    69bd:	c3                   	ret
    69be:	66 90                	xchg   %ax,%ax
    69c0:	83 fa 01             	cmp    $0x1,%edx
    69c3:	74 13                	je     69d8 <setmailboxkind+0x28>
    69c5:	83 fa 02             	cmp    $0x2,%edx
    69c8:	75 1e                	jne    69e8 <setmailboxkind+0x38>
    69ca:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
    69d1:	31 c0                	xor    %eax,%eax
    69d3:	c3                   	ret
    69d4:	0f 1f 40 00          	nopl   0x0(%rax)
    69d8:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
    69df:	31 c0                	xor    %eax,%eax
    69e1:	c3                   	ret
    69e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    69e8:	83 fa 03             	cmp    $0x3,%edx
    69eb:	75 ce                	jne    69bb <setmailboxkind+0xb>
    69ed:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
    69f4:	31 c0                	xor    %eax,%eax
    69f6:	c3                   	ret
    69f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006a00 <fswap>:
    6a00:	f3 0f 1e fa          	endbr64
    6a04:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    6a0b:	8b 97 9c 01 00 00    	mov    0x19c(%rdi),%edx
    6a11:	44 8b 97 30 01 00 00 	mov    0x130(%rdi),%r10d
    6a18:	48 63 4f 04          	movslq 0x4(%rdi),%rcx
    6a1c:	8b 86 c4 00 00 00    	mov    0xc4(%rsi),%eax
    6a22:	0f af d0             	imul   %eax,%edx
    6a25:	41 01 d2             	add    %edx,%r10d
    6a28:	85 c0                	test   %eax,%eax
    6a2a:	0f 8e 1b 01 00 00    	jle    6b4b <fswap+0x14b>
    6a30:	4d 63 d2             	movslq %r10d,%r10
    6a33:	41 56                	push   %r14
    6a35:	48 63 d2             	movslq %edx,%rdx
    6a38:	48 c1 e1 09          	shl    $0x9,%rcx
    6a3c:	41 55                	push   %r13
    6a3e:	4c 63 d8             	movslq %eax,%r11
    6a41:	41 54                	push   %r12
    6a43:	49 01 d3             	add    %rdx,%r11
    6a46:	55                   	push   %rbp
    6a47:	49 c1 e3 08          	shl    $0x8,%r11
    6a4b:	53                   	push   %rbx
    6a4c:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
    6a53:	4c 89 d7             	mov    %r10,%rdi
    6a56:	48 8b 76 20          	mov    0x20(%rsi),%rsi
    6a5a:	48 c1 e7 05          	shl    $0x5,%rdi
    6a5e:	4c 29 d7             	sub    %r10,%rdi
    6a61:	49 c1 e2 08          	shl    $0x8,%r10
    6a65:	48 8b 5c fe 38       	mov    0x38(%rsi,%rdi,8),%rbx
    6a6a:	48 8b ac 0b 70 01 00 00 	mov    0x170(%rbx,%rcx,1),%rbp
    6a72:	48 89 d1             	mov    %rdx,%rcx
    6a75:	48 c1 e1 05          	shl    $0x5,%rcx
    6a79:	48 29 d1             	sub    %rdx,%rcx
    6a7c:	4c 8d 0c ce          	lea    (%rsi,%rcx,8),%r9
    6a80:	48 89 d6             	mov    %rdx,%rsi
    6a83:	48 c1 e6 08          	shl    $0x8,%rsi
    6a87:	eb 1e                	jmp    6aa7 <fswap+0xa7>
    6a89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6a90:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    6a97:	49 81 c1 f8 00 00 00 	add    $0xf8,%r9
    6a9e:	49 39 f3             	cmp    %rsi,%r11
    6aa1:	0f 84 99 00 00 00    	je     6b40 <fswap+0x140>
    6aa7:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    6aaf:	75 df                	jne    6a90 <fswap+0x90>
    6ab1:	49 8b 79 38          	mov    0x38(%r9),%rdi
    6ab5:	45 85 c0             	test   %r8d,%r8d
    6ab8:	7e d6                	jle    6a90 <fswap+0x90>
    6aba:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    6ac1:	31 c9                	xor    %ecx,%ecx
    6ac3:	eb 58                	jmp    6b1d <fswap+0x11d>
    6ac5:	0f 1f 00             	nopl   (%rax)
    6ac8:	48 63 d2             	movslq %edx,%rdx
    6acb:	48 c1 e2 09          	shl    $0x9,%rdx
    6acf:	4c 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%r13
    6ad7:	49 01 f5             	add    %rsi,%r13
    6ada:	4c 89 ea             	mov    %r13,%rdx
    6add:	4d 8b 6d 00          	mov    0x0(%r13),%r13
    6ae1:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    6ae9:	75 22                	jne    6b0d <fswap+0x10d>
    6aeb:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    6af2:	4c 89 32             	mov    %r14,(%rdx)
    6af5:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    6afc:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    6b03:	4c 89 30             	mov    %r14,(%rax)
    6b06:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
    6b0d:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    6b14:	41 39 c8             	cmp    %ecx,%r8d
    6b17:	0f 84 73 ff ff ff    	je     6a90 <fswap+0x90>
    6b1d:	83 c1 01             	add    $0x1,%ecx
    6b20:	89 c8                	mov    %ecx,%eax
    6b22:	99                   	cltd
    6b23:	41 f7 f8             	idiv   %r8d
    6b26:	48 8b 07             	mov    (%rdi),%rax
    6b29:	4c 01 d0             	add    %r10,%rax
    6b2c:	4c 8b 20             	mov    (%rax),%r12
    6b2f:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    6b38:	74 8e                	je     6ac8 <fswap+0xc8>
    6b3a:	e9 51 ff ff ff       	jmp    6a90 <fswap+0x90>
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
    6b65:	48 8b 8f 28 01 00 00 	mov    0x128(%rdi),%rcx
    6b6c:	48 8b b9 f0 00 00 00 	mov    0xf0(%rcx),%rdi
    6b73:	8b 81 e8 00 00 00    	mov    0xe8(%rcx),%eax
    6b79:	8b 37                	mov    (%rdi),%esi
    6b7b:	83 fe ff             	cmp    $0xffffffff,%esi
    6b7e:	0f 84 6c 04 00 00    	je     6ff0 <barriered_work+0x4a0>
    6b84:	39 c6                	cmp    %eax,%esi
    6b86:	74 18                	je     6ba0 <barriered_work+0x50>
    6b88:	48 83 c4 58          	add    $0x58,%rsp
    6b8c:	31 c0                	xor    %eax,%eax
    6b8e:	5b                   	pop    %rbx
    6b8f:	5d                   	pop    %rbp
    6b90:	41 5c                	pop    %r12
    6b92:	41 5d                	pop    %r13
    6b94:	41 5e                	pop    %r14
    6b96:	41 5f                	pop    %r15
    6b98:	c3                   	ret
    6b99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6ba0:	8d 46 01             	lea    0x1(%rsi),%eax
    6ba3:	99                   	cltd
    6ba4:	f7 b9 c0 00 00 00    	idivl  0xc0(%rcx)
    6baa:	31 c0                	xor    %eax,%eax
    6bac:	89 17                	mov    %edx,(%rdi)
    6bae:	89 d1                	mov    %edx,%ecx
    6bb0:	bf 01 00 00 00       	mov    $0x1,%edi
    6bb5:	89 f2                	mov    %esi,%edx
    6bb7:	48 8d 35 6d 16 00 00 	lea    0x166d(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6bbe:	e8 ed b8 ff ff       	call   24b0 <__printf_chk@plt>
    6bc3:	44 8b 63 04          	mov    0x4(%rbx),%r12d
    6bc7:	48 89 df             	mov    %rbx,%rdi
    6bca:	44 39 a3 30 01 00 00 	cmp    %r12d,0x130(%rbx)
    6bd1:	0f 85 69 02 00 00    	jne    6e40 <barriered_work+0x2f0>
    6bd7:	e8 44 fa ff ff       	call   6620 <receive>
    6bdc:	8b 8b 40 01 00 00    	mov    0x140(%rbx),%ecx
    6be2:	85 c9                	test   %ecx,%ecx
    6be4:	0f 8e a9 02 00 00    	jle    6e93 <barriered_work+0x343>
    6bea:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6bf0:	4c 8b bb 28 01 00 00 	mov    0x128(%rbx),%r15
    6bf7:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
    6bff:	31 f6                	xor    %esi,%esi
    6c01:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
    6c05:	45 8b 77 08          	mov    0x8(%r15),%r14d
    6c09:	49 63 c4             	movslq %r12d,%rax
    6c0c:	48 c1 e0 09          	shl    $0x9,%rax
    6c10:	49 89 c5             	mov    %rax,%r13
    6c13:	49 63 c6             	movslq %r14d,%rax
    6c16:	48 89 c2             	mov    %rax,%rdx
    6c19:	48 c1 e2 05          	shl    $0x5,%rdx
    6c1d:	48 29 c2             	sub    %rax,%rdx
    6c20:	48 c1 e0 08          	shl    $0x8,%rax
    6c24:	48 8d 2c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rbp
    6c2c:	48 63 d1             	movslq %ecx,%rdx
    6c2f:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    6c34:	44 89 e1             	mov    %r12d,%ecx
    6c37:	49 89 d2             	mov    %rdx,%r10
    6c3a:	eb 1d                	jmp    6c59 <barriered_work+0x109>
    6c3c:	0f 1f 40 00          	nopl   0x0(%rax)
    6c40:	48 83 04 24 01       	addq   $0x1,(%rsp)
    6c45:	48 8b 04 24          	mov    (%rsp),%rax
    6c49:	48 81 c6 f8 00 00 00 	add    $0xf8,%rsi
    6c50:	49 39 c2             	cmp    %rax,%r10
    6c53:	0f 84 37 02 00 00    	je     6e90 <barriered_work+0x340>
    6c59:	8b 04 24             	mov    (%rsp),%eax
    6c5c:	41 39 c6             	cmp    %eax,%r14d
    6c5f:	74 df                	je     6c40 <barriered_work+0xf0>
    6c61:	49 8b 57 20          	mov    0x20(%r15),%rdx
    6c65:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    6c6a:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    6c6e:	44 8b 80 a0 01 00 00 	mov    0x1a0(%rax),%r8d
    6c75:	45 85 c0             	test   %r8d,%r8d
    6c78:	75 c6                	jne    6c40 <barriered_work+0xf0>
    6c7a:	4c 8b 44 2a 38       	mov    0x38(%rdx,%rbp,1),%r8
    6c7f:	4b 8d 14 28          	lea    (%r8,%r13,1),%rdx
    6c83:	44 8b 8a a0 01 00 00 	mov    0x1a0(%rdx),%r9d
    6c8a:	45 85 c9             	test   %r9d,%r9d
    6c8d:	75 b1                	jne    6c40 <barriered_work+0xf0>
    6c8f:	4c 8b 24 24          	mov    (%rsp),%r12
    6c93:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    6c9a:	49 c1 e4 08          	shl    $0x8,%r12
    6c9e:	42 83 bc 22 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r12,1)
    6ca7:	75 97                	jne    6c40 <barriered_work+0xf0>
    6ca9:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6cb0:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    6cb5:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    6cbd:	75 81                	jne    6c40 <barriered_work+0xf0>
    6cbf:	48 63 44 24 1c       	movslq 0x1c(%rsp),%rax
    6cc4:	85 c0                	test   %eax,%eax
    6cc6:	0f 8e 74 ff ff ff    	jle    6c40 <barriered_work+0xf0>
    6ccc:	48 89 c2             	mov    %rax,%rdx
    6ccf:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
    6cd4:	b8 70 01 00 00       	mov    $0x170,%eax
    6cd9:	48 c1 e2 09          	shl    $0x9,%rdx
    6cdd:	89 4c 24 30          	mov    %ecx,0x30(%rsp)
    6ce1:	44 89 74 24 34       	mov    %r14d,0x34(%rsp)
    6ce6:	4c 8d 9a a0 01 00 00 	lea    0x1a0(%rdx),%r11
    6ced:	48 89 54 24 48       	mov    %rdx,0x48(%rsp)
    6cf2:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    6cf7:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    6cfc:	4c 89 54 24 38       	mov    %r10,0x38(%rsp)
    6d01:	44 8b 54 24 1c       	mov    0x1c(%rsp),%r10d
    6d06:	48 89 74 24 40       	mov    %rsi,0x40(%rsp)
    6d0b:	48 89 c6             	mov    %rax,%rsi
    6d0e:	66 90                	xchg   %ax,%ax
    6d10:	41 83 c1 01          	add    $0x1,%r9d
    6d14:	49 8b 0c 30          	mov    (%r8,%rsi,1),%rcx
    6d18:	44 89 c8             	mov    %r9d,%eax
    6d1b:	99                   	cltd
    6d1c:	4c 01 e1             	add    %r12,%rcx
    6d1f:	41 f7 fa             	idiv   %r10d
    6d22:	4c 8b 31             	mov    (%rcx),%r14
    6d25:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    6d2a:	4c 8b b1 80 00 00 00 	mov    0x80(%rcx),%r14
    6d31:	48 63 d2             	movslq %edx,%rdx
    6d34:	48 c1 e2 09          	shl    $0x9,%rdx
    6d38:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    6d40:	4c 01 e8             	add    %r13,%rax
    6d43:	4c 8b 38             	mov    (%rax),%r15
    6d46:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    6d4d:	4c 89 30             	mov    %r14,(%rax)
    6d50:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    6d55:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    6d5c:	48 89 11             	mov    %rdx,(%rcx)
    6d5f:	4c 89 b9 80 00 00 00 	mov    %r15,0x80(%rcx)
    6d66:	b9 a0 01 00 00       	mov    $0x1a0,%ecx
    6d6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6d70:	41 c7 04 08 01 00 00 00 	movl   $0x1,(%r8,%rcx,1)
    6d78:	c7 04 0f 01 00 00 00 	movl   $0x1,(%rdi,%rcx,1)
    6d7f:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    6d86:	49 39 cb             	cmp    %rcx,%r11
    6d89:	75 e5                	jne    6d70 <barriered_work+0x220>
    6d8b:	48 8b 0c 37          	mov    (%rdi,%rsi,1),%rcx
    6d8f:	48 8b 00             	mov    (%rax),%rax
    6d92:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
    6d9d:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    6da4:	4a 8b 8c 29 80 00 00 00 	mov    0x80(%rcx,%r13,1),%rcx
    6dac:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    6db6:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    6dc0:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    6dca:	45 39 ca             	cmp    %r9d,%r10d
    6dcd:	0f 85 3d ff ff ff    	jne    6d10 <barriered_work+0x1c0>
    6dd3:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    6dd8:	48 8b 54 24 48       	mov    0x48(%rsp),%rdx
    6ddd:	b8 70 01 00 00       	mov    $0x170,%eax
    6de2:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    6de7:	8b 4c 24 30          	mov    0x30(%rsp),%ecx
    6deb:	44 8b 74 24 34       	mov    0x34(%rsp),%r14d
    6df0:	4c 8b 54 24 38       	mov    0x38(%rsp),%r10
    6df5:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    6dfa:	4c 8d 9a 70 01 00 00 	lea    0x170(%rdx),%r11
    6e01:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    6e06:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    6e0b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6e10:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    6e14:	4d 8b 0c 00          	mov    (%r8,%rax,1),%r9
    6e18:	4a 8b 14 3a          	mov    (%rdx,%r15,1),%rdx
    6e1c:	4b 39 14 21          	cmp    %rdx,(%r9,%r12,1)
    6e20:	0f 84 2e 02 00 00    	je     7054 <barriered_work+0x504>
    6e26:	48 05 00 02 00 00    	add    $0x200,%rax
    6e2c:	49 39 c3             	cmp    %rax,%r11
    6e2f:	75 df                	jne    6e10 <barriered_work+0x2c0>
    6e31:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    6e36:	e9 05 fe ff ff       	jmp    6c40 <barriered_work+0xf0>
    6e3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6e40:	e8 db f7 ff ff       	call   6620 <receive>
    6e45:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6e4c:	75 16                	jne    6e64 <barriered_work+0x314>
    6e4e:	66 90                	xchg   %ax,%ax
    6e50:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6e58:	0f ae f8             	sfence
    6e5b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6e62:	74 ec                	je     6e50 <barriered_work+0x300>
    6e64:	48 89 df             	mov    %rbx,%rdi
    6e67:	e8 14 f9 ff ff       	call   6780 <sendm>
    6e6c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6e72:	83 e8 01             	sub    $0x1,%eax
    6e75:	44 39 e0             	cmp    %r12d,%eax
    6e78:	0f 84 fd 00 00 00    	je     6f7b <barriered_work+0x42b>
    6e7e:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    6e88:	0f ae f8             	sfence
    6e8b:	e9 f8 fc ff ff       	jmp    6b88 <barriered_work+0x38>
    6e90:	41 89 cc             	mov    %ecx,%r12d
    6e93:	48 89 df             	mov    %rbx,%rdi
    6e96:	e8 65 fb ff ff       	call   6a00 <fswap>
    6e9b:	48 89 df             	mov    %rbx,%rdi
    6e9e:	e8 7d f7 ff ff       	call   6620 <receive>
    6ea3:	0f ae f8             	sfence
    6ea6:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6ead:	31 ff                	xor    %edi,%edi
    6eaf:	48 c1 e6 05          	shl    $0x5,%rsi
    6eb3:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6eba:	e8 91 b4 ff ff       	call   2350 <clock_gettime@plt>
    6ebf:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6ec6:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6ecd:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6ed1:	8b 72 10             	mov    0x10(%rdx),%esi
    6ed4:	8d 6e 01             	lea    0x1(%rsi),%ebp
    6ed7:	89 6a 10             	mov    %ebp,0x10(%rdx)
    6eda:	75 55                	jne    6f31 <barriered_work+0x3e1>
    6edc:	0f 1f 40 00          	nopl   0x0(%rax)
    6ee0:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    6ee7:	48 8b 40 18          	mov    0x18(%rax),%rax
    6eeb:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
    6eef:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6ef7:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6efb:	48 c1 e7 09          	shl    $0x9,%rdi
    6eff:	48 03 78 38          	add    0x38(%rax),%rdi
    6f03:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    6f09:	0f ae f8             	sfence
    6f0c:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6f13:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6f1a:	74 c4                	je     6ee0 <barriered_work+0x390>
    6f1c:	48 8b 40 48          	mov    0x48(%rax),%rax
    6f20:	3b 68 10             	cmp    0x10(%rax),%ebp
    6f23:	74 0c                	je     6f31 <barriered_work+0x3e1>
    6f25:	48 8d 3d 34 13 00 00 	lea    0x1334(%rip),%rdi        # 8260 <_IO_stdin_used+0x260>
    6f2c:	e8 ff b3 ff ff       	call   2330 <puts@plt>
    6f31:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6f38:	31 ff                	xor    %edi,%edi
    6f3a:	48 c1 e6 05          	shl    $0x5,%rsi
    6f3e:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6f45:	48 83 c6 10          	add    $0x10,%rsi
    6f49:	e8 02 b4 ff ff       	call   2350 <clock_gettime@plt>
    6f4e:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6f55:	48 83 c0 01          	add    $0x1,%rax
    6f59:	48 99                	cqto
    6f5b:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6f62:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6f68:	83 e8 01             	sub    $0x1,%eax
    6f6b:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    6f72:	44 39 e0             	cmp    %r12d,%eax
    6f75:	0f 85 03 ff ff ff    	jne    6e7e <barriered_work+0x32e>
    6f7b:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    6f82:	85 d2                	test   %edx,%edx
    6f84:	0f 8e f4 fe ff ff    	jle    6e7e <barriered_work+0x32e>
    6f8a:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    6f91:	48 c1 e2 09          	shl    $0x9,%rdx
    6f95:	48 63 71 08          	movslq 0x8(%rcx),%rsi
    6f99:	48 89 f0             	mov    %rsi,%rax
    6f9c:	48 c1 e0 05          	shl    $0x5,%rax
    6fa0:	48 29 f0             	sub    %rsi,%rax
    6fa3:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    6fa7:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    6fab:	48 8b 40 38          	mov    0x38(%rax),%rax
    6faf:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    6fb3:	80 e6 02             	and    $0x2,%dh
    6fb6:	74 18                	je     6fd0 <barriered_work+0x480>
    6fb8:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    6fbf:	48 05 00 02 00 00    	add    $0x200,%rax
    6fc5:	48 39 c8             	cmp    %rcx,%rax
    6fc8:	0f 84 b0 fe ff ff    	je     6e7e <barriered_work+0x32e>
    6fce:	66 90                	xchg   %ax,%ax
    6fd0:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    6fd7:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
    6fde:	48 05 00 04 00 00    	add    $0x400,%rax
    6fe4:	48 39 c8             	cmp    %rcx,%rax
    6fe7:	75 e7                	jne    6fd0 <barriered_work+0x480>
    6fe9:	e9 90 fe ff ff       	jmp    6e7e <barriered_work+0x32e>
    6fee:	66 90                	xchg   %ax,%ax
    6ff0:	85 c0                	test   %eax,%eax
    6ff2:	0f 85 cb fb ff ff    	jne    6bc3 <barriered_work+0x73>
    6ff8:	69 83 80 00 00 00 1d e6 cb 0b 	imul   $0xbcbe61d,0x80(%rbx),%eax
    7002:	05 40 7c 0a 00       	add    $0xa7c40,%eax
    7007:	c1 c8 05             	ror    $0x5,%eax
    700a:	3d c4 a7 00 00       	cmp    $0xa7c4,%eax
    700f:	0f 87 ae fb ff ff    	ja     6bc3 <barriered_work+0x73>
    7015:	b9 ff ff ff ff       	mov    $0xffffffff,%ecx
    701a:	31 d2                	xor    %edx,%edx
    701c:	48 8d 35 2d 16 00 00 	lea    0x162d(%rip),%rsi        # 8650 <_IO_stdin_used+0x650>
    7023:	31 c0                	xor    %eax,%eax
    7025:	bf 01 00 00 00       	mov    $0x1,%edi
    702a:	e8 81 b4 ff ff       	call   24b0 <__printf_chk@plt>
    702f:	48 8b b3 28 01 00 00 	mov    0x128(%rbx),%rsi
    7036:	8b 86 e8 00 00 00    	mov    0xe8(%rsi),%eax
    703c:	48 8b 8e f0 00 00 00 	mov    0xf0(%rsi),%rcx
    7043:	83 c0 01             	add    $0x1,%eax
    7046:	99                   	cltd
    7047:	f7 be c0 00 00 00    	idivl  0xc0(%rsi)
    704d:	89 11                	mov    %edx,(%rcx)
    704f:	e9 6f fb ff ff       	jmp    6bc3 <barriered_work+0x73>
    7054:	bf 01 00 00 00       	mov    $0x1,%edi
    7059:	48 8d 35 e5 11 00 00 	lea    0x11e5(%rip),%rsi        # 8245 <_IO_stdin_used+0x245>
    7060:	31 c0                	xor    %eax,%eax
    7062:	e8 49 b4 ff ff       	call   24b0 <__printf_chk@plt>
    7067:	bf 01 00 00 00       	mov    $0x1,%edi
    706c:	e8 9f b4 ff ff       	call   2510 <exit@plt>
    7071:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    707c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000007080 <barriered_work_ingest_andwork>:
    7080:	f3 0f 1e fa          	endbr64
    7084:	53                   	push   %rbx
    7085:	48 89 fb             	mov    %rdi,%rbx
    7088:	e8 a3 f1 ff ff       	call   6230 <barriered_work_ingest>
    708d:	48 89 df             	mov    %rbx,%rdi
    7090:	5b                   	pop    %rbx
    7091:	e9 ba fa ff ff       	jmp    6b50 <barriered_work>
    7096:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000070a0 <barriered_nulltask>:
    70a0:	f3 0f 1e fa          	endbr64
    70a4:	31 c0                	xor    %eax,%eax
    70a6:	c3                   	ret
    70a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000070b0 <barriered_steal>:
    70b0:	f3 0f 1e fa          	endbr64
    70b4:	31 c0                	xor    %eax,%eax
    70b6:	c3                   	ret
    70b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000070c0 <after>:
    70c0:	f3 0f 1e fa          	endbr64
    70c4:	31 c0                	xor    %eax,%eax
    70c6:	48 39 d7             	cmp    %rdx,%rdi
    70c9:	7e 08                	jle    70d3 <after+0x13>
    70cb:	31 c0                	xor    %eax,%eax
    70cd:	48 39 ce             	cmp    %rcx,%rsi
    70d0:	0f 9f c0             	setg   %al
    70d3:	c3                   	ret
    70d4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    70df:	90                   	nop

00000000000070e0 <within>:
    70e0:	f3 0f 1e fa          	endbr64
    70e4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    70e9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    70ee:	31 c0                	xor    %eax,%eax
    70f0:	48 39 d7             	cmp    %rdx,%rdi
    70f3:	7f 18                	jg     710d <within+0x2d>
    70f5:	4d 39 d8             	cmp    %r11,%r8
    70f8:	0f 9e c2             	setle  %dl
    70fb:	48 39 ce             	cmp    %rcx,%rsi
    70fe:	0f 9e c0             	setle  %al
    7101:	21 c2                	and    %eax,%edx
    7103:	31 c0                	xor    %eax,%eax
    7105:	4d 39 d1             	cmp    %r10,%r9
    7108:	0f 9e c0             	setle  %al
    710b:	21 d0                	and    %edx,%eax
    710d:	c3                   	ret
    710e:	66 90                	xchg   %ax,%ax

0000000000007110 <overlap>:
    7110:	f3 0f 1e fa          	endbr64
    7114:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    7119:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    711e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    7123:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    7128:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    712d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    7132:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    7137:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    713c:	48 39 fe             	cmp    %rdi,%rsi
    713f:	7d 2f                	jge    7170 <overlap+0x60>
    7141:	48 39 ca             	cmp    %rcx,%rdx
    7144:	7d 62                	jge    71a8 <overlap+0x98>
    7146:	4d 39 da             	cmp    %r11,%r10
    7149:	7d 0e                	jge    7159 <overlap+0x49>
    714b:	b8 01 00 00 00       	mov    $0x1,%eax
    7150:	4d 39 c1             	cmp    %r8,%r9
    7153:	0f 8c 7f 00 00 00    	jl     71d8 <overlap+0xc8>
    7159:	31 c0                	xor    %eax,%eax
    715b:	4d 39 c1             	cmp    %r8,%r9
    715e:	7f 4c                	jg     71ac <overlap+0x9c>
    7160:	31 c0                	xor    %eax,%eax
    7162:	4d 39 da             	cmp    %r11,%r10
    7165:	0f 9e c0             	setle  %al
    7168:	c3                   	ret
    7169:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7170:	7e 4e                	jle    71c0 <overlap+0xb0>
    7172:	48 39 ca             	cmp    %rcx,%rdx
    7175:	7f 39                	jg     71b0 <overlap+0xa0>
    7177:	75 31                	jne    71aa <overlap+0x9a>
    7179:	4d 39 c1             	cmp    %r8,%r9
    717c:	7c 2c                	jl     71aa <overlap+0x9a>
    717e:	b8 01 00 00 00       	mov    $0x1,%eax
    7183:	4d 39 da             	cmp    %r11,%r10
    7186:	7d 24                	jge    71ac <overlap+0x9c>
    7188:	48 39 ca             	cmp    %rcx,%rdx
    718b:	0f 94 c2             	sete   %dl
    718e:	48 39 fe             	cmp    %rdi,%rsi
    7191:	0f 94 c0             	sete   %al
    7194:	21 c2                	and    %eax,%edx
    7196:	31 c0                	xor    %eax,%eax
    7198:	4d 39 c1             	cmp    %r8,%r9
    719b:	0f 94 c0             	sete   %al
    719e:	21 d0                	and    %edx,%eax
    71a0:	c3                   	ret
    71a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    71a8:	74 af                	je     7159 <overlap+0x49>
    71aa:	31 c0                	xor    %eax,%eax
    71ac:	c3                   	ret
    71ad:	0f 1f 00             	nopl   (%rax)
    71b0:	4d 39 da             	cmp    %r11,%r10
    71b3:	7e c4                	jle    7179 <overlap+0x69>
    71b5:	b8 01 00 00 00       	mov    $0x1,%eax
    71ba:	4d 39 c1             	cmp    %r8,%r9
    71bd:	7e ba                	jle    7179 <overlap+0x69>
    71bf:	c3                   	ret
    71c0:	48 39 ca             	cmp    %rcx,%rdx
    71c3:	7c 94                	jl     7159 <overlap+0x49>
    71c5:	4d 39 c1             	cmp    %r8,%r9
    71c8:	7d b4                	jge    717e <overlap+0x6e>
    71ca:	48 39 ca             	cmp    %rcx,%rdx
    71cd:	74 91                	je     7160 <overlap+0x50>
    71cf:	eb d9                	jmp    71aa <overlap+0x9a>
    71d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    71d8:	c3                   	ret
    71d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000071e0 <verify>:
    71e0:	f3 0f 1e fa          	endbr64
    71e4:	85 f6                	test   %esi,%esi
    71e6:	0f 8e 44 03 00 00    	jle    7530 <verify+0x350>
    71ec:	41 57                	push   %r15
    71ee:	41 89 f7             	mov    %esi,%r15d
    71f1:	41 56                	push   %r14
    71f3:	45 31 f6             	xor    %r14d,%r14d
    71f6:	41 55                	push   %r13
    71f8:	41 54                	push   %r12
    71fa:	55                   	push   %rbp
    71fb:	53                   	push   %rbx
    71fc:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    7200:	48 83 ec 58          	sub    $0x58,%rsp
    7204:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    7209:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    720e:	45 31 e4             	xor    %r12d,%r12d
    7211:	45 39 e6             	cmp    %r12d,%r14d
    7214:	0f 84 4e 02 00 00    	je     7468 <verify+0x288>
    721a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    721f:	8b 50 08             	mov    0x8(%rax),%edx
    7222:	85 d2                	test   %edx,%edx
    7224:	0f 8e 3e 02 00 00    	jle    7468 <verify+0x288>
    722a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    722f:	31 c9                	xor    %ecx,%ecx
    7231:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    7236:	31 c0                	xor    %eax,%eax
    7238:	44 89 f2             	mov    %r14d,%edx
    723b:	bf 01 00 00 00       	mov    $0x1,%edi
    7240:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    7245:	48 8d 35 24 10 00 00 	lea    0x1024(%rip),%rsi        # 8270 <_IO_stdin_used+0x270>
    724c:	e8 5f b2 ff ff       	call   24b0 <__printf_chk@plt>
    7251:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7256:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    725b:	8b 40 08             	mov    0x8(%rax),%eax
    725e:	85 c0                	test   %eax,%eax
    7260:	0f 8e e6 01 00 00    	jle    744c <verify+0x26c>
    7266:	48 89 c8             	mov    %rcx,%rax
    7269:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    726e:	31 db                	xor    %ebx,%ebx
    7270:	48 c1 e0 09          	shl    $0x9,%rax
    7274:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    7279:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    727e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7283:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    7288:	4c 8b 20             	mov    (%rax),%r12
    728b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7290:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    7295:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    729a:	49 89 de             	mov    %rbx,%r14
    729d:	48 8d 35 e1 0f 00 00 	lea    0xfe1(%rip),%rsi        # 8285 <_IO_stdin_used+0x285>
    72a4:	49 c1 e6 09          	shl    $0x9,%r14
    72a8:	bf 01 00 00 00       	mov    $0x1,%edi
    72ad:	48 8b 45 00          	mov    0x0(%rbp),%rax
    72b1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    72b9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    72be:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    72c6:	31 c0                	xor    %eax,%eax
    72c8:	e8 e3 b1 ff ff       	call   24b0 <__printf_chk@plt>
    72cd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    72d2:	4c 8b 20             	mov    (%rax),%r12
    72d5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    72de:	0f 8e 47 01 00 00    	jle    742b <verify+0x24b>
    72e4:	4c 03 75 00          	add    0x0(%rbp),%r14
    72e8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    72ed:	ba 01 00 00 00       	mov    $0x1,%edx
    72f2:	4d 89 f5             	mov    %r14,%r13
    72f5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    72fc:	4d 85 f6             	test   %r14,%r14
    72ff:	0f 8e 21 01 00 00    	jle    7426 <verify+0x246>
    7305:	0f 1f 00             	nopl   (%rax)
    7308:	48 89 d5             	mov    %rdx,%rbp
    730b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7310:	31 db                	xor    %ebx,%ebx
    7312:	4d 89 f2             	mov    %r14,%r10
    7315:	48 c1 e5 05          	shl    $0x5,%rbp
    7319:	48 83 ed 20          	sub    $0x20,%rbp
    731d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    7321:	49 89 ee             	mov    %rbp,%r14
    7324:	48 89 dd             	mov    %rbx,%rbp
    7327:	48 89 d3             	mov    %rdx,%rbx
    732a:	eb 31                	jmp    735d <verify+0x17d>
    732c:	0f 1f 40 00          	nopl   0x0(%rax)
    7330:	4c 39 c2             	cmp    %r8,%rdx
    7333:	0f 8d 57 01 00 00    	jge    7490 <verify+0x2b0>
    7339:	4c 39 df             	cmp    %r11,%rdi
    733c:	7e 05                	jle    7343 <verify+0x163>
    733e:	49 39 c1             	cmp    %rax,%r9
    7341:	7c 75                	jl     73b8 <verify+0x1d8>
    7343:	4c 39 df             	cmp    %r11,%rdi
    7346:	0f 8d ab 01 00 00    	jge    74f7 <verify+0x317>
    734c:	0f 1f 40 00          	nopl   0x0(%rax)
    7350:	48 83 c5 01          	add    $0x1,%rbp
    7354:	49 39 ea             	cmp    %rbp,%r10
    7357:	0f 8e a9 00 00 00    	jle    7406 <verify+0x226>
    735d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    7364:	48 89 e8             	mov    %rbp,%rax
    7367:	48 c1 e0 05          	shl    $0x5,%rax
    736b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    7372:	4c 01 f2             	add    %r14,%rdx
    7375:	48 8b 08             	mov    (%rax),%rcx
    7378:	48 8b 78 10          	mov    0x10(%rax),%rdi
    737c:	48 8b 32             	mov    (%rdx),%rsi
    737f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    7383:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    7387:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    738b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    738f:	48 8b 40 18          	mov    0x18(%rax),%rax
    7393:	48 39 f1             	cmp    %rsi,%rcx
    7396:	7c 98                	jl     7330 <verify+0x150>
    7398:	0f 8e 42 01 00 00    	jle    74e0 <verify+0x300>
    739e:	4c 39 c2             	cmp    %r8,%rdx
    73a1:	0f 8f f9 00 00 00    	jg     74a0 <verify+0x2c0>
    73a7:	75 a7                	jne    7350 <verify+0x170>
    73a9:	4c 39 df             	cmp    %r11,%rdi
    73ac:	7f a2                	jg     7350 <verify+0x170>
    73ae:	49 39 c1             	cmp    %rax,%r9
    73b1:	7c 9d                	jl     7350 <verify+0x170>
    73b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    73b8:	49 89 c1             	mov    %rax,%r9
    73bb:	48 89 f9             	mov    %rdi,%rcx
    73be:	48 89 f2             	mov    %rsi,%rdx
    73c1:	bf 01 00 00 00       	mov    $0x1,%edi
    73c6:	48 8d 35 a3 12 00 00 	lea    0x12a3(%rip),%rsi        # 8670 <_IO_stdin_used+0x670>
    73cd:	31 c0                	xor    %eax,%eax
    73cf:	48 83 c5 01          	add    $0x1,%rbp
    73d3:	e8 d8 b0 ff ff       	call   24b0 <__printf_chk@plt>
    73d8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    73dd:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    73e2:	4c 03 28             	add    (%rax),%r13
    73e5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    73ea:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
    73f1:	4c 8b 20             	mov    (%rax),%r12
    73f4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    73f9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    73fd:	49 39 ea             	cmp    %rbp,%r10
    7400:	0f 8f 57 ff ff ff    	jg     735d <verify+0x17d>
    7406:	48 89 da             	mov    %rbx,%rdx
    7409:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7410:	7d 14                	jge    7426 <verify+0x246>
    7412:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7419:	48 83 c2 01          	add    $0x1,%rdx
    741d:	4d 85 f6             	test   %r14,%r14
    7420:	0f 8f e2 fe ff ff    	jg     7308 <verify+0x128>
    7426:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    742b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7430:	48 83 c3 01          	add    $0x1,%rbx
    7434:	39 58 08             	cmp    %ebx,0x8(%rax)
    7437:	0f 8f 53 fe ff ff    	jg     7290 <verify+0xb0>
    743d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    7442:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    7447:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
    744c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7451:	48 83 c1 01          	add    $0x1,%rcx
    7455:	39 48 08             	cmp    %ecx,0x8(%rax)
    7458:	0f 8f d8 fd ff ff    	jg     7236 <verify+0x56>
    745e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    7463:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    7468:	48 81 44 24 10 f8 00 00 00 	addq   $0xf8,0x10(%rsp)
    7471:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    7476:	41 39 c7             	cmp    %eax,%r15d
    7479:	0f 84 86 00 00 00    	je     7505 <verify+0x325>
    747f:	41 89 c4             	mov    %eax,%r12d
    7482:	e9 8a fd ff ff       	jmp    7211 <verify+0x31>
    7487:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    7490:	0f 85 ba fe ff ff    	jne    7350 <verify+0x170>
    7496:	e9 a8 fe ff ff       	jmp    7343 <verify+0x163>
    749b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    74a0:	49 39 c1             	cmp    %rax,%r9
    74a3:	7e 09                	jle    74ae <verify+0x2ce>
    74a5:	4c 39 df             	cmp    %r11,%rdi
    74a8:	0f 8c 0a ff ff ff    	jl     73b8 <verify+0x1d8>
    74ae:	4c 39 df             	cmp    %r11,%rdi
    74b1:	0f 8f 99 fe ff ff    	jg     7350 <verify+0x170>
    74b7:	49 39 c1             	cmp    %rax,%r9
    74ba:	0f 8d f8 fe ff ff    	jge    73b8 <verify+0x1d8>
    74c0:	48 39 f1             	cmp    %rsi,%rcx
    74c3:	0f 85 87 fe ff ff    	jne    7350 <verify+0x170>
    74c9:	4c 39 c2             	cmp    %r8,%rdx
    74cc:	0f 85 7e fe ff ff    	jne    7350 <verify+0x170>
    74d2:	4c 39 df             	cmp    %r11,%rdi
    74d5:	0f 84 dd fe ff ff    	je     73b8 <verify+0x1d8>
    74db:	e9 70 fe ff ff       	jmp    7350 <verify+0x170>
    74e0:	4c 39 c2             	cmp    %r8,%rdx
    74e3:	0f 8c 5a fe ff ff    	jl     7343 <verify+0x163>
    74e9:	4c 39 df             	cmp    %r11,%rdi
    74ec:	7e c9                	jle    74b7 <verify+0x2d7>
    74ee:	4c 39 c2             	cmp    %r8,%rdx
    74f1:	0f 85 59 fe ff ff    	jne    7350 <verify+0x170>
    74f7:	49 39 c1             	cmp    %rax,%r9
    74fa:	0f 8f 50 fe ff ff    	jg     7350 <verify+0x170>
    7500:	e9 b3 fe ff ff       	jmp    73b8 <verify+0x1d8>
    7505:	48 81 44 24 18 f8 00 00 00 	addq   $0xf8,0x18(%rsp)
    750e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7512:	45 39 e6             	cmp    %r12d,%r14d
    7515:	74 08                	je     751f <verify+0x33f>
    7517:	41 89 c6             	mov    %eax,%r14d
    751a:	e9 ea fc ff ff       	jmp    7209 <verify+0x29>
    751f:	48 83 c4 58          	add    $0x58,%rsp
    7523:	31 c0                	xor    %eax,%eax
    7525:	5b                   	pop    %rbx
    7526:	5d                   	pop    %rbp
    7527:	41 5c                	pop    %r12
    7529:	41 5d                	pop    %r13
    752b:	41 5e                	pop    %r14
    752d:	41 5f                	pop    %r15
    752f:	c3                   	ret
    7530:	31 c0                	xor    %eax,%eax
    7532:	c3                   	ret

Disassembly of section .fini:

0000000000007534 <_fini>:
    7534:	f3 0f 1e fa          	endbr64
    7538:	48 83 ec 08          	sub    $0x8,%rsp
    753c:	48 83 c4 08          	add    $0x8,%rsp
    7540:	c3                   	ret
