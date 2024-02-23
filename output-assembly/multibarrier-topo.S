
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
    2676:	48 8d 3d 03 60 00 00 	lea    0x6003(%rip),%rdi        # 8680 <_IO_stdin_used+0x680>
    267d:	41 56                	push   %r14
    267f:	41 55                	push   %r13
    2681:	41 54                	push   %r12
    2683:	4c 8d 25 0f 5d 00 00 	lea    0x5d0f(%rip),%r12        # 8399 <_IO_stdin_used+0x399>
    268a:	55                   	push   %rbp
    268b:	53                   	push   %rbx
    268c:	48 81 ec 28 01 00 00 	sub    $0x128,%rsp
    2693:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    269c:	48 89 84 24 18 01 00 00 	mov    %rax,0x118(%rsp)
    26a4:	48 8d 05 85 1f 00 00 	lea    0x1f85(%rip),%rax        # 4630 <barriered_reset>
    26ab:	66 48 0f 6e f0       	movq   %rax,%xmm6
    26b0:	0f 16 35 a1 85 00 00 	movhps 0x85a1(%rip),%xmm6        # ac58 <__do_global_dtors_aux_fini_array_entry+0x8>
    26b7:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    26bf:	e8 6c fc ff ff       	call   2330 <puts@plt>
    26c4:	bf 0a 00 00 00       	mov    $0xa,%edi
    26c9:	e8 42 fc ff ff       	call   2310 <putchar@plt>
    26ce:	ba 01 00 00 00       	mov    $0x1,%edx
    26d3:	48 8d 35 b7 5b 00 00 	lea    0x5bb7(%rip),%rsi        # 8291 <_IO_stdin_used+0x291>
    26da:	31 c0                	xor    %eax,%eax
    26dc:	bf 01 00 00 00       	mov    $0x1,%edi
    26e1:	e8 ca fd ff ff       	call   24b0 <__printf_chk@plt>
    26e6:	ba 06 00 00 00       	mov    $0x6,%edx
    26eb:	48 8d 35 af 5b 00 00 	lea    0x5baf(%rip),%rsi        # 82a1 <_IO_stdin_used+0x2a1>
    26f2:	31 c0                	xor    %eax,%eax
    26f4:	bf 01 00 00 00       	mov    $0x1,%edi
    26f9:	e8 b2 fd ff ff       	call   24b0 <__printf_chk@plt>
    26fe:	ba 03 00 00 00       	mov    $0x3,%edx
    2703:	48 8d 35 ac 5b 00 00 	lea    0x5bac(%rip),%rsi        # 82b6 <_IO_stdin_used+0x2b6>
    270a:	31 c0                	xor    %eax,%eax
    270c:	bf 01 00 00 00       	mov    $0x1,%edi
    2711:	e8 9a fd ff ff       	call   24b0 <__printf_chk@plt>
    2716:	ba 02 00 00 00       	mov    $0x2,%edx
    271b:	48 8d 35 a4 5b 00 00 	lea    0x5ba4(%rip),%rsi        # 82c6 <_IO_stdin_used+0x2c6>
    2722:	31 c0                	xor    %eax,%eax
    2724:	bf 01 00 00 00       	mov    $0x1,%edi
    2729:	e8 82 fd ff ff       	call   24b0 <__printf_chk@plt>
    272e:	48 8d 3d a7 5b 00 00 	lea    0x5ba7(%rip),%rdi        # 82dc <_IO_stdin_used+0x2dc>
    2735:	e8 f6 fb ff ff       	call   2330 <puts@plt>
    273a:	ba 02 00 00 00       	mov    $0x2,%edx
    273f:	48 8d 35 b2 5b 00 00 	lea    0x5bb2(%rip),%rsi        # 82f8 <_IO_stdin_used+0x2f8>
    2746:	31 c0                	xor    %eax,%eax
    2748:	bf 01 00 00 00       	mov    $0x1,%edi
    274d:	e8 5e fd ff ff       	call   24b0 <__printf_chk@plt>
    2752:	ba 0a 00 00 00       	mov    $0xa,%edx
    2757:	48 8d 35 b4 5b 00 00 	lea    0x5bb4(%rip),%rsi        # 8312 <_IO_stdin_used+0x312>
    275e:	31 c0                	xor    %eax,%eax
    2760:	bf 01 00 00 00       	mov    $0x1,%edi
    2765:	e8 46 fd ff ff       	call   24b0 <__printf_chk@plt>
    276a:	ba 01 00 00 00       	mov    $0x1,%edx
    276f:	48 8d 35 b0 5b 00 00 	lea    0x5bb0(%rip),%rsi        # 8326 <_IO_stdin_used+0x326>
    2776:	31 c0                	xor    %eax,%eax
    2778:	bf 01 00 00 00       	mov    $0x1,%edi
    277d:	e8 2e fd ff ff       	call   24b0 <__printf_chk@plt>
    2782:	ba 01 00 00 00       	mov    $0x1,%edx
    2787:	48 8d 35 a9 5b 00 00 	lea    0x5ba9(%rip),%rsi        # 8337 <_IO_stdin_used+0x337>
    278e:	31 c0                	xor    %eax,%eax
    2790:	bf 01 00 00 00       	mov    $0x1,%edi
    2795:	e8 16 fd ff ff       	call   24b0 <__printf_chk@plt>
    279a:	ba 02 00 00 00       	mov    $0x2,%edx
    279f:	48 8d 35 a9 5b 00 00 	lea    0x5ba9(%rip),%rsi        # 834f <_IO_stdin_used+0x34f>
    27a6:	31 c0                	xor    %eax,%eax
    27a8:	bf 01 00 00 00       	mov    $0x1,%edi
    27ad:	e8 fe fc ff ff       	call   24b0 <__printf_chk@plt>
    27b2:	ba 01 00 00 00       	mov    $0x1,%edx
    27b7:	48 8d 35 2a 5f 00 00 	lea    0x5f2a(%rip),%rsi        # 86e8 <_IO_stdin_used+0x6e8>
    27be:	31 c0                	xor    %eax,%eax
    27c0:	bf 01 00 00 00       	mov    $0x1,%edi
    27c5:	e8 e6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27ca:	ba 01 00 00 00       	mov    $0x1,%edx
    27cf:	48 8d 35 42 5f 00 00 	lea    0x5f42(%rip),%rsi        # 8718 <_IO_stdin_used+0x718>
    27d6:	31 c0                	xor    %eax,%eax
    27d8:	bf 01 00 00 00       	mov    $0x1,%edi
    27dd:	e8 ce fc ff ff       	call   24b0 <__printf_chk@plt>
    27e2:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    27e7:	48 8d 35 7d 5b 00 00 	lea    0x5b7d(%rip),%rsi        # 836b <_IO_stdin_used+0x36b>
    27ee:	31 c0                	xor    %eax,%eax
    27f0:	bf 01 00 00 00       	mov    $0x1,%edi
    27f5:	e8 b6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27fa:	ba 05 00 00 00       	mov    $0x5,%edx
    27ff:	48 8d 35 7f 5b 00 00 	lea    0x5b7f(%rip),%rsi        # 8385 <_IO_stdin_used+0x385>
    2806:	31 c0                	xor    %eax,%eax
    2808:	bf 01 00 00 00       	mov    $0x1,%edi
    280d:	e8 9e fc ff ff       	call   24b0 <__printf_chk@plt>
    2812:	48 8d 3d dc 58 00 00 	lea    0x58dc(%rip),%rdi        # 80f5 <_IO_stdin_used+0xf5>
    2819:	e8 12 fb ff ff       	call   2330 <puts@plt>
    281e:	be 18 00 00 00       	mov    $0x18,%esi
    2823:	bf 01 00 00 00       	mov    $0x1,%edi
    2828:	e8 d3 fb ff ff       	call   2400 <calloc@plt>
    282d:	be 18 00 00 00       	mov    $0x18,%esi
    2832:	45 31 ff             	xor    %r15d,%r15d
    2835:	45 31 f6             	xor    %r14d,%r14d
    2838:	bf 03 00 00 00       	mov    $0x3,%edi
    283d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2842:	e8 b9 fb ff ff       	call   2400 <calloc@plt>
    2847:	be f8 00 00 00       	mov    $0xf8,%esi
    284c:	bf 0a 00 00 00       	mov    $0xa,%edi
    2851:	48 89 84 24 a0 00 00 00 	mov    %rax,0xa0(%rsp)
    2859:	e8 a2 fb ff ff       	call   2400 <calloc@plt>
    285e:	be 28 00 00 00       	mov    $0x28,%esi
    2863:	bf 01 00 00 00       	mov    $0x1,%edi
    2868:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    286d:	e8 8e fb ff ff       	call   2400 <calloc@plt>
    2872:	be 28 00 00 00       	mov    $0x28,%esi
    2877:	bf 64 00 00 00       	mov    $0x64,%edi
    287c:	48 89 84 24 d8 00 00 00 	mov    %rax,0xd8(%rsp)
    2884:	e8 77 fb ff ff       	call   2400 <calloc@plt>
    2889:	48 89 84 24 e0 00 00 00 	mov    %rax,0xe0(%rsp)
    2891:	48 89 c3             	mov    %rax,%rbx
    2894:	49 89 dd             	mov    %rbx,%r13
    2897:	31 ed                	xor    %ebp,%ebp
    2899:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    28a0:	41 8d 14 2e          	lea    (%r14,%rbp,1),%edx
    28a4:	41 89 e8             	mov    %ebp,%r8d
    28a7:	44 89 f9             	mov    %r15d,%ecx
    28aa:	4c 89 e6             	mov    %r12,%rsi
    28ad:	bf 01 00 00 00       	mov    $0x1,%edi
    28b2:	31 c0                	xor    %eax,%eax
    28b4:	83 c5 01             	add    $0x1,%ebp
    28b7:	e8 f4 fb ff ff       	call   24b0 <__printf_chk@plt>
    28bc:	4c 89 ef             	mov    %r13,%rdi
    28bf:	31 f6                	xor    %esi,%esi
    28c1:	49 83 c5 28          	add    $0x28,%r13
    28c5:	e8 b6 fc ff ff       	call   2580 <pthread_mutex_init@plt>
    28ca:	83 fd 0a             	cmp    $0xa,%ebp
    28cd:	75 d1                	jne    28a0 <main+0x230>
    28cf:	41 83 c6 0a          	add    $0xa,%r14d
    28d3:	41 83 c7 01          	add    $0x1,%r15d
    28d7:	48 81 c3 90 01 00 00 	add    $0x190,%rbx
    28de:	41 83 fe 64          	cmp    $0x64,%r14d
    28e2:	75 b0                	jne    2894 <main+0x224>
    28e4:	ba 06 00 00 00       	mov    $0x6,%edx
    28e9:	48 8d 35 b9 5a 00 00 	lea    0x5ab9(%rip),%rsi        # 83a9 <_IO_stdin_used+0x3a9>
    28f0:	bf 01 00 00 00       	mov    $0x1,%edi
    28f5:	31 c0                	xor    %eax,%eax
    28f7:	e8 b4 fb ff ff       	call   24b0 <__printf_chk@plt>
    28fc:	ba 0c 00 00 00       	mov    $0xc,%edx
    2901:	48 8d 35 b7 5a 00 00 	lea    0x5ab7(%rip),%rsi        # 83bf <_IO_stdin_used+0x3bf>
    2908:	31 c0                	xor    %eax,%eax
    290a:	bf 01 00 00 00       	mov    $0x1,%edi
    290f:	e8 9c fb ff ff       	call   24b0 <__printf_chk@plt>
    2914:	be 10 00 00 00       	mov    $0x10,%esi
    2919:	bf 0c 00 00 00       	mov    $0xc,%edi
    291e:	e8 dd fa ff ff       	call   2400 <calloc@plt>
    2923:	48 89 84 24 c0 00 00 00 	mov    %rax,0xc0(%rsp)
    292b:	48 89 c5             	mov    %rax,%rbp
    292e:	4c 8d a0 c0 00 00 00 	lea    0xc0(%rax),%r12
    2935:	49 89 c6             	mov    %rax,%r14
    2938:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    293f:	be 00 01 00 00       	mov    $0x100,%esi
    2944:	bf 01 00 00 00       	mov    $0x1,%edi
    2949:	49 83 c6 10          	add    $0x10,%r14
    294d:	e8 ae fa ff ff       	call   2400 <calloc@plt>
    2952:	be 20 00 00 00       	mov    $0x20,%esi
    2957:	bf 64 00 00 00       	mov    $0x64,%edi
    295c:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    2960:	48 89 c3             	mov    %rax,%rbx
    2963:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
    296d:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
    2977:	e8 84 fa ff ff       	call   2400 <calloc@plt>
    297c:	48 89 83 88 00 00 00 	mov    %rax,0x88(%rbx)
    2983:	4d 39 f4             	cmp    %r14,%r12
    2986:	75 b0                	jne    2938 <main+0x2c8>
    2988:	be 08 00 00 00       	mov    $0x8,%esi
    298d:	bf 64 00 00 00       	mov    $0x64,%edi
    2992:	31 db                	xor    %ebx,%ebx
    2994:	45 31 ff             	xor    %r15d,%r15d
    2997:	48 8b 05 62 63 00 00 	mov    0x6362(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
    299e:	4c 8d b4 24 08 01 00 00 	lea    0x108(%rsp),%r14
    29a6:	41 89 dd             	mov    %ebx,%r13d
    29a9:	c7 84 24 10 01 00 00 06 00 00 00 	movl   $0x6,0x110(%rsp)
    29b4:	48 89 84 24 08 01 00 00 	mov    %rax,0x108(%rsp)
    29bc:	e8 3f fa ff ff       	call   2400 <calloc@plt>
    29c1:	be 10 00 00 00       	mov    $0x10,%esi
    29c6:	bf 01 00 00 00       	mov    $0x1,%edi
    29cb:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    29d3:	e8 28 fa ff ff       	call   2400 <calloc@plt>
    29d8:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    29e0:	49 89 c3             	mov    %rax,%r11
    29e3:	c7 00 ff ff ff ff    	movl   $0xffffffff,(%rax)
    29e9:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    29ee:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
    29f6:	49 89 43 08          	mov    %rax,0x8(%r11)
    29fa:	48 8b 84 24 a0 00 00 00 	mov    0xa0(%rsp),%rax
    2a02:	c7 44 24 78 00 00 00 00 	movl   $0x0,0x78(%rsp)
    2a0a:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
    2a12:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    2a1a:	4c 89 9c 24 d0 00 00 00 	mov    %r11,0xd0(%rsp)
    2a22:	be 00 01 00 00       	mov    $0x100,%esi
    2a27:	bf 01 00 00 00       	mov    $0x1,%edi
    2a2c:	44 89 7c 24 50       	mov    %r15d,0x50(%rsp)
    2a31:	e8 ca f9 ff ff       	call   2400 <calloc@plt>
    2a36:	be 08 00 00 00       	mov    $0x8,%esi
    2a3b:	bf 64 00 00 00       	mov    $0x64,%edi
    2a40:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a45:	e8 b6 f9 ff ff       	call   2400 <calloc@plt>
    2a4a:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2a4f:	48 8b 9c 24 a8 00 00 00 	mov    0xa8(%rsp),%rbx
    2a57:	48 c7 44 24 68 00 00 00 00 	movq   $0x0,0x68(%rsp)
    2a60:	48 89 ac 24 e8 00 00 00 	mov    %rbp,0xe8(%rsp)
    2a68:	48 89 82 88 00 00 00 	mov    %rax,0x88(%rdx)
    2a6f:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    2a77:	4a 89 14 fb          	mov    %rdx,(%rbx,%r15,8)
    2a7b:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    2a80:	48 89 82 98 00 00 00 	mov    %rax,0x98(%rdx)
    2a87:	43 8b 04 be          	mov    (%r14,%r15,4),%eax
    2a8b:	c7 82 90 00 00 00 06 00 00 00 	movl   $0x6,0x90(%rdx)
    2a95:	89 82 a0 00 00 00    	mov    %eax,0xa0(%rdx)
    2a9b:	4c 89 f8             	mov    %r15,%rax
    2a9e:	48 c1 e0 05          	shl    $0x5,%rax
    2aa2:	48 89 94 24 f0 00 00 00 	mov    %rdx,0xf0(%rsp)
    2aaa:	4c 29 f8             	sub    %r15,%rax
    2aad:	48 89 9c 24 c8 00 00 00 	mov    %rbx,0xc8(%rsp)
    2ab5:	48 c1 e0 04          	shl    $0x4,%rax
    2ab9:	4c 89 b4 24 f8 00 00 00 	mov    %r14,0xf8(%rsp)
    2ac1:	4d 89 fe             	mov    %r15,%r14
    2ac4:	4c 8d 0c 18          	lea    (%rax,%rbx,1),%r9
    2ac8:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2acd:	43 8d 1c 3f          	lea    (%r15,%r15,1),%ebx
    2ad1:	41 89 df             	mov    %ebx,%r15d
    2ad4:	48 c1 e0 04          	shl    $0x4,%rax
    2ad8:	48 01 e8             	add    %rbp,%rax
    2adb:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2ae0:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    2ae8:	8b 54 24 50          	mov    0x50(%rsp),%edx
    2aec:	44 89 f9             	mov    %r15d,%ecx
    2aef:	bf 01 00 00 00       	mov    $0x1,%edi
    2af4:	48 8b 9c 24 f0 00 00 00 	mov    0xf0(%rsp),%rbx
    2afc:	48 8d 35 3d 5c 00 00 	lea    0x5c3d(%rip),%rsi        # 8740 <_IO_stdin_used+0x740>
    2b03:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2b08:	49 89 81 e0 00 00 00 	mov    %rax,0xe0(%r9)
    2b0f:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    2b17:	49 89 99 d8 00 00 00 	mov    %rbx,0xd8(%r9)
    2b1e:	41 89 91 e8 00 00 00 	mov    %edx,0xe8(%r9)
    2b25:	49 89 81 f0 00 00 00 	mov    %rax,0xf0(%r9)
    2b2c:	31 c0                	xor    %eax,%eax
    2b2e:	e8 7d f9 ff ff       	call   24b0 <__printf_chk@plt>
    2b33:	be 08 00 00 00       	mov    $0x8,%esi
    2b38:	bf 02 00 00 00       	mov    $0x2,%edi
    2b3d:	e8 be f8 ff ff       	call   2400 <calloc@plt>
    2b42:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2b47:	be 80 00 00 00       	mov    $0x80,%esi
    2b4c:	bf 01 00 00 00       	mov    $0x1,%edi
    2b51:	48 89 c5             	mov    %rax,%rbp
    2b54:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    2b5b:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    2b60:	4c 89 0c 18          	mov    %r9,(%rax,%rbx,1)
    2b64:	e8 97 f8 ff ff       	call   2400 <calloc@plt>
    2b69:	45 89 f8             	mov    %r15d,%r8d
    2b6c:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2b71:	41 83 e0 01          	and    $0x1,%r8d
    2b75:	48 89 c3             	mov    %rax,%rbx
    2b78:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2b7d:	0f 84 83 0a 00 00    	je     3606 <main+0xf96>
    2b83:	41 8d 57 ff          	lea    -0x1(%r15),%edx
    2b87:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    2b8c:	48 89 d0             	mov    %rdx,%rax
    2b8f:	48 89 d1             	mov    %rdx,%rcx
    2b92:	48 c1 e0 05          	shl    $0x5,%rax
    2b96:	48 29 d0             	sub    %rdx,%rax
    2b99:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
    2b9d:	41 8d 7f 01          	lea    0x1(%r15),%edi
    2ba1:	89 bc 24 80 00 00 00 	mov    %edi,0x80(%rsp)
    2ba8:	48 8d 45 08          	lea    0x8(%rbp),%rax
    2bac:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2bb1:	4c 89 c8             	mov    %r9,%rax
    2bb4:	48 89 45 08          	mov    %rax,0x8(%rbp)
    2bb8:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    2bc0:	48 8d 35 a9 5b 00 00 	lea    0x5ba9(%rip),%rsi        # 8770 <_IO_stdin_used+0x770>
    2bc7:	bf 01 00 00 00       	mov    $0x1,%edi
    2bcc:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2bd0:	49 89 41 48          	mov    %rax,0x48(%r9)
    2bd4:	31 c0                	xor    %eax,%eax
    2bd6:	48 89 55 00          	mov    %rdx,0x0(%rbp)
    2bda:	44 89 fa             	mov    %r15d,%edx
    2bdd:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2be2:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2be6:	e8 c5 f8 ff ff       	call   24b0 <__printf_chk@plt>
    2beb:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2bef:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2bf4:	31 c0                	xor    %eax,%eax
    2bf6:	44 89 fa             	mov    %r15d,%edx
    2bf9:	48 8d 35 a0 5b 00 00 	lea    0x5ba0(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
    2c00:	bf 01 00 00 00       	mov    $0x1,%edi
    2c05:	41 89 89 b8 00 00 00 	mov    %ecx,0xb8(%r9)
    2c0c:	8b 4c 24 78          	mov    0x78(%rsp),%ecx
    2c10:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2c15:	e8 96 f8 ff ff       	call   24b0 <__printf_chk@plt>
    2c1a:	41 83 ff 01          	cmp    $0x1,%r15d
    2c1e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2c23:	0f 8f c0 10 00 00    	jg     3ce9 <main+0x1679>
    2c29:	48 63 44 24 78       	movslq 0x78(%rsp),%rax
    2c2e:	48 89 c7             	mov    %rax,%rdi
    2c31:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2c37:	77 12                	ja     2c4b <main+0x5db>
    2c39:	48 c1 e8 06          	shr    $0x6,%rax
    2c3d:	ba 01 00 00 00       	mov    $0x1,%edx
    2c42:	89 f9                	mov    %edi,%ecx
    2c44:	48 d3 e2             	shl    %cl,%rdx
    2c47:	48 09 14 c3          	or     %rdx,(%rbx,%rax,8)
    2c4b:	83 44 24 78 02       	addl   $0x2,0x78(%rsp)
    2c50:	45 89 79 08          	mov    %r15d,0x8(%r9)
    2c54:	be 10 00 00 00       	mov    $0x10,%esi
    2c59:	bf 64 00 00 00       	mov    $0x64,%edi
    2c5e:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
    2c66:	49 89 99 b0 00 00 00 	mov    %rbx,0xb0(%r9)
    2c6d:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
    2c74:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
    2c7c:	49 89 69 18          	mov    %rbp,0x18(%r9)
    2c80:	31 ed                	xor    %ebp,%ebp
    2c82:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
    2c89:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2c8e:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
    2c95:	49 89 41 20          	mov    %rax,0x20(%r9)
    2c99:	48 8b 05 68 60 00 00 	mov    0x6068(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    2ca0:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
    2ca8:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
    2caf:	48 8b 05 5a 60 00 00 	mov    0x605a(%rip),%rax        # 8d10 <_IO_stdin_used+0xd10>
    2cb6:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2cbb:	49 89 41 28          	mov    %rax,0x28(%r9)
    2cbf:	e8 3c f7 ff ff       	call   2400 <calloc@plt>
    2cc4:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2cc9:	be 10 00 00 00       	mov    $0x10,%esi
    2cce:	bf 64 00 00 00       	mov    $0x64,%edi
    2cd3:	49 89 41 68          	mov    %rax,0x68(%r9)
    2cd7:	e8 24 f7 ff ff       	call   2400 <calloc@plt>
    2cdc:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2ce1:	be 28 00 00 00       	mov    $0x28,%esi
    2ce6:	66 0f 6f 3d e2 5f 00 00 	movdqa 0x5fe2(%rip),%xmm7        # 8cd0 <_IO_stdin_used+0xcd0>
    2cee:	bf 64 00 00 00       	mov    $0x64,%edi
    2cf3:	49 89 41 70          	mov    %rax,0x70(%r9)
    2cf7:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
    2cff:	e8 fc f6 ff ff       	call   2400 <calloc@plt>
    2d04:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2d09:	bf 03 00 00 00       	mov    $0x3,%edi
    2d0e:	66 0f 6f 35 ba 5f 00 00 	movdqa 0x5fba(%rip),%xmm6        # 8cd0 <_IO_stdin_used+0xcd0>
    2d16:	be 00 02 00 00       	mov    $0x200,%esi
    2d1b:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
    2d22:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
    2d2a:	e8 d1 f6 ff ff       	call   2400 <calloc@plt>
    2d2f:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2d34:	44 89 7c 24 18       	mov    %r15d,0x18(%rsp)
    2d39:	45 89 ef             	mov    %r13d,%r15d
    2d3c:	48 63 bc 24 80 00 00 00 	movslq 0x80(%rsp),%rdi
    2d44:	48 89 c2             	mov    %rax,%rdx
    2d47:	49 89 41 38          	mov    %rax,0x38(%r9)
    2d4b:	48 89 fb             	mov    %rdi,%rbx
    2d4e:	48 69 ff ab aa aa 2a 	imul   $0x2aaaaaab,%rdi,%rdi
    2d55:	4c 89 4c 24 48       	mov    %r9,0x48(%rsp)
    2d5a:	89 d8                	mov    %ebx,%eax
    2d5c:	c1 f8 1f             	sar    $0x1f,%eax
    2d5f:	48 c1 ef 20          	shr    $0x20,%rdi
    2d63:	29 c7                	sub    %eax,%edi
    2d65:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2d68:	01 c0                	add    %eax,%eax
    2d6a:	29 c3                	sub    %eax,%ebx
    2d6c:	89 9c 24 84 00 00 00 	mov    %ebx,0x84(%rsp)
    2d73:	48 63 c5             	movslq %ebp,%rax
    2d76:	be 00 01 00 00       	mov    $0x100,%esi
    2d7b:	bf 06 00 00 00       	mov    $0x6,%edi
    2d80:	45 31 ed             	xor    %r13d,%r13d
    2d83:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2d88:	48 c1 e0 09          	shl    $0x9,%rax
    2d8c:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
    2d90:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2d95:	48 8d 05 54 18 00 00 	lea    0x1854(%rip),%rax        # 45f0 <do_protected_write>
    2d9c:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
    2da3:	e8 58 f6 ff ff       	call   2400 <calloc@plt>
    2da8:	8b 74 24 58          	mov    0x58(%rsp),%esi
    2dac:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
    2db3:	48 89 c1             	mov    %rax,%rcx
    2db6:	49 89 c4             	mov    %rax,%r12
    2db9:	85 f6                	test   %esi,%esi
    2dbb:	0f 84 84 01 00 00    	je     2f45 <main+0x8d5>
    2dc1:	8b 44 24 18          	mov    0x18(%rsp),%eax
    2dc5:	48 89 8c 24 88 00 00 00 	mov    %rcx,0x88(%rsp)
    2dcd:	48 89 cb             	mov    %rcx,%rbx
    2dd0:	45 89 ec             	mov    %r13d,%r12d
    2dd3:	83 e8 01             	sub    $0x1,%eax
    2dd6:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2dda:	eb 19                	jmp    2df5 <main+0x785>
    2ddc:	0f 1f 40 00          	nopl   0x0(%rax)
    2de0:	41 83 c4 01          	add    $0x1,%r12d
    2de4:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    2deb:	41 83 fc 06          	cmp    $0x6,%r12d
    2def:	0f 84 d0 02 00 00    	je     30c5 <main+0xa55>
    2df5:	45 89 e5             	mov    %r12d,%r13d
    2df8:	31 c0                	xor    %eax,%eax
    2dfa:	44 89 e2             	mov    %r12d,%edx
    2dfd:	bf 01 00 00 00       	mov    $0x1,%edi
    2e02:	41 d1 fd             	sar    %r13d
    2e05:	48 8d 35 cd 55 00 00 	lea    0x55cd(%rip),%rsi        # 83d9 <_IO_stdin_used+0x3d9>
    2e0c:	44 89 e9             	mov    %r13d,%ecx
    2e0f:	e8 9c f6 ff ff       	call   24b0 <__printf_chk@plt>
    2e14:	45 39 f5             	cmp    %r14d,%r13d
    2e17:	75 c7                	jne    2de0 <main+0x770>
    2e19:	be 08 00 00 00       	mov    $0x8,%esi
    2e1e:	bf 01 00 00 00       	mov    $0x1,%edi
    2e23:	e8 d8 f5 ff ff       	call   2400 <calloc@plt>
    2e28:	be 08 00 00 00       	mov    $0x8,%esi
    2e2d:	bf 01 00 00 00       	mov    $0x1,%edi
    2e32:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2e37:	e8 c4 f5 ff ff       	call   2400 <calloc@plt>
    2e3c:	be 80 04 00 00       	mov    $0x480,%esi
    2e41:	bf 03 00 00 00       	mov    $0x3,%edi
    2e46:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2e4b:	e8 b0 f5 ff ff       	call   2400 <calloc@plt>
    2e50:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    2e54:	44 89 e2             	mov    %r12d,%edx
    2e57:	48 c7 83 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%rbx)
    2e62:	49 89 c5             	mov    %rax,%r13
    2e65:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    2e6b:	48 8d 35 4e 59 00 00 	lea    0x594e(%rip),%rsi        # 87c0 <_IO_stdin_used+0x7c0>
    2e72:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
    2e78:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
    2e82:	44 89 a0 14 04 00 00 	mov    %r12d,0x414(%rax)
    2e89:	41 8d 47 01          	lea    0x1(%r15),%eax
    2e8d:	41 89 85 98 08 00 00 	mov    %eax,0x898(%r13)
    2e94:	49 8d 85 80 04 00 00 	lea    0x480(%r13),%rax
    2e9b:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
    2ea2:	8b 44 24 70          	mov    0x70(%rsp),%eax
    2ea6:	45 89 bd 18 04 00 00 	mov    %r15d,0x418(%r13)
    2ead:	41 83 c7 02          	add    $0x2,%r15d
    2eb1:	41 89 bd 8c 08 00 00 	mov    %edi,0x88c(%r13)
    2eb8:	89 c1                	mov    %eax,%ecx
    2eba:	bf 01 00 00 00       	mov    $0x1,%edi
    2ebf:	89 83 b4 00 00 00    	mov    %eax,0xb4(%rbx)
    2ec5:	31 c0                	xor    %eax,%eax
    2ec7:	41 c7 85 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r13)
    2ed2:	41 89 ad 90 08 00 00 	mov    %ebp,0x890(%r13)
    2ed9:	45 89 a5 94 08 00 00 	mov    %r12d,0x894(%r13)
    2ee0:	4c 89 2b             	mov    %r13,(%rbx)
    2ee3:	48 c7 83 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%rbx)
    2eee:	41 c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r13)
    2ef9:	41 c7 85 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r13)
    2f04:	c7 83 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%rbx)
    2f0e:	e8 9d f5 ff ff       	call   24b0 <__printf_chk@plt>
    2f13:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    2f18:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    2f1d:	66 0f 6f 35 bb 5d 00 00 	movdqa 0x5dbb(%rip),%xmm6        # 8ce0 <_IO_stdin_used+0xce0>
    2f25:	4d 89 5d 00          	mov    %r11,0x0(%r13)
    2f29:	4d 89 95 80 04 00 00 	mov    %r10,0x480(%r13)
    2f30:	41 0f 29 b5 80 00 00 00 	movaps %xmm6,0x80(%r13)
    2f38:	41 0f 29 b5 00 05 00 00 	movaps %xmm6,0x500(%r13)
    2f40:	e9 9b fe ff ff       	jmp    2de0 <main+0x770>
    2f45:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
    2f4a:	44 89 eb             	mov    %r13d,%ebx
    2f4d:	eb 14                	jmp    2f63 <main+0x8f3>
    2f4f:	90                   	nop
    2f50:	83 c3 01             	add    $0x1,%ebx
    2f53:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    2f5a:	83 fb 06             	cmp    $0x6,%ebx
    2f5d:	0f 84 5b 01 00 00    	je     30be <main+0xa4e>
    2f63:	41 89 dd             	mov    %ebx,%r13d
    2f66:	31 c0                	xor    %eax,%eax
    2f68:	89 da                	mov    %ebx,%edx
    2f6a:	bf 01 00 00 00       	mov    $0x1,%edi
    2f6f:	41 d1 fd             	sar    %r13d
    2f72:	48 8d 35 60 54 00 00 	lea    0x5460(%rip),%rsi        # 83d9 <_IO_stdin_used+0x3d9>
    2f79:	44 89 e9             	mov    %r13d,%ecx
    2f7c:	e8 2f f5 ff ff       	call   24b0 <__printf_chk@plt>
    2f81:	45 39 f5             	cmp    %r14d,%r13d
    2f84:	75 ca                	jne    2f50 <main+0x8e0>
    2f86:	be 08 00 00 00       	mov    $0x8,%esi
    2f8b:	bf 01 00 00 00       	mov    $0x1,%edi
    2f90:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    2f97:	e8 64 f4 ff ff       	call   2400 <calloc@plt>
    2f9c:	be 08 00 00 00       	mov    $0x8,%esi
    2fa1:	bf 01 00 00 00       	mov    $0x1,%edi
    2fa6:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    2fab:	e8 50 f4 ff ff       	call   2400 <calloc@plt>
    2fb0:	be 80 04 00 00       	mov    $0x480,%esi
    2fb5:	bf 03 00 00 00       	mov    $0x3,%edi
    2fba:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2fbf:	e8 3c f4 ff ff       	call   2400 <calloc@plt>
    2fc4:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    2fc8:	89 da                	mov    %ebx,%edx
    2fca:	49 c7 44 24 88 00 00 00 00 	movq   $0x0,-0x78(%r12)
    2fd3:	49 89 c5             	mov    %rax,%r13
    2fd6:	89 98 14 04 00 00    	mov    %ebx,0x414(%rax)
    2fdc:	48 8d 35 dd 57 00 00 	lea    0x57dd(%rip),%rsi        # 87c0 <_IO_stdin_used+0x7c0>
    2fe3:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
    2fe9:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
    2ff3:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    2ff9:	41 8d 47 01          	lea    0x1(%r15),%eax
    2ffd:	41 89 85 98 08 00 00 	mov    %eax,0x898(%r13)
    3004:	49 8d 85 80 04 00 00 	lea    0x480(%r13),%rax
    300b:	49 89 44 24 80       	mov    %rax,-0x80(%r12)
    3010:	8b 84 24 84 00 00 00 	mov    0x84(%rsp),%eax
    3017:	45 89 bd 18 04 00 00 	mov    %r15d,0x418(%r13)
    301e:	41 83 c7 02          	add    $0x2,%r15d
    3022:	41 89 44 24 b4       	mov    %eax,-0x4c(%r12)
    3027:	89 c1                	mov    %eax,%ecx
    3029:	31 c0                	xor    %eax,%eax
    302b:	41 89 bd 8c 08 00 00 	mov    %edi,0x88c(%r13)
    3032:	bf 01 00 00 00       	mov    $0x1,%edi
    3037:	41 89 9d 94 08 00 00 	mov    %ebx,0x894(%r13)
    303e:	83 c3 01             	add    $0x1,%ebx
    3041:	4d 89 ac 24 00 ff ff ff 	mov    %r13,-0x100(%r12)
    3049:	49 c7 44 24 90 00 00 00 00 	movq   $0x0,-0x70(%r12)
    3052:	41 c7 44 24 b0 01 00 00 00 	movl   $0x1,-0x50(%r12)
    305b:	41 c7 85 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r13)
    3066:	41 89 ad 90 08 00 00 	mov    %ebp,0x890(%r13)
    306d:	41 c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r13)
    3078:	41 c7 85 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r13)
    3083:	e8 28 f4 ff ff       	call   24b0 <__printf_chk@plt>
    3088:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
    308d:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
    3092:	66 0f 6f 35 46 5c 00 00 	movdqa 0x5c46(%rip),%xmm6        # 8ce0 <_IO_stdin_used+0xce0>
    309a:	4d 89 5d 00          	mov    %r11,0x0(%r13)
    309e:	4d 89 95 80 04 00 00 	mov    %r10,0x480(%r13)
    30a5:	41 0f 29 b5 80 00 00 00 	movaps %xmm6,0x80(%r13)
    30ad:	41 0f 29 b5 00 05 00 00 	movaps %xmm6,0x500(%r13)
    30b5:	83 fb 06             	cmp    $0x6,%ebx
    30b8:	0f 85 a5 fe ff ff    	jne    2f63 <main+0x8f3>
    30be:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    30c3:	eb 08                	jmp    30cd <main+0xa5d>
    30c5:	48 8b 8c 24 88 00 00 00 	mov    0x88(%rsp),%rcx
    30cd:	49 89 cd             	mov    %rcx,%r13
    30d0:	31 db                	xor    %ebx,%ebx
    30d2:	89 e9                	mov    %ebp,%ecx
    30d4:	4c 89 f5             	mov    %r14,%rbp
    30d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    30e0:	89 d8                	mov    %ebx,%eax
    30e2:	d1 f8                	sar    %eax
    30e4:	39 e8                	cmp    %ebp,%eax
    30e6:	0f 84 8b 01 00 00    	je     3277 <main+0xc07>
    30ec:	89 da                	mov    %ebx,%edx
    30ee:	48 8d 35 f4 52 00 00 	lea    0x52f4(%rip),%rsi        # 83e9 <_IO_stdin_used+0x3e9>
    30f5:	bf 01 00 00 00       	mov    $0x1,%edi
    30fa:	31 c0                	xor    %eax,%eax
    30fc:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    3100:	e8 ab f3 ff ff       	call   24b0 <__printf_chk@plt>
    3105:	be 08 00 00 00       	mov    $0x8,%esi
    310a:	bf 01 00 00 00       	mov    $0x1,%edi
    310f:	e8 ec f2 ff ff       	call   2400 <calloc@plt>
    3114:	be 08 00 00 00       	mov    $0x8,%esi
    3119:	bf 01 00 00 00       	mov    $0x1,%edi
    311e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3123:	e8 d8 f2 ff ff       	call   2400 <calloc@plt>
    3128:	be 80 04 00 00       	mov    $0x480,%esi
    312d:	bf 03 00 00 00       	mov    $0x3,%edi
    3132:	49 89 c6             	mov    %rax,%r14
    3135:	e8 c6 f2 ff ff       	call   2400 <calloc@plt>
    313a:	be 80 04 00 00       	mov    $0x480,%esi
    313f:	bf 03 00 00 00       	mov    $0x3,%edi
    3144:	49 89 c4             	mov    %rax,%r12
    3147:	e8 b4 f2 ff ff       	call   2400 <calloc@plt>
    314c:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    3150:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
    3154:	41 8d 77 01          	lea    0x1(%r15),%esi
    3158:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    315d:	66 0f 6f 35 7b 5b 00 00 	movdqa 0x5b7b(%rip),%xmm6        # 8ce0 <_IO_stdin_used+0xce0>
    3165:	41 89 b4 24 98 08 00 00 	mov    %esi,0x898(%r12)
    316d:	49 8d b4 24 80 04 00 00 	lea    0x480(%r12),%rsi
    3175:	45 89 bc 24 18 04 00 00 	mov    %r15d,0x418(%r12)
    317d:	41 83 c7 02          	add    $0x2,%r15d
    3181:	41 c7 84 24 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%r12)
    318d:	41 89 bc 24 0c 04 00 00 	mov    %edi,0x40c(%r12)
    3195:	41 89 8c 24 10 04 00 00 	mov    %ecx,0x410(%r12)
    319d:	41 89 9c 24 14 04 00 00 	mov    %ebx,0x414(%r12)
    31a5:	41 c7 84 24 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r12)
    31b1:	41 89 bc 24 8c 08 00 00 	mov    %edi,0x88c(%r12)
    31b9:	41 89 8c 24 90 08 00 00 	mov    %ecx,0x890(%r12)
    31c1:	41 89 9c 24 94 08 00 00 	mov    %ebx,0x894(%r12)
    31c9:	4d 89 65 00          	mov    %r12,0x0(%r13)
    31cd:	4d 89 a5 a0 00 00 00 	mov    %r12,0xa0(%r13)
    31d4:	49 89 b5 80 00 00 00 	mov    %rsi,0x80(%r13)
    31db:	49 c7 85 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r13)
    31e6:	49 c7 85 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r13)
    31f1:	41 c7 84 24 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r12)
    31fd:	41 c7 84 24 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r12)
    3209:	49 89 b5 a8 00 00 00 	mov    %rsi,0xa8(%r13)
    3210:	41 c7 85 b0 00 00 00 02 00 00 00 	movl   $0x2,0xb0(%r13)
    321b:	4c 89 20             	mov    %r12,(%rax)
    321e:	48 89 70 08          	mov    %rsi,0x8(%rax)
    3222:	49 89 85 98 00 00 00 	mov    %rax,0x98(%r13)
    3229:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
    3235:	41 c7 84 24 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r12)
    3241:	49 89 14 24          	mov    %rdx,(%r12)
    3245:	4d 89 b4 24 80 04 00 00 	mov    %r14,0x480(%r12)
    324d:	41 c7 84 24 80 05 00 00 01 00 00 00 	movl   $0x1,0x580(%r12)
    3259:	41 c7 84 24 00 06 00 00 00 00 00 00 	movl   $0x0,0x600(%r12)
    3265:	41 0f 29 b4 24 80 00 00 00 	movaps %xmm6,0x80(%r12)
    326e:	41 0f 29 b4 24 00 05 00 00 	movaps %xmm6,0x500(%r12)
    3277:	83 c3 01             	add    $0x1,%ebx
    327a:	49 81 c5 00 01 00 00 	add    $0x100,%r13
    3281:	83 fb 06             	cmp    $0x6,%ebx
    3284:	0f 85 56 fe ff ff    	jne    30e0 <main+0xa70>
    328a:	be 01 00 00 00       	mov    $0x1,%esi
    328f:	bf 00 01 00 00       	mov    $0x100,%edi
    3294:	49 89 ee             	mov    %rbp,%r14
    3297:	89 cd                	mov    %ecx,%ebp
    3299:	e8 62 f1 ff ff       	call   2400 <calloc@plt>
    329e:	bf 20 00 00 00       	mov    $0x20,%edi
    32a3:	48 89 c3             	mov    %rax,%rbx
    32a6:	e8 c5 f1 ff ff       	call   2470 <malloc@plt>
    32ab:	48 83 ec 08          	sub    $0x8,%rsp
    32af:	48 89 df             	mov    %rbx,%rdi
    32b2:	41 89 e9             	mov    %ebp,%r9d
    32b5:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    32ba:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    32bf:	ba 00 01 00 00       	mov    $0x100,%edx
    32c4:	31 c0                	xor    %eax,%eax
    32c6:	48 8d 0d 1b 55 00 00 	lea    0x551b(%rip),%rcx        # 87e8 <_IO_stdin_used+0x7e8>
    32cd:	be 01 00 00 00       	mov    $0x1,%esi
    32d2:	41 55                	push   %r13
    32d4:	44 8b 44 24 28       	mov    0x28(%rsp),%r8d
    32d9:	e8 c2 f2 ff ff       	call   25a0 <__sprintf_chk@plt>
    32de:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    32e3:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    32e8:	44 89 ef             	mov    %r13d,%edi
    32eb:	be 20 00 00 00       	mov    $0x20,%esi
    32f0:	45 89 6b 18          	mov    %r13d,0x18(%r11)
    32f4:	4c 8b 6c 24 58       	mov    0x58(%rsp),%r13
    32f9:	49 89 43 10          	mov    %rax,0x10(%r11)
    32fd:	49 63 45 08          	movslq 0x8(%r13),%rax
    3301:	49 8b 55 38          	mov    0x38(%r13),%rdx
    3305:	49 89 1b             	mov    %rbx,(%r11)
    3308:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    330d:	49 89 43 08          	mov    %rax,0x8(%r11)
    3311:	8b 44 24 30          	mov    0x30(%rsp),%eax
    3315:	48 01 d3             	add    %rdx,%rbx
    3318:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    331d:	89 83 a0 01 00 00    	mov    %eax,0x1a0(%rbx)
    3323:	83 c0 01             	add    $0x1,%eax
    3326:	89 44 24 30          	mov    %eax,0x30(%rsp)
    332a:	8d 45 01             	lea    0x1(%rbp),%eax
    332d:	83 e0 01             	and    $0x1,%eax
    3330:	89 bb 9c 01 00 00    	mov    %edi,0x19c(%rbx)
    3336:	bf 63 00 00 00       	mov    $0x63,%edi
    333b:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
    3341:	89 83 98 01 00 00    	mov    %eax,0x198(%rbx)
    3347:	4c 89 9b 90 01 00 00 	mov    %r11,0x190(%rbx)
    334e:	c7 83 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbx)
    3358:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
    3363:	e8 98 f0 ff ff       	call   2400 <calloc@plt>
    3368:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
    3373:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
    337a:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    337f:	48 8b 00             	mov    (%rax),%rax
    3382:	8b 48 04             	mov    0x4(%rax),%ecx
    3385:	49 39 c5             	cmp    %rax,%r13
    3388:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
    338f:	89 8b 30 01 00 00    	mov    %ecx,0x130(%rbx)
    3395:	5a                   	pop    %rdx
    3396:	59                   	pop    %rcx
    3397:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    339c:	0f 85 4a 11 00 00    	jne    44ec <main+0x1e7c>
    33a2:	66 0f 6f 05 46 59 00 00 	movdqa 0x5946(%rip),%xmm0        # 8cf0 <_IO_stdin_used+0xcf0>
    33aa:	89 6b 04             	mov    %ebp,0x4(%rbx)
    33ad:	48 8b 05 4c 59 00 00 	mov    0x594c(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
    33b4:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
    33be:	c7 83 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rbx)
    33c8:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
    33cf:	0f 11 83 34 01 00 00 	movups %xmm0,0x134(%rbx)
    33d6:	83 fd 01             	cmp    $0x1,%ebp
    33d9:	0f 84 05 01 00 00    	je     34e4 <main+0xe74>
    33df:	85 ed                	test   %ebp,%ebp
    33e1:	0f 84 e5 00 00 00    	je     34cc <main+0xe5c>
    33e7:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
    33ec:	48 8d 05 7d 37 00 00 	lea    0x377d(%rip),%rax        # 6b70 <barriered_work>
    33f3:	be 08 00 00 00       	mov    $0x8,%esi
    33f8:	45 89 fd             	mov    %r15d,%r13d
    33fb:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
    3402:	bf 01 00 00 00       	mov    $0x1,%edi
    3407:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    3412:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    3417:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    341c:	e8 df ef ff ff       	call   2400 <calloc@plt>
    3421:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3426:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
    342b:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    3430:	83 44 24 7c 01       	addl   $0x1,0x7c(%rsp)
    3435:	49 89 41 50          	mov    %rax,0x50(%r9)
    3439:	49 81 c1 f8 00 00 00 	add    $0xf8,%r9
    3440:	66 0f 6f bc 24 b0 00 00 00 	movdqa 0xb0(%rsp),%xmm7
    3449:	48 89 18             	mov    %rbx,(%rax)
    344c:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3451:	48 83 c3 10          	add    $0x10,%rbx
    3455:	48 89 5c 24 60       	mov    %rbx,0x60(%rsp)
    345a:	48 8b 00             	mov    (%rax),%rax
    345d:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
    3464:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
    346e:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
    3475:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
    347f:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
    3489:	41 8b 81 0c ff ff ff 	mov    -0xf4(%r9),%eax
    3490:	c7 82 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rdx)
    349a:	48 83 7c 24 68 08    	cmpq   $0x8,0x68(%rsp)
    34a0:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
    34a6:	48 8b 05 53 58 00 00 	mov    0x5853(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
    34ad:	48 89 82 44 05 00 00 	mov    %rax,0x544(%rdx)
    34b4:	74 3c                	je     34f2 <main+0xe82>
    34b6:	48 c7 44 24 68 08 00 00 00 	movq   $0x8,0x68(%rsp)
    34bf:	44 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%r15d
    34c7:	e9 14 f6 ff ff       	jmp    2ae0 <main+0x470>
    34cc:	48 8d 05 6d 3c 00 00 	lea    0x3c6d(%rip),%rax        # 7140 <barriered_work_ingest_andwork>
    34d3:	bd 01 00 00 00       	mov    $0x1,%ebp
    34d8:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
    34df:	e9 8f f8 ff ff       	jmp    2d73 <main+0x703>
    34e4:	48 8d 05 85 36 00 00 	lea    0x3685(%rip),%rax        # 6b70 <barriered_work>
    34eb:	bd 02 00 00 00       	mov    $0x2,%ebp
    34f0:	eb e6                	jmp    34d8 <main+0xe68>
    34f2:	4d 89 f7             	mov    %r14,%r15
    34f5:	48 8b ac 24 e8 00 00 00 	mov    0xe8(%rsp),%rbp
    34fd:	48 83 84 24 98 00 00 00 18 	addq   $0x18,0x98(%rsp)
    3506:	49 83 c7 01          	add    $0x1,%r15
    350a:	4c 8b b4 24 f8 00 00 00 	mov    0xf8(%rsp),%r14
    3512:	49 83 ff 03          	cmp    $0x3,%r15
    3516:	0f 85 06 f5 ff ff    	jne    2a22 <main+0x3b2>
    351c:	be 08 00 00 00       	mov    $0x8,%esi
    3521:	bf 00 04 00 00       	mov    $0x400,%edi
    3526:	31 ed                	xor    %ebp,%ebp
    3528:	e8 d3 ee ff ff       	call   2400 <calloc@plt>
    352d:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3532:	49 89 c7             	mov    %rax,%r15
    3535:	31 c0                	xor    %eax,%eax
    3537:	49 89 d1             	mov    %rdx,%r9
    353a:	31 db                	xor    %ebx,%ebx
    353c:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3540:	45 85 d2             	test   %r10d,%r10d
    3543:	0f 8e a8 00 00 00    	jle    35f1 <main+0xf81>
    3549:	49 8b 79 38          	mov    0x38(%r9),%rdi
    354d:	4d 63 c2             	movslq %r10d,%r8
    3550:	48 63 cd             	movslq %ebp,%rcx
    3553:	49 c1 e0 09          	shl    $0x9,%r8
    3557:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    355b:	49 01 f8             	add    %rdi,%r8
    355e:	66 90                	xchg   %ax,%ax
    3560:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
    3567:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    356e:	48 83 c6 60          	add    $0x60,%rsi
    3572:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
    357a:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    357e:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    3586:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    358e:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    3596:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
    359d:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
    35a5:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    35ac:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
    35b3:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
    35ba:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    35be:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
    35c5:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
    35cc:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    35d0:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    35d4:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    35d8:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    35dc:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    35e0:	49 39 f8             	cmp    %rdi,%r8
    35e3:	0f 85 77 ff ff ff    	jne    3560 <main+0xef0>
    35e9:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    35ed:	8d 6c 8d 00          	lea    0x0(%rbp,%rcx,4),%ebp
    35f1:	49 81 c1 f8 00 00 00 	add    $0xf8,%r9
    35f8:	85 db                	test   %ebx,%ebx
    35fa:	75 3a                	jne    3636 <main+0xfc6>
    35fc:	bb 01 00 00 00       	mov    $0x1,%ebx
    3601:	e9 36 ff ff ff       	jmp    353c <main+0xecc>
    3606:	41 8d 57 01          	lea    0x1(%r15),%edx
    360a:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    360f:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    3614:	45 31 c0             	xor    %r8d,%r8d
    3617:	48 89 d0             	mov    %rdx,%rax
    361a:	89 94 24 80 00 00 00 	mov    %edx,0x80(%rsp)
    3621:	89 d1                	mov    %edx,%ecx
    3623:	48 c1 e0 05          	shl    $0x5,%rax
    3627:	48 29 d0             	sub    %rdx,%rax
    362a:	4c 89 ca             	mov    %r9,%rdx
    362d:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3631:	e9 7e f5 ff ff       	jmp    2bb4 <main+0x544>
    3636:	83 c0 02             	add    $0x2,%eax
    3639:	48 81 c2 f0 01 00 00 	add    $0x1f0,%rdx
    3640:	83 f8 06             	cmp    $0x6,%eax
    3643:	0f 85 ee fe ff ff    	jne    3537 <main+0xec7>
    3649:	48 8d 3d b7 4d 00 00 	lea    0x4db7(%rip),%rdi        # 8407 <_IO_stdin_used+0x407>
    3650:	e8 db ec ff ff       	call   2330 <puts@plt>
    3655:	48 8d 35 c0 4d 00 00 	lea    0x4dc0(%rip),%rsi        # 841c <_IO_stdin_used+0x41c>
    365c:	48 8d 3d bb 4d 00 00 	lea    0x4dbb(%rip),%rdi        # 841e <_IO_stdin_used+0x41e>
    3663:	e8 88 ee ff ff       	call   24f0 <fopen@plt>
    3668:	49 89 c6             	mov    %rax,%r14
    366b:	85 ed                	test   %ebp,%ebp
    366d:	7e 76                	jle    36e5 <main+0x1075>
    366f:	48 63 ed             	movslq %ebp,%rbp
    3672:	4c 8d 2d 82 4d 00 00 	lea    0x4d82(%rip),%r13        # 83fb <_IO_stdin_used+0x3fb>
    3679:	4c 8d 25 bf 4d 00 00 	lea    0x4dbf(%rip),%r12        # 843f <_IO_stdin_used+0x43f>
    3680:	49 8d 04 ef          	lea    (%r15,%rbp,8),%rax
    3684:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3689:	be 01 00 00 00       	mov    $0x1,%esi
    368e:	bf fa 00 00 00       	mov    $0xfa,%edi
    3693:	49 83 c7 08          	add    $0x8,%r15
    3697:	e8 64 ed ff ff       	call   2400 <calloc@plt>
    369c:	4c 89 e9             	mov    %r13,%rcx
    369f:	ba fa 00 00 00       	mov    $0xfa,%edx
    36a4:	be 01 00 00 00       	mov    $0x1,%esi
    36a9:	48 89 c5             	mov    %rax,%rbp
    36ac:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    36b0:	48 89 ef             	mov    %rbp,%rdi
    36b3:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    36ba:	31 c0                	xor    %eax,%eax
    36bc:	e8 df ee ff ff       	call   25a0 <__sprintf_chk@plt>
    36c1:	48 89 ea             	mov    %rbp,%rdx
    36c4:	4c 89 e6             	mov    %r12,%rsi
    36c7:	bf 01 00 00 00       	mov    $0x1,%edi
    36cc:	31 c0                	xor    %eax,%eax
    36ce:	e8 dd ed ff ff       	call   24b0 <__printf_chk@plt>
    36d3:	4c 89 f6             	mov    %r14,%rsi
    36d6:	48 89 ef             	mov    %rbp,%rdi
    36d9:	e8 e2 ec ff ff       	call   23c0 <fputs@plt>
    36de:	4c 39 7c 24 08       	cmp    %r15,0x8(%rsp)
    36e3:	75 a4                	jne    3689 <main+0x1019>
    36e5:	4c 89 f7             	mov    %r14,%rdi
    36e8:	45 31 f6             	xor    %r14d,%r14d
    36eb:	4c 8d 25 77 4d 00 00 	lea    0x4d77(%rip),%r12        # 8469 <_IO_stdin_used+0x469>
    36f2:	e8 69 ec ff ff       	call   2360 <fclose@plt>
    36f7:	48 8d 3d 29 4d 00 00 	lea    0x4d29(%rip),%rdi        # 8427 <_IO_stdin_used+0x427>
    36fe:	4c 89 f5             	mov    %r14,%rbp
    3701:	e8 2a ec ff ff       	call   2330 <puts@plt>
    3706:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    370a:	48 89 eb             	mov    %rbp,%rbx
    370d:	89 ea                	mov    %ebp,%edx
    370f:	48 8d 35 2c 4d 00 00 	lea    0x4d2c(%rip),%rsi        # 8442 <_IO_stdin_used+0x442>
    3716:	31 c0                	xor    %eax,%eax
    3718:	bf 01 00 00 00       	mov    $0x1,%edi
    371d:	48 c1 e3 05          	shl    $0x5,%rbx
    3721:	44 8d 6c 2d 00       	lea    0x0(%rbp,%rbp,1),%r13d
    3726:	45 31 ff             	xor    %r15d,%r15d
    3729:	e8 82 ed ff ff       	call   24b0 <__printf_chk@plt>
    372e:	48 29 eb             	sub    %rbp,%rbx
    3731:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3736:	48 c1 e3 04          	shl    $0x4,%rbx
    373a:	48 01 c3             	add    %rax,%rbx
    373d:	43 8d 0c 2f          	lea    (%r15,%r13,1),%ecx
    3741:	44 89 fa             	mov    %r15d,%edx
    3744:	48 8d 35 01 4d 00 00 	lea    0x4d01(%rip),%rsi        # 844c <_IO_stdin_used+0x44c>
    374b:	31 c0                	xor    %eax,%eax
    374d:	bf 01 00 00 00       	mov    $0x1,%edi
    3752:	45 31 f6             	xor    %r14d,%r14d
    3755:	e8 56 ed ff ff       	call   24b0 <__printf_chk@plt>
    375a:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
    375f:	4c 89 f1             	mov    %r14,%rcx
    3762:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    3767:	48 89 dd             	mov    %rbx,%rbp
    376a:	89 ca                	mov    %ecx,%edx
    376c:	48 8d 35 eb 4c 00 00 	lea    0x4ceb(%rip),%rsi        # 845e <_IO_stdin_used+0x45e>
    3773:	bf 01 00 00 00       	mov    $0x1,%edi
    3778:	31 c0                	xor    %eax,%eax
    377a:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    377f:	45 31 ed             	xor    %r13d,%r13d
    3782:	e8 29 ed ff ff       	call   24b0 <__printf_chk@plt>
    3787:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    378c:	48 c1 e3 09          	shl    $0x9,%rbx
    3790:	eb 32                	jmp    37c4 <main+0x1154>
    3792:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3798:	83 fe 01             	cmp    $0x1,%esi
    379b:	0f 84 a9 00 00 00    	je     384a <main+0x11da>
    37a1:	44 89 f2             	mov    %r14d,%edx
    37a4:	4c 89 e6             	mov    %r12,%rsi
    37a7:	bf 01 00 00 00       	mov    $0x1,%edi
    37ac:	49 83 c5 01          	add    $0x1,%r13
    37b0:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    37b7:	31 c0                	xor    %eax,%eax
    37b9:	e8 f2 ec ff ff       	call   24b0 <__printf_chk@plt>
    37be:	49 83 fd 06          	cmp    $0x6,%r13
    37c2:	74 50                	je     3814 <main+0x11a4>
    37c4:	be 01 00 00 00       	mov    $0x1,%esi
    37c9:	bf 64 00 00 00       	mov    $0x64,%edi
    37ce:	45 89 ee             	mov    %r13d,%r14d
    37d1:	e8 2a ec ff ff       	call   2400 <calloc@plt>
    37d6:	4c 8b 45 38          	mov    0x38(%rbp),%r8
    37da:	4c 89 ef             	mov    %r13,%rdi
    37dd:	48 89 c1             	mov    %rax,%rcx
    37e0:	48 c1 e7 08          	shl    $0x8,%rdi
    37e4:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    37ec:	48 01 f8             	add    %rdi,%rax
    37ef:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    37f5:	83 fe 02             	cmp    $0x2,%esi
    37f8:	75 9e                	jne    3798 <main+0x1128>
    37fa:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    3804:	48 89 01             	mov    %rax,(%rcx)
    3807:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    380f:	48 01 f8             	add    %rdi,%rax
    3812:	eb 8d                	jmp    37a1 <main+0x1131>
    3814:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    3819:	48 83 c1 01          	add    $0x1,%rcx
    381d:	48 83 f9 03          	cmp    $0x3,%rcx
    3821:	0f 85 43 ff ff ff    	jne    376a <main+0x10fa>
    3827:	48 89 eb             	mov    %rbp,%rbx
    382a:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    382f:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    3834:	48 81 c3 f8 00 00 00 	add    $0xf8,%rbx
    383b:	45 85 ff             	test   %r15d,%r15d
    383e:	75 27                	jne    3867 <main+0x11f7>
    3840:	44 8b 7c 24 10       	mov    0x10(%rsp),%r15d
    3845:	e9 f3 fe ff ff       	jmp    373d <main+0x10cd>
    384a:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3850:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    3857:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    385f:	48 01 f8             	add    %rdi,%rax
    3862:	e9 3a ff ff ff       	jmp    37a1 <main+0x1131>
    3867:	48 83 c5 01          	add    $0x1,%rbp
    386b:	48 83 fd 03          	cmp    $0x3,%rbp
    386f:	0f 85 95 fe ff ff    	jne    370a <main+0x109a>
    3875:	ba 07 00 00 00       	mov    $0x7,%edx
    387a:	48 8d 35 03 4c 00 00 	lea    0x4c03(%rip),%rsi        # 8484 <_IO_stdin_used+0x484>
    3881:	bf 01 00 00 00       	mov    $0x1,%edi
    3886:	31 c0                	xor    %eax,%eax
    3888:	e8 23 ec ff ff       	call   24b0 <__printf_chk@plt>
    388d:	be 08 00 00 00       	mov    $0x8,%esi
    3892:	bf 02 00 00 00       	mov    $0x2,%edi
    3897:	e8 64 eb ff ff       	call   2400 <calloc@plt>
    389c:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    38a1:	be 38 00 00 00       	mov    $0x38,%esi
    38a6:	4c 8d af c8 06 00 00 	lea    0x6c8(%rdi),%r13
    38ad:	48 89 78 08          	mov    %rdi,0x8(%rax)
    38b1:	4c 8d a7 f8 00 00 00 	lea    0xf8(%rdi),%r12
    38b8:	48 89 87 e0 06 00 00 	mov    %rax,0x6e0(%rdi)
    38bf:	4c 89 28             	mov    %r13,(%rax)
    38c2:	48 8b 47 38          	mov    0x38(%rdi),%rax
    38c6:	c7 87 f0 06 00 00 02 00 00 00 	movl   $0x2,0x6f0(%rdi)
    38d0:	c7 87 cc 06 00 00 00 00 00 00 	movl   $0x0,0x6cc(%rdi)
    38da:	c7 87 08 07 00 00 03 00 00 00 	movl   $0x3,0x708(%rdi)
    38e4:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    38ee:	48 8b 87 30 01 00 00 	mov    0x130(%rdi),%rax
    38f5:	bf 0a 00 00 00       	mov    $0xa,%edi
    38fa:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3904:	e8 f7 ea ff ff       	call   2400 <calloc@plt>
    3909:	be 38 00 00 00       	mov    $0x38,%esi
    390e:	bf 0a 00 00 00       	mov    $0xa,%edi
    3913:	49 89 c6             	mov    %rax,%r14
    3916:	e8 e5 ea ff ff       	call   2400 <calloc@plt>
    391b:	be 38 00 00 00       	mov    $0x38,%esi
    3920:	bf 0a 00 00 00       	mov    $0xa,%edi
    3925:	48 89 c5             	mov    %rax,%rbp
    3928:	e8 d3 ea ff ff       	call   2400 <calloc@plt>
    392d:	be 38 00 00 00       	mov    $0x38,%esi
    3932:	bf 0a 00 00 00       	mov    $0xa,%edi
    3937:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    393c:	e8 bf ea ff ff       	call   2400 <calloc@plt>
    3941:	be 08 00 00 00       	mov    $0x8,%esi
    3946:	bf 0a 00 00 00       	mov    $0xa,%edi
    394b:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3950:	e8 ab ea ff ff       	call   2400 <calloc@plt>
    3955:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    395a:	be 08 00 00 00       	mov    $0x8,%esi
    395f:	48 89 c3             	mov    %rax,%rbx
    3962:	48 8b 05 af 53 00 00 	mov    0x53af(%rip),%rax        # 8d18 <_IO_stdin_used+0xd18>
    3969:	c7 87 dc 05 00 00 00 00 00 00 	movl   $0x0,0x5dc(%rdi)
    3973:	48 89 87 10 06 00 00 	mov    %rax,0x610(%rdi)
    397a:	bf 0a 00 00 00       	mov    $0xa,%edi
    397f:	e8 7c ea ff ff       	call   2400 <calloc@plt>
    3984:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3989:	4c 89 60 08          	mov    %r12,0x8(%rax)
    398d:	48 8d 97 f0 01 00 00 	lea    0x1f0(%rdi),%rdx
    3994:	48 8d 8f d0 05 00 00 	lea    0x5d0(%rdi),%rcx
    399b:	48 89 38             	mov    %rdi,(%rax)
    399e:	48 89 50 10          	mov    %rdx,0x10(%rax)
    39a2:	48 8d 97 e8 02 00 00 	lea    0x2e8(%rdi),%rdx
    39a9:	48 8d b7 c0 07 00 00 	lea    0x7c0(%rdi),%rsi
    39b0:	48 89 50 18          	mov    %rdx,0x18(%rax)
    39b4:	48 8d 97 e0 03 00 00 	lea    0x3e0(%rdi),%rdx
    39bb:	48 89 50 20          	mov    %rdx,0x20(%rax)
    39bf:	48 8d 97 d8 04 00 00 	lea    0x4d8(%rdi),%rdx
    39c6:	48 89 50 28          	mov    %rdx,0x28(%rax)
    39ca:	48 8d 97 b8 08 00 00 	lea    0x8b8(%rdi),%rdx
    39d1:	48 89 48 30          	mov    %rcx,0x30(%rax)
    39d5:	48 89 70 40          	mov    %rsi,0x40(%rax)
    39d9:	48 89 50 48          	mov    %rdx,0x48(%rax)
    39dd:	ba 06 00 00 00       	mov    $0x6,%edx
    39e2:	48 89 87 e8 05 00 00 	mov    %rax,0x5e8(%rdi)
    39e9:	4c 89 68 38          	mov    %r13,0x38(%rax)
    39ed:	48 8b 05 2c 53 00 00 	mov    0x532c(%rip),%rax        # 8d20 <_IO_stdin_used+0xd20>
    39f4:	c7 87 00 06 00 00 06 00 00 00 	movl   $0x6,0x600(%rdi)
    39fe:	48 89 87 f8 05 00 00 	mov    %rax,0x5f8(%rdi)
    3a05:	31 c0                	xor    %eax,%eax
    3a07:	c7 87 d4 05 00 00 00 00 00 00 	movl   $0x0,0x5d4(%rdi)
    3a11:	bf 01 00 00 00       	mov    $0x1,%edi
    3a16:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    3a1b:	48 8d 35 71 4a 00 00 	lea    0x4a71(%rip),%rsi        # 8493 <_IO_stdin_used+0x493>
    3a22:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    3a27:	e8 84 ea ff ff       	call   24b0 <__printf_chk@plt>
    3a2c:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    3a31:	48 8d 15 a8 0d 00 00 	lea    0xda8(%rip),%rdx        # 47e0 <timer_thread>
    3a38:	48 8d b5 50 01 00 00 	lea    0x150(%rbp),%rsi
    3a3f:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    3a43:	e8 88 ea ff ff       	call   24d0 <pthread_create@plt>
    3a48:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    3a4d:	4c 89 f0             	mov    %r14,%rax
    3a50:	48 89 d9             	mov    %rbx,%rcx
    3a53:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    3a58:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3a5e:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3a63:	45 31 f6             	xor    %r14d,%r14d
    3a66:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
    3a6b:	44 89 7c 24 20       	mov    %r15d,0x20(%rsp)
    3a70:	45 89 d7             	mov    %r10d,%r15d
    3a73:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3a78:	47 8d 24 36          	lea    (%r14,%r14,1),%r12d
    3a7c:	49 89 c5             	mov    %rax,%r13
    3a7f:	48 89 cb             	mov    %rcx,%rbx
    3a82:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    3a87:	48 89 d5             	mov    %rdx,%rbp
    3a8a:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
    3a8f:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    3a96:	44 89 e2             	mov    %r12d,%edx
    3a99:	44 89 f1             	mov    %r14d,%ecx
    3a9c:	31 c0                	xor    %eax,%eax
    3a9e:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    3aa5:	48 8d 35 6c 4d 00 00 	lea    0x4d6c(%rip),%rsi        # 8818 <_IO_stdin_used+0x818>
    3aac:	bf 01 00 00 00       	mov    $0x1,%edi
    3ab1:	41 83 c4 01          	add    $0x1,%r12d
    3ab5:	e8 f6 e9 ff ff       	call   24b0 <__printf_chk@plt>
    3aba:	48 89 e9             	mov    %rbp,%rcx
    3abd:	4c 89 ee             	mov    %r13,%rsi
    3ac0:	48 89 df             	mov    %rbx,%rdi
    3ac3:	48 8d 15 96 28 00 00 	lea    0x2896(%rip),%rdx        # 6360 <barriered_thread>
    3aca:	48 81 c5 f8 00 00 00 	add    $0xf8,%rbp
    3ad1:	48 83 c3 08          	add    $0x8,%rbx
    3ad5:	49 83 c5 38          	add    $0x38,%r13
    3ad9:	e8 f2 e9 ff ff       	call   24d0 <pthread_create@plt>
    3ade:	48 8b 55 b8          	mov    -0x48(%rbp),%rdx
    3ae2:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    3ae6:	be 08 00 00 00       	mov    $0x8,%esi
    3aeb:	e8 30 e8 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    3af0:	45 39 e7             	cmp    %r12d,%r15d
    3af3:	75 9a                	jne    3a8f <main+0x141f>
    3af5:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3afa:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    3aff:	41 83 c6 01          	add    $0x1,%r14d
    3b03:	41 83 c7 02          	add    $0x2,%r15d
    3b07:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    3b0c:	48 83 c1 10          	add    $0x10,%rcx
    3b10:	48 83 c0 70          	add    $0x70,%rax
    3b14:	48 81 c2 f0 01 00 00 	add    $0x1f0,%rdx
    3b1b:	41 83 fe 03          	cmp    $0x3,%r14d
    3b1f:	0f 85 4e ff ff ff    	jne    3a73 <main+0x1403>
    3b25:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3b2a:	be d8 00 00 00       	mov    $0xd8,%esi
    3b2f:	bf 01 00 00 00       	mov    $0x1,%edi
    3b34:	48 8b 05 ed 51 00 00 	mov    0x51ed(%rip),%rax        # 8d28 <_IO_stdin_used+0xd28>
    3b3b:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    3b40:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    3b45:	41 c7 86 d4 06 00 00 02 00 00 00 	movl   $0x2,0x6d4(%r14)
    3b50:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    3b55:	49 89 86 08 07 00 00 	mov    %rax,0x708(%r14)
    3b5c:	44 8b 7c 24 20       	mov    0x20(%rsp),%r15d
    3b61:	48 8d 6b 40          	lea    0x40(%rbx),%rbp
    3b65:	e8 96 e8 ff ff       	call   2400 <calloc@plt>
    3b6a:	be 00 08 00 00       	mov    $0x800,%esi
    3b6f:	31 ff                	xor    %edi,%edi
    3b71:	49 89 86 20 07 00 00 	mov    %rax,0x720(%r14)
    3b78:	e8 a3 e9 ff ff       	call   2520 <eventfd@plt>
    3b7d:	be 08 00 00 00       	mov    $0x8,%esi
    3b82:	bf 02 00 00 00       	mov    $0x2,%edi
    3b87:	41 89 86 28 07 00 00 	mov    %eax,0x728(%r14)
    3b8e:	e8 6d e8 ff ff       	call   2400 <calloc@plt>
    3b93:	ba 07 00 00 00       	mov    $0x7,%edx
    3b98:	bf 01 00 00 00       	mov    $0x1,%edi
    3b9d:	41 c7 86 f0 06 00 00 02 00 00 00 	movl   $0x2,0x6f0(%r14)
    3ba8:	4c 89 30             	mov    %r14,(%rax)
    3bab:	48 8d 35 ff 48 00 00 	lea    0x48ff(%rip),%rsi        # 84b1 <_IO_stdin_used+0x4b1>
    3bb2:	49 89 86 e0 06 00 00 	mov    %rax,0x6e0(%r14)
    3bb9:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3bbd:	31 c0                	xor    %eax,%eax
    3bbf:	41 c7 86 cc 06 00 00 07 00 00 00 	movl   $0x7,0x6cc(%r14)
    3bca:	41 be 08 00 00 00    	mov    $0x8,%r14d
    3bd0:	e8 db e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bd5:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3bda:	4c 89 e9             	mov    %r13,%rcx
    3bdd:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3be1:	48 8d 15 88 1f 00 00 	lea    0x1f88(%rip),%rdx        # 5b70 <io_thread>
    3be8:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3bef:	e8 dc e8 ff ff       	call   24d0 <pthread_create@plt>
    3bf4:	ba 08 00 00 00       	mov    $0x8,%edx
    3bf9:	48 8d 35 c8 48 00 00 	lea    0x48c8(%rip),%rsi        # 84c8 <_IO_stdin_used+0x4c8>
    3c00:	31 c0                	xor    %eax,%eax
    3c02:	bf 01 00 00 00       	mov    $0x1,%edi
    3c07:	e8 a4 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c0c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3c11:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    3c16:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    3c1c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3c21:	44 89 f2             	mov    %r14d,%edx
    3c24:	48 8d 35 b3 48 00 00 	lea    0x48b3(%rip),%rsi        # 84de <_IO_stdin_used+0x4de>
    3c2b:	bf 01 00 00 00       	mov    $0x1,%edi
    3c30:	31 c0                	xor    %eax,%eax
    3c32:	e8 79 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3c37:	be 08 00 00 00       	mov    $0x8,%esi
    3c3c:	bf 01 00 00 00       	mov    $0x1,%edi
    3c41:	48 8b 05 e0 50 00 00 	mov    0x50e0(%rip),%rax        # 8d28 <_IO_stdin_used+0xd28>
    3c48:	41 c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%r13)
    3c50:	49 89 45 40          	mov    %rax,0x40(%r13)
    3c54:	e8 a7 e7 ff ff       	call   2400 <calloc@plt>
    3c59:	48 8b bc 24 c0 00 00 00 	mov    0xc0(%rsp),%rdi
    3c61:	be 08 00 00 00       	mov    $0x8,%esi
    3c66:	41 c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r13)
    3c71:	49 89 45 50          	mov    %rax,0x50(%r13)
    3c75:	48 89 38             	mov    %rdi,(%rax)
    3c78:	bf 02 00 00 00       	mov    $0x2,%edi
    3c7d:	e8 7e e7 ff ff       	call   2400 <calloc@plt>
    3c82:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    3c87:	4c 89 e9             	mov    %r13,%rcx
    3c8a:	48 89 ef             	mov    %rbp,%rdi
    3c8d:	49 89 45 18          	mov    %rax,0x18(%r13)
    3c91:	48 8d 15 38 0a 00 00 	lea    0xa38(%rip),%rdx        # 46d0 <external_thread>
    3c98:	48 83 c5 08          	add    $0x8,%rbp
    3c9c:	49 81 c5 f8 00 00 00 	add    $0xf8,%r13
    3ca3:	48 89 30             	mov    %rsi,(%rax)
    3ca6:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3cab:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3caf:	48 8b 05 5a 50 00 00 	mov    0x505a(%rip),%rax        # 8d10 <_IO_stdin_used+0xd10>
    3cb6:	45 89 b5 0c ff ff ff 	mov    %r14d,-0xf4(%r13)
    3cbd:	49 89 85 30 ff ff ff 	mov    %rax,-0xd0(%r13)
    3cc4:	e8 07 e8 ff ff       	call   24d0 <pthread_create@plt>
    3cc9:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3ccf:	48 83 84 24 c0 00 00 00 10 	addq   $0x10,0xc0(%rsp)
    3cd8:	41 83 fe 08          	cmp    $0x8,%r14d
    3cdc:	75 17                	jne    3cf5 <main+0x1685>
    3cde:	41 be 09 00 00 00    	mov    $0x9,%r14d
    3ce4:	e9 38 ff ff ff       	jmp    3c21 <main+0x15b1>
    3ce9:	48 81 0b ff 0f 00 00 	orq    $0xfff,(%rbx)
    3cf0:	e9 5b ef ff ff       	jmp    2c50 <main+0x5e0>
    3cf5:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3cfa:	48 8d 2d fa 47 00 00 	lea    0x47fa(%rip),%rbp        # 84fb <_IO_stdin_used+0x4fb>
    3d01:	4c 8d 68 04          	lea    0x4(%rax),%r13
    3d05:	4c 8d a0 b4 09 00 00 	lea    0x9b4(%rax),%r12
    3d0c:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    3d10:	41 8b 55 00          	mov    0x0(%r13),%edx
    3d14:	48 89 ee             	mov    %rbp,%rsi
    3d17:	bf 01 00 00 00       	mov    $0x1,%edi
    3d1c:	31 c0                	xor    %eax,%eax
    3d1e:	49 81 c5 f8 00 00 00 	add    $0xf8,%r13
    3d25:	e8 86 e7 ff ff       	call   24b0 <__printf_chk@plt>
    3d2a:	4d 39 ec             	cmp    %r13,%r12
    3d2d:	75 dd                	jne    3d0c <main+0x169c>
    3d2f:	48 8d 3d d8 47 00 00 	lea    0x47d8(%rip),%rdi        # 850e <_IO_stdin_used+0x50e>
    3d36:	45 31 ed             	xor    %r13d,%r13d
    3d39:	4c 8d a4 24 00 01 00 00 	lea    0x100(%rsp),%r12
    3d41:	e8 ea e5 ff ff       	call   2330 <puts@plt>
    3d46:	48 8d 2d df 47 00 00 	lea    0x47df(%rip),%rbp        # 852c <_IO_stdin_used+0x52c>
    3d4d:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    3d51:	4c 89 e6             	mov    %r12,%rsi
    3d54:	e8 07 e8 ff ff       	call   2560 <pthread_join@plt>
    3d59:	44 89 ea             	mov    %r13d,%edx
    3d5c:	48 89 ee             	mov    %rbp,%rsi
    3d5f:	bf 01 00 00 00       	mov    $0x1,%edi
    3d64:	31 c0                	xor    %eax,%eax
    3d66:	49 83 c5 01          	add    $0x1,%r13
    3d6a:	e8 41 e7 ff ff       	call   24b0 <__printf_chk@plt>
    3d6f:	49 83 fd 0a          	cmp    $0xa,%r13
    3d73:	75 d8                	jne    3d4d <main+0x16dd>
    3d75:	be 08 00 00 00       	mov    $0x8,%esi
    3d7a:	bf 00 04 00 00       	mov    $0x400,%edi
    3d7f:	31 db                	xor    %ebx,%ebx
    3d81:	e8 7a e6 ff ff       	call   2400 <calloc@plt>
    3d86:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3d8b:	48 89 c5             	mov    %rax,%rbp
    3d8e:	31 c0                	xor    %eax,%eax
    3d90:	49 89 d1             	mov    %rdx,%r9
    3d93:	45 31 db             	xor    %r11d,%r11d
    3d96:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3d9a:	45 85 d2             	test   %r10d,%r10d
    3d9d:	0f 8e ad 00 00 00    	jle    3e50 <main+0x17e0>
    3da3:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3da7:	4d 63 c2             	movslq %r10d,%r8
    3daa:	48 63 cb             	movslq %ebx,%rcx
    3dad:	49 c1 e0 09          	shl    $0x9,%r8
    3db1:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    3db6:	49 01 f8             	add    %rdi,%r8
    3db9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3dc0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
    3dc7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3dce:	48 83 c6 60          	add    $0x60,%rsi
    3dd2:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
    3dda:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3dde:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    3de6:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    3dee:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    3df6:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
    3dfd:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
    3e05:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    3e0c:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
    3e13:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
    3e1a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3e1e:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
    3e25:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
    3e2c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3e30:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3e34:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3e38:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3e3c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
    3e40:	4c 39 c7             	cmp    %r8,%rdi
    3e43:	0f 85 77 ff ff ff    	jne    3dc0 <main+0x1750>
    3e49:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3e4d:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    3e50:	49 81 c1 f8 00 00 00 	add    $0xf8,%r9
    3e57:	45 85 db             	test   %r11d,%r11d
    3e5a:	75 08                	jne    3e64 <main+0x17f4>
    3e5c:	45 89 fb             	mov    %r15d,%r11d
    3e5f:	e9 32 ff ff ff       	jmp    3d96 <main+0x1726>
    3e64:	83 c0 02             	add    $0x2,%eax
    3e67:	48 81 c2 f0 01 00 00 	add    $0x1f0,%rdx
    3e6e:	83 f8 06             	cmp    $0x6,%eax
    3e71:	0f 85 19 ff ff ff    	jne    3d90 <main+0x1720>
    3e77:	48 8d 3d c2 46 00 00 	lea    0x46c2(%rip),%rdi        # 8540 <_IO_stdin_used+0x540>
    3e7e:	e8 ad e4 ff ff       	call   2330 <puts@plt>
    3e83:	48 8d 35 92 45 00 00 	lea    0x4592(%rip),%rsi        # 841c <_IO_stdin_used+0x41c>
    3e8a:	48 8d 3d c7 46 00 00 	lea    0x46c7(%rip),%rdi        # 8558 <_IO_stdin_used+0x558>
    3e91:	e8 5a e6 ff ff       	call   24f0 <fopen@plt>
    3e96:	49 89 c6             	mov    %rax,%r14
    3e99:	85 db                	test   %ebx,%ebx
    3e9b:	7e 73                	jle    3f10 <main+0x18a0>
    3e9d:	48 63 db             	movslq %ebx,%rbx
    3ea0:	49 89 ef             	mov    %rbp,%r15
    3ea3:	4c 8d 2d 51 45 00 00 	lea    0x4551(%rip),%r13        # 83fb <_IO_stdin_used+0x3fb>
    3eaa:	48 8d 6c dd 00       	lea    0x0(%rbp,%rbx,8),%rbp
    3eaf:	4c 8d 25 89 45 00 00 	lea    0x4589(%rip),%r12        # 843f <_IO_stdin_used+0x43f>
    3eb6:	be 01 00 00 00       	mov    $0x1,%esi
    3ebb:	bf fa 00 00 00       	mov    $0xfa,%edi
    3ec0:	49 83 c7 08          	add    $0x8,%r15
    3ec4:	e8 37 e5 ff ff       	call   2400 <calloc@plt>
    3ec9:	4c 89 e9             	mov    %r13,%rcx
    3ecc:	ba fa 00 00 00       	mov    $0xfa,%edx
    3ed1:	be 01 00 00 00       	mov    $0x1,%esi
    3ed6:	48 89 c3             	mov    %rax,%rbx
    3ed9:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3edd:	48 89 df             	mov    %rbx,%rdi
    3ee0:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3ee7:	31 c0                	xor    %eax,%eax
    3ee9:	e8 b2 e6 ff ff       	call   25a0 <__sprintf_chk@plt>
    3eee:	48 89 da             	mov    %rbx,%rdx
    3ef1:	4c 89 e6             	mov    %r12,%rsi
    3ef4:	bf 01 00 00 00       	mov    $0x1,%edi
    3ef9:	31 c0                	xor    %eax,%eax
    3efb:	e8 b0 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3f00:	4c 89 f6             	mov    %r14,%rsi
    3f03:	48 89 df             	mov    %rbx,%rdi
    3f06:	e8 b5 e4 ff ff       	call   23c0 <fputs@plt>
    3f0b:	49 39 ef             	cmp    %rbp,%r15
    3f0e:	75 a6                	jne    3eb6 <main+0x1846>
    3f10:	4c 89 f7             	mov    %r14,%rdi
    3f13:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
    3f19:	31 db                	xor    %ebx,%ebx
    3f1b:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
    3f25:	e8 36 e4 ff ff       	call   2360 <fclose@plt>
    3f2a:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
    3f33:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    3f3c:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3f45:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
    3f4e:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
    3f56:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    3f5b:	4c 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%r14
    3f63:	45 89 e5             	mov    %r12d,%r13d
    3f66:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    3f6b:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3f70:	44 89 e8             	mov    %r13d,%eax
    3f73:	41 83 c5 01          	add    $0x1,%r13d
    3f77:	bf 0a 00 00 00       	mov    $0xa,%edi
    3f7c:	41 f6 c5 01          	test   $0x1,%r13b
    3f80:	8d 50 02             	lea    0x2(%rax),%edx
    3f83:	0f 44 c2             	cmove  %edx,%eax
    3f86:	4c 63 e0             	movslq %eax,%r12
    3f89:	e8 82 e3 ff ff       	call   2310 <putchar@plt>
    3f8e:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3f93:	bf 01 00 00 00       	mov    $0x1,%edi
    3f98:	48 8d 35 c2 45 00 00 	lea    0x45c2(%rip),%rsi        # 8561 <_IO_stdin_used+0x561>
    3f9f:	48 8b 10             	mov    (%rax),%rdx
    3fa2:	31 c0                	xor    %eax,%eax
    3fa4:	e8 07 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3fa9:	41 8b 56 40          	mov    0x40(%r14),%edx
    3fad:	85 d2                	test   %edx,%edx
    3faf:	0f 8e 30 05 00 00    	jle    44e5 <main+0x1e75>
    3fb5:	48 63 ca             	movslq %edx,%rcx
    3fb8:	49 8b 46 38          	mov    0x38(%r14),%rax
    3fbc:	31 d2                	xor    %edx,%edx
    3fbe:	48 c1 e1 09          	shl    $0x9,%rcx
    3fc2:	48 01 c1             	add    %rax,%rcx
    3fc5:	0f 1f 00             	nopl   (%rax)
    3fc8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3fcf:	48 05 00 02 00 00    	add    $0x200,%rax
    3fd5:	48 39 c8             	cmp    %rcx,%rax
    3fd8:	75 ee                	jne    3fc8 <main+0x1958>
    3fda:	4c 89 e0             	mov    %r12,%rax
    3fdd:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3fe2:	48 c1 e0 05          	shl    $0x5,%rax
    3fe6:	4c 29 e0             	sub    %r12,%rax
    3fe9:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3fed:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3ff1:	85 c9                	test   %ecx,%ecx
    3ff3:	7e 1d                	jle    4012 <main+0x19a2>
    3ff5:	48 8b 40 38          	mov    0x38(%rax),%rax
    3ff9:	48 c1 e1 09          	shl    $0x9,%rcx
    3ffd:	48 01 c1             	add    %rax,%rcx
    4000:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    4007:	48 05 00 02 00 00    	add    $0x200,%rax
    400d:	48 39 c8             	cmp    %rcx,%rax
    4010:	75 ee                	jne    4000 <main+0x1990>
    4012:	48 8d 35 5d 45 00 00 	lea    0x455d(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    4019:	bf 01 00 00 00       	mov    $0x1,%edi
    401e:	31 c0                	xor    %eax,%eax
    4020:	e8 8b e4 ff ff       	call   24b0 <__printf_chk@plt>
    4025:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    402a:	bf 01 00 00 00       	mov    $0x1,%edi
    402f:	48 8d 35 12 48 00 00 	lea    0x4812(%rip),%rsi        # 8848 <_IO_stdin_used+0x848>
    4036:	48 8b 08             	mov    (%rax),%rcx
    4039:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    4043:	48 f7 e9             	imul   %rcx
    4046:	48 c1 f9 3f          	sar    $0x3f,%rcx
    404a:	31 c0                	xor    %eax,%eax
    404c:	48 d1 fa             	sar    %rdx
    404f:	48 29 ca             	sub    %rcx,%rdx
    4052:	e8 59 e4 ff ff       	call   24b0 <__printf_chk@plt>
    4057:	bf 0a 00 00 00       	mov    $0xa,%edi
    405c:	e8 af e2 ff ff       	call   2310 <putchar@plt>
    4061:	45 8b 66 40          	mov    0x40(%r14),%r12d
    4065:	45 85 e4             	test   %r12d,%r12d
    4068:	0f 8e 47 01 00 00    	jle    41b5 <main+0x1b45>
    406e:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    4073:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    4078:	31 d2                	xor    %edx,%edx
    407a:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    407f:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    4084:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    4089:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4090:	49 8b 46 38          	mov    0x38(%r14),%rax
    4094:	49 89 d1             	mov    %rdx,%r9
    4097:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    409c:	41 89 d5             	mov    %edx,%r13d
    409f:	49 c1 e1 09          	shl    $0x9,%r9
    40a3:	45 31 e4             	xor    %r12d,%r12d
    40a6:	4c 01 c8             	add    %r9,%rax
    40a9:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    40ae:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
    40b5:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
    40bc:	48 03 b8 80 01 00 00 	add    0x180(%rax),%rdi
    40c3:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    40c8:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    40cd:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    40d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    40d8:	8b 54 24 08          	mov    0x8(%rsp),%edx
    40dc:	45 89 e0             	mov    %r12d,%r8d
    40df:	44 89 e9             	mov    %r13d,%ecx
    40e2:	bf 01 00 00 00       	mov    $0x1,%edi
    40e7:	48 8d 35 95 44 00 00 	lea    0x4495(%rip),%rsi        # 8583 <_IO_stdin_used+0x583>
    40ee:	31 c0                	xor    %eax,%eax
    40f0:	e8 bb e3 ff ff       	call   24b0 <__printf_chk@plt>
    40f5:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    40fa:	4c 89 e0             	mov    %r12,%rax
    40fd:	45 89 e0             	mov    %r12d,%r8d
    4100:	49 8b 56 38          	mov    0x38(%r14),%rdx
    4104:	48 c1 e0 08          	shl    $0x8,%rax
    4108:	48 83 ec 08          	sub    $0x8,%rsp
    410c:	49 83 c4 01          	add    $0x1,%r12
    4110:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    4118:	48 8b 38             	mov    (%rax),%rdi
    411b:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    4122:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
    4129:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
    4130:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
    4137:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    413e:	bf 01 00 00 00       	mov    $0x1,%edi
    4143:	48 01 c3             	add    %rax,%rbx
    4146:	48 01 f0             	add    %rsi,%rax
    4149:	49 01 cf             	add    %rcx,%r15
    414c:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
    4150:	48 01 f3             	add    %rsi,%rbx
    4153:	50                   	push   %rax
    4154:	49 01 d7             	add    %rdx,%r15
    4157:	8b 54 24 18          	mov    0x18(%rsp),%edx
    415b:	44 89 e9             	mov    %r13d,%ecx
    415e:	48 8d 35 03 47 00 00 	lea    0x4703(%rip),%rsi        # 8868 <_IO_stdin_used+0x868>
    4165:	31 c0                	xor    %eax,%eax
    4167:	e8 44 e3 ff ff       	call   24b0 <__printf_chk@plt>
    416c:	41 5a                	pop    %r10
    416e:	41 5b                	pop    %r11
    4170:	49 83 fc 06          	cmp    $0x6,%r12
    4174:	0f 85 5e ff ff ff    	jne    40d8 <main+0x1a68>
    417a:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    417f:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    4184:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    4189:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    418e:	48 83 c2 01          	add    $0x1,%rdx
    4192:	41 39 56 40          	cmp    %edx,0x40(%r14)
    4196:	0f 8f f4 fe ff ff    	jg     4090 <main+0x1a20>
    419c:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    41a1:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    41a6:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    41ab:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    41b0:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    41b5:	45 31 ff             	xor    %r15d,%r15d
    41b8:	49 83 be a0 00 00 00 00 	cmpq   $0x0,0xa0(%r14)
    41c0:	4c 8d 25 c1 46 00 00 	lea    0x46c1(%rip),%r12        # 8888 <_IO_stdin_used+0x888>
    41c7:	7e 5f                	jle    4228 <main+0x1bb8>
    41c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    41d0:	49 8b 86 90 00 00 00 	mov    0x90(%r14),%rax
    41d7:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    41db:	48 83 ec 08          	sub    $0x8,%rsp
    41df:	bf 01 00 00 00       	mov    $0x1,%edi
    41e4:	49 83 c7 01          	add    $0x1,%r15
    41e8:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
    41ec:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    41f0:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    41f4:	48 89 f0             	mov    %rsi,%rax
    41f7:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    41fb:	4c 2b 01             	sub    (%rcx),%r8
    41fe:	48 f7 e5             	mul    %rbp
    4201:	8b 49 20             	mov    0x20(%rcx),%ecx
    4204:	56                   	push   %rsi
    4205:	31 c0                	xor    %eax,%eax
    4207:	4c 89 e6             	mov    %r12,%rsi
    420a:	48 c1 ea 12          	shr    $0x12,%rdx
    420e:	49 89 d1             	mov    %rdx,%r9
    4211:	ba 02 00 00 00       	mov    $0x2,%edx
    4216:	e8 95 e2 ff ff       	call   24b0 <__printf_chk@plt>
    421b:	41 58                	pop    %r8
    421d:	41 59                	pop    %r9
    421f:	4d 39 be a0 00 00 00 	cmp    %r15,0xa0(%r14)
    4226:	7f a8                	jg     41d0 <main+0x1b60>
    4228:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    422f:	85 d2                	test   %edx,%edx
    4231:	0f 8e 0a 01 00 00    	jle    4341 <main+0x1cd1>
    4237:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
    423c:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4240:	45 31 ff             	xor    %r15d,%r15d
    4243:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    4248:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4250:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    4254:	44 89 fb             	mov    %r15d,%ebx
    4257:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    425f:	8b 30                	mov    (%rax),%esi
    4261:	85 f6                	test   %esi,%esi
    4263:	0f 8e c1 00 00 00    	jle    432a <main+0x1cba>
    4269:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    426e:	31 d2                	xor    %edx,%edx
    4270:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4274:	49 89 f8             	mov    %rdi,%r8
    4277:	48 89 d7             	mov    %rdx,%rdi
    427a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4280:	49 89 fc             	mov    %rdi,%r12
    4283:	45 31 ff             	xor    %r15d,%r15d
    4286:	49 c1 e4 08          	shl    $0x8,%r12
    428a:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    428e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4294:	85 d2                	test   %edx,%edx
    4296:	7e 77                	jle    430f <main+0x1c9f>
    4298:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    429d:	0f 1f 00             	nopl   (%rax)
    42a0:	4c 89 f9             	mov    %r15,%rcx
    42a3:	48 83 ec 08          	sub    $0x8,%rsp
    42a7:	bf 01 00 00 00       	mov    $0x1,%edi
    42ac:	49 83 c7 01          	add    $0x1,%r15
    42b0:	48 c1 e1 05          	shl    $0x5,%rcx
    42b4:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
    42bb:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    42bf:	48 2b 71 08          	sub    0x8(%rcx),%rsi
    42c3:	48 89 f0             	mov    %rsi,%rax
    42c6:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    42ca:	4c 2b 01             	sub    (%rcx),%r8
    42cd:	56                   	push   %rsi
    42ce:	48 f7 e5             	mul    %rbp
    42d1:	89 d9                	mov    %ebx,%ecx
    42d3:	48 8d 35 fe 45 00 00 	lea    0x45fe(%rip),%rsi        # 88d8 <_IO_stdin_used+0x8d8>
    42da:	31 c0                	xor    %eax,%eax
    42dc:	48 c1 ea 12          	shr    $0x12,%rdx
    42e0:	49 89 d1             	mov    %rdx,%r9
    42e3:	ba 02 00 00 00       	mov    $0x2,%edx
    42e8:	e8 c3 e1 ff ff       	call   24b0 <__printf_chk@plt>
    42ed:	4d 8b 46 50          	mov    0x50(%r14),%r8
    42f1:	5e                   	pop    %rsi
    42f2:	5f                   	pop    %rdi
    42f3:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    42f7:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    42fb:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    42ff:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    4306:	7f 98                	jg     42a0 <main+0x1c30>
    4308:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    430d:	8b 32                	mov    (%rdx),%esi
    430f:	48 83 c7 01          	add    $0x1,%rdi
    4313:	39 fe                	cmp    %edi,%esi
    4315:	0f 8f 65 ff ff ff    	jg     4280 <main+0x1c10>
    431b:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    4320:	41 8b 96 bc 00 00 00 	mov    0xbc(%r14),%edx
    4327:	4c 89 c7             	mov    %r8,%rdi
    432a:	49 83 c7 01          	add    $0x1,%r15
    432e:	44 39 fa             	cmp    %r15d,%edx
    4331:	0f 8f 19 ff ff ff    	jg     4250 <main+0x1be0>
    4337:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    433c:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    4341:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    4347:	49 81 c6 f8 00 00 00 	add    $0xf8,%r14
    434e:	44 39 6c 24 48       	cmp    %r13d,0x48(%rsp)
    4353:	0f 85 17 fc ff ff    	jne    3f70 <main+0x1900>
    4359:	48 83 84 24 90 00 00 00 30 	addq   $0x30,0x90(%rsp)
    4362:	44 8b 44 24 48       	mov    0x48(%rsp),%r8d
    4367:	48 81 84 24 c8 00 00 00 f0 01 00 00 	addq   $0x1f0,0xc8(%rsp)
    4373:	41 83 f8 05          	cmp    $0x5,%r8d
    4377:	74 08                	je     4381 <main+0x1d11>
    4379:	45 89 c4             	mov    %r8d,%r12d
    437c:	e9 cd fb ff ff       	jmp    3f4e <main+0x18de>
    4381:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    4386:	bf 01 00 00 00       	mov    $0x1,%edi
    438b:	31 c0                	xor    %eax,%eax
    438d:	49 89 df             	mov    %rbx,%r15
    4390:	48 8d 35 fc 41 00 00 	lea    0x41fc(%rip),%rsi        # 8593 <_IO_stdin_used+0x593>
    4397:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    43a1:	4c 89 f2             	mov    %r14,%rdx
    43a4:	e8 07 e1 ff ff       	call   24b0 <__printf_chk@plt>
    43a9:	bf 0a 00 00 00       	mov    $0xa,%edi
    43ae:	e8 5d df ff ff       	call   2310 <putchar@plt>
    43b3:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
    43bb:	48 8d 35 6e 45 00 00 	lea    0x456e(%rip),%rsi        # 8930 <_IO_stdin_used+0x930>
    43c2:	31 c0                	xor    %eax,%eax
    43c4:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    43c8:	bf 01 00 00 00       	mov    $0x1,%edi
    43cd:	e8 de e0 ff ff       	call   24b0 <__printf_chk@plt>
    43d2:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    43d7:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    43dc:	48 8d 35 75 45 00 00 	lea    0x4575(%rip),%rsi        # 8958 <_IO_stdin_used+0x958>
    43e3:	48 f7 eb             	imul   %rbx
    43e6:	48 c1 ff 3f          	sar    $0x3f,%rdi
    43ea:	31 c0                	xor    %eax,%eax
    43ec:	48 d1 fa             	sar    %rdx
    43ef:	48 29 fa             	sub    %rdi,%rdx
    43f2:	bf 01 00 00 00       	mov    $0x1,%edi
    43f7:	e8 b4 e0 ff ff       	call   24b0 <__printf_chk@plt>
    43fc:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4401:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    4406:	48 8d 35 7b 45 00 00 	lea    0x457b(%rip),%rsi        # 8988 <_IO_stdin_used+0x988>
    440d:	48 f7 eb             	imul   %rbx
    4410:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4414:	31 c0                	xor    %eax,%eax
    4416:	48 d1 fa             	sar    %rdx
    4419:	48 29 fa             	sub    %rdi,%rdx
    441c:	bf 01 00 00 00       	mov    $0x1,%edi
    4421:	e8 8a e0 ff ff       	call   24b0 <__printf_chk@plt>
    4426:	4c 89 f0             	mov    %r14,%rax
    4429:	bf 01 00 00 00       	mov    $0x1,%edi
    442e:	48 8d 35 83 45 00 00 	lea    0x4583(%rip),%rsi        # 89b8 <_IO_stdin_used+0x9b8>
    4435:	48 f7 eb             	imul   %rbx
    4438:	4c 89 f0             	mov    %r14,%rax
    443b:	48 c1 f8 3f          	sar    $0x3f,%rax
    443f:	48 d1 fa             	sar    %rdx
    4442:	48 29 c2             	sub    %rax,%rdx
    4445:	31 c0                	xor    %eax,%eax
    4447:	e8 64 e0 ff ff       	call   24b0 <__printf_chk@plt>
    444c:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4451:	bf 01 00 00 00       	mov    $0x1,%edi
    4456:	48 8d 35 4a 41 00 00 	lea    0x414a(%rip),%rsi        # 85a7 <_IO_stdin_used+0x5a7>
    445d:	48 f7 eb             	imul   %rbx
    4460:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4465:	48 c1 f8 3f          	sar    $0x3f,%rax
    4469:	48 d1 fa             	sar    %rdx
    446c:	48 29 c2             	sub    %rax,%rdx
    446f:	31 c0                	xor    %eax,%eax
    4471:	48 89 d5             	mov    %rdx,%rbp
    4474:	e8 37 e0 ff ff       	call   24b0 <__printf_chk@plt>
    4479:	4c 89 f8             	mov    %r15,%rax
    447c:	bf 01 00 00 00       	mov    $0x1,%edi
    4481:	48 8d 35 50 45 00 00 	lea    0x4550(%rip),%rsi        # 89d8 <_IO_stdin_used+0x9d8>
    4488:	48 f7 eb             	imul   %rbx
    448b:	4c 89 f8             	mov    %r15,%rax
    448e:	48 c1 f8 3f          	sar    $0x3f,%rax
    4492:	48 89 d3             	mov    %rdx,%rbx
    4495:	48 d1 fb             	sar    %rbx
    4498:	48 29 c3             	sub    %rax,%rbx
    449b:	31 c0                	xor    %eax,%eax
    449d:	48 89 da             	mov    %rbx,%rdx
    44a0:	48 29 eb             	sub    %rbp,%rbx
    44a3:	e8 08 e0 ff ff       	call   24b0 <__printf_chk@plt>
    44a8:	31 c0                	xor    %eax,%eax
    44aa:	48 89 da             	mov    %rbx,%rdx
    44ad:	bf 01 00 00 00       	mov    $0x1,%edi
    44b2:	48 8d 35 0a 41 00 00 	lea    0x410a(%rip),%rsi        # 85c3 <_IO_stdin_used+0x5c3>
    44b9:	e8 f2 df ff ff       	call   24b0 <__printf_chk@plt>
    44be:	48 8b 84 24 18 01 00 00 	mov    0x118(%rsp),%rax
    44c6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    44cf:	75 25                	jne    44f6 <main+0x1e86>
    44d1:	48 81 c4 28 01 00 00 	add    $0x128,%rsp
    44d8:	31 c0                	xor    %eax,%eax
    44da:	5b                   	pop    %rbx
    44db:	5d                   	pop    %rbp
    44dc:	41 5c                	pop    %r12
    44de:	41 5d                	pop    %r13
    44e0:	41 5e                	pop    %r14
    44e2:	41 5f                	pop    %r15
    44e4:	c3                   	ret
    44e5:	31 d2                	xor    %edx,%edx
    44e7:	e9 ee fa ff ff       	jmp    3fda <main+0x196a>
    44ec:	bf 01 00 00 00       	mov    $0x1,%edi
    44f1:	e8 1a e0 ff ff       	call   2510 <exit@plt>
    44f6:	e8 85 de ff ff       	call   2380 <__stack_chk_fail@plt>
    44fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004500 <_start>:
    4500:	f3 0f 1e fa          	endbr64
    4504:	31 ed                	xor    %ebp,%ebp
    4506:	49 89 d1             	mov    %rdx,%r9
    4509:	5e                   	pop    %rsi
    450a:	48 89 e2             	mov    %rsp,%rdx
    450d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4511:	50                   	push   %rax
    4512:	54                   	push   %rsp
    4513:	45 31 c0             	xor    %r8d,%r8d
    4516:	31 c9                	xor    %ecx,%ecx
    4518:	48 8d 3d 51 e1 ff ff 	lea    -0x1eaf(%rip),%rdi        # 2670 <main>
    451f:	ff 15 b3 6a 00 00    	call   *0x6ab3(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    4525:	f4                   	hlt
    4526:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004530 <deregister_tm_clones>:
    4530:	48 8d 3d e9 6a 00 00 	lea    0x6ae9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4537:	48 8d 05 e2 6a 00 00 	lea    0x6ae2(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    453e:	48 39 f8             	cmp    %rdi,%rax
    4541:	74 15                	je     4558 <deregister_tm_clones+0x28>
    4543:	48 8b 05 96 6a 00 00 	mov    0x6a96(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    454a:	48 85 c0             	test   %rax,%rax
    454d:	74 09                	je     4558 <deregister_tm_clones+0x28>
    454f:	ff e0                	jmp    *%rax
    4551:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4558:	c3                   	ret
    4559:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004560 <register_tm_clones>:
    4560:	48 8d 3d b9 6a 00 00 	lea    0x6ab9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4567:	48 8d 35 b2 6a 00 00 	lea    0x6ab2(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    456e:	48 29 fe             	sub    %rdi,%rsi
    4571:	48 89 f0             	mov    %rsi,%rax
    4574:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4578:	48 c1 f8 03          	sar    $0x3,%rax
    457c:	48 01 c6             	add    %rax,%rsi
    457f:	48 d1 fe             	sar    %rsi
    4582:	74 14                	je     4598 <register_tm_clones+0x38>
    4584:	48 8b 05 65 6a 00 00 	mov    0x6a65(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    458b:	48 85 c0             	test   %rax,%rax
    458e:	74 08                	je     4598 <register_tm_clones+0x38>
    4590:	ff e0                	jmp    *%rax
    4592:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4598:	c3                   	ret
    4599:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000045a0 <__do_global_dtors_aux>:
    45a0:	f3 0f 1e fa          	endbr64
    45a4:	80 3d 7d 6a 00 00 00 	cmpb   $0x0,0x6a7d(%rip)        # b028 <completed.0>
    45ab:	75 2b                	jne    45d8 <__do_global_dtors_aux+0x38>
    45ad:	55                   	push   %rbp
    45ae:	48 83 3d 42 6a 00 00 00 	cmpq   $0x0,0x6a42(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    45b6:	48 89 e5             	mov    %rsp,%rbp
    45b9:	74 0c                	je     45c7 <__do_global_dtors_aux+0x27>
    45bb:	48 8b 3d 46 6a 00 00 	mov    0x6a46(%rip),%rdi        # b008 <__dso_handle>
    45c2:	e8 29 dd ff ff       	call   22f0 <__cxa_finalize@plt>
    45c7:	e8 64 ff ff ff       	call   4530 <deregister_tm_clones>
    45cc:	c6 05 55 6a 00 00 01 	movb   $0x1,0x6a55(%rip)        # b028 <completed.0>
    45d3:	5d                   	pop    %rbp
    45d4:	c3                   	ret
    45d5:	0f 1f 00             	nopl   (%rax)
    45d8:	c3                   	ret
    45d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000045e0 <frame_dummy>:
    45e0:	f3 0f 1e fa          	endbr64
    45e4:	e9 77 ff ff ff       	jmp    4560 <register_tm_clones>
    45e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000045f0 <do_protected_write>:
    45f0:	f3 0f 1e fa          	endbr64
    45f4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    45fb:	48 8b 40 48          	mov    0x48(%rax),%rax
    45ff:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
    4607:	48 8b 48 08          	mov    0x8(%rax),%rcx
    460b:	48 83 00 01          	addq   $0x1,(%rax)
    460f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4616:	48 85 c9             	test   %rcx,%rcx
    4619:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4620:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4624:	48 89 50 08          	mov    %rdx,0x8(%rax)
    4628:	31 c0                	xor    %eax,%eax
    462a:	c3                   	ret
    462b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004630 <barriered_reset>:
    4630:	f3 0f 1e fa          	endbr64
    4634:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    463b:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    4642:	85 c9                	test   %ecx,%ecx
    4644:	7e 48                	jle    468e <barriered_reset+0x5e>
    4646:	48 63 97 30 01 00 00 	movslq 0x130(%rdi),%rdx
    464d:	49 8b 40 18          	mov    0x18(%r8),%rax
    4651:	48 c1 e1 09          	shl    $0x9,%rcx
    4655:	49 8b 70 38          	mov    0x38(%r8),%rsi
    4659:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    465d:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4661:	31 c0                	xor    %eax,%eax
    4663:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4668:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
    4670:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
    4678:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    4683:	48 05 00 02 00 00    	add    $0x200,%rax
    4689:	48 39 c1             	cmp    %rax,%rcx
    468c:	75 da                	jne    4668 <barriered_reset+0x38>
    468e:	49 8b 88 f0 00 00 00 	mov    0xf0(%r8),%rcx
    4695:	8b 01                	mov    (%rcx),%eax
    4697:	83 f8 ff             	cmp    $0xffffffff,%eax
    469a:	74 0e                	je     46aa <barriered_reset+0x7a>
    469c:	41 8b b8 c0 00 00 00 	mov    0xc0(%r8),%edi
    46a3:	8d 57 ff             	lea    -0x1(%rdi),%edx
    46a6:	39 d0                	cmp    %edx,%eax
    46a8:	74 06                	je     46b0 <barriered_reset+0x80>
    46aa:	0f ae f8             	sfence
    46ad:	31 c0                	xor    %eax,%eax
    46af:	c3                   	ret
    46b0:	41 83 78 04 01       	cmpl   $0x1,0x4(%r8)
    46b5:	75 f3                	jne    46aa <barriered_reset+0x7a>
    46b7:	49 8b 80 d8 00 00 00 	mov    0xd8(%r8),%rax
    46be:	83 00 01             	addl   $0x1,(%rax)
    46c1:	c7 01 ff ff ff ff    	movl   $0xffffffff,(%rcx)
    46c7:	eb e1                	jmp    46aa <barriered_reset+0x7a>
    46c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000046d0 <external_thread>:
    46d0:	f3 0f 1e fa          	endbr64
    46d4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    46d8:	0f 85 fb 00 00 00    	jne    47d9 <external_thread+0x109>
    46de:	41 57                	push   %r15
    46e0:	49 89 ff             	mov    %rdi,%r15
    46e3:	41 56                	push   %r14
    46e5:	41 55                	push   %r13
    46e7:	4c 8d 2d 16 39 00 00 	lea    0x3916(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
    46ee:	41 54                	push   %r12
    46f0:	55                   	push   %rbp
    46f1:	53                   	push   %rbx
    46f2:	48 83 ec 08          	sub    $0x8,%rsp
    46f6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    46fc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    4700:	85 c9                	test   %ecx,%ecx
    4702:	7e 6e                	jle    4772 <external_thread+0xa2>
    4704:	45 31 e4             	xor    %r12d,%r12d
    4707:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4710:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    4718:	31 db                	xor    %ebx,%ebx
    471a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    471e:	48 8b 06             	mov    (%rsi),%rax
    4721:	8b 10                	mov    (%rax),%edx
    4723:	85 d2                	test   %edx,%edx
    4725:	7e 2a                	jle    4751 <external_thread+0x81>
    4727:	48 8b 48 08          	mov    0x8(%rax),%rcx
    472b:	48 89 dd             	mov    %rbx,%rbp
    472e:	48 c1 e5 08          	shl    $0x8,%rbp
    4732:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4736:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    473d:	45 85 c0             	test   %r8d,%r8d
    4740:	74 36                	je     4778 <external_thread+0xa8>
    4742:	48 83 c3 01          	add    $0x1,%rbx
    4746:	39 da                	cmp    %ebx,%edx
    4748:	7f e1                	jg     472b <external_thread+0x5b>
    474a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4751:	49 83 c4 01          	add    $0x1,%r12
    4755:	44 39 e1             	cmp    %r12d,%ecx
    4758:	7f b6                	jg     4710 <external_thread+0x40>
    475a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    475f:	74 9f                	je     4700 <external_thread+0x30>
    4761:	48 83 c4 08          	add    $0x8,%rsp
    4765:	31 c0                	xor    %eax,%eax
    4767:	5b                   	pop    %rbx
    4768:	5d                   	pop    %rbp
    4769:	41 5c                	pop    %r12
    476b:	41 5d                	pop    %r13
    476d:	41 5e                	pop    %r14
    476f:	41 5f                	pop    %r15
    4771:	c3                   	ret
    4772:	eb fe                	jmp    4772 <external_thread+0xa2>
    4774:	0f 1f 40 00          	nopl   0x0(%rax)
    4778:	4c 89 28             	mov    %r13,(%rax)
    477b:	48 8b 06             	mov    (%rsi),%rax
    477e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4782:	48 01 ef             	add    %rbp,%rdi
    4785:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    478c:	48 c1 e6 05          	shl    $0x5,%rsi
    4790:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4797:	bf 04 00 00 00       	mov    $0x4,%edi
    479c:	e8 af db ff ff       	call   2350 <clock_gettime@plt>
    47a1:	49 8b 47 50          	mov    0x50(%r15),%rax
    47a5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    47a9:	48 8b 40 08          	mov    0x8(%rax),%rax
    47ad:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
    47b8:	0f ae f8             	sfence
    47bb:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    47bf:	48 83 c3 01          	add    $0x1,%rbx
    47c3:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    47c7:	48 8b 06             	mov    (%rsi),%rax
    47ca:	8b 10                	mov    (%rax),%edx
    47cc:	39 da                	cmp    %ebx,%edx
    47ce:	0f 8f 53 ff ff ff    	jg     4727 <external_thread+0x57>
    47d4:	e9 71 ff ff ff       	jmp    474a <external_thread+0x7a>
    47d9:	31 c0                	xor    %eax,%eax
    47db:	c3                   	ret
    47dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000047e0 <timer_thread>:
    47e0:	f3 0f 1e fa          	endbr64
    47e4:	41 57                	push   %r15
    47e6:	48 8d 35 23 38 00 00 	lea    0x3823(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    47ed:	49 89 ff             	mov    %rdi,%r15
    47f0:	41 56                	push   %r14
    47f2:	41 55                	push   %r13
    47f4:	41 54                	push   %r12
    47f6:	55                   	push   %rbp
    47f7:	53                   	push   %rbx
    47f8:	48 83 ec 58          	sub    $0x58,%rsp
    47fc:	8b 57 04             	mov    0x4(%rdi),%edx
    47ff:	bf 01 00 00 00       	mov    $0x1,%edi
    4804:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    480d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    4812:	31 c0                	xor    %eax,%eax
    4814:	e8 97 dc ff ff       	call   24b0 <__printf_chk@plt>
    4819:	66 0f 6f 05 cf 43 00 00 	movdqa 0x43cf(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4821:	ba 88 13 00 00       	mov    $0x1388,%edx
    4826:	31 c0                	xor    %eax,%eax
    4828:	48 8d 35 f3 37 00 00 	lea    0x37f3(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    482f:	bf 01 00 00 00       	mov    $0x1,%edi
    4834:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4839:	e8 72 dc ff ff       	call   24b0 <__printf_chk@plt>
    483e:	41 8b 47 44          	mov    0x44(%r15),%eax
    4842:	89 c3                	mov    %eax,%ebx
    4844:	85 c0                	test   %eax,%eax
    4846:	0f 84 9a 00 00 00    	je     48e6 <timer_thread+0x106>
    484c:	45 31 f6             	xor    %r14d,%r14d
    484f:	31 db                	xor    %ebx,%ebx
    4851:	49 89 e5             	mov    %rsp,%r13
    4854:	31 ed                	xor    %ebp,%ebp
    4856:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    485b:	4c 89 e7             	mov    %r12,%rdi
    485e:	4c 89 ee             	mov    %r13,%rsi
    4861:	41 83 c6 01          	add    $0x1,%r14d
    4865:	e8 36 db ff ff       	call   23a0 <nanosleep@plt>
    486a:	49 63 47 30          	movslq 0x30(%r15),%rax
    486e:	8d 7b 01             	lea    0x1(%rbx),%edi
    4871:	85 c0                	test   %eax,%eax
    4873:	7e 4a                	jle    48bf <timer_thread+0xdf>
    4875:	49 8b 4f 18          	mov    0x18(%r15),%rcx
    4879:	4c 63 c3             	movslq %ebx,%r8
    487c:	49 c1 e0 09          	shl    $0x9,%r8
    4880:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4884:	0f 1f 40 00          	nopl   0x0(%rax)
    4888:	48 8b 19             	mov    (%rcx),%rbx
    488b:	89 f8                	mov    %edi,%eax
    488d:	48 83 c1 08          	add    $0x8,%rcx
    4891:	99                   	cltd
    4892:	f7 7b 40             	idivl  0x40(%rbx)
    4895:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4899:	83 ea 01             	sub    $0x1,%edx
    489c:	48 63 d2             	movslq %edx,%rdx
    489f:	48 c1 e2 09          	shl    $0x9,%rdx
    48a3:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    48ae:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    48ba:	49 39 c9             	cmp    %rcx,%r9
    48bd:	75 c9                	jne    4888 <timer_thread+0xa8>
    48bf:	0f ae f0             	mfence
    48c2:	49 8b 47 18          	mov    0x18(%r15),%rax
    48c6:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    48ca:	89 fb                	mov    %edi,%ebx
    48cc:	48 8b 00             	mov    (%rax),%rax
    48cf:	39 78 40             	cmp    %edi,0x40(%rax)
    48d2:	0f 4e dd             	cmovle %ebp,%ebx
    48d5:	85 c9                	test   %ecx,%ecx
    48d7:	74 0d                	je     48e6 <timer_thread+0x106>
    48d9:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    48e0:	0f 85 75 ff ff ff    	jne    485b <timer_thread+0x7b>
    48e6:	48 8d 3d 4b 37 00 00 	lea    0x374b(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    48ed:	e8 3e da ff ff       	call   2330 <puts@plt>
    48f2:	49 63 57 30          	movslq 0x30(%r15),%rdx
    48f6:	85 d2                	test   %edx,%edx
    48f8:	7e 6b                	jle    4965 <timer_thread+0x185>
    48fa:	49 63 47 40          	movslq 0x40(%r15),%rax
    48fe:	85 c0                	test   %eax,%eax
    4900:	7e 63                	jle    4965 <timer_thread+0x185>
    4902:	48 c1 e0 09          	shl    $0x9,%rax
    4906:	4d 8b 47 18          	mov    0x18(%r15),%r8
    490a:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4912:	31 c9                	xor    %ecx,%ecx
    4914:	48 89 c6             	mov    %rax,%rsi
    4917:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    491b:	48 8b 40 38          	mov    0x38(%rax),%rax
    491f:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4923:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4929:	74 15                	je     4940 <timer_thread+0x160>
    492b:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    4935:	48 05 00 02 00 00    	add    $0x200,%rax
    493b:	48 39 c2             	cmp    %rax,%rdx
    493e:	74 1c                	je     495c <timer_thread+0x17c>
    4940:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    494a:	48 05 00 04 00 00    	add    $0x400,%rax
    4950:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    4957:	48 39 c2             	cmp    %rax,%rdx
    495a:	75 e4                	jne    4940 <timer_thread+0x160>
    495c:	48 83 c1 08          	add    $0x8,%rcx
    4960:	48 39 cf             	cmp    %rcx,%rdi
    4963:	75 b2                	jne    4917 <timer_thread+0x137>
    4965:	0f ae f0             	mfence
    4968:	66 0f 6f 05 90 42 00 00 	movdqa 0x4290(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4970:	41 89 dc             	mov    %ebx,%r12d
    4973:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    4978:	49 63 47 28          	movslq 0x28(%r15),%rax
    497c:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    4981:	85 c0                	test   %eax,%eax
    4983:	7e 46                	jle    49cb <timer_thread+0x1eb>
    4985:	49 8b 4f 18          	mov    0x18(%r15),%rcx
    4989:	49 63 ec             	movslq %r12d,%rbp
    498c:	48 c1 e5 09          	shl    $0x9,%rbp
    4990:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4994:	0f 1f 40 00          	nopl   0x0(%rax)
    4998:	48 8b 19             	mov    (%rcx),%rbx
    499b:	89 f8                	mov    %edi,%eax
    499d:	48 83 c1 08          	add    $0x8,%rcx
    49a1:	99                   	cltd
    49a2:	f7 7b 40             	idivl  0x40(%rbx)
    49a5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    49a9:	48 63 d2             	movslq %edx,%rdx
    49ac:	48 c1 e2 09          	shl    $0x9,%rdx
    49b0:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    49bb:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    49c6:	49 39 c8             	cmp    %rcx,%r8
    49c9:	75 cd                	jne    4998 <timer_thread+0x1b8>
    49cb:	0f ae f0             	mfence
    49ce:	49 8b 77 18          	mov    0x18(%r15),%rsi
    49d2:	45 31 e4             	xor    %r12d,%r12d
    49d5:	48 8b 06             	mov    (%rsi),%rax
    49d8:	39 78 40             	cmp    %edi,0x40(%rax)
    49db:	44 0f 4f e7          	cmovg  %edi,%r12d
    49df:	41 8b 7f 30          	mov    0x30(%r15),%edi
    49e3:	85 ff                	test   %edi,%edi
    49e5:	0f 8e a9 01 00 00    	jle    4b94 <timer_thread+0x3b4>
    49eb:	45 31 f6             	xor    %r14d,%r14d
    49ee:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    49f4:	4c 89 f5             	mov    %r14,%rbp
    49f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4a00:	89 eb                	mov    %ebp,%ebx
    4a02:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    4a0a:	45 31 f6             	xor    %r14d,%r14d
    4a0d:	85 ff                	test   %edi,%edi
    4a0f:	7e 77                	jle    4a88 <timer_thread+0x2a8>
    4a11:	4c 89 f6             	mov    %r14,%rsi
    4a14:	48 63 cf             	movslq %edi,%rcx
    4a17:	45 31 c0             	xor    %r8d,%r8d
    4a1a:	48 c1 e6 09          	shl    $0x9,%rsi
    4a1e:	66 90                	xchg   %ax,%ax
    4a20:	41 39 e8             	cmp    %ebp,%r8d
    4a23:	74 45                	je     4a6a <timer_thread+0x28a>
    4a25:	49 8b 47 18          	mov    0x18(%r15),%rax
    4a29:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    4a2d:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4a31:	4c 89 c0             	mov    %r8,%rax
    4a34:	48 c1 e0 08          	shl    $0x8,%rax
    4a38:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4a40:	48 8b 10             	mov    (%rax),%rdx
    4a43:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    4a4a:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4a51:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4a58:	4d 85 c9             	test   %r9,%r9
    4a5b:	0f 8f 97 00 00 00    	jg     4af8 <timer_thread+0x318>
    4a61:	4d 85 db             	test   %r11,%r11
    4a64:	0f 8f 8e 00 00 00    	jg     4af8 <timer_thread+0x318>
    4a6a:	49 83 c0 01          	add    $0x1,%r8
    4a6e:	4c 39 c1             	cmp    %r8,%rcx
    4a71:	75 ad                	jne    4a20 <timer_thread+0x240>
    4a73:	49 83 fe 01          	cmp    $0x1,%r14
    4a77:	74 0f                	je     4a88 <timer_thread+0x2a8>
    4a79:	41 be 01 00 00 00    	mov    $0x1,%r14d
    4a7f:	85 ff                	test   %edi,%edi
    4a81:	7f 8e                	jg     4a11 <timer_thread+0x231>
    4a83:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4a88:	48 83 c5 01          	add    $0x1,%rbp
    4a8c:	39 ef                	cmp    %ebp,%edi
    4a8e:	0f 8f 6c ff ff ff    	jg     4a00 <timer_thread+0x220>
    4a94:	44 89 d5             	mov    %r10d,%ebp
    4a97:	85 ff                	test   %edi,%edi
    4a99:	7e 3b                	jle    4ad6 <timer_thread+0x2f6>
    4a9b:	31 db                	xor    %ebx,%ebx
    4a9d:	bf 01 00 00 00       	mov    $0x1,%edi
    4aa2:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4aa6:	41 8b 57 40          	mov    0x40(%r15),%edx
    4aaa:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4aae:	48 8b 40 38          	mov    0x38(%rax),%rax
    4ab2:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    4ab8:	39 d1                	cmp    %edx,%ecx
    4aba:	0f 8c a8 00 00 00    	jl     4b68 <timer_thread+0x388>
    4ac0:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    4ac6:	39 d0                	cmp    %edx,%eax
    4ac8:	7c 6e                	jl     4b38 <timer_thread+0x358>
    4aca:	48 83 c3 01          	add    $0x1,%rbx
    4ace:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4ad2:	7f d6                	jg     4aaa <timer_thread+0x2ca>
    4ad4:	21 fd                	and    %edi,%ebp
    4ad6:	85 ed                	test   %ebp,%ebp
    4ad8:	0f 85 b6 00 00 00    	jne    4b94 <timer_thread+0x3b4>
    4ade:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4ae3:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4ae8:	e8 b3 d8 ff ff       	call   23a0 <nanosleep@plt>
    4aed:	e9 86 fe ff ff       	jmp    4978 <timer_thread+0x198>
    4af2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4af8:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    4afe:	48 83 ec 08          	sub    $0x8,%rsp
    4b02:	bf 01 00 00 00       	mov    $0x1,%edi
    4b07:	44 89 f1             	mov    %r14d,%ecx
    4b0a:	48 8d 35 4c 35 00 00 	lea    0x354c(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    4b11:	50                   	push   %rax
    4b12:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    4b18:	89 da                	mov    %ebx,%edx
    4b1a:	50                   	push   %rax
    4b1b:	31 c0                	xor    %eax,%eax
    4b1d:	41 53                	push   %r11
    4b1f:	e8 8c d9 ff ff       	call   24b0 <__printf_chk@plt>
    4b24:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4b28:	48 83 c4 20          	add    $0x20,%rsp
    4b2c:	45 31 d2             	xor    %r10d,%r10d
    4b2f:	e9 3f ff ff ff       	jmp    4a73 <timer_thread+0x293>
    4b34:	0f 1f 40 00          	nopl   0x0(%rax)
    4b38:	89 c2                	mov    %eax,%edx
    4b3a:	bf 01 00 00 00       	mov    $0x1,%edi
    4b3f:	31 c0                	xor    %eax,%eax
    4b41:	48 83 c3 01          	add    $0x1,%rbx
    4b45:	48 8d 35 d6 37 00 00 	lea    0x37d6(%rip),%rsi        # 8322 <_IO_stdin_used+0x322>
    4b4c:	e8 5f d9 ff ff       	call   24b0 <__printf_chk@plt>
    4b51:	31 ff                	xor    %edi,%edi
    4b53:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4b57:	0f 8f 45 ff ff ff    	jg     4aa2 <timer_thread+0x2c2>
    4b5d:	e9 72 ff ff ff       	jmp    4ad4 <timer_thread+0x2f4>
    4b62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b68:	89 ca                	mov    %ecx,%edx
    4b6a:	48 8d 35 b1 37 00 00 	lea    0x37b1(%rip),%rsi        # 8322 <_IO_stdin_used+0x322>
    4b71:	bf 01 00 00 00       	mov    $0x1,%edi
    4b76:	31 c0                	xor    %eax,%eax
    4b78:	e8 33 d9 ff ff       	call   24b0 <__printf_chk@plt>
    4b7d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4b81:	41 8b 57 40          	mov    0x40(%r15),%edx
    4b85:	31 ff                	xor    %edi,%edi
    4b87:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4b8b:	48 8b 40 38          	mov    0x38(%rax),%rax
    4b8f:	e9 2c ff ff ff       	jmp    4ac0 <timer_thread+0x2e0>
    4b94:	48 8d 3d b9 34 00 00 	lea    0x34b9(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4b9b:	e8 90 d7 ff ff       	call   2330 <puts@plt>
    4ba0:	41 8b 57 44          	mov    0x44(%r15),%edx
    4ba4:	85 d2                	test   %edx,%edx
    4ba6:	0f 84 eb 00 00 00    	je     4c97 <timer_thread+0x4b7>
    4bac:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4bb0:	31 db                	xor    %ebx,%ebx
    4bb2:	48 8d 2d c1 34 00 00 	lea    0x34c1(%rip),%rbp        # 807a <_IO_stdin_used+0x7a>
    4bb9:	4c 8d 25 d5 34 00 00 	lea    0x34d5(%rip),%r12        # 8095 <_IO_stdin_used+0x95>
    4bc0:	85 c0                	test   %eax,%eax
    4bc2:	7e 38                	jle    4bfc <timer_thread+0x41c>
    4bc4:	0f 1f 40 00          	nopl   0x0(%rax)
    4bc8:	31 c0                	xor    %eax,%eax
    4bca:	89 da                	mov    %ebx,%edx
    4bcc:	48 89 ee             	mov    %rbp,%rsi
    4bcf:	bf 01 00 00 00       	mov    $0x1,%edi
    4bd4:	e8 d7 d8 ff ff       	call   24b0 <__printf_chk@plt>
    4bd9:	49 8b 47 18          	mov    0x18(%r15),%rax
    4bdd:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4be1:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
    4be5:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
    4bec:	0f 84 d2 00 00 00    	je     4cc4 <timer_thread+0x4e4>
    4bf2:	48 83 c3 01          	add    $0x1,%rbx
    4bf6:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4bfa:	7f cc                	jg     4bc8 <timer_thread+0x3e8>
    4bfc:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4c00:	85 d2                	test   %edx,%edx
    4c02:	7e 7c                	jle    4c80 <timer_thread+0x4a0>
    4c04:	41 8b 47 40          	mov    0x40(%r15),%eax
    4c08:	85 c0                	test   %eax,%eax
    4c0a:	7e 74                	jle    4c80 <timer_thread+0x4a0>
    4c0c:	48 63 f0             	movslq %eax,%rsi
    4c0f:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4c13:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4c1b:	31 c9                	xor    %ecx,%ecx
    4c1d:	48 c1 e6 09          	shl    $0x9,%rsi
    4c21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c28:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4c2c:	48 8b 40 38          	mov    0x38(%rax),%rax
    4c30:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4c34:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4c3a:	74 1c                	je     4c58 <timer_thread+0x478>
    4c3c:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4c46:	48 05 00 02 00 00    	add    $0x200,%rax
    4c4c:	48 39 d0             	cmp    %rdx,%rax
    4c4f:	74 26                	je     4c77 <timer_thread+0x497>
    4c51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c58:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4c62:	48 05 00 04 00 00    	add    $0x400,%rax
    4c68:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
    4c72:	48 39 d0             	cmp    %rdx,%rax
    4c75:	75 e1                	jne    4c58 <timer_thread+0x478>
    4c77:	48 83 c1 08          	add    $0x8,%rcx
    4c7b:	48 39 cf             	cmp    %rcx,%rdi
    4c7e:	75 a8                	jne    4c28 <timer_thread+0x448>
    4c80:	0f ae f0             	mfence
    4c83:	48 8d 3d 1d 34 00 00 	lea    0x341d(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4c8a:	e8 a1 d6 ff ff       	call   2330 <puts@plt>
    4c8f:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4c97:	48 8d 3d 10 34 00 00 	lea    0x3410(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4c9e:	e8 8d d6 ff ff       	call   2330 <puts@plt>
    4ca3:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4ca8:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4cb1:	75 41                	jne    4cf4 <timer_thread+0x514>
    4cb3:	48 83 c4 58          	add    $0x58,%rsp
    4cb7:	31 c0                	xor    %eax,%eax
    4cb9:	5b                   	pop    %rbx
    4cba:	5d                   	pop    %rbp
    4cbb:	41 5c                	pop    %r12
    4cbd:	41 5d                	pop    %r13
    4cbf:	41 5e                	pop    %r14
    4cc1:	41 5f                	pop    %r15
    4cc3:	c3                   	ret
    4cc4:	4c 89 e7             	mov    %r12,%rdi
    4cc7:	e8 64 d6 ff ff       	call   2330 <puts@plt>
    4ccc:	49 8b 47 18          	mov    0x18(%r15),%rax
    4cd0:	be 01 00 00 00       	mov    $0x1,%esi
    4cd5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4cd9:	48 83 c3 01          	add    $0x1,%rbx
    4cdd:	8b 78 60             	mov    0x60(%rax),%edi
    4ce0:	e8 7b d7 ff ff       	call   2460 <eventfd_write@plt>
    4ce5:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4ce9:	0f 8f d9 fe ff ff    	jg     4bc8 <timer_thread+0x3e8>
    4cef:	e9 08 ff ff ff       	jmp    4bfc <timer_thread+0x41c>
    4cf4:	e8 87 d6 ff ff       	call   2380 <__stack_chk_fail@plt>
    4cf9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004d00 <minf>:
    4d00:	f3 0f 1e fa          	endbr64
    4d04:	39 f7                	cmp    %esi,%edi
    4d06:	89 f0                	mov    %esi,%eax
    4d08:	0f 4e c7             	cmovle %edi,%eax
    4d0b:	c3                   	ret
    4d0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004d10 <maxf>:
    4d10:	f3 0f 1e fa          	endbr64
    4d14:	39 f7                	cmp    %esi,%edi
    4d16:	89 f0                	mov    %esi,%eax
    4d18:	0f 4d c7             	cmovge %edi,%eax
    4d1b:	c3                   	ret
    4d1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004d20 <strtolower>:
    4d20:	f3 0f 1e fa          	endbr64
    4d24:	55                   	push   %rbp
    4d25:	53                   	push   %rbx
    4d26:	48 83 ec 08          	sub    $0x8,%rsp
    4d2a:	48 0f be 1f          	movsbq (%rdi),%rbx
    4d2e:	84 db                	test   %bl,%bl
    4d30:	74 24                	je     4d56 <strtolower+0x36>
    4d32:	48 89 fd             	mov    %rdi,%rbp
    4d35:	e8 56 d8 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4d3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d40:	48 8b 10             	mov    (%rax),%rdx
    4d43:	48 83 c5 01          	add    $0x1,%rbp
    4d47:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4d4a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    4d4d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4d52:	84 db                	test   %bl,%bl
    4d54:	75 ea                	jne    4d40 <strtolower+0x20>
    4d56:	48 83 c4 08          	add    $0x8,%rsp
    4d5a:	5b                   	pop    %rbx
    4d5b:	5d                   	pop    %rbp
    4d5c:	c3                   	ret
    4d5d:	0f 1f 00             	nopl   (%rax)

0000000000004d60 <zh_malloc>:
    4d60:	f3 0f 1e fa          	endbr64
    4d64:	48 83 ec 08          	sub    $0x8,%rsp
    4d68:	e8 03 d7 ff ff       	call   2470 <malloc@plt>
    4d6d:	48 85 c0             	test   %rax,%rax
    4d70:	74 05                	je     4d77 <zh_malloc+0x17>
    4d72:	48 83 c4 08          	add    $0x8,%rsp
    4d76:	c3                   	ret
    4d77:	48 8b 0d a2 62 00 00 	mov    0x62a2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4d7e:	ba 28 00 00 00       	mov    $0x28,%edx
    4d83:	be 01 00 00 00       	mov    $0x1,%esi
    4d88:	48 8d 3d 49 38 00 00 	lea    0x3849(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    4d8f:	e8 9c d7 ff ff       	call   2530 <fwrite@plt>
    4d94:	bf 01 00 00 00       	mov    $0x1,%edi
    4d99:	e8 72 d7 ff ff       	call   2510 <exit@plt>
    4d9e:	66 90                	xchg   %ax,%ax

0000000000004da0 <get_filename_ext>:
    4da0:	f3 0f 1e fa          	endbr64
    4da4:	53                   	push   %rbx
    4da5:	be 2e 00 00 00       	mov    $0x2e,%esi
    4daa:	48 89 fb             	mov    %rdi,%rbx
    4dad:	e8 fe d5 ff ff       	call   23b0 <strrchr@plt>
    4db2:	48 85 c0             	test   %rax,%rax
    4db5:	74 11                	je     4dc8 <get_filename_ext+0x28>
    4db7:	48 39 c3             	cmp    %rax,%rbx
    4dba:	74 0c                	je     4dc8 <get_filename_ext+0x28>
    4dbc:	48 83 c0 01          	add    $0x1,%rax
    4dc0:	5b                   	pop    %rbx
    4dc1:	c3                   	ret
    4dc2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4dc8:	48 8d 05 27 33 00 00 	lea    0x3327(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
    4dcf:	5b                   	pop    %rbx
    4dd0:	c3                   	ret
    4dd1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4ddc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004de0 <send_headers>:
    4de0:	f3 0f 1e fa          	endbr64
    4de4:	41 55                	push   %r13
    4de6:	49 89 f5             	mov    %rsi,%r13
    4de9:	48 89 fe             	mov    %rdi,%rsi
    4dec:	41 54                	push   %r12
    4dee:	55                   	push   %rbp
    4def:	48 89 d5             	mov    %rdx,%rbp
    4df2:	ba 00 04 00 00       	mov    $0x400,%edx
    4df7:	53                   	push   %rbx
    4df8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4dff:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4e08:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4e10:	31 c0                	xor    %eax,%eax
    4e12:	49 89 e4             	mov    %rsp,%r12
    4e15:	4c 89 e7             	mov    %r12,%rdi
    4e18:	e8 73 d6 ff ff       	call   2490 <__strcpy_chk@plt>
    4e1d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4e22:	84 db                	test   %bl,%bl
    4e24:	74 24                	je     4e4a <send_headers+0x6a>
    4e26:	e8 65 d7 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4e2b:	48 8b 08             	mov    (%rax),%rcx
    4e2e:	4c 89 e0             	mov    %r12,%rax
    4e31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4e38:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    4e3b:	48 83 c0 01          	add    $0x1,%rax
    4e3f:	88 50 ff             	mov    %dl,-0x1(%rax)
    4e42:	48 0f be 18          	movsbq (%rax),%rbx
    4e46:	84 db                	test   %bl,%bl
    4e48:	75 ee                	jne    4e38 <send_headers+0x58>
    4e4a:	bf 11 00 00 00       	mov    $0x11,%edi
    4e4f:	e8 1c d6 ff ff       	call   2470 <malloc@plt>
    4e54:	48 85 c0             	test   %rax,%rax
    4e57:	0f 84 7e 04 00 00    	je     52db <send_headers+0x4fb>
    4e5d:	66 0f 6f 05 ab 3d 00 00 	movdqa 0x3dab(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e65:	48 89 45 00          	mov    %rax,0x0(%rbp)
    4e69:	bf 17 00 00 00       	mov    $0x17,%edi
    4e6e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4e76:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4e7a:	0f 11 00             	movups %xmm0,(%rax)
    4e7d:	e8 ee d5 ff ff       	call   2470 <malloc@plt>
    4e82:	48 85 c0             	test   %rax,%rax
    4e85:	0f 84 50 04 00 00    	je     52db <send_headers+0x4fb>
    4e8b:	66 0f 6f 05 8d 3d 00 00 	movdqa 0x3d8d(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4e93:	48 89 45 10          	mov    %rax,0x10(%rbp)
    4e97:	4c 89 e7             	mov    %r12,%rdi
    4e9a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    4ea4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4eac:	0f 11 00             	movups %xmm0,(%rax)
    4eaf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    4eb3:	be 2e 00 00 00       	mov    $0x2e,%esi
    4eb8:	e8 f3 d4 ff ff       	call   23b0 <strrchr@plt>
    4ebd:	48 85 c0             	test   %rax,%rax
    4ec0:	0f 84 ea 02 00 00    	je     51b0 <send_headers+0x3d0>
    4ec6:	4c 39 e0             	cmp    %r12,%rax
    4ec9:	0f 84 e1 02 00 00    	je     51b0 <send_headers+0x3d0>
    4ecf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    4ed3:	48 8d 3d ea 31 00 00 	lea    0x31ea(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4eda:	48 89 de             	mov    %rbx,%rsi
    4edd:	e8 2e d5 ff ff       	call   2410 <strcmp@plt>
    4ee2:	85 c0                	test   %eax,%eax
    4ee4:	75 20                	jne    4f06 <send_headers+0x126>
    4ee6:	66 0f 6f 05 42 3d 00 00 	movdqa 0x3d42(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4eee:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ef6:	66 0f 6f 05 42 3d 00 00 	movdqa 0x3d42(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4efe:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4f06:	48 89 de             	mov    %rbx,%rsi
    4f09:	48 8d 3d b8 31 00 00 	lea    0x31b8(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4f10:	e8 fb d4 ff ff       	call   2410 <strcmp@plt>
    4f15:	85 c0                	test   %eax,%eax
    4f17:	75 20                	jne    4f39 <send_headers+0x159>
    4f19:	66 0f 6f 05 0f 3d 00 00 	movdqa 0x3d0f(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4f21:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f29:	66 0f 6f 05 0f 3d 00 00 	movdqa 0x3d0f(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4f31:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4f39:	48 89 de             	mov    %rbx,%rsi
    4f3c:	48 8d 3d 8a 31 00 00 	lea    0x318a(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4f43:	e8 c8 d4 ff ff       	call   2410 <strcmp@plt>
    4f48:	85 c0                	test   %eax,%eax
    4f4a:	0f 84 10 02 00 00    	je     5160 <send_headers+0x380>
    4f50:	48 89 de             	mov    %rbx,%rsi
    4f53:	48 8d 3d 77 31 00 00 	lea    0x3177(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4f5a:	e8 b1 d4 ff ff       	call   2410 <strcmp@plt>
    4f5f:	85 c0                	test   %eax,%eax
    4f61:	0f 84 a9 02 00 00    	je     5210 <send_headers+0x430>
    4f67:	48 89 de             	mov    %rbx,%rsi
    4f6a:	48 8d 3d 64 31 00 00 	lea    0x3164(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4f71:	e8 9a d4 ff ff       	call   2410 <strcmp@plt>
    4f76:	85 c0                	test   %eax,%eax
    4f78:	0f 84 6a 02 00 00    	je     51e8 <send_headers+0x408>
    4f7e:	48 89 de             	mov    %rbx,%rsi
    4f81:	48 8d 3d 90 31 00 00 	lea    0x3190(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4f88:	e8 83 d4 ff ff       	call   2410 <strcmp@plt>
    4f8d:	85 c0                	test   %eax,%eax
    4f8f:	0f 84 2b 02 00 00    	je     51c0 <send_headers+0x3e0>
    4f95:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4f98:	0f 84 52 01 00 00    	je     50f0 <send_headers+0x310>
    4f9e:	48 89 de             	mov    %rbx,%rsi
    4fa1:	48 8d 3d 31 31 00 00 	lea    0x3131(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4fa8:	e8 63 d4 ff ff       	call   2410 <strcmp@plt>
    4fad:	85 c0                	test   %eax,%eax
    4faf:	0f 84 ab 02 00 00    	je     5260 <send_headers+0x480>
    4fb5:	48 89 de             	mov    %rbx,%rsi
    4fb8:	48 8d 3d 1e 31 00 00 	lea    0x311e(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4fbf:	e8 4c d4 ff ff       	call   2410 <strcmp@plt>
    4fc4:	85 c0                	test   %eax,%eax
    4fc6:	0f 84 6c 02 00 00    	je     5238 <send_headers+0x458>
    4fcc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4fd4:	4c 89 e7             	mov    %r12,%rdi
    4fd7:	e8 94 d3 ff ff       	call   2370 <strlen@plt>
    4fdc:	48 89 c7             	mov    %rax,%rdi
    4fdf:	48 89 c3             	mov    %rax,%rbx
    4fe2:	e8 89 d4 ff ff       	call   2470 <malloc@plt>
    4fe7:	48 85 c0             	test   %rax,%rax
    4fea:	0f 84 eb 02 00 00    	je     52db <send_headers+0x4fb>
    4ff0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4ff4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    4ff8:	83 fb 08             	cmp    $0x8,%ebx
    4ffb:	0f 83 3f 01 00 00    	jae    5140 <send_headers+0x360>
    5001:	f6 c3 04             	test   $0x4,%bl
    5004:	0f 85 7b 02 00 00    	jne    5285 <send_headers+0x4a5>
    500a:	85 db                	test   %ebx,%ebx
    500c:	74 13                	je     5021 <send_headers+0x241>
    500e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    5016:	88 10                	mov    %dl,(%rax)
    5018:	f6 c3 02             	test   $0x2,%bl
    501b:	0f 85 96 02 00 00    	jne    52b7 <send_headers+0x4d7>
    5021:	4d 89 e8             	mov    %r13,%r8
    5024:	48 8d 0d b6 30 00 00 	lea    0x30b6(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    502b:	4c 89 e7             	mov    %r12,%rdi
    502e:	31 c0                	xor    %eax,%eax
    5030:	ba 00 04 00 00       	mov    $0x400,%edx
    5035:	be 01 00 00 00       	mov    $0x1,%esi
    503a:	e8 61 d5 ff ff       	call   25a0 <__sprintf_chk@plt>
    503f:	4c 89 e7             	mov    %r12,%rdi
    5042:	e8 29 d3 ff ff       	call   2370 <strlen@plt>
    5047:	48 89 c7             	mov    %rax,%rdi
    504a:	48 89 c3             	mov    %rax,%rbx
    504d:	e8 1e d4 ff ff       	call   2470 <malloc@plt>
    5052:	48 85 c0             	test   %rax,%rax
    5055:	0f 84 80 02 00 00    	je     52db <send_headers+0x4fb>
    505b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    505f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    5063:	83 fb 08             	cmp    $0x8,%ebx
    5066:	0f 83 1c 01 00 00    	jae    5188 <send_headers+0x3a8>
    506c:	f6 c3 04             	test   $0x4,%bl
    506f:	0f 85 29 02 00 00    	jne    529e <send_headers+0x4be>
    5075:	85 db                	test   %ebx,%ebx
    5077:	74 13                	je     508c <send_headers+0x2ac>
    5079:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    5081:	88 10                	mov    %dl,(%rax)
    5083:	f6 c3 02             	test   $0x2,%bl
    5086:	0f 85 3d 02 00 00    	jne    52c9 <send_headers+0x4e9>
    508c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    5091:	bf 02 00 00 00       	mov    $0x2,%edi
    5096:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    509e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    50a6:	e8 c5 d3 ff ff       	call   2470 <malloc@plt>
    50ab:	48 85 c0             	test   %rax,%rax
    50ae:	0f 84 27 02 00 00    	je     52db <send_headers+0x4fb>
    50b4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    50bc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    50c0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    50c8:	66 89 10             	mov    %dx,(%rax)
    50cb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    50d3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    50dc:	0f 85 20 02 00 00    	jne    5302 <send_headers+0x522>
    50e2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    50e9:	5b                   	pop    %rbx
    50ea:	5d                   	pop    %rbp
    50eb:	41 5c                	pop    %r12
    50ed:	41 5d                	pop    %r13
    50ef:	c3                   	ret
    50f0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    50f4:	0f 85 a4 fe ff ff    	jne    4f9e <send_headers+0x1be>
    50fa:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    50fe:	0f 85 9a fe ff ff    	jne    4f9e <send_headers+0x1be>
    5104:	66 0f 6f 05 84 3b 00 00 	movdqa 0x3b84(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    510c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    5116:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    511e:	66 0f 6f 05 7a 3b 00 00 	movdqa 0x3b7a(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    5126:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    512e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    5136:	e9 63 fe ff ff       	jmp    4f9e <send_headers+0x1be>
    513b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5140:	89 da                	mov    %ebx,%edx
    5142:	48 89 c7             	mov    %rax,%rdi
    5145:	4c 89 e6             	mov    %r12,%rsi
    5148:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    514d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5152:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5155:	c1 e9 03             	shr    $0x3,%ecx
    5158:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    515b:	e9 c1 fe ff ff       	jmp    5021 <send_headers+0x241>
    5160:	66 0f 6f 05 c8 3a 00 00 	movdqa 0x3ac8(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    5168:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5170:	66 0f 6f 05 d8 3a 00 00 	movdqa 0x3ad8(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5178:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5180:	e9 cb fd ff ff       	jmp    4f50 <send_headers+0x170>
    5185:	0f 1f 00             	nopl   (%rax)
    5188:	89 da                	mov    %ebx,%edx
    518a:	48 89 c7             	mov    %rax,%rdi
    518d:	4c 89 e6             	mov    %r12,%rsi
    5190:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    5195:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    519a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    519d:	c1 e9 03             	shr    $0x3,%ecx
    51a0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    51a3:	e9 e4 fe ff ff       	jmp    508c <send_headers+0x2ac>
    51a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    51b0:	48 8d 1d 3f 2f 00 00 	lea    0x2f3f(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    51b7:	e9 94 fd ff ff       	jmp    4f50 <send_headers+0x170>
    51bc:	0f 1f 40 00          	nopl   0x0(%rax)
    51c0:	66 0f 6f 05 a8 3a 00 00 	movdqa 0x3aa8(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    51c8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    51d0:	66 0f 6f 05 a8 3a 00 00 	movdqa 0x3aa8(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    51d8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    51e0:	e9 b0 fd ff ff       	jmp    4f95 <send_headers+0x1b5>
    51e5:	0f 1f 00             	nopl   (%rax)
    51e8:	66 0f 6f 05 80 3a 00 00 	movdqa 0x3a80(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    51f0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    51f8:	66 0f 6f 05 80 3a 00 00 	movdqa 0x3a80(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    5200:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5208:	e9 71 fd ff ff       	jmp    4f7e <send_headers+0x19e>
    520d:	0f 1f 00             	nopl   (%rax)
    5210:	66 0f 6f 05 18 3a 00 00 	movdqa 0x3a18(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    5218:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5220:	66 0f 6f 05 38 3a 00 00 	movdqa 0x3a38(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5228:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5230:	e9 32 fd ff ff       	jmp    4f67 <send_headers+0x187>
    5235:	0f 1f 00             	nopl   (%rax)
    5238:	66 0f 6f 05 30 3a 00 00 	movdqa 0x3a30(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    5240:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5248:	66 0f 6f 05 70 3a 00 00 	movdqa 0x3a70(%rip),%xmm0        # 8cc0 <_IO_stdin_used+0xcc0>
    5250:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5258:	e9 6f fd ff ff       	jmp    4fcc <send_headers+0x1ec>
    525d:	0f 1f 00             	nopl   (%rax)
    5260:	66 0f 6f 05 08 3a 00 00 	movdqa 0x3a08(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    5268:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5270:	66 0f 6f 05 38 3a 00 00 	movdqa 0x3a38(%rip),%xmm0        # 8cb0 <_IO_stdin_used+0xcb0>
    5278:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5280:	e9 30 fd ff ff       	jmp    4fb5 <send_headers+0x1d5>
    5285:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    528c:	89 db                	mov    %ebx,%ebx
    528e:	89 10                	mov    %edx,(%rax)
    5290:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5295:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5299:	e9 83 fd ff ff       	jmp    5021 <send_headers+0x241>
    529e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    52a5:	89 db                	mov    %ebx,%ebx
    52a7:	89 10                	mov    %edx,(%rax)
    52a9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    52ae:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    52b2:	e9 d5 fd ff ff       	jmp    508c <send_headers+0x2ac>
    52b7:	89 db                	mov    %ebx,%ebx
    52b9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    52bf:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    52c4:	e9 58 fd ff ff       	jmp    5021 <send_headers+0x241>
    52c9:	89 db                	mov    %ebx,%ebx
    52cb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    52d1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    52d6:	e9 b1 fd ff ff       	jmp    508c <send_headers+0x2ac>
    52db:	48 8b 0d 3e 5d 00 00 	mov    0x5d3e(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    52e2:	ba 28 00 00 00       	mov    $0x28,%edx
    52e7:	be 01 00 00 00       	mov    $0x1,%esi
    52ec:	48 8d 3d e5 32 00 00 	lea    0x32e5(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    52f3:	e8 38 d2 ff ff       	call   2530 <fwrite@plt>
    52f8:	bf 01 00 00 00       	mov    $0x1,%edi
    52fd:	e8 0e d2 ff ff       	call   2510 <exit@plt>
    5302:	e8 79 d0 ff ff       	call   2380 <__stack_chk_fail@plt>
    5307:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005310 <copy_file_contents>:
    5310:	f3 0f 1e fa          	endbr64
    5314:	41 55                	push   %r13
    5316:	49 89 d5             	mov    %rdx,%r13
    5319:	41 54                	push   %r12
    531b:	49 89 fc             	mov    %rdi,%r12
    531e:	48 89 f7             	mov    %rsi,%rdi
    5321:	55                   	push   %rbp
    5322:	53                   	push   %rbx
    5323:	48 89 f3             	mov    %rsi,%rbx
    5326:	48 83 ec 08          	sub    $0x8,%rsp
    532a:	e8 41 d1 ff ff       	call   2470 <malloc@plt>
    532f:	48 85 c0             	test   %rax,%rax
    5332:	74 6b                	je     539f <copy_file_contents+0x8f>
    5334:	4c 89 e7             	mov    %r12,%rdi
    5337:	48 89 c5             	mov    %rax,%rbp
    533a:	31 f6                	xor    %esi,%esi
    533c:	31 c0                	xor    %eax,%eax
    533e:	e8 9d d1 ff ff       	call   24e0 <open@plt>
    5343:	41 89 c4             	mov    %eax,%r12d
    5346:	85 c0                	test   %eax,%eax
    5348:	0f 88 88 d2 ff ff    	js     25d6 <copy_file_contents.cold>
    534e:	48 89 da             	mov    %rbx,%rdx
    5351:	48 89 ee             	mov    %rbp,%rsi
    5354:	89 c7                	mov    %eax,%edi
    5356:	e8 95 d0 ff ff       	call   23f0 <read@plt>
    535b:	48 98                	cltq
    535d:	48 39 d8             	cmp    %rbx,%rax
    5360:	7c 1e                	jl     5380 <copy_file_contents+0x70>
    5362:	44 89 e7             	mov    %r12d,%edi
    5365:	e8 66 d0 ff ff       	call   23d0 <close@plt>
    536a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    536e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    5372:	48 83 c4 08          	add    $0x8,%rsp
    5376:	5b                   	pop    %rbx
    5377:	5d                   	pop    %rbp
    5378:	41 5c                	pop    %r12
    537a:	41 5d                	pop    %r13
    537c:	c3                   	ret
    537d:	0f 1f 00             	nopl   (%rax)
    5380:	48 8b 0d 99 5c 00 00 	mov    0x5c99(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5387:	ba 1a 00 00 00       	mov    $0x1a,%edx
    538c:	be 01 00 00 00       	mov    $0x1,%esi
    5391:	48 8d 3d 5f 2d 00 00 	lea    0x2d5f(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    5398:	e8 93 d1 ff ff       	call   2530 <fwrite@plt>
    539d:	eb c3                	jmp    5362 <copy_file_contents+0x52>
    539f:	48 8b 0d 7a 5c 00 00 	mov    0x5c7a(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    53a6:	ba 28 00 00 00       	mov    $0x28,%edx
    53ab:	be 01 00 00 00       	mov    $0x1,%esi
    53b0:	48 8d 3d 21 32 00 00 	lea    0x3221(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    53b7:	e8 74 d1 ff ff       	call   2530 <fwrite@plt>
    53bc:	bf 01 00 00 00       	mov    $0x1,%edi
    53c1:	e8 4a d1 ff ff       	call   2510 <exit@plt>
    53c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000053d0 <add_write_request>:
    53d0:	f3 0f 1e fa          	endbr64
    53d4:	8b 46 44             	mov    0x44(%rsi),%eax
    53d7:	48 89 fa             	mov    %rdi,%rdx
    53da:	48 89 f7             	mov    %rsi,%rdi
    53dd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    53e3:	8d 70 01             	lea    0x1(%rax),%esi
    53e6:	48 8b 07             	mov    (%rdi),%rax
    53e9:	44 8b 00             	mov    (%rax),%r8d
    53ec:	f6 c1 02             	test   $0x2,%cl
    53ef:	74 00                	je     53f1 <add_write_request+0x21>
    53f1:	89 f0                	mov    %esi,%eax
    53f3:	44 29 c0             	sub    %r8d,%eax
    53f6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    53f9:	0f 82 e3 d1 ff ff    	jb     25e2 <add_write_request.cold>
    53ff:	c1 e9 0a             	shr    $0xa,%ecx
    5402:	48 83 ec 08          	sub    $0x8,%rsp
    5406:	8b 47 44             	mov    0x44(%rdi),%eax
    5409:	23 47 58             	and    0x58(%rdi),%eax
    540c:	83 e1 01             	and    $0x1,%ecx
    540f:	89 77 44             	mov    %esi,0x44(%rdi)
    5412:	8b 72 08             	mov    0x8(%rdx),%esi
    5415:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5419:	d3 e0                	shl    %cl,%eax
    541b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    541e:	48 c1 e0 06          	shl    $0x6,%rax
    5422:	48 03 47 38          	add    0x38(%rdi),%rax
    5426:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    542c:	89 70 04             	mov    %esi,0x4(%rax)
    542f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    5433:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    5439:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5441:	48 89 70 10          	mov    %rsi,0x10(%rax)
    5445:	89 48 18             	mov    %ecx,0x18(%rax)
    5448:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    544f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5457:	48 89 50 20          	mov    %rdx,0x20(%rax)
    545b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    545f:	e8 2c cf ff ff       	call   2390 <io_uring_submit@plt>
    5464:	31 c0                	xor    %eax,%eax
    5466:	48 83 c4 08          	add    $0x8,%rsp
    546a:	c3                   	ret
    546b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005470 <add_read_request>:
    5470:	f3 0f 1e fa          	endbr64
    5474:	41 55                	push   %r13
    5476:	41 89 fd             	mov    %edi,%r13d
    5479:	41 54                	push   %r12
    547b:	55                   	push   %rbp
    547c:	53                   	push   %rbx
    547d:	48 89 f3             	mov    %rsi,%rbx
    5480:	48 83 ec 08          	sub    $0x8,%rsp
    5484:	8b 46 44             	mov    0x44(%rsi),%eax
    5487:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    548d:	48 8b 16             	mov    (%rsi),%rdx
    5490:	83 c0 01             	add    $0x1,%eax
    5493:	8b 32                	mov    (%rdx),%esi
    5495:	f6 c1 02             	test   $0x2,%cl
    5498:	74 00                	je     549a <add_read_request+0x2a>
    549a:	89 c2                	mov    %eax,%edx
    549c:	29 f2                	sub    %esi,%edx
    549e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    54a1:	0f 82 4b d1 ff ff    	jb     25f2 <add_read_request.cold>
    54a7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    54aa:	c1 e9 0a             	shr    $0xa,%ecx
    54ad:	89 43 44             	mov    %eax,0x44(%rbx)
    54b0:	bf 20 00 00 00       	mov    $0x20,%edi
    54b5:	83 e1 01             	and    $0x1,%ecx
    54b8:	23 6b 58             	and    0x58(%rbx),%ebp
    54bb:	d3 e5                	shl    %cl,%ebp
    54bd:	48 c1 e5 06          	shl    $0x6,%rbp
    54c1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    54c5:	e8 a6 cf ff ff       	call   2470 <malloc@plt>
    54ca:	be 01 00 00 00       	mov    $0x1,%esi
    54cf:	bf 00 20 00 00       	mov    $0x2000,%edi
    54d4:	49 89 c4             	mov    %rax,%r12
    54d7:	e8 24 cf ff ff       	call   2400 <calloc@plt>
    54dc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    54e1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    54e5:	48 89 df             	mov    %rbx,%rdi
    54e8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    54ed:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    54f2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    54fb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    5503:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    5507:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    550b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    5512:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    551a:	48 89 45 10          	mov    %rax,0x10(%rbp)
    551e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    5526:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    552e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5532:	e8 59 ce ff ff       	call   2390 <io_uring_submit@plt>
    5537:	48 83 c4 08          	add    $0x8,%rsp
    553b:	31 c0                	xor    %eax,%eax
    553d:	5b                   	pop    %rbx
    553e:	5d                   	pop    %rbp
    553f:	41 5c                	pop    %r12
    5541:	41 5d                	pop    %r13
    5543:	c3                   	ret
    5544:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    554f:	90                   	nop

0000000000005550 <_send_static_string_content>:
    5550:	f3 0f 1e fa          	endbr64
    5554:	41 56                	push   %r14
    5556:	41 89 f6             	mov    %esi,%r14d
    5559:	41 55                	push   %r13
    555b:	49 89 fd             	mov    %rdi,%r13
    555e:	bf 20 00 00 00       	mov    $0x20,%edi
    5563:	41 54                	push   %r12
    5565:	55                   	push   %rbp
    5566:	48 89 d5             	mov    %rdx,%rbp
    5569:	53                   	push   %rbx
    556a:	e8 01 cf ff ff       	call   2470 <malloc@plt>
    556f:	48 85 c0             	test   %rax,%rax
    5572:	0f 84 dd 00 00 00    	je     5655 <_send_static_string_content+0x105>
    5578:	48 89 c3             	mov    %rax,%rbx
    557b:	4c 89 ef             	mov    %r13,%rdi
    557e:	e8 ed cd ff ff       	call   2370 <strlen@plt>
    5583:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    558a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    558e:	48 89 c7             	mov    %rax,%rdi
    5591:	49 89 c4             	mov    %rax,%r12
    5594:	e8 d7 ce ff ff       	call   2470 <malloc@plt>
    5599:	48 89 c7             	mov    %rax,%rdi
    559c:	48 85 c0             	test   %rax,%rax
    559f:	0f 84 b0 00 00 00    	je     5655 <_send_static_string_content+0x105>
    55a5:	48 89 43 10          	mov    %rax,0x10(%rbx)
    55a9:	4c 89 e2             	mov    %r12,%rdx
    55ac:	4c 89 ee             	mov    %r13,%rsi
    55af:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    55b3:	e8 88 ce ff ff       	call   2440 <memcpy@plt>
    55b8:	8b 45 44             	mov    0x44(%rbp),%eax
    55bb:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    55c1:	8d 50 01             	lea    0x1(%rax),%edx
    55c4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    55c8:	8b 30                	mov    (%rax),%esi
    55ca:	f6 c1 02             	test   $0x2,%cl
    55cd:	0f 85 7d 00 00 00    	jne    5650 <_send_static_string_content+0x100>
    55d3:	89 d0                	mov    %edx,%eax
    55d5:	29 f0                	sub    %esi,%eax
    55d7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    55da:	0f 82 1c d0 ff ff    	jb     25fc <_send_static_string_content.cold>
    55e0:	c1 e9 0a             	shr    $0xa,%ecx
    55e3:	8b 45 44             	mov    0x44(%rbp),%eax
    55e6:	23 45 58             	and    0x58(%rbp),%eax
    55e9:	89 55 44             	mov    %edx,0x44(%rbp)
    55ec:	83 e1 01             	and    $0x1,%ecx
    55ef:	8b 53 04             	mov    0x4(%rbx),%edx
    55f2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    55f8:	66 0f ef c0          	pxor   %xmm0,%xmm0
    55fc:	d3 e0                	shl    %cl,%eax
    55fe:	8b 4b 08             	mov    0x8(%rbx),%ecx
    5601:	48 89 ef             	mov    %rbp,%rdi
    5604:	48 c1 e0 06          	shl    $0x6,%rax
    5608:	48 03 45 38          	add    0x38(%rbp),%rax
    560c:	89 48 04             	mov    %ecx,0x4(%rax)
    560f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    5613:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    5619:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5621:	48 89 48 10          	mov    %rcx,0x10(%rax)
    5625:	89 50 18             	mov    %edx,0x18(%rax)
    5628:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    562f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5637:	48 89 58 20          	mov    %rbx,0x20(%rax)
    563b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    563f:	5b                   	pop    %rbx
    5640:	5d                   	pop    %rbp
    5641:	41 5c                	pop    %r12
    5643:	41 5d                	pop    %r13
    5645:	41 5e                	pop    %r14
    5647:	e9 44 cd ff ff       	jmp    2390 <io_uring_submit@plt>
    564c:	0f 1f 40 00          	nopl   0x0(%rax)
    5650:	e9 7e ff ff ff       	jmp    55d3 <_send_static_string_content+0x83>
    5655:	48 8b 0d c4 59 00 00 	mov    0x59c4(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    565c:	ba 28 00 00 00       	mov    $0x28,%edx
    5661:	be 01 00 00 00       	mov    $0x1,%esi
    5666:	48 8d 3d 6b 2f 00 00 	lea    0x2f6b(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    566d:	e8 be ce ff ff       	call   2530 <fwrite@plt>
    5672:	bf 01 00 00 00       	mov    $0x1,%edi
    5677:	e8 94 ce ff ff       	call   2510 <exit@plt>
    567c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005680 <handle_unimplemented_method>:
    5680:	f3 0f 1e fa          	endbr64
    5684:	48 89 f2             	mov    %rsi,%rdx
    5687:	89 fe                	mov    %edi,%esi
    5689:	48 8b 3d 88 59 00 00 	mov    0x5988(%rip),%rdi        # b018 <unimplemented_content>
    5690:	e9 bb fe ff ff       	jmp    5550 <_send_static_string_content>
    5695:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000056a0 <handle_http_404>:
    56a0:	f3 0f 1e fa          	endbr64
    56a4:	48 89 f2             	mov    %rsi,%rdx
    56a7:	89 fe                	mov    %edi,%esi
    56a9:	48 8b 3d 60 59 00 00 	mov    0x5960(%rip),%rdi        # b010 <http_404_content>
    56b0:	e9 9b fe ff ff       	jmp    5550 <_send_static_string_content>
    56b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000056c0 <handle_get_method>:
    56c0:	f3 0f 1e fa          	endbr64
    56c4:	41 56                	push   %r14
    56c6:	41 55                	push   %r13
    56c8:	49 89 d5             	mov    %rdx,%r13
    56cb:	41 54                	push   %r12
    56cd:	41 89 f4             	mov    %esi,%r12d
    56d0:	55                   	push   %rbp
    56d1:	48 89 fd             	mov    %rdi,%rbp
    56d4:	53                   	push   %rbx
    56d5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    56dc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    56e5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    56ed:	31 c0                	xor    %eax,%eax
    56ef:	e8 7c cc ff ff       	call   2370 <strlen@plt>
    56f4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    56f9:	48 89 c3             	mov    %rax,%rbx
    56fc:	0f 84 b6 00 00 00    	je     57b8 <handle_get_method+0xf8>
    5702:	b8 69 63 00 00       	mov    $0x6369,%eax
    5707:	48 89 ee             	mov    %rbp,%rsi
    570a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    570e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5713:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    571b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5723:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    572e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    5736:	e8 e5 cc ff ff       	call   2420 <__memcpy_chk@plt>
    573b:	48 89 e6             	mov    %rsp,%rsi
    573e:	4c 89 f7             	mov    %r14,%rdi
    5741:	e8 ea cc ff ff       	call   2430 <stat@plt>
    5746:	83 f8 ff             	cmp    $0xffffffff,%eax
    5749:	0f 84 d3 00 00 00    	je     5822 <handle_get_method+0x162>
    574f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5753:	25 00 f0 00 00       	and    $0xf000,%eax
    5758:	3d 00 80 00 00       	cmp    $0x8000,%eax
    575d:	0f 84 f5 00 00 00    	je     5858 <handle_get_method+0x198>
    5763:	48 8b 3d a6 58 00 00 	mov    0x58a6(%rip),%rdi        # b010 <http_404_content>
    576a:	4c 89 ea             	mov    %r13,%rdx
    576d:	44 89 e6             	mov    %r12d,%esi
    5770:	e8 db fd ff ff       	call   5550 <_send_static_string_content>
    5775:	4c 89 f2             	mov    %r14,%rdx
    5778:	bf 01 00 00 00       	mov    $0x1,%edi
    577d:	31 c0                	xor    %eax,%eax
    577f:	48 8d 35 c1 29 00 00 	lea    0x29c1(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5786:	e8 25 cd ff ff       	call   24b0 <__printf_chk@plt>
    578b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5793:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    579c:	0f 85 20 01 00 00    	jne    58c2 <handle_get_method+0x202>
    57a2:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    57a9:	5b                   	pop    %rbx
    57aa:	5d                   	pop    %rbp
    57ab:	41 5c                	pop    %r12
    57ad:	41 5d                	pop    %r13
    57af:	41 5e                	pop    %r14
    57b1:	c3                   	ret
    57b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    57b8:	ba 69 63 00 00       	mov    $0x6369,%edx
    57bd:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    57c5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    57ca:	48 89 ee             	mov    %rbp,%rsi
    57cd:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    57d5:	48 89 c2             	mov    %rax,%rdx
    57d8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    57e0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    57eb:	e8 30 cc ff ff       	call   2420 <__memcpy_chk@plt>
    57f0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    57f5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    57fa:	48 8d 35 11 29 00 00 	lea    0x2911(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    5801:	48 29 d9             	sub    %rbx,%rcx
    5804:	ba 0b 00 00 00       	mov    $0xb,%edx
    5809:	e8 12 cc ff ff       	call   2420 <__memcpy_chk@plt>
    580e:	48 89 e6             	mov    %rsp,%rsi
    5811:	4c 89 f7             	mov    %r14,%rdi
    5814:	e8 17 cc ff ff       	call   2430 <stat@plt>
    5819:	83 f8 ff             	cmp    $0xffffffff,%eax
    581c:	0f 85 2d ff ff ff    	jne    574f <handle_get_method+0x8f>
    5822:	4c 89 f2             	mov    %r14,%rdx
    5825:	48 89 e9             	mov    %rbp,%rcx
    5828:	48 8d 35 ee 28 00 00 	lea    0x28ee(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    582f:	31 c0                	xor    %eax,%eax
    5831:	bf 01 00 00 00       	mov    $0x1,%edi
    5836:	e8 75 cc ff ff       	call   24b0 <__printf_chk@plt>
    583b:	48 8b 3d ce 57 00 00 	mov    0x57ce(%rip),%rdi        # b010 <http_404_content>
    5842:	4c 89 ea             	mov    %r13,%rdx
    5845:	44 89 e6             	mov    %r12d,%esi
    5848:	e8 03 fd ff ff       	call   5550 <_send_static_string_content>
    584d:	e9 39 ff ff ff       	jmp    578b <handle_get_method+0xcb>
    5852:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5858:	bf 70 00 00 00       	mov    $0x70,%edi
    585d:	e8 0e cc ff ff       	call   2470 <malloc@plt>
    5862:	48 89 c3             	mov    %rax,%rbx
    5865:	48 85 c0             	test   %rax,%rax
    5868:	74 5d                	je     58c7 <handle_get_method+0x207>
    586a:	44 89 60 08          	mov    %r12d,0x8(%rax)
    586e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5873:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5877:	4c 89 f7             	mov    %r14,%rdi
    587a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    5881:	e8 5a f5 ff ff       	call   4de0 <send_headers>
    5886:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    588b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    588f:	4c 89 f7             	mov    %r14,%rdi
    5892:	e8 79 fa ff ff       	call   5310 <copy_file_contents>
    5897:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    589c:	4c 89 f2             	mov    %r14,%rdx
    589f:	31 c0                	xor    %eax,%eax
    58a1:	48 8d 35 8d 28 00 00 	lea    0x288d(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    58a8:	bf 01 00 00 00       	mov    $0x1,%edi
    58ad:	e8 fe cb ff ff       	call   24b0 <__printf_chk@plt>
    58b2:	4c 89 ee             	mov    %r13,%rsi
    58b5:	48 89 df             	mov    %rbx,%rdi
    58b8:	e8 13 fb ff ff       	call   53d0 <add_write_request>
    58bd:	e9 c9 fe ff ff       	jmp    578b <handle_get_method+0xcb>
    58c2:	e8 b9 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    58c7:	48 8b 0d 52 57 00 00 	mov    0x5752(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    58ce:	ba 28 00 00 00       	mov    $0x28,%edx
    58d3:	be 01 00 00 00       	mov    $0x1,%esi
    58d8:	48 8d 3d f9 2c 00 00 	lea    0x2cf9(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    58df:	e8 4c cc ff ff       	call   2530 <fwrite@plt>
    58e4:	bf 01 00 00 00       	mov    $0x1,%edi
    58e9:	e8 22 cc ff ff       	call   2510 <exit@plt>
    58ee:	66 90                	xchg   %ax,%ax

00000000000058f0 <handle_http_method>:
    58f0:	f3 0f 1e fa          	endbr64
    58f4:	41 57                	push   %r15
    58f6:	41 56                	push   %r14
    58f8:	4c 8d 35 ad 27 00 00 	lea    0x27ad(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
    58ff:	41 55                	push   %r13
    5901:	49 89 d5             	mov    %rdx,%r13
    5904:	41 54                	push   %r12
    5906:	41 89 f4             	mov    %esi,%r12d
    5909:	4c 89 f6             	mov    %r14,%rsi
    590c:	55                   	push   %rbp
    590d:	53                   	push   %rbx
    590e:	48 83 ec 18          	sub    $0x18,%rsp
    5912:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    591b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5920:	31 c0                	xor    %eax,%eax
    5922:	49 89 e7             	mov    %rsp,%r15
    5925:	4c 89 fa             	mov    %r15,%rdx
    5928:	e8 b3 ca ff ff       	call   23e0 <strtok_r@plt>
    592d:	48 0f be 18          	movsbq (%rax),%rbx
    5931:	48 89 c5             	mov    %rax,%rbp
    5934:	84 db                	test   %bl,%bl
    5936:	74 1d                	je     5955 <handle_http_method+0x65>
    5938:	e8 53 cc ff ff       	call   2590 <__ctype_tolower_loc@plt>
    593d:	48 89 ea             	mov    %rbp,%rdx
    5940:	48 8b 08             	mov    (%rax),%rcx
    5943:	48 83 c2 01          	add    $0x1,%rdx
    5947:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    594a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    594d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5951:	84 db                	test   %bl,%bl
    5953:	75 eb                	jne    5940 <handle_http_method+0x50>
    5955:	4c 89 fa             	mov    %r15,%rdx
    5958:	4c 89 f6             	mov    %r14,%rsi
    595b:	31 ff                	xor    %edi,%edi
    595d:	e8 7e ca ff ff       	call   23e0 <strtok_r@plt>
    5962:	48 8d 35 f1 27 00 00 	lea    0x27f1(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    5969:	48 89 ef             	mov    %rbp,%rdi
    596c:	48 89 c3             	mov    %rax,%rbx
    596f:	e8 9c ca ff ff       	call   2410 <strcmp@plt>
    5974:	4c 89 ea             	mov    %r13,%rdx
    5977:	44 89 e6             	mov    %r12d,%esi
    597a:	85 c0                	test   %eax,%eax
    597c:	75 2a                	jne    59a8 <handle_http_method+0xb8>
    597e:	48 89 df             	mov    %rbx,%rdi
    5981:	e8 3a fd ff ff       	call   56c0 <handle_get_method>
    5986:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    598b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5994:	75 20                	jne    59b6 <handle_http_method+0xc6>
    5996:	48 83 c4 18          	add    $0x18,%rsp
    599a:	5b                   	pop    %rbx
    599b:	5d                   	pop    %rbp
    599c:	41 5c                	pop    %r12
    599e:	41 5d                	pop    %r13
    59a0:	41 5e                	pop    %r14
    59a2:	41 5f                	pop    %r15
    59a4:	c3                   	ret
    59a5:	0f 1f 00             	nopl   (%rax)
    59a8:	48 8b 3d 69 56 00 00 	mov    0x5669(%rip),%rdi        # b018 <unimplemented_content>
    59af:	e8 9c fb ff ff       	call   5550 <_send_static_string_content>
    59b4:	eb d0                	jmp    5986 <handle_http_method+0x96>
    59b6:	e8 c5 c9 ff ff       	call   2380 <__stack_chk_fail@plt>
    59bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000059c0 <get_line>:
    59c0:	f3 0f 1e fa          	endbr64
    59c4:	85 d2                	test   %edx,%edx
    59c6:	7e 38                	jle    5a00 <get_line+0x40>
    59c8:	48 63 d2             	movslq %edx,%rdx
    59cb:	48 83 c7 01          	add    $0x1,%rdi
    59cf:	48 01 f2             	add    %rsi,%rdx
    59d2:	eb 11                	jmp    59e5 <get_line+0x25>
    59d4:	0f 1f 40 00          	nopl   0x0(%rax)
    59d8:	48 83 c6 01          	add    $0x1,%rsi
    59dc:	48 83 c7 01          	add    $0x1,%rdi
    59e0:	48 39 d6             	cmp    %rdx,%rsi
    59e3:	74 1b                	je     5a00 <get_line+0x40>
    59e5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    59e9:	88 06                	mov    %al,(%rsi)
    59eb:	3c 0d                	cmp    $0xd,%al
    59ed:	75 e9                	jne    59d8 <get_line+0x18>
    59ef:	80 3f 0a             	cmpb   $0xa,(%rdi)
    59f2:	75 e4                	jne    59d8 <get_line+0x18>
    59f4:	c6 06 00             	movb   $0x0,(%rsi)
    59f7:	31 c0                	xor    %eax,%eax
    59f9:	c3                   	ret
    59fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5a00:	b8 01 00 00 00       	mov    $0x1,%eax
    5a05:	c3                   	ret
    5a06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005a10 <handle_client_request>:
    5a10:	f3 0f 1e fa          	endbr64
    5a14:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    5a1b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    5a1f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5a28:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5a30:	31 c0                	xor    %eax,%eax
    5a32:	49 89 e2             	mov    %rsp,%r10
    5a35:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    5a3d:	4c 89 d0             	mov    %r10,%rax
    5a40:	eb 13                	jmp    5a55 <handle_client_request+0x45>
    5a42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5a48:	48 83 c0 01          	add    $0x1,%rax
    5a4c:	48 83 c1 01          	add    $0x1,%rcx
    5a50:	4c 39 c8             	cmp    %r9,%rax
    5a53:	74 4b                	je     5aa0 <handle_client_request+0x90>
    5a55:	44 0f b6 01          	movzbl (%rcx),%r8d
    5a59:	44 88 00             	mov    %r8b,(%rax)
    5a5c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5a60:	75 e6                	jne    5a48 <handle_client_request+0x38>
    5a62:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5a66:	75 e0                	jne    5a48 <handle_client_request+0x38>
    5a68:	c6 00 00             	movb   $0x0,(%rax)
    5a6b:	8b 47 08             	mov    0x8(%rdi),%eax
    5a6e:	48 89 f2             	mov    %rsi,%rdx
    5a71:	4c 89 d7             	mov    %r10,%rdi
    5a74:	89 c6                	mov    %eax,%esi
    5a76:	e8 75 fe ff ff       	call   58f0 <handle_http_method>
    5a7b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5a83:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5a8c:	75 39                	jne    5ac7 <handle_client_request+0xb7>
    5a8e:	31 c0                	xor    %eax,%eax
    5a90:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5a97:	c3                   	ret
    5a98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5aa0:	48 8b 0d 79 55 00 00 	mov    0x5579(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5aa7:	ba 12 00 00 00       	mov    $0x12,%edx
    5aac:	be 01 00 00 00       	mov    $0x1,%esi
    5ab1:	48 8d 3d a6 26 00 00 	lea    0x26a6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5ab8:	e8 73 ca ff ff       	call   2530 <fwrite@plt>
    5abd:	bf 01 00 00 00       	mov    $0x1,%edi
    5ac2:	e8 49 ca ff ff       	call   2510 <exit@plt>
    5ac7:	e8 b4 c8 ff ff       	call   2380 <__stack_chk_fail@plt>
    5acc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005ad0 <add_accept_request>:
    5ad0:	f3 0f 1e fa          	endbr64
    5ad4:	55                   	push   %rbp
    5ad5:	53                   	push   %rbx
    5ad6:	48 89 cb             	mov    %rcx,%rbx
    5ad9:	48 83 ec 08          	sub    $0x8,%rsp
    5add:	8b 41 44             	mov    0x44(%rcx),%eax
    5ae0:	4c 8b 03             	mov    (%rbx),%r8
    5ae3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    5ae9:	83 c0 01             	add    $0x1,%eax
    5aec:	45 8b 08             	mov    (%r8),%r9d
    5aef:	f6 c1 02             	test   $0x2,%cl
    5af2:	74 00                	je     5af4 <add_accept_request+0x24>
    5af4:	41 89 c0             	mov    %eax,%r8d
    5af7:	45 29 c8             	sub    %r9d,%r8d
    5afa:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    5afe:	0f 82 08 cb ff ff    	jb     260c <add_accept_request.cold>
    5b04:	c1 e9 0a             	shr    $0xa,%ecx
    5b07:	8b 6b 44             	mov    0x44(%rbx),%ebp
    5b0a:	23 6b 58             	and    0x58(%rbx),%ebp
    5b0d:	89 43 44             	mov    %eax,0x44(%rbx)
    5b10:	83 e1 01             	and    $0x1,%ecx
    5b13:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5b17:	d3 e5                	shl    %cl,%ebp
    5b19:	48 c1 e5 06          	shl    $0x6,%rbp
    5b1d:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5b21:	89 7d 04             	mov    %edi,0x4(%rbp)
    5b24:	bf 10 00 00 00       	mov    $0x10,%edi
    5b29:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    5b30:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    5b34:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    5b38:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    5b40:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    5b48:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5b4c:	e8 1f c9 ff ff       	call   2470 <malloc@plt>
    5b51:	48 89 df             	mov    %rbx,%rdi
    5b54:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    5b5a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    5b5e:	48 83 c4 08          	add    $0x8,%rsp
    5b62:	5b                   	pop    %rbx
    5b63:	5d                   	pop    %rbp
    5b64:	e9 27 c8 ff ff       	jmp    2390 <io_uring_submit@plt>
    5b69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005b70 <io_thread>:
    5b70:	f3 0f 1e fa          	endbr64
    5b74:	41 57                	push   %r15
    5b76:	31 d2                	xor    %edx,%edx
    5b78:	41 56                	push   %r14
    5b7a:	41 55                	push   %r13
    5b7c:	41 54                	push   %r12
    5b7e:	55                   	push   %rbp
    5b7f:	48 89 fd             	mov    %rdi,%rbp
    5b82:	53                   	push   %rbx
    5b83:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    5b8a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5b93:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    5b9b:	48 8b 47 58          	mov    0x58(%rdi),%rax
    5b9f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5ba4:	bf 00 01 00 00       	mov    $0x100,%edi
    5ba9:	48 89 de             	mov    %rbx,%rsi
    5bac:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5bb0:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5bb5:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5bba:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    5bbf:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5bc4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    5bcc:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5bd1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5bd9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5bde:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5be6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5beb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5bf3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5bf8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5c00:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5c05:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    5c0d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5c15:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5c1d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5c25:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5c2d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5c35:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5c3d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5c45:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5c4d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5c55:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5c5d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5c64:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    5c6c:	e8 df c7 ff ff       	call   2450 <io_uring_queue_init@plt>
    5c71:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5c75:	31 f6                	xor    %esi,%esi
    5c77:	e8 d4 c8 ff ff       	call   2550 <io_uring_register_eventfd@plt>
    5c7c:	31 d2                	xor    %edx,%edx
    5c7e:	be 01 00 00 00       	mov    $0x1,%esi
    5c83:	bf 02 00 00 00       	mov    $0x2,%edi
    5c88:	e8 23 c9 ff ff       	call   25b0 <socket@plt>
    5c8d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5c90:	0f 84 b8 c9 ff ff    	je     264e <io_thread.cold+0x38>
    5c96:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5c9b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5ca1:	89 c7                	mov    %eax,%edi
    5ca3:	41 89 c4             	mov    %eax,%r12d
    5ca6:	ba 02 00 00 00       	mov    $0x2,%edx
    5cab:	be 01 00 00 00       	mov    $0x1,%esi
    5cb0:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    5cb8:	e8 83 c6 ff ff       	call   2340 <setsockopt@plt>
    5cbd:	85 c0                	test   %eax,%eax
    5cbf:	0f 88 5d c9 ff ff    	js     2622 <io_thread.cold+0xc>
    5cc5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    5cca:	ba 10 00 00 00       	mov    $0x10,%edx
    5ccf:	44 89 e7             	mov    %r12d,%edi
    5cd2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5cdb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    5ce3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
    5ceb:	e8 d0 c7 ff ff       	call   24c0 <bind@plt>
    5cf0:	85 c0                	test   %eax,%eax
    5cf2:	0f 88 62 c9 ff ff    	js     265a <io_thread.cold+0x44>
    5cf8:	be 0a 00 00 00       	mov    $0xa,%esi
    5cfd:	44 89 e7             	mov    %r12d,%edi
    5d00:	e8 7b c7 ff ff       	call   2480 <listen@plt>
    5d05:	85 c0                	test   %eax,%eax
    5d07:	0f 88 21 c9 ff ff    	js     262e <io_thread.cold+0x18>
    5d0d:	ba db 18 00 00       	mov    $0x18db,%edx
    5d12:	48 8d 35 8a 24 00 00 	lea    0x248a(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5d19:	bf 01 00 00 00       	mov    $0x1,%edi
    5d1e:	31 c0                	xor    %eax,%eax
    5d20:	e8 8b c7 ff ff       	call   24b0 <__printf_chk@plt>
    5d25:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5d2a:	48 89 d9             	mov    %rbx,%rcx
    5d2d:	44 89 e7             	mov    %r12d,%edi
    5d30:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5d35:	48 89 c6             	mov    %rax,%rsi
    5d38:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5d3d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    5d42:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    5d4a:	e8 81 fd ff ff       	call   5ad0 <add_accept_request>
    5d4f:	bf 01 00 00 00       	mov    $0x1,%edi
    5d54:	be 10 00 00 00       	mov    $0x10,%esi
    5d59:	e8 a2 c6 ff ff       	call   2400 <calloc@plt>
    5d5e:	bf 0a 00 00 00       	mov    $0xa,%edi
    5d63:	49 89 c5             	mov    %rax,%r13
    5d66:	e8 05 c7 ff ff       	call   2470 <malloc@plt>
    5d6b:	48 85 c0             	test   %rax,%rax
    5d6e:	0f 84 ae 04 00 00    	je     6222 <io_thread+0x6b2>
    5d74:	49 89 45 00          	mov    %rax,0x0(%r13)
    5d78:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5d7f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5d86:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    5d8e:	8d 50 01             	lea    0x1(%rax),%edx
    5d91:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5d96:	8b 30                	mov    (%rax),%esi
    5d98:	f6 c1 02             	test   $0x2,%cl
    5d9b:	0f 85 0f 04 00 00    	jne    61b0 <io_thread+0x640>
    5da1:	89 d0                	mov    %edx,%eax
    5da3:	29 f0                	sub    %esi,%eax
    5da5:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5dac:	0f 82 92 c8 ff ff    	jb     2644 <io_thread.cold+0x2e>
    5db2:	c1 e9 0a             	shr    $0xa,%ecx
    5db5:	48 8d 75 60          	lea    0x60(%rbp),%rsi
    5db9:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5dbd:	48 89 df             	mov    %rbx,%rdi
    5dc0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5dc7:	83 e1 01             	and    $0x1,%ecx
    5dca:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5dd1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5dd8:	d3 e0                	shl    %cl,%eax
    5dda:	8b 55 60             	mov    0x60(%rbp),%edx
    5ddd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5de2:	48 c1 e0 06          	shl    $0x6,%rax
    5de6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5dee:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5df4:	89 50 04             	mov    %edx,0x4(%rax)
    5df7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5dff:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5e03:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5e0b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5e13:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5e17:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5e1b:	e8 70 c5 ff ff       	call   2390 <io_uring_submit@plt>
    5e20:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5e24:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5e29:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5e31:	0f 85 d7 01 00 00    	jne    600e <io_thread+0x49e>
    5e37:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5e3c:	4d 89 ce             	mov    %r9,%r14
    5e3f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5e44:	0f 1f 40 00          	nopl   0x0(%rax)
    5e48:	48 8d 3d 6a 23 00 00 	lea    0x236a(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5e4f:	e8 dc c4 ff ff       	call   2330 <puts@plt>
    5e54:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5e5b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    5e62:	c1 e9 0b             	shr    $0xb,%ecx
    5e65:	83 e1 01             	and    $0x1,%ecx
    5e68:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5e70:	8b 00                	mov    (%rax),%eax
    5e72:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5e7a:	8b 16                	mov    (%rsi),%edx
    5e7c:	39 d0                	cmp    %edx,%eax
    5e7e:	74 36                	je     5eb6 <io_thread+0x346>
    5e80:	89 f8                	mov    %edi,%eax
    5e82:	21 d0                	and    %edx,%eax
    5e84:	d3 e0                	shl    %cl,%eax
    5e86:	48 c1 e0 04          	shl    $0x4,%rax
    5e8a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    5e92:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5e9a:	0f 85 a8 01 00 00    	jne    6048 <io_thread+0x4d8>
    5ea0:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5ea4:	0f 85 0e 03 00 00    	jne    61b8 <io_thread+0x648>
    5eaa:	8b 40 08             	mov    0x8(%rax),%eax
    5ead:	83 c2 01             	add    $0x1,%edx
    5eb0:	89 16                	mov    %edx,(%rsi)
    5eb2:	85 c0                	test   %eax,%eax
    5eb4:	79 b2                	jns    5e68 <io_thread+0x2f8>
    5eb6:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    5ebf:	90                   	nop
    5ec0:	45 31 c0             	xor    %r8d,%r8d
    5ec3:	31 d2                	xor    %edx,%edx
    5ec5:	b9 01 00 00 00       	mov    $0x1,%ecx
    5eca:	4c 89 f6             	mov    %r14,%rsi
    5ecd:	48 89 df             	mov    %rbx,%rdi
    5ed0:	e8 cb c5 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5ed5:	41 89 c7             	mov    %eax,%r15d
    5ed8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5edd:	48 83 38 01          	cmpq   $0x1,(%rax)
    5ee1:	0f 84 e1 02 00 00    	je     61c8 <io_thread+0x658>
    5ee7:	48 8d 3d f1 22 00 00 	lea    0x22f1(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5eee:	e8 3d c4 ff ff       	call   2330 <puts@plt>
    5ef3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5ef8:	4c 8b 22             	mov    (%rdx),%r12
    5efb:	45 85 ff             	test   %r15d,%r15d
    5efe:	0f 88 12 c7 ff ff    	js     2616 <io_thread.cold>
    5f04:	8b 42 08             	mov    0x8(%rdx),%eax
    5f07:	45 8b 04 24          	mov    (%r12),%r8d
    5f0b:	85 c0                	test   %eax,%eax
    5f0d:	0f 88 d5 02 00 00    	js     61e8 <io_thread+0x678>
    5f13:	41 83 f8 01          	cmp    $0x1,%r8d
    5f17:	0f 84 7b 01 00 00    	je     6098 <io_thread+0x528>
    5f1d:	41 83 f8 02          	cmp    $0x2,%r8d
    5f21:	0f 84 a1 01 00 00    	je     60c8 <io_thread+0x558>
    5f27:	45 85 c0             	test   %r8d,%r8d
    5f2a:	0f 85 50 01 00 00    	jne    6080 <io_thread+0x510>
    5f30:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5f35:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5f3a:	48 89 d9             	mov    %rbx,%rcx
    5f3d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5f41:	e8 8a fb ff ff       	call   5ad0 <add_accept_request>
    5f46:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f4b:	48 89 de             	mov    %rbx,%rsi
    5f4e:	8b 78 08             	mov    0x8(%rax),%edi
    5f51:	e8 1a f5 ff ff       	call   5470 <add_read_request>
    5f56:	4c 89 e7             	mov    %r12,%rdi
    5f59:	e8 a2 c3 ff ff       	call   2300 <free@plt>
    5f5e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f63:	48 85 c0             	test   %rax,%rax
    5f66:	0f 85 14 01 00 00    	jne    6080 <io_thread+0x510>
    5f6c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5f73:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5f7a:	8d 50 01             	lea    0x1(%rax),%edx
    5f7d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5f82:	8b 30                	mov    (%rax),%esi
    5f84:	f6 c1 02             	test   $0x2,%cl
    5f87:	74 00                	je     5f89 <io_thread+0x419>
    5f89:	89 d0                	mov    %edx,%eax
    5f8b:	29 f0                	sub    %esi,%eax
    5f8d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5f94:	0f 82 a0 c6 ff ff    	jb     263a <io_thread.cold+0x24>
    5f9a:	c1 e9 0a             	shr    $0xa,%ecx
    5f9d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5fa2:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5fa6:	48 89 df             	mov    %rbx,%rdi
    5fa9:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5fb0:	83 e1 01             	and    $0x1,%ecx
    5fb3:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5fba:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5fc1:	d3 e0                	shl    %cl,%eax
    5fc3:	8b 55 60             	mov    0x60(%rbp),%edx
    5fc6:	48 c1 e0 06          	shl    $0x6,%rax
    5fca:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5fd2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5fd8:	89 50 04             	mov    %edx,0x4(%rax)
    5fdb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5fe3:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5fe7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5fef:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5ff7:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5ffb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5fff:	e8 8c c3 ff ff       	call   2390 <io_uring_submit@plt>
    6004:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    6008:	0f 84 3a fe ff ff    	je     5e48 <io_thread+0x2d8>
    600e:	48 8d 3d 03 22 00 00 	lea    0x2203(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    6015:	e8 16 c3 ff ff       	call   2330 <puts@plt>
    601a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    6022:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    602b:	0f 85 18 02 00 00    	jne    6249 <io_thread+0x6d9>
    6031:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    6038:	31 c0                	xor    %eax,%eax
    603a:	5b                   	pop    %rbx
    603b:	5d                   	pop    %rbp
    603c:	41 5c                	pop    %r12
    603e:	41 5d                	pop    %r13
    6040:	41 5e                	pop    %r14
    6042:	41 5f                	pop    %r15
    6044:	c3                   	ret
    6045:	0f 1f 00             	nopl   (%rax)
    6048:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    604d:	48 85 c0             	test   %rax,%rax
    6050:	0f 84 6a fe ff ff    	je     5ec0 <io_thread+0x350>
    6056:	48 83 38 01          	cmpq   $0x1,(%rax)
    605a:	0f 84 68 01 00 00    	je     61c8 <io_thread+0x658>
    6060:	48 8d 3d 78 21 00 00 	lea    0x2178(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    6067:	e8 c4 c2 ff ff       	call   2330 <puts@plt>
    606c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    6071:	4c 8b 22             	mov    (%rdx),%r12
    6074:	e9 8b fe ff ff       	jmp    5f04 <io_thread+0x394>
    6079:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6080:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    6088:	8b 02                	mov    (%rdx),%eax
    608a:	83 c0 01             	add    $0x1,%eax
    608d:	89 02                	mov    %eax,(%rdx)
    608f:	e9 d8 fe ff ff       	jmp    5f6c <io_thread+0x3fc>
    6094:	0f 1f 40 00          	nopl   0x0(%rax)
    6098:	85 c0                	test   %eax,%eax
    609a:	75 74                	jne    6110 <io_thread+0x5a0>
    609c:	48 8b 0d 7d 4f 00 00 	mov    0x4f7d(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    60a3:	ba 0f 00 00 00       	mov    $0xf,%edx
    60a8:	be 01 00 00 00       	mov    $0x1,%esi
    60ad:	48 8d 3d 54 21 00 00 	lea    0x2154(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    60b4:	e8 77 c4 ff ff       	call   2530 <fwrite@plt>
    60b9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    60be:	e9 a0 fe ff ff       	jmp    5f63 <io_thread+0x3f3>
    60c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    60c8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    60cd:	45 31 ff             	xor    %r15d,%r15d
    60d0:	85 c0                	test   %eax,%eax
    60d2:	7e 20                	jle    60f4 <io_thread+0x584>
    60d4:	0f 1f 40 00          	nopl   0x0(%rax)
    60d8:	4c 89 f8             	mov    %r15,%rax
    60db:	49 83 c7 01          	add    $0x1,%r15
    60df:	48 c1 e0 04          	shl    $0x4,%rax
    60e3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    60e8:	e8 13 c2 ff ff       	call   2300 <free@plt>
    60ed:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    60f2:	7f e4                	jg     60d8 <io_thread+0x568>
    60f4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    60f9:	e8 d2 c2 ff ff       	call   23d0 <close@plt>
    60fe:	4c 89 e7             	mov    %r12,%rdi
    6101:	e8 fa c1 ff ff       	call   2300 <free@plt>
    6106:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    610b:	e9 53 fe ff ff       	jmp    5f63 <io_thread+0x3f3>
    6110:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    6115:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    611a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    6122:	eb 11                	jmp    6135 <io_thread+0x5c5>
    6124:	0f 1f 40 00          	nopl   0x0(%rax)
    6128:	48 83 c0 01          	add    $0x1,%rax
    612c:	48 83 c2 01          	add    $0x1,%rdx
    6130:	48 39 c6             	cmp    %rax,%rsi
    6133:	74 4b                	je     6180 <io_thread+0x610>
    6135:	0f b6 0a             	movzbl (%rdx),%ecx
    6138:	88 08                	mov    %cl,(%rax)
    613a:	80 f9 0d             	cmp    $0xd,%cl
    613d:	75 e9                	jne    6128 <io_thread+0x5b8>
    613f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    6143:	75 e3                	jne    6128 <io_thread+0x5b8>
    6145:	c6 00 00             	movb   $0x0,(%rax)
    6148:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    614d:	48 89 da             	mov    %rbx,%rdx
    6150:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    6155:	e8 96 f7 ff ff       	call   58f0 <handle_http_method>
    615a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    615f:	e8 9c c1 ff ff       	call   2300 <free@plt>
    6164:	4c 89 e7             	mov    %r12,%rdi
    6167:	e8 94 c1 ff ff       	call   2300 <free@plt>
    616c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    6171:	e9 ed fd ff ff       	jmp    5f63 <io_thread+0x3f3>
    6176:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6180:	48 8b 0d 99 4e 00 00 	mov    0x4e99(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6187:	ba 12 00 00 00       	mov    $0x12,%edx
    618c:	be 01 00 00 00       	mov    $0x1,%esi
    6191:	48 8d 3d c6 1f 00 00 	lea    0x1fc6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6198:	e8 93 c3 ff ff       	call   2530 <fwrite@plt>
    619d:	bf 01 00 00 00       	mov    $0x1,%edi
    61a2:	e8 69 c3 ff ff       	call   2510 <exit@plt>
    61a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    61b0:	e9 ec fb ff ff       	jmp    5da1 <io_thread+0x231>
    61b5:	0f 1f 00             	nopl   (%rax)
    61b8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    61bd:	e9 94 fe ff ff       	jmp    6056 <io_thread+0x4e6>
    61c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    61c8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    61d0:	48 8d 3d f4 1f 00 00 	lea    0x1ff4(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    61d7:	8b 02                	mov    (%rdx),%eax
    61d9:	83 c0 01             	add    $0x1,%eax
    61dc:	89 02                	mov    %eax,(%rdx)
    61de:	e8 4d c1 ff ff       	call   2330 <puts@plt>
    61e3:	e9 26 fe ff ff       	jmp    600e <io_thread+0x49e>
    61e8:	f7 d8                	neg    %eax
    61ea:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    61ef:	89 c7                	mov    %eax,%edi
    61f1:	e8 7a c3 ff ff       	call   2570 <strerror@plt>
    61f6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    61fb:	be 01 00 00 00       	mov    $0x1,%esi
    6200:	48 8b 3d 19 4e 00 00 	mov    0x4e19(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    6207:	48 89 c1             	mov    %rax,%rcx
    620a:	48 8d 15 f7 23 00 00 	lea    0x23f7(%rip),%rdx        # 8608 <_IO_stdin_used+0x608>
    6211:	31 c0                	xor    %eax,%eax
    6213:	e8 28 c3 ff ff       	call   2540 <__fprintf_chk@plt>
    6218:	bf 01 00 00 00       	mov    $0x1,%edi
    621d:	e8 ee c2 ff ff       	call   2510 <exit@plt>
    6222:	48 8b 0d f7 4d 00 00 	mov    0x4df7(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6229:	ba 28 00 00 00       	mov    $0x28,%edx
    622e:	be 01 00 00 00       	mov    $0x1,%esi
    6233:	48 8d 3d 9e 23 00 00 	lea    0x239e(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    623a:	e8 f1 c2 ff ff       	call   2530 <fwrite@plt>
    623f:	bf 01 00 00 00       	mov    $0x1,%edi
    6244:	e8 c7 c2 ff ff       	call   2510 <exit@plt>
    6249:	e8 32 c1 ff ff       	call   2380 <__stack_chk_fail@plt>
    624e:	66 90                	xchg   %ax,%ax

0000000000006250 <barriered_work_ingest>:
    6250:	f3 0f 1e fa          	endbr64
    6254:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    625b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    6261:	85 c9                	test   %ecx,%ecx
    6263:	0f 8e ea 00 00 00    	jle    6353 <barriered_work_ingest+0x103>
    6269:	41 56                	push   %r14
    626b:	41 55                	push   %r13
    626d:	45 31 ed             	xor    %r13d,%r13d
    6270:	41 54                	push   %r12
    6272:	49 89 fc             	mov    %rdi,%r12
    6275:	55                   	push   %rbp
    6276:	53                   	push   %rbx
    6277:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    627b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6280:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    6284:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    628c:	31 db                	xor    %ebx,%ebx
    628e:	8b 10                	mov    (%rax),%edx
    6290:	85 d2                	test   %edx,%edx
    6292:	7e 26                	jle    62ba <barriered_work_ingest+0x6a>
    6294:	48 8b 48 08          	mov    0x8(%rax),%rcx
    6298:	48 89 dd             	mov    %rbx,%rbp
    629b:	48 c1 e5 08          	shl    $0x8,%rbp
    629f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    62a3:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    62aa:	74 24                	je     62d0 <barriered_work_ingest+0x80>
    62ac:	48 83 c3 01          	add    $0x1,%rbx
    62b0:	39 da                	cmp    %ebx,%edx
    62b2:	7f e4                	jg     6298 <barriered_work_ingest+0x48>
    62b4:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    62ba:	49 83 c5 01          	add    $0x1,%r13
    62be:	44 39 e9             	cmp    %r13d,%ecx
    62c1:	7f bd                	jg     6280 <barriered_work_ingest+0x30>
    62c3:	5b                   	pop    %rbx
    62c4:	31 c0                	xor    %eax,%eax
    62c6:	5d                   	pop    %rbp
    62c7:	41 5c                	pop    %r12
    62c9:	41 5d                	pop    %r13
    62cb:	41 5e                	pop    %r14
    62cd:	c3                   	ret
    62ce:	66 90                	xchg   %ax,%ax
    62d0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
    62d9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    62e0:	bf 04 00 00 00       	mov    $0x4,%edi
    62e5:	48 c1 e6 05          	shl    $0x5,%rsi
    62e9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    62f0:	48 83 c6 10          	add    $0x10,%rsi
    62f4:	e8 57 c0 ff ff       	call   2350 <clock_gettime@plt>
    62f9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    6301:	48 8b 40 50          	mov    0x50(%rax),%rax
    6305:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    6309:	48 03 68 08          	add    0x8(%rax),%rbp
    630d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    6317:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    631d:	83 c0 01             	add    $0x1,%eax
    6320:	99                   	cltd
    6321:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    6327:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
    632d:	0f ae f8             	sfence
    6330:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    6338:	48 83 c3 01          	add    $0x1,%rbx
    633c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6340:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    6344:	8b 10                	mov    (%rax),%edx
    6346:	39 da                	cmp    %ebx,%edx
    6348:	0f 8f 46 ff ff ff    	jg     6294 <barriered_work_ingest+0x44>
    634e:	e9 61 ff ff ff       	jmp    62b4 <barriered_work_ingest+0x64>
    6353:	31 c0                	xor    %eax,%eax
    6355:	c3                   	ret
    6356:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006360 <barriered_thread>:
    6360:	f3 0f 1e fa          	endbr64
    6364:	41 56                	push   %r14
    6366:	41 55                	push   %r13
    6368:	41 54                	push   %r12
    636a:	45 31 e4             	xor    %r12d,%r12d
    636d:	55                   	push   %rbp
    636e:	31 ed                	xor    %ebp,%ebp
    6370:	53                   	push   %rbx
    6371:	48 89 fb             	mov    %rdi,%rbx
    6374:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6378:	0f 85 74 02 00 00    	jne    65f2 <barriered_thread+0x292>
    637e:	8b 43 40             	mov    0x40(%rbx),%eax
    6381:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6388:	41 39 c4             	cmp    %eax,%r12d
    638b:	0f 8d 6f 01 00 00    	jge    6500 <barriered_thread+0x1a0>
    6391:	49 63 fc             	movslq %r12d,%rdi
    6394:	48 c1 e7 09          	shl    $0x9,%rdi
    6398:	49 89 fd             	mov    %rdi,%r13
    639b:	eb 32                	jmp    63cf <barriered_thread+0x6f>
    639d:	0f 1f 00             	nopl   (%rax)
    63a0:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    63a4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    63a8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    63ac:	48 8b 78 38          	mov    0x38(%rax),%rdi
    63b0:	4c 01 ef             	add    %r13,%rdi
    63b3:	e8 98 fe ff ff       	call   6250 <barriered_work_ingest>
    63b8:	8b 43 40             	mov    0x40(%rbx),%eax
    63bb:	41 83 c4 01          	add    $0x1,%r12d
    63bf:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    63c6:	44 39 e0             	cmp    %r12d,%eax
    63c9:	0f 8e 19 02 00 00    	jle    65e8 <barriered_thread+0x288>
    63cf:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    63d3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    63d7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    63de:	75 c0                	jne    63a0 <barriered_thread+0x40>
    63e0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
    63e4:	83 e8 01             	sub    $0x1,%eax
    63e7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    63ec:	45 85 e4             	test   %r12d,%r12d
    63ef:	0f 4f c1             	cmovg  %ecx,%eax
    63f2:	45 85 c0             	test   %r8d,%r8d
    63f5:	0f 8e 2d 01 00 00    	jle    6528 <barriered_thread+0x1c8>
    63fb:	48 63 c8             	movslq %eax,%rcx
    63fe:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6402:	49 63 d0             	movslq %r8d,%rdx
    6405:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
    640b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    6412:	48 c1 e1 09          	shl    $0x9,%rcx
    6416:	45 31 d2             	xor    %r10d,%r10d
    6419:	45 31 f6             	xor    %r14d,%r14d
    641c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6420:	48 8b 10             	mov    (%rax),%rdx
    6423:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6427:	49 01 cb             	add    %rcx,%r11
    642a:	4c 89 da             	mov    %r11,%rdx
    642d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6434:	75 04                	jne    643a <barriered_thread+0xda>
    6436:	41 83 c6 01          	add    $0x1,%r14d
    643a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6440:	75 04                	jne    6446 <barriered_thread+0xe6>
    6442:	41 83 c2 01          	add    $0x1,%r10d
    6446:	48 83 c0 08          	add    $0x8,%rax
    644a:	48 39 c6             	cmp    %rax,%rsi
    644d:	75 d1                	jne    6420 <barriered_thread+0xc0>
    644f:	45 85 d2             	test   %r10d,%r10d
    6452:	0f 84 c0 00 00 00    	je     6518 <barriered_thread+0x1b8>
    6458:	45 39 d0             	cmp    %r10d,%r8d
    645b:	0f 84 b7 00 00 00    	je     6518 <barriered_thread+0x1b8>
    6461:	45 85 f6             	test   %r14d,%r14d
    6464:	74 0a                	je     6470 <barriered_thread+0x110>
    6466:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    646a:	0f 85 ae 01 00 00    	jne    661e <barriered_thread+0x2be>
    6470:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6474:	4c 01 ea             	add    %r13,%rdx
    6477:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
    647e:	45 85 e4             	test   %r12d,%r12d
    6481:	75 14                	jne    6497 <barriered_thread+0x137>
    6483:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    648a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6491:	0f 8c 69 01 00 00    	jl     6600 <barriered_thread+0x2a0>
    6497:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    649b:	48 8b 43 18          	mov    0x18(%rbx),%rax
    649f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
    64a9:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    64ad:	48 8b 78 38          	mov    0x38(%rax),%rdi
    64b1:	4c 01 ef             	add    %r13,%rdi
    64b4:	ff 92 18 01 00 00    	call   *0x118(%rdx)
    64ba:	48 8b 43 38          	mov    0x38(%rbx),%rax
    64be:	4c 01 e8             	add    %r13,%rax
    64c1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    64c8:	8b 43 40             	mov    0x40(%rbx),%eax
    64cb:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
    64d0:	83 e8 01             	sub    $0x1,%eax
    64d3:	44 39 e0             	cmp    %r12d,%eax
    64d6:	0f 84 a4 00 00 00    	je     6580 <barriered_thread+0x220>
    64dc:	0f ae f8             	sfence
    64df:	85 ed                	test   %ebp,%ebp
    64e1:	0f 84 d1 00 00 00    	je     65b8 <barriered_thread+0x258>
    64e7:	bd 01 00 00 00       	mov    $0x1,%ebp
    64ec:	e9 c7 fe ff ff       	jmp    63b8 <barriered_thread+0x58>
    64f1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    64f5:	0f 85 f7 00 00 00    	jne    65f2 <barriered_thread+0x292>
    64fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6500:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    6508:	85 c0                	test   %eax,%eax
    650a:	7e e5                	jle    64f1 <barriered_thread+0x191>
    650c:	45 31 e4             	xor    %r12d,%r12d
    650f:	e9 7d fe ff ff       	jmp    6391 <barriered_thread+0x31>
    6514:	0f 1f 40 00          	nopl   0x0(%rax)
    6518:	83 fd 01             	cmp    $0x1,%ebp
    651b:	74 1b                	je     6538 <barriered_thread+0x1d8>
    651d:	31 ed                	xor    %ebp,%ebp
    651f:	e9 3d ff ff ff       	jmp    6461 <barriered_thread+0x101>
    6524:	0f 1f 40 00          	nopl   0x0(%rax)
    6528:	83 fd 01             	cmp    $0x1,%ebp
    652b:	0f 85 43 ff ff ff    	jne    6474 <barriered_thread+0x114>
    6531:	45 31 f6             	xor    %r14d,%r14d
    6534:	0f 1f 40 00          	nopl   0x0(%rax)
    6538:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    653f:	bf 04 00 00 00       	mov    $0x4,%edi
    6544:	31 ed                	xor    %ebp,%ebp
    6546:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    654a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6551:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6556:	e8 f5 bd ff ff       	call   2350 <clock_gettime@plt>
    655b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6562:	48 83 c0 01          	add    $0x1,%rax
    6566:	48 99                	cqto
    6568:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    656f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
    6576:	e9 e6 fe ff ff       	jmp    6461 <barriered_thread+0x101>
    657b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6580:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6587:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    658e:	0f 8d 48 ff ff ff    	jge    64dc <barriered_thread+0x17c>
    6594:	48 c1 e6 04          	shl    $0x4,%rsi
    6598:	bf 04 00 00 00       	mov    $0x4,%edi
    659d:	48 03 73 70          	add    0x70(%rbx),%rsi
    65a1:	e8 aa bd ff ff       	call   2350 <clock_gettime@plt>
    65a6:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    65ae:	e9 29 ff ff ff       	jmp    64dc <barriered_thread+0x17c>
    65b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    65b8:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    65bf:	bf 04 00 00 00       	mov    $0x4,%edi
    65c4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    65c8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    65cf:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    65d3:	44 89 66 20          	mov    %r12d,0x20(%rsi)
    65d7:	e8 74 bd ff ff       	call   2350 <clock_gettime@plt>
    65dc:	e9 06 ff ff ff       	jmp    64e7 <barriered_thread+0x187>
    65e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    65e8:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    65ec:	0f 84 96 fd ff ff    	je     6388 <barriered_thread+0x28>
    65f2:	5b                   	pop    %rbx
    65f3:	31 c0                	xor    %eax,%eax
    65f5:	5d                   	pop    %rbp
    65f6:	41 5c                	pop    %r12
    65f8:	41 5d                	pop    %r13
    65fa:	41 5e                	pop    %r14
    65fc:	c3                   	ret
    65fd:	0f 1f 00             	nopl   (%rax)
    6600:	48 c1 e6 04          	shl    $0x4,%rsi
    6604:	bf 04 00 00 00       	mov    $0x4,%edi
    6609:	48 03 73 68          	add    0x68(%rbx),%rsi
    660d:	e8 3e bd ff ff       	call   2350 <clock_gettime@plt>
    6612:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6616:	4c 01 ea             	add    %r13,%rdx
    6619:	e9 79 fe ff ff       	jmp    6497 <barriered_thread+0x137>
    661e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6622:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6626:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    662a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    662e:	4c 01 ef             	add    %r13,%rdi
    6631:	e8 1a fc ff ff       	call   6250 <barriered_work_ingest>
    6636:	e9 39 fd ff ff       	jmp    6374 <barriered_thread+0x14>
    663b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006640 <receive>:
    6640:	f3 0f 1e fa          	endbr64
    6644:	41 56                	push   %r14
    6646:	41 55                	push   %r13
    6648:	41 54                	push   %r12
    664a:	55                   	push   %rbp
    664b:	53                   	push   %rbx
    664c:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    6653:	45 85 e4             	test   %r12d,%r12d
    6656:	0f 8e 27 01 00 00    	jle    6783 <receive+0x143>
    665c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    6663:	48 89 fe             	mov    %rdi,%rsi
    6666:	31 db                	xor    %ebx,%ebx
    6668:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    666c:	49 89 ed             	mov    %rbp,%r13
    666f:	90                   	nop
    6670:	41 39 dd             	cmp    %ebx,%r13d
    6673:	0f 84 fd 00 00 00    	je     6776 <receive+0x136>
    6679:	48 89 d8             	mov    %rbx,%rax
    667c:	48 c1 e0 08          	shl    $0x8,%rax
    6680:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    6687:	48 8b 10             	mov    (%rax),%rdx
    668a:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    6690:	83 f8 01             	cmp    $0x1,%eax
    6693:	74 11                	je     66a6 <receive+0x66>
    6695:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    669c:	75 08                	jne    66a6 <receive+0x66>
    669e:	85 c0                	test   %eax,%eax
    66a0:	0f 84 d0 00 00 00    	je     6776 <receive+0x136>
    66a6:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    66ad:	48 85 ff             	test   %rdi,%rdi
    66b0:	0f 8e a2 00 00 00    	jle    6758 <receive+0x118>
    66b6:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    66bd:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    66c4:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    66c8:	4c 8b 1a             	mov    (%rdx),%r11
    66cb:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    66cf:	49 01 f9             	add    %rdi,%r9
    66d2:	49 01 f8             	add    %rdi,%r8
    66d5:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    66dc:	eb 08                	jmp    66e6 <receive+0xa6>
    66de:	66 90                	xchg   %ax,%ax
    66e0:	48 83 e8 01          	sub    $0x1,%rax
    66e4:	72 72                	jb     6758 <receive+0x118>
    66e6:	4c 89 c9             	mov    %r9,%rcx
    66e9:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
    66f0:	48 29 c1             	sub    %rax,%rcx
    66f3:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
    66fa:	4c 89 c1             	mov    %r8,%rcx
    66fd:	48 29 c1             	sub    %rax,%rcx
    6700:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
    6707:	48 89 f9             	mov    %rdi,%rcx
    670a:	48 29 c1             	sub    %rax,%rcx
    670d:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
    6714:	48 63 c8             	movslq %eax,%rcx
    6717:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
    671b:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    671f:	75 bf                	jne    66e0 <receive+0xa0>
    6721:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    6725:	75 b9                	jne    66e0 <receive+0xa0>
    6727:	49 63 46 04          	movslq 0x4(%r14),%rax
    672b:	31 c9                	xor    %ecx,%ecx
    672d:	bf 01 00 00 00       	mov    $0x1,%edi
    6732:	ba 01 00 00 00       	mov    $0x1,%edx
    6737:	48 8d 35 f2 1e 00 00 	lea    0x1ef2(%rip),%rsi        # 8630 <_IO_stdin_used+0x630>
    673e:	48 39 e8             	cmp    %rbp,%rax
    6741:	0f 94 c1             	sete   %cl
    6744:	31 c0                	xor    %eax,%eax
    6746:	e8 65 bd ff ff       	call   24b0 <__printf_chk@plt>
    674b:	bf 01 00 00 00       	mov    $0x1,%edi
    6750:	e8 bb bd ff ff       	call   2510 <exit@plt>
    6755:	0f 1f 00             	nopl   (%rax)
    6758:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
    6762:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
    676c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
    6776:	48 83 c3 01          	add    $0x1,%rbx
    677a:	49 39 dc             	cmp    %rbx,%r12
    677d:	0f 85 ed fe ff ff    	jne    6670 <receive+0x30>
    6783:	0f ae f8             	sfence
    6786:	31 c0                	xor    %eax,%eax
    6788:	5b                   	pop    %rbx
    6789:	5d                   	pop    %rbp
    678a:	41 5c                	pop    %r12
    678c:	41 5d                	pop    %r13
    678e:	41 5e                	pop    %r14
    6790:	c3                   	ret
    6791:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    679c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000067a0 <sendm>:
    67a0:	f3 0f 1e fa          	endbr64
    67a4:	41 57                	push   %r15
    67a6:	48 89 f9             	mov    %rdi,%rcx
    67a9:	41 56                	push   %r14
    67ab:	41 55                	push   %r13
    67ad:	41 54                	push   %r12
    67af:	55                   	push   %rbp
    67b0:	53                   	push   %rbx
    67b1:	48 63 bf 40 01 00 00 	movslq 0x140(%rdi),%rdi
    67b8:	85 ff                	test   %edi,%edi
    67ba:	7e 67                	jle    6823 <sendm+0x83>
    67bc:	48 8b 81 28 01 00 00 	mov    0x128(%rcx),%rax
    67c3:	44 8b 48 08          	mov    0x8(%rax),%r9d
    67c7:	31 c0                	xor    %eax,%eax
    67c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    67d0:	41 39 c1             	cmp    %eax,%r9d
    67d3:	74 45                	je     681a <sendm+0x7a>
    67d5:	48 89 c2             	mov    %rax,%rdx
    67d8:	48 c1 e2 08          	shl    $0x8,%rdx
    67dc:	48 03 91 70 01 00 00 	add    0x170(%rcx),%rdx
    67e3:	48 8b 92 80 00 00 00 	mov    0x80(%rdx),%rdx
    67ea:	48 8b b2 80 00 00 00 	mov    0x80(%rdx),%rsi
    67f1:	48 85 f6             	test   %rsi,%rsi
    67f4:	7f 24                	jg     681a <sendm+0x7a>
    67f6:	44 8b 82 00 01 00 00 	mov    0x100(%rdx),%r8d
    67fd:	41 83 f8 01          	cmp    $0x1,%r8d
    6801:	74 0e                	je     6811 <sendm+0x71>
    6803:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    680a:	75 05                	jne    6811 <sendm+0x71>
    680c:	45 85 c0             	test   %r8d,%r8d
    680f:	74 09                	je     681a <sendm+0x7a>
    6811:	83 b9 88 01 00 00 01 	cmpl   $0x1,0x188(%rcx)
    6818:	74 1e                	je     6838 <sendm+0x98>
    681a:	48 83 c0 01          	add    $0x1,%rax
    681e:	48 39 c7             	cmp    %rax,%rdi
    6821:	75 ad                	jne    67d0 <sendm+0x30>
    6823:	0f ae f8             	sfence
    6826:	31 c0                	xor    %eax,%eax
    6828:	5b                   	pop    %rbx
    6829:	5d                   	pop    %rbp
    682a:	41 5c                	pop    %r12
    682c:	41 5d                	pop    %r13
    682e:	41 5e                	pop    %r14
    6830:	41 5f                	pop    %r15
    6832:	c3                   	ret
    6833:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6838:	48 63 aa 88 00 00 00 	movslq 0x88(%rdx),%rbp
    683f:	48 39 ee             	cmp    %rbp,%rsi
    6842:	0f 8d a5 00 00 00    	jge    68ed <sendm+0x14d>
    6848:	48 8b 99 08 01 00 00 	mov    0x108(%rcx),%rbx
    684f:	4c 8b aa 80 03 00 00 	mov    0x380(%rdx),%r13
    6856:	4c 8b 1a             	mov    (%rdx),%r11
    6859:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    685e:	48 89 eb             	mov    %rbp,%rbx
    6861:	48 29 f3             	sub    %rsi,%rbx
    6864:	4c 8d 43 ff          	lea    -0x1(%rbx),%r8
    6868:	49 83 f8 02          	cmp    $0x2,%r8
    686c:	0f 86 0e 01 00 00    	jbe    6980 <sendm+0x1e0>
    6872:	4c 8d 14 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r10
    687a:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    6882:	4f 8d 34 13          	lea    (%r11,%r10,1),%r14
    6886:	4c 8d b9 90 01 00 00 	lea    0x190(%rcx),%r15
    688d:	4f 8d 24 03          	lea    (%r11,%r8,1),%r12
    6891:	4d 39 f7             	cmp    %r14,%r15
    6894:	73 7a                	jae    6910 <sendm+0x170>
    6896:	4c 8d b1 98 01 00 00 	lea    0x198(%rcx),%r14
    689d:	4d 39 f4             	cmp    %r14,%r12
    68a0:	73 6e                	jae    6910 <sendm+0x170>
    68a2:	4d 01 d8             	add    %r11,%r8
    68a5:	4b 8d 34 13          	lea    (%r11,%r10,1),%rsi
    68a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    68b0:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    68b7:	49 83 c0 08          	add    $0x8,%r8
    68bb:	4d 89 50 f8          	mov    %r10,-0x8(%r8)
    68bf:	4c 39 c6             	cmp    %r8,%rsi
    68c2:	75 ec                	jne    68b0 <sendm+0x110>
    68c4:	0f 1f 40 00          	nopl   0x0(%rax)
    68c8:	48 8b 74 24 f0       	mov    -0x10(%rsp),%rsi
    68cd:	48 01 de             	add    %rbx,%rsi
    68d0:	4c 01 eb             	add    %r13,%rbx
    68d3:	48 89 b1 08 01 00 00 	mov    %rsi,0x108(%rcx)
    68da:	48 89 9a 80 03 00 00 	mov    %rbx,0x380(%rdx)
    68e1:	48 89 aa 80 00 00 00 	mov    %rbp,0x80(%rdx)
    68e8:	4d 89 54 eb f8       	mov    %r10,-0x8(%r11,%rbp,8)
    68ed:	c7 82 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rdx)
    68f7:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    6901:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
    690b:	e9 0a ff ff ff       	jmp    681a <sendm+0x7a>
    6910:	49 89 de             	mov    %rbx,%r14
    6913:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    691a:	4d 89 e0             	mov    %r12,%r8
    691d:	49 d1 ee             	shr    %r14
    6920:	49 c1 e6 04          	shl    $0x4,%r14
    6924:	66 49 0f 6e c2       	movq   %r10,%xmm0
    6929:	4f 8d 3c 34          	lea    (%r12,%r14,1),%r15
    692d:	41 83 e6 10          	and    $0x10,%r14d
    6931:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    6935:	74 11                	je     6948 <sendm+0x1a8>
    6937:	49 83 c0 10          	add    $0x10,%r8
    693b:	41 0f 11 04 24       	movups %xmm0,(%r12)
    6940:	4d 39 f8             	cmp    %r15,%r8
    6943:	74 15                	je     695a <sendm+0x1ba>
    6945:	0f 1f 00             	nopl   (%rax)
    6948:	41 0f 11 00          	movups %xmm0,(%r8)
    694c:	49 83 c0 20          	add    $0x20,%r8
    6950:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
    6955:	4d 39 f8             	cmp    %r15,%r8
    6958:	75 ee                	jne    6948 <sendm+0x1a8>
    695a:	49 89 d8             	mov    %rbx,%r8
    695d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6961:	4c 01 c6             	add    %r8,%rsi
    6964:	f6 c3 01             	test   $0x1,%bl
    6967:	0f 84 5b ff ff ff    	je     68c8 <sendm+0x128>
    696d:	4c 8b 91 90 01 00 00 	mov    0x190(%rcx),%r10
    6974:	4d 89 14 f3          	mov    %r10,(%r11,%rsi,8)
    6978:	e9 4b ff ff ff       	jmp    68c8 <sendm+0x128>
    697d:	0f 1f 00             	nopl   (%rax)
    6980:	4c 8d 04 f5 00 00 00 00 	lea    0x0(,%rsi,8),%r8
    6988:	4c 8d 14 ed 00 00 00 00 	lea    0x0(,%rbp,8),%r10
    6990:	e9 0d ff ff ff       	jmp    68a2 <sendm+0x102>
    6995:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000069a0 <mailboxkind>:
    69a0:	f3 0f 1e fa          	endbr64
    69a4:	85 f6                	test   %esi,%esi
    69a6:	74 18                	je     69c0 <mailboxkind+0x20>
    69a8:	31 c0                	xor    %eax,%eax
    69aa:	83 fe 01             	cmp    $0x1,%esi
    69ad:	74 01                	je     69b0 <mailboxkind+0x10>
    69af:	c3                   	ret
    69b0:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
    69b7:	c3                   	ret
    69b8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    69c0:	48 8b 07             	mov    (%rdi),%rax
    69c3:	c3                   	ret
    69c4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    69cf:	90                   	nop

00000000000069d0 <setmailboxkind>:
    69d0:	f3 0f 1e fa          	endbr64
    69d4:	85 d2                	test   %edx,%edx
    69d6:	75 08                	jne    69e0 <setmailboxkind+0x10>
    69d8:	48 89 37             	mov    %rsi,(%rdi)
    69db:	31 c0                	xor    %eax,%eax
    69dd:	c3                   	ret
    69de:	66 90                	xchg   %ax,%ax
    69e0:	83 fa 01             	cmp    $0x1,%edx
    69e3:	74 13                	je     69f8 <setmailboxkind+0x28>
    69e5:	83 fa 02             	cmp    $0x2,%edx
    69e8:	75 1e                	jne    6a08 <setmailboxkind+0x38>
    69ea:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
    69f1:	31 c0                	xor    %eax,%eax
    69f3:	c3                   	ret
    69f4:	0f 1f 40 00          	nopl   0x0(%rax)
    69f8:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
    69ff:	31 c0                	xor    %eax,%eax
    6a01:	c3                   	ret
    6a02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6a08:	83 fa 03             	cmp    $0x3,%edx
    6a0b:	75 ce                	jne    69db <setmailboxkind+0xb>
    6a0d:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
    6a14:	31 c0                	xor    %eax,%eax
    6a16:	c3                   	ret
    6a17:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006a20 <fswap>:
    6a20:	f3 0f 1e fa          	endbr64
    6a24:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    6a2b:	8b 97 9c 01 00 00    	mov    0x19c(%rdi),%edx
    6a31:	44 8b 97 30 01 00 00 	mov    0x130(%rdi),%r10d
    6a38:	48 63 4f 04          	movslq 0x4(%rdi),%rcx
    6a3c:	8b 86 c4 00 00 00    	mov    0xc4(%rsi),%eax
    6a42:	0f af d0             	imul   %eax,%edx
    6a45:	41 01 d2             	add    %edx,%r10d
    6a48:	85 c0                	test   %eax,%eax
    6a4a:	0f 8e 1b 01 00 00    	jle    6b6b <fswap+0x14b>
    6a50:	4d 63 d2             	movslq %r10d,%r10
    6a53:	41 56                	push   %r14
    6a55:	48 63 d2             	movslq %edx,%rdx
    6a58:	48 c1 e1 09          	shl    $0x9,%rcx
    6a5c:	41 55                	push   %r13
    6a5e:	4c 63 d8             	movslq %eax,%r11
    6a61:	41 54                	push   %r12
    6a63:	49 01 d3             	add    %rdx,%r11
    6a66:	55                   	push   %rbp
    6a67:	49 c1 e3 08          	shl    $0x8,%r11
    6a6b:	53                   	push   %rbx
    6a6c:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
    6a73:	4c 89 d7             	mov    %r10,%rdi
    6a76:	48 8b 76 20          	mov    0x20(%rsi),%rsi
    6a7a:	48 c1 e7 05          	shl    $0x5,%rdi
    6a7e:	4c 29 d7             	sub    %r10,%rdi
    6a81:	49 c1 e2 08          	shl    $0x8,%r10
    6a85:	48 8b 5c fe 38       	mov    0x38(%rsi,%rdi,8),%rbx
    6a8a:	48 8b ac 0b 70 01 00 00 	mov    0x170(%rbx,%rcx,1),%rbp
    6a92:	48 89 d1             	mov    %rdx,%rcx
    6a95:	48 c1 e1 05          	shl    $0x5,%rcx
    6a99:	48 29 d1             	sub    %rdx,%rcx
    6a9c:	4c 8d 0c ce          	lea    (%rsi,%rcx,8),%r9
    6aa0:	48 89 d6             	mov    %rdx,%rsi
    6aa3:	48 c1 e6 08          	shl    $0x8,%rsi
    6aa7:	eb 1e                	jmp    6ac7 <fswap+0xa7>
    6aa9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6ab0:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    6ab7:	49 81 c1 f8 00 00 00 	add    $0xf8,%r9
    6abe:	49 39 f3             	cmp    %rsi,%r11
    6ac1:	0f 84 99 00 00 00    	je     6b60 <fswap+0x140>
    6ac7:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    6acf:	75 df                	jne    6ab0 <fswap+0x90>
    6ad1:	49 8b 79 38          	mov    0x38(%r9),%rdi
    6ad5:	45 85 c0             	test   %r8d,%r8d
    6ad8:	7e d6                	jle    6ab0 <fswap+0x90>
    6ada:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    6ae1:	31 c9                	xor    %ecx,%ecx
    6ae3:	eb 58                	jmp    6b3d <fswap+0x11d>
    6ae5:	0f 1f 00             	nopl   (%rax)
    6ae8:	48 63 d2             	movslq %edx,%rdx
    6aeb:	48 c1 e2 09          	shl    $0x9,%rdx
    6aef:	4c 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%r13
    6af7:	49 01 f5             	add    %rsi,%r13
    6afa:	4c 89 ea             	mov    %r13,%rdx
    6afd:	4d 8b 6d 00          	mov    0x0(%r13),%r13
    6b01:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    6b09:	75 22                	jne    6b2d <fswap+0x10d>
    6b0b:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    6b12:	4c 89 32             	mov    %r14,(%rdx)
    6b15:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    6b1c:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    6b23:	4c 89 30             	mov    %r14,(%rax)
    6b26:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
    6b2d:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    6b34:	41 39 c8             	cmp    %ecx,%r8d
    6b37:	0f 84 73 ff ff ff    	je     6ab0 <fswap+0x90>
    6b3d:	83 c1 01             	add    $0x1,%ecx
    6b40:	89 c8                	mov    %ecx,%eax
    6b42:	99                   	cltd
    6b43:	41 f7 f8             	idiv   %r8d
    6b46:	48 8b 07             	mov    (%rdi),%rax
    6b49:	4c 01 d0             	add    %r10,%rax
    6b4c:	4c 8b 20             	mov    (%rax),%r12
    6b4f:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    6b58:	74 8e                	je     6ae8 <fswap+0xc8>
    6b5a:	e9 51 ff ff ff       	jmp    6ab0 <fswap+0x90>
    6b5f:	90                   	nop
    6b60:	5b                   	pop    %rbx
    6b61:	31 c0                	xor    %eax,%eax
    6b63:	5d                   	pop    %rbp
    6b64:	41 5c                	pop    %r12
    6b66:	41 5d                	pop    %r13
    6b68:	41 5e                	pop    %r14
    6b6a:	c3                   	ret
    6b6b:	31 c0                	xor    %eax,%eax
    6b6d:	c3                   	ret
    6b6e:	66 90                	xchg   %ax,%ax

0000000000006b70 <barriered_work>:
    6b70:	f3 0f 1e fa          	endbr64
    6b74:	41 57                	push   %r15
    6b76:	41 56                	push   %r14
    6b78:	41 55                	push   %r13
    6b7a:	41 54                	push   %r12
    6b7c:	55                   	push   %rbp
    6b7d:	53                   	push   %rbx
    6b7e:	48 89 fb             	mov    %rdi,%rbx
    6b81:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
    6b88:	66 0f 6f 05 60 20 00 00 	movdqa 0x2060(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    6b90:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    6b99:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    6b9e:	31 c0                	xor    %eax,%eax
    6ba0:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    6ba7:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
    6bac:	48 8b 88 f0 00 00 00 	mov    0xf0(%rax),%rcx
    6bb3:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
    6bb8:	8b 11                	mov    (%rcx),%edx
    6bba:	83 fa ff             	cmp    $0xffffffff,%edx
    6bbd:	0f 84 dd 02 00 00    	je     6ea0 <barriered_work+0x330>
    6bc3:	3b 90 e8 00 00 00    	cmp    0xe8(%rax),%edx
    6bc9:	74 2d                	je     6bf8 <barriered_work+0x88>
    6bcb:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    6bd0:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    6bd9:	0f 85 50 05 00 00    	jne    712f <barriered_work+0x5bf>
    6bdf:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    6be6:	31 c0                	xor    %eax,%eax
    6be8:	5b                   	pop    %rbx
    6be9:	5d                   	pop    %rbp
    6bea:	41 5c                	pop    %r12
    6bec:	41 5d                	pop    %r13
    6bee:	41 5e                	pop    %r14
    6bf0:	41 5f                	pop    %r15
    6bf2:	c3                   	ret
    6bf3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6bf8:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    6bff:	8b 41 04             	mov    0x4(%rcx),%eax
    6c02:	85 ed                	test   %ebp,%ebp
    6c04:	0f 85 a6 04 00 00    	jne    70b0 <barriered_work+0x540>
    6c0a:	85 c0                	test   %eax,%eax
    6c0c:	0f 84 a6 04 00 00    	je     70b8 <barriered_work+0x548>
    6c12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6c18:	44 8b 63 04          	mov    0x4(%rbx),%r12d
    6c1c:	48 89 df             	mov    %rbx,%rdi
    6c1f:	41 39 ec             	cmp    %ebp,%r12d
    6c22:	0f 85 c8 02 00 00    	jne    6ef0 <barriered_work+0x380>
    6c28:	e8 13 fa ff ff       	call   6640 <receive>
    6c2d:	44 8b b3 40 01 00 00 	mov    0x140(%rbx),%r14d
    6c34:	45 85 f6             	test   %r14d,%r14d
    6c37:	0f 8e 0b 03 00 00    	jle    6f48 <barriered_work+0x3d8>
    6c3d:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6c43:	48 c1 e5 09          	shl    $0x9,%rbp
    6c47:	45 31 c0             	xor    %r8d,%r8d
    6c4a:	31 f6                	xor    %esi,%esi
    6c4c:	48 8b 93 28 01 00 00 	mov    0x128(%rbx),%rdx
    6c53:	49 89 ed             	mov    %rbp,%r13
    6c56:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
    6c5b:	89 44 24 24          	mov    %eax,0x24(%rsp)
    6c5f:	48 63 42 08          	movslq 0x8(%rdx),%rax
    6c63:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
    6c6b:	48 89 c1             	mov    %rax,%rcx
    6c6e:	49 89 c7             	mov    %rax,%r15
    6c71:	48 c1 e1 05          	shl    $0x5,%rcx
    6c75:	48 29 c1             	sub    %rax,%rcx
    6c78:	48 c1 e0 08          	shl    $0x8,%rax
    6c7c:	48 8d 2c cd 00 00 00 00 	lea    0x0(,%rcx,8),%rbp
    6c84:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    6c89:	48 89 d9             	mov    %rbx,%rcx
    6c8c:	48 89 d3             	mov    %rdx,%rbx
    6c8f:	eb 27                	jmp    6cb8 <barriered_work+0x148>
    6c91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6c98:	83 44 24 0c 01       	addl   $0x1,0xc(%rsp)
    6c9d:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    6ca1:	48 81 c6 f8 00 00 00 	add    $0xf8,%rsi
    6ca8:	49 81 c0 00 01 00 00 	add    $0x100,%r8
    6caf:	44 39 f0             	cmp    %r14d,%eax
    6cb2:	0f 84 88 02 00 00    	je     6f40 <barriered_work+0x3d0>
    6cb8:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    6cbc:	41 39 c7             	cmp    %eax,%r15d
    6cbf:	74 d7                	je     6c98 <barriered_work+0x128>
    6cc1:	48 8b 53 20          	mov    0x20(%rbx),%rdx
    6cc5:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    6cca:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    6cce:	44 8b 88 a0 01 00 00 	mov    0x1a0(%rax),%r9d
    6cd5:	45 85 c9             	test   %r9d,%r9d
    6cd8:	75 be                	jne    6c98 <barriered_work+0x128>
    6cda:	4c 8b 4c 2a 38       	mov    0x38(%rdx,%rbp,1),%r9
    6cdf:	4b 8d 14 29          	lea    (%r9,%r13,1),%rdx
    6ce3:	44 8b 92 a0 01 00 00 	mov    0x1a0(%rdx),%r10d
    6cea:	45 85 d2             	test   %r10d,%r10d
    6ced:	75 a9                	jne    6c98 <barriered_work+0x128>
    6cef:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    6cf6:	42 83 bc 02 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r8,1)
    6cff:	75 97                	jne    6c98 <barriered_work+0x128>
    6d01:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6d08:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    6d0d:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    6d15:	75 81                	jne    6c98 <barriered_work+0x128>
    6d17:	48 63 44 24 24       	movslq 0x24(%rsp),%rax
    6d1c:	85 c0                	test   %eax,%eax
    6d1e:	0f 8e 74 ff ff ff    	jle    6c98 <barriered_work+0x128>
    6d24:	48 89 c2             	mov    %rax,%rdx
    6d27:	44 89 7c 24 38       	mov    %r15d,0x38(%rsp)
    6d2c:	41 bc 70 01 00 00    	mov    $0x170,%r12d
    6d32:	48 c1 e2 09          	shl    $0x9,%rdx
    6d36:	44 89 74 24 3c       	mov    %r14d,0x3c(%rsp)
    6d3b:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    6d40:	4c 8d 9a a0 01 00 00 	lea    0x1a0(%rdx),%r11
    6d47:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    6d4c:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    6d51:	8b 5c 24 24          	mov    0x24(%rsp),%ebx
    6d55:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    6d5a:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    6d5f:	90                   	nop
    6d60:	41 83 c2 01          	add    $0x1,%r10d
    6d64:	4b 8b 34 21          	mov    (%r9,%r12,1),%rsi
    6d68:	44 89 d0             	mov    %r10d,%eax
    6d6b:	99                   	cltd
    6d6c:	4c 01 c6             	add    %r8,%rsi
    6d6f:	f7 fb                	idiv   %ebx
    6d71:	4c 8b 36             	mov    (%rsi),%r14
    6d74:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    6d79:	4c 8b b6 80 00 00 00 	mov    0x80(%rsi),%r14
    6d80:	48 63 d2             	movslq %edx,%rdx
    6d83:	48 c1 e2 09          	shl    $0x9,%rdx
    6d87:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    6d8f:	4c 01 e8             	add    %r13,%rax
    6d92:	4c 8b 38             	mov    (%rax),%r15
    6d95:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    6d9c:	4c 89 30             	mov    %r14,(%rax)
    6d9f:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    6da4:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    6dab:	48 89 16             	mov    %rdx,(%rsi)
    6dae:	4c 89 be 80 00 00 00 	mov    %r15,0x80(%rsi)
    6db5:	be a0 01 00 00       	mov    $0x1a0,%esi
    6dba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6dc0:	41 c7 04 31 01 00 00 00 	movl   $0x1,(%r9,%rsi,1)
    6dc8:	c7 04 37 01 00 00 00 	movl   $0x1,(%rdi,%rsi,1)
    6dcf:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    6dd6:	4c 39 de             	cmp    %r11,%rsi
    6dd9:	75 e5                	jne    6dc0 <barriered_work+0x250>
    6ddb:	4a 8b 34 27          	mov    (%rdi,%r12,1),%rsi
    6ddf:	48 8b 00             	mov    (%rax),%rax
    6de2:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
    6ded:	49 81 c4 00 02 00 00 	add    $0x200,%r12
    6df4:	4a 8b b4 2e 80 00 00 00 	mov    0x80(%rsi,%r13,1),%rsi
    6dfc:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
    6e06:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    6e10:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    6e1a:	44 39 d3             	cmp    %r10d,%ebx
    6e1d:	0f 85 3d ff ff ff    	jne    6d60 <barriered_work+0x1f0>
    6e23:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    6e28:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    6e2d:	b8 70 01 00 00       	mov    $0x170,%eax
    6e32:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    6e37:	44 8b 7c 24 38       	mov    0x38(%rsp),%r15d
    6e3c:	44 8b 74 24 3c       	mov    0x3c(%rsp),%r14d
    6e41:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    6e46:	4c 8d 9a 70 01 00 00 	lea    0x170(%rdx),%r11
    6e4d:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    6e52:	eb 13                	jmp    6e67 <barriered_work+0x2f7>
    6e54:	0f 1f 40 00          	nopl   0x0(%rax)
    6e58:	48 05 00 02 00 00    	add    $0x200,%rax
    6e5e:	4c 39 d8             	cmp    %r11,%rax
    6e61:	0f 84 31 fe ff ff    	je     6c98 <barriered_work+0x128>
    6e67:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    6e6b:	4d 8b 14 01          	mov    (%r9,%rax,1),%r10
    6e6f:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    6e73:	4b 39 14 02          	cmp    %rdx,(%r10,%r8,1)
    6e77:	75 df                	jne    6e58 <barriered_work+0x2e8>
    6e79:	bf 01 00 00 00       	mov    $0x1,%edi
    6e7e:	48 8d 35 c3 13 00 00 	lea    0x13c3(%rip),%rsi        # 8248 <_IO_stdin_used+0x248>
    6e85:	31 c0                	xor    %eax,%eax
    6e87:	e8 24 b6 ff ff       	call   24b0 <__printf_chk@plt>
    6e8c:	bf 01 00 00 00       	mov    $0x1,%edi
    6e91:	e8 7a b6 ff ff       	call   2510 <exit@plt>
    6e96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6ea0:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    6ea7:	85 ed                	test   %ebp,%ebp
    6ea9:	0f 85 69 fd ff ff    	jne    6c18 <barriered_work+0xa8>
    6eaf:	44 8b 90 e8 00 00 00 	mov    0xe8(%rax),%r10d
    6eb6:	45 85 d2             	test   %r10d,%r10d
    6eb9:	0f 85 59 fd ff ff    	jne    6c18 <barriered_work+0xa8>
    6ebf:	69 87 80 00 00 00 1d e6 cb 0b 	imul   $0xbcbe61d,0x80(%rdi),%eax
    6ec9:	05 40 7c 0a 00       	add    $0xa7c40,%eax
    6ece:	c1 c8 05             	ror    $0x5,%eax
    6ed1:	3d c4 a7 00 00       	cmp    $0xa7c4,%eax
    6ed6:	0f 87 3c fd ff ff    	ja     6c18 <barriered_work+0xa8>
    6edc:	48 c7 01 00 00 00 00 	movq   $0x0,(%rcx)
    6ee3:	e9 30 fd ff ff       	jmp    6c18 <barriered_work+0xa8>
    6ee8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6ef0:	e8 4b f7 ff ff       	call   6640 <receive>
    6ef5:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6efc:	75 16                	jne    6f14 <barriered_work+0x3a4>
    6efe:	66 90                	xchg   %ax,%ax
    6f00:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6f08:	0f ae f8             	sfence
    6f0b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6f12:	74 ec                	je     6f00 <barriered_work+0x390>
    6f14:	48 89 df             	mov    %rbx,%rdi
    6f17:	e8 84 f8 ff ff       	call   67a0 <sendm>
    6f1c:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6f22:	83 e8 01             	sub    $0x1,%eax
    6f25:	44 39 e0             	cmp    %r12d,%eax
    6f28:	0f 84 05 01 00 00    	je     7033 <barriered_work+0x4c3>
    6f2e:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    6f38:	0f ae f8             	sfence
    6f3b:	e9 8b fc ff ff       	jmp    6bcb <barriered_work+0x5b>
    6f40:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    6f45:	48 89 cb             	mov    %rcx,%rbx
    6f48:	48 89 df             	mov    %rbx,%rdi
    6f4b:	e8 d0 fa ff ff       	call   6a20 <fswap>
    6f50:	48 89 df             	mov    %rbx,%rdi
    6f53:	e8 e8 f6 ff ff       	call   6640 <receive>
    6f58:	0f ae f8             	sfence
    6f5b:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6f62:	31 ff                	xor    %edi,%edi
    6f64:	48 c1 e6 05          	shl    $0x5,%rsi
    6f68:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6f6f:	e8 dc b3 ff ff       	call   2350 <clock_gettime@plt>
    6f74:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6f7b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6f82:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6f86:	8b 4a 10             	mov    0x10(%rdx),%ecx
    6f89:	8d 69 01             	lea    0x1(%rcx),%ebp
    6f8c:	89 6a 10             	mov    %ebp,0x10(%rdx)
    6f8f:	75 58                	jne    6fe9 <barriered_work+0x479>
    6f91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6f98:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    6f9f:	48 8b 40 18          	mov    0x18(%rax),%rax
    6fa3:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
    6fa7:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6faf:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6fb3:	48 c1 e7 09          	shl    $0x9,%rdi
    6fb7:	48 03 78 38          	add    0x38(%rax),%rdi
    6fbb:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    6fc1:	0f ae f8             	sfence
    6fc4:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6fcb:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6fd2:	74 c4                	je     6f98 <barriered_work+0x428>
    6fd4:	48 8b 40 48          	mov    0x48(%rax),%rax
    6fd8:	3b 68 10             	cmp    0x10(%rax),%ebp
    6fdb:	74 0c                	je     6fe9 <barriered_work+0x479>
    6fdd:	48 8d 3d 7f 12 00 00 	lea    0x127f(%rip),%rdi        # 8263 <_IO_stdin_used+0x263>
    6fe4:	e8 47 b3 ff ff       	call   2330 <puts@plt>
    6fe9:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6ff0:	31 ff                	xor    %edi,%edi
    6ff2:	48 c1 e6 05          	shl    $0x5,%rsi
    6ff6:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6ffd:	48 83 c6 10          	add    $0x10,%rsi
    7001:	e8 4a b3 ff ff       	call   2350 <clock_gettime@plt>
    7006:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    700d:	48 83 c0 01          	add    $0x1,%rax
    7011:	48 99                	cqto
    7013:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    701a:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    7020:	83 e8 01             	sub    $0x1,%eax
    7023:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    702a:	44 39 e0             	cmp    %r12d,%eax
    702d:	0f 85 fb fe ff ff    	jne    6f2e <barriered_work+0x3be>
    7033:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    703a:	85 d2                	test   %edx,%edx
    703c:	0f 8e ec fe ff ff    	jle    6f2e <barriered_work+0x3be>
    7042:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    7049:	48 c1 e2 09          	shl    $0x9,%rdx
    704d:	48 63 71 08          	movslq 0x8(%rcx),%rsi
    7051:	48 89 f0             	mov    %rsi,%rax
    7054:	48 c1 e0 05          	shl    $0x5,%rax
    7058:	48 29 f0             	sub    %rsi,%rax
    705b:	48 8b 71 20          	mov    0x20(%rcx),%rsi
    705f:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
    7063:	48 8b 40 38          	mov    0x38(%rax),%rax
    7067:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    706b:	80 e6 02             	and    $0x2,%dh
    706e:	74 20                	je     7090 <barriered_work+0x520>
    7070:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    7077:	48 05 00 02 00 00    	add    $0x200,%rax
    707d:	48 39 c8             	cmp    %rcx,%rax
    7080:	0f 84 a8 fe ff ff    	je     6f2e <barriered_work+0x3be>
    7086:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    7090:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    7097:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
    709e:	48 05 00 04 00 00    	add    $0x400,%rax
    70a4:	48 39 c8             	cmp    %rcx,%rax
    70a7:	75 e7                	jne    7090 <barriered_work+0x520>
    70a9:	e9 80 fe ff ff       	jmp    6f2e <barriered_work+0x3be>
    70ae:	66 90                	xchg   %ax,%ax
    70b0:	39 c5                	cmp    %eax,%ebp
    70b2:	0f 85 60 fb ff ff    	jne    6c18 <barriered_work+0xa8>
    70b8:	48 8b 69 08          	mov    0x8(%rcx),%rbp
    70bc:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
    70c1:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
    70c6:	8b 45 10             	mov    0x10(%rbp),%eax
    70c9:	48 83 45 00 01       	addq   $0x1,0x0(%rbp)
    70ce:	44 8d 60 01          	lea    0x1(%rax),%r12d
    70d2:	44 89 65 10          	mov    %r12d,0x10(%rbp)
    70d6:	e8 c5 b2 ff ff       	call   23a0 <nanosleep@plt>
    70db:	44 3b 65 10          	cmp    0x10(%rbp),%r12d
    70df:	74 0c                	je     70ed <barriered_work+0x57d>
    70e1:	48 8d 3d 43 11 00 00 	lea    0x1143(%rip),%rdi        # 822b <_IO_stdin_used+0x22b>
    70e8:	e8 43 b2 ff ff       	call   2330 <puts@plt>
    70ed:	48 63 ab 30 01 00 00 	movslq 0x130(%rbx),%rbp
    70f4:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    70fb:	8d 45 01             	lea    0x1(%rbp),%eax
    70fe:	48 8b b1 f0 00 00 00 	mov    0xf0(%rcx),%rsi
    7105:	99                   	cltd
    7106:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    710c:	89 56 04             	mov    %edx,0x4(%rsi)
    710f:	83 fd 01             	cmp    $0x1,%ebp
    7112:	0f 85 00 fb ff ff    	jne    6c18 <barriered_work+0xa8>
    7118:	8b 81 e8 00 00 00    	mov    0xe8(%rcx),%eax
    711e:	83 c0 01             	add    $0x1,%eax
    7121:	99                   	cltd
    7122:	f7 b9 c0 00 00 00    	idivl  0xc0(%rcx)
    7128:	89 16                	mov    %edx,(%rsi)
    712a:	e9 e9 fa ff ff       	jmp    6c18 <barriered_work+0xa8>
    712f:	e8 4c b2 ff ff       	call   2380 <__stack_chk_fail@plt>
    7134:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    713f:	90                   	nop

0000000000007140 <barriered_work_ingest_andwork>:
    7140:	f3 0f 1e fa          	endbr64
    7144:	53                   	push   %rbx
    7145:	48 89 fb             	mov    %rdi,%rbx
    7148:	e8 03 f1 ff ff       	call   6250 <barriered_work_ingest>
    714d:	48 89 df             	mov    %rbx,%rdi
    7150:	5b                   	pop    %rbx
    7151:	e9 1a fa ff ff       	jmp    6b70 <barriered_work>
    7156:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000007160 <barriered_nulltask>:
    7160:	f3 0f 1e fa          	endbr64
    7164:	31 c0                	xor    %eax,%eax
    7166:	c3                   	ret
    7167:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007170 <barriered_steal>:
    7170:	f3 0f 1e fa          	endbr64
    7174:	31 c0                	xor    %eax,%eax
    7176:	c3                   	ret
    7177:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007180 <after>:
    7180:	f3 0f 1e fa          	endbr64
    7184:	31 c0                	xor    %eax,%eax
    7186:	48 39 d7             	cmp    %rdx,%rdi
    7189:	7e 08                	jle    7193 <after+0x13>
    718b:	31 c0                	xor    %eax,%eax
    718d:	48 39 ce             	cmp    %rcx,%rsi
    7190:	0f 9f c0             	setg   %al
    7193:	c3                   	ret
    7194:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    719f:	90                   	nop

00000000000071a0 <within>:
    71a0:	f3 0f 1e fa          	endbr64
    71a4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    71a9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    71ae:	31 c0                	xor    %eax,%eax
    71b0:	48 39 d7             	cmp    %rdx,%rdi
    71b3:	7f 18                	jg     71cd <within+0x2d>
    71b5:	4d 39 d8             	cmp    %r11,%r8
    71b8:	0f 9e c2             	setle  %dl
    71bb:	48 39 ce             	cmp    %rcx,%rsi
    71be:	0f 9e c0             	setle  %al
    71c1:	21 c2                	and    %eax,%edx
    71c3:	31 c0                	xor    %eax,%eax
    71c5:	4d 39 d1             	cmp    %r10,%r9
    71c8:	0f 9e c0             	setle  %al
    71cb:	21 d0                	and    %edx,%eax
    71cd:	c3                   	ret
    71ce:	66 90                	xchg   %ax,%ax

00000000000071d0 <overlap>:
    71d0:	f3 0f 1e fa          	endbr64
    71d4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    71d9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    71de:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    71e3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    71e8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    71ed:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    71f2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    71f7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    71fc:	48 39 fe             	cmp    %rdi,%rsi
    71ff:	7d 2f                	jge    7230 <overlap+0x60>
    7201:	48 39 ca             	cmp    %rcx,%rdx
    7204:	7d 62                	jge    7268 <overlap+0x98>
    7206:	4d 39 da             	cmp    %r11,%r10
    7209:	7d 0e                	jge    7219 <overlap+0x49>
    720b:	b8 01 00 00 00       	mov    $0x1,%eax
    7210:	4d 39 c1             	cmp    %r8,%r9
    7213:	0f 8c 7f 00 00 00    	jl     7298 <overlap+0xc8>
    7219:	31 c0                	xor    %eax,%eax
    721b:	4d 39 c1             	cmp    %r8,%r9
    721e:	7f 4c                	jg     726c <overlap+0x9c>
    7220:	31 c0                	xor    %eax,%eax
    7222:	4d 39 da             	cmp    %r11,%r10
    7225:	0f 9e c0             	setle  %al
    7228:	c3                   	ret
    7229:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7230:	7e 4e                	jle    7280 <overlap+0xb0>
    7232:	48 39 ca             	cmp    %rcx,%rdx
    7235:	7f 39                	jg     7270 <overlap+0xa0>
    7237:	75 31                	jne    726a <overlap+0x9a>
    7239:	4d 39 c1             	cmp    %r8,%r9
    723c:	7c 2c                	jl     726a <overlap+0x9a>
    723e:	b8 01 00 00 00       	mov    $0x1,%eax
    7243:	4d 39 da             	cmp    %r11,%r10
    7246:	7d 24                	jge    726c <overlap+0x9c>
    7248:	48 39 ca             	cmp    %rcx,%rdx
    724b:	0f 94 c2             	sete   %dl
    724e:	48 39 fe             	cmp    %rdi,%rsi
    7251:	0f 94 c0             	sete   %al
    7254:	21 c2                	and    %eax,%edx
    7256:	31 c0                	xor    %eax,%eax
    7258:	4d 39 c1             	cmp    %r8,%r9
    725b:	0f 94 c0             	sete   %al
    725e:	21 d0                	and    %edx,%eax
    7260:	c3                   	ret
    7261:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7268:	74 af                	je     7219 <overlap+0x49>
    726a:	31 c0                	xor    %eax,%eax
    726c:	c3                   	ret
    726d:	0f 1f 00             	nopl   (%rax)
    7270:	4d 39 da             	cmp    %r11,%r10
    7273:	7e c4                	jle    7239 <overlap+0x69>
    7275:	b8 01 00 00 00       	mov    $0x1,%eax
    727a:	4d 39 c1             	cmp    %r8,%r9
    727d:	7e ba                	jle    7239 <overlap+0x69>
    727f:	c3                   	ret
    7280:	48 39 ca             	cmp    %rcx,%rdx
    7283:	7c 94                	jl     7219 <overlap+0x49>
    7285:	4d 39 c1             	cmp    %r8,%r9
    7288:	7d b4                	jge    723e <overlap+0x6e>
    728a:	48 39 ca             	cmp    %rcx,%rdx
    728d:	74 91                	je     7220 <overlap+0x50>
    728f:	eb d9                	jmp    726a <overlap+0x9a>
    7291:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7298:	c3                   	ret
    7299:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000072a0 <verify>:
    72a0:	f3 0f 1e fa          	endbr64
    72a4:	85 f6                	test   %esi,%esi
    72a6:	0f 8e 44 03 00 00    	jle    75f0 <verify+0x350>
    72ac:	41 57                	push   %r15
    72ae:	41 89 f7             	mov    %esi,%r15d
    72b1:	41 56                	push   %r14
    72b3:	45 31 f6             	xor    %r14d,%r14d
    72b6:	41 55                	push   %r13
    72b8:	41 54                	push   %r12
    72ba:	55                   	push   %rbp
    72bb:	53                   	push   %rbx
    72bc:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    72c0:	48 83 ec 58          	sub    $0x58,%rsp
    72c4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    72c9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    72ce:	45 31 e4             	xor    %r12d,%r12d
    72d1:	45 39 e6             	cmp    %r12d,%r14d
    72d4:	0f 84 4e 02 00 00    	je     7528 <verify+0x288>
    72da:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    72df:	8b 50 08             	mov    0x8(%rax),%edx
    72e2:	85 d2                	test   %edx,%edx
    72e4:	0f 8e 3e 02 00 00    	jle    7528 <verify+0x288>
    72ea:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    72ef:	31 c9                	xor    %ecx,%ecx
    72f1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    72f6:	31 c0                	xor    %eax,%eax
    72f8:	44 89 f2             	mov    %r14d,%edx
    72fb:	bf 01 00 00 00       	mov    $0x1,%edi
    7300:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    7305:	48 8d 35 67 0f 00 00 	lea    0xf67(%rip),%rsi        # 8273 <_IO_stdin_used+0x273>
    730c:	e8 9f b1 ff ff       	call   24b0 <__printf_chk@plt>
    7311:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7316:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    731b:	8b 40 08             	mov    0x8(%rax),%eax
    731e:	85 c0                	test   %eax,%eax
    7320:	0f 8e e6 01 00 00    	jle    750c <verify+0x26c>
    7326:	48 89 c8             	mov    %rcx,%rax
    7329:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    732e:	31 db                	xor    %ebx,%ebx
    7330:	48 c1 e0 09          	shl    $0x9,%rax
    7334:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    7339:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    733e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7343:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    7348:	4c 8b 20             	mov    (%rax),%r12
    734b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7350:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    7355:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    735a:	49 89 de             	mov    %rbx,%r14
    735d:	48 8d 35 24 0f 00 00 	lea    0xf24(%rip),%rsi        # 8288 <_IO_stdin_used+0x288>
    7364:	49 c1 e6 09          	shl    $0x9,%r14
    7368:	bf 01 00 00 00       	mov    $0x1,%edi
    736d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    7371:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    7379:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    737e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    7386:	31 c0                	xor    %eax,%eax
    7388:	e8 23 b1 ff ff       	call   24b0 <__printf_chk@plt>
    738d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7392:	4c 8b 20             	mov    (%rax),%r12
    7395:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    739e:	0f 8e 47 01 00 00    	jle    74eb <verify+0x24b>
    73a4:	4c 03 75 00          	add    0x0(%rbp),%r14
    73a8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    73ad:	ba 01 00 00 00       	mov    $0x1,%edx
    73b2:	4d 89 f5             	mov    %r14,%r13
    73b5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    73bc:	4d 85 f6             	test   %r14,%r14
    73bf:	0f 8e 21 01 00 00    	jle    74e6 <verify+0x246>
    73c5:	0f 1f 00             	nopl   (%rax)
    73c8:	48 89 d5             	mov    %rdx,%rbp
    73cb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    73d0:	31 db                	xor    %ebx,%ebx
    73d2:	4d 89 f2             	mov    %r14,%r10
    73d5:	48 c1 e5 05          	shl    $0x5,%rbp
    73d9:	48 83 ed 20          	sub    $0x20,%rbp
    73dd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    73e1:	49 89 ee             	mov    %rbp,%r14
    73e4:	48 89 dd             	mov    %rbx,%rbp
    73e7:	48 89 d3             	mov    %rdx,%rbx
    73ea:	eb 31                	jmp    741d <verify+0x17d>
    73ec:	0f 1f 40 00          	nopl   0x0(%rax)
    73f0:	4c 39 c2             	cmp    %r8,%rdx
    73f3:	0f 8d 57 01 00 00    	jge    7550 <verify+0x2b0>
    73f9:	4c 39 df             	cmp    %r11,%rdi
    73fc:	7e 05                	jle    7403 <verify+0x163>
    73fe:	49 39 c1             	cmp    %rax,%r9
    7401:	7c 75                	jl     7478 <verify+0x1d8>
    7403:	4c 39 df             	cmp    %r11,%rdi
    7406:	0f 8d ab 01 00 00    	jge    75b7 <verify+0x317>
    740c:	0f 1f 40 00          	nopl   0x0(%rax)
    7410:	48 83 c5 01          	add    $0x1,%rbp
    7414:	49 39 ea             	cmp    %rbp,%r10
    7417:	0f 8e a9 00 00 00    	jle    74c6 <verify+0x226>
    741d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    7424:	48 89 e8             	mov    %rbp,%rax
    7427:	48 c1 e0 05          	shl    $0x5,%rax
    742b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    7432:	4c 01 f2             	add    %r14,%rdx
    7435:	48 8b 08             	mov    (%rax),%rcx
    7438:	48 8b 78 10          	mov    0x10(%rax),%rdi
    743c:	48 8b 32             	mov    (%rdx),%rsi
    743f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    7443:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    7447:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    744b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    744f:	48 8b 40 18          	mov    0x18(%rax),%rax
    7453:	48 39 f1             	cmp    %rsi,%rcx
    7456:	7c 98                	jl     73f0 <verify+0x150>
    7458:	0f 8e 42 01 00 00    	jle    75a0 <verify+0x300>
    745e:	4c 39 c2             	cmp    %r8,%rdx
    7461:	0f 8f f9 00 00 00    	jg     7560 <verify+0x2c0>
    7467:	75 a7                	jne    7410 <verify+0x170>
    7469:	4c 39 df             	cmp    %r11,%rdi
    746c:	7f a2                	jg     7410 <verify+0x170>
    746e:	49 39 c1             	cmp    %rax,%r9
    7471:	7c 9d                	jl     7410 <verify+0x170>
    7473:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7478:	49 89 c1             	mov    %rax,%r9
    747b:	48 89 f9             	mov    %rdi,%rcx
    747e:	48 89 f2             	mov    %rsi,%rdx
    7481:	bf 01 00 00 00       	mov    $0x1,%edi
    7486:	48 8d 35 cb 11 00 00 	lea    0x11cb(%rip),%rsi        # 8658 <_IO_stdin_used+0x658>
    748d:	31 c0                	xor    %eax,%eax
    748f:	48 83 c5 01          	add    $0x1,%rbp
    7493:	e8 18 b0 ff ff       	call   24b0 <__printf_chk@plt>
    7498:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    749d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    74a2:	4c 03 28             	add    (%rax),%r13
    74a5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    74aa:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
    74b1:	4c 8b 20             	mov    (%rax),%r12
    74b4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    74b9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    74bd:	49 39 ea             	cmp    %rbp,%r10
    74c0:	0f 8f 57 ff ff ff    	jg     741d <verify+0x17d>
    74c6:	48 89 da             	mov    %rbx,%rdx
    74c9:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    74d0:	7d 14                	jge    74e6 <verify+0x246>
    74d2:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    74d9:	48 83 c2 01          	add    $0x1,%rdx
    74dd:	4d 85 f6             	test   %r14,%r14
    74e0:	0f 8f e2 fe ff ff    	jg     73c8 <verify+0x128>
    74e6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    74eb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    74f0:	48 83 c3 01          	add    $0x1,%rbx
    74f4:	39 58 08             	cmp    %ebx,0x8(%rax)
    74f7:	0f 8f 53 fe ff ff    	jg     7350 <verify+0xb0>
    74fd:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    7502:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    7507:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
    750c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7511:	48 83 c1 01          	add    $0x1,%rcx
    7515:	39 48 08             	cmp    %ecx,0x8(%rax)
    7518:	0f 8f d8 fd ff ff    	jg     72f6 <verify+0x56>
    751e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    7523:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    7528:	48 81 44 24 10 f8 00 00 00 	addq   $0xf8,0x10(%rsp)
    7531:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    7536:	41 39 c7             	cmp    %eax,%r15d
    7539:	0f 84 86 00 00 00    	je     75c5 <verify+0x325>
    753f:	41 89 c4             	mov    %eax,%r12d
    7542:	e9 8a fd ff ff       	jmp    72d1 <verify+0x31>
    7547:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    7550:	0f 85 ba fe ff ff    	jne    7410 <verify+0x170>
    7556:	e9 a8 fe ff ff       	jmp    7403 <verify+0x163>
    755b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7560:	49 39 c1             	cmp    %rax,%r9
    7563:	7e 09                	jle    756e <verify+0x2ce>
    7565:	4c 39 df             	cmp    %r11,%rdi
    7568:	0f 8c 0a ff ff ff    	jl     7478 <verify+0x1d8>
    756e:	4c 39 df             	cmp    %r11,%rdi
    7571:	0f 8f 99 fe ff ff    	jg     7410 <verify+0x170>
    7577:	49 39 c1             	cmp    %rax,%r9
    757a:	0f 8d f8 fe ff ff    	jge    7478 <verify+0x1d8>
    7580:	48 39 f1             	cmp    %rsi,%rcx
    7583:	0f 85 87 fe ff ff    	jne    7410 <verify+0x170>
    7589:	4c 39 c2             	cmp    %r8,%rdx
    758c:	0f 85 7e fe ff ff    	jne    7410 <verify+0x170>
    7592:	4c 39 df             	cmp    %r11,%rdi
    7595:	0f 84 dd fe ff ff    	je     7478 <verify+0x1d8>
    759b:	e9 70 fe ff ff       	jmp    7410 <verify+0x170>
    75a0:	4c 39 c2             	cmp    %r8,%rdx
    75a3:	0f 8c 5a fe ff ff    	jl     7403 <verify+0x163>
    75a9:	4c 39 df             	cmp    %r11,%rdi
    75ac:	7e c9                	jle    7577 <verify+0x2d7>
    75ae:	4c 39 c2             	cmp    %r8,%rdx
    75b1:	0f 85 59 fe ff ff    	jne    7410 <verify+0x170>
    75b7:	49 39 c1             	cmp    %rax,%r9
    75ba:	0f 8f 50 fe ff ff    	jg     7410 <verify+0x170>
    75c0:	e9 b3 fe ff ff       	jmp    7478 <verify+0x1d8>
    75c5:	48 81 44 24 18 f8 00 00 00 	addq   $0xf8,0x18(%rsp)
    75ce:	41 8d 46 01          	lea    0x1(%r14),%eax
    75d2:	45 39 e6             	cmp    %r12d,%r14d
    75d5:	74 08                	je     75df <verify+0x33f>
    75d7:	41 89 c6             	mov    %eax,%r14d
    75da:	e9 ea fc ff ff       	jmp    72c9 <verify+0x29>
    75df:	48 83 c4 58          	add    $0x58,%rsp
    75e3:	31 c0                	xor    %eax,%eax
    75e5:	5b                   	pop    %rbx
    75e6:	5d                   	pop    %rbp
    75e7:	41 5c                	pop    %r12
    75e9:	41 5d                	pop    %r13
    75eb:	41 5e                	pop    %r14
    75ed:	41 5f                	pop    %r15
    75ef:	c3                   	ret
    75f0:	31 c0                	xor    %eax,%eax
    75f2:	c3                   	ret

Disassembly of section .fini:

00000000000075f4 <_fini>:
    75f4:	f3 0f 1e fa          	endbr64
    75f8:	48 83 ec 08          	sub    $0x8,%rsp
    75fc:	48 83 c4 08          	add    $0x8,%rsp
    7600:	c3                   	ret
