
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
    268c:	48 81 ec 18 01 00 00 	sub    $0x118,%rsp
    2693:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    269c:	48 89 84 24 08 01 00 00 	mov    %rax,0x108(%rsp)
    26a4:	48 8d 05 55 1f 00 00 	lea    0x1f55(%rip),%rax        # 4600 <barriered_reset>
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
    2847:	be 00 01 00 00       	mov    $0x100,%esi
    284c:	bf 0a 00 00 00       	mov    $0xa,%edi
    2851:	48 89 84 24 80 00 00 00 	mov    %rax,0x80(%rsp)
    2859:	e8 a2 fb ff ff       	call   2400 <calloc@plt>
    285e:	be 28 00 00 00       	mov    $0x28,%esi
    2863:	bf 01 00 00 00       	mov    $0x1,%edi
    2868:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    286d:	e8 8e fb ff ff       	call   2400 <calloc@plt>
    2872:	be 28 00 00 00       	mov    $0x28,%esi
    2877:	bf 64 00 00 00       	mov    $0x64,%edi
    287c:	48 89 84 24 c8 00 00 00 	mov    %rax,0xc8(%rsp)
    2884:	e8 77 fb ff ff       	call   2400 <calloc@plt>
    2889:	48 89 84 24 d0 00 00 00 	mov    %rax,0xd0(%rsp)
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
    2923:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
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
    299e:	4c 8d b4 24 f8 00 00 00 	lea    0xf8(%rsp),%r14
    29a6:	41 89 dd             	mov    %ebx,%r13d
    29a9:	c7 84 24 00 01 00 00 06 00 00 00 	movl   $0x6,0x100(%rsp)
    29b4:	48 89 84 24 f8 00 00 00 	mov    %rax,0xf8(%rsp)
    29bc:	e8 3f fa ff ff       	call   2400 <calloc@plt>
    29c1:	be 10 00 00 00       	mov    $0x10,%esi
    29c6:	bf 01 00 00 00       	mov    $0x1,%edi
    29cb:	48 89 84 24 a0 00 00 00 	mov    %rax,0xa0(%rsp)
    29d3:	e8 28 fa ff ff       	call   2400 <calloc@plt>
    29d8:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
    29e0:	49 89 c3             	mov    %rax,%r11
    29e3:	c7 00 ff ff ff ff    	movl   $0xffffffff,(%rax)
    29e9:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    29ee:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
    29f6:	49 89 43 08          	mov    %rax,0x8(%r11)
    29fa:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    2a02:	c7 44 24 78 00 00 00 00 	movl   $0x0,0x78(%rsp)
    2a0a:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
    2a12:	4c 89 9c 24 c0 00 00 00 	mov    %r11,0xc0(%rsp)
    2a1a:	be 00 01 00 00       	mov    $0x100,%esi
    2a1f:	bf 01 00 00 00       	mov    $0x1,%edi
    2a24:	44 89 7c 24 50       	mov    %r15d,0x50(%rsp)
    2a29:	e8 d2 f9 ff ff       	call   2400 <calloc@plt>
    2a2e:	be 08 00 00 00       	mov    $0x8,%esi
    2a33:	bf 64 00 00 00       	mov    $0x64,%edi
    2a38:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2a3d:	e8 be f9 ff ff       	call   2400 <calloc@plt>
    2a42:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2a47:	48 8b 9c 24 a0 00 00 00 	mov    0xa0(%rsp),%rbx
    2a4f:	48 c7 44 24 68 00 00 00 00 	movq   $0x0,0x68(%rsp)
    2a58:	48 89 ac 24 d8 00 00 00 	mov    %rbp,0xd8(%rsp)
    2a60:	48 89 82 88 00 00 00 	mov    %rax,0x88(%rdx)
    2a67:	48 8b 84 24 c0 00 00 00 	mov    0xc0(%rsp),%rax
    2a6f:	4a 89 14 fb          	mov    %rdx,(%rbx,%r15,8)
    2a73:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    2a78:	48 89 82 98 00 00 00 	mov    %rax,0x98(%rdx)
    2a7f:	43 8b 04 be          	mov    (%r14,%r15,4),%eax
    2a83:	c7 82 90 00 00 00 06 00 00 00 	movl   $0x6,0x90(%rdx)
    2a8d:	89 82 a0 00 00 00    	mov    %eax,0xa0(%rdx)
    2a93:	4c 89 f8             	mov    %r15,%rax
    2a96:	48 c1 e0 09          	shl    $0x9,%rax
    2a9a:	48 89 94 24 e0 00 00 00 	mov    %rdx,0xe0(%rsp)
    2aa2:	4c 8d 0c 18          	lea    (%rax,%rbx,1),%r9
    2aa6:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2aab:	43 8d 1c 3f          	lea    (%r15,%r15,1),%ebx
    2aaf:	4c 89 b4 24 e8 00 00 00 	mov    %r14,0xe8(%rsp)
    2ab7:	4d 89 fe             	mov    %r15,%r14
    2aba:	41 89 df             	mov    %ebx,%r15d
    2abd:	48 c1 e0 04          	shl    $0x4,%rax
    2ac1:	48 01 e8             	add    %rbp,%rax
    2ac4:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2ac9:	48 8b 84 24 a0 00 00 00 	mov    0xa0(%rsp),%rax
    2ad1:	8b 54 24 50          	mov    0x50(%rsp),%edx
    2ad5:	44 89 f9             	mov    %r15d,%ecx
    2ad8:	bf 01 00 00 00       	mov    $0x1,%edi
    2add:	48 8b 9c 24 e0 00 00 00 	mov    0xe0(%rsp),%rbx
    2ae5:	48 8d 35 54 5c 00 00 	lea    0x5c54(%rip),%rsi        # 8740 <_IO_stdin_used+0x740>
    2aec:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2af1:	49 89 81 e0 00 00 00 	mov    %rax,0xe0(%r9)
    2af8:	48 8b 84 24 c0 00 00 00 	mov    0xc0(%rsp),%rax
    2b00:	49 89 99 d8 00 00 00 	mov    %rbx,0xd8(%r9)
    2b07:	41 89 91 e8 00 00 00 	mov    %edx,0xe8(%r9)
    2b0e:	49 89 81 f0 00 00 00 	mov    %rax,0xf0(%r9)
    2b15:	31 c0                	xor    %eax,%eax
    2b17:	e8 94 f9 ff ff       	call   24b0 <__printf_chk@plt>
    2b1c:	be 08 00 00 00       	mov    $0x8,%esi
    2b21:	bf 02 00 00 00       	mov    $0x2,%edi
    2b26:	e8 d5 f8 ff ff       	call   2400 <calloc@plt>
    2b2b:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2b30:	be 80 00 00 00       	mov    $0x80,%esi
    2b35:	bf 01 00 00 00       	mov    $0x1,%edi
    2b3a:	48 89 c5             	mov    %rax,%rbp
    2b3d:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    2b44:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    2b49:	4c 89 0c 18          	mov    %r9,(%rax,%rbx,1)
    2b4d:	e8 ae f8 ff ff       	call   2400 <calloc@plt>
    2b52:	45 89 f8             	mov    %r15d,%r8d
    2b55:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2b5a:	41 83 e0 01          	and    $0x1,%r8d
    2b5e:	48 89 c3             	mov    %rax,%rbx
    2b61:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2b66:	0f 84 16 11 00 00    	je     3c82 <main+0x1612>
    2b6c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2b71:	41 8d 57 ff          	lea    -0x1(%r15),%edx
    2b75:	41 8d 7f 01          	lea    0x1(%r15),%edi
    2b79:	48 89 d1             	mov    %rdx,%rcx
    2b7c:	89 bc 24 88 00 00 00 	mov    %edi,0x88(%rsp)
    2b83:	48 c1 e2 08          	shl    $0x8,%rdx
    2b87:	48 01 c2             	add    %rax,%rdx
    2b8a:	48 8d 45 08          	lea    0x8(%rbp),%rax
    2b8e:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2b93:	4c 89 c8             	mov    %r9,%rax
    2b96:	48 89 45 08          	mov    %rax,0x8(%rbp)
    2b9a:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    2ba2:	48 8d 35 c7 5b 00 00 	lea    0x5bc7(%rip),%rsi        # 8770 <_IO_stdin_used+0x770>
    2ba9:	bf 01 00 00 00       	mov    $0x1,%edi
    2bae:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2bb2:	49 89 41 48          	mov    %rax,0x48(%r9)
    2bb6:	31 c0                	xor    %eax,%eax
    2bb8:	48 89 55 00          	mov    %rdx,0x0(%rbp)
    2bbc:	44 89 fa             	mov    %r15d,%edx
    2bbf:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2bc4:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2bc8:	e8 e3 f8 ff ff       	call   24b0 <__printf_chk@plt>
    2bcd:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2bd1:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2bd6:	31 c0                	xor    %eax,%eax
    2bd8:	44 89 fa             	mov    %r15d,%edx
    2bdb:	48 8d 35 be 5b 00 00 	lea    0x5bbe(%rip),%rsi        # 87a0 <_IO_stdin_used+0x7a0>
    2be2:	bf 01 00 00 00       	mov    $0x1,%edi
    2be7:	41 89 89 b8 00 00 00 	mov    %ecx,0xb8(%r9)
    2bee:	8b 4c 24 78          	mov    0x78(%rsp),%ecx
    2bf2:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2bf7:	e8 b4 f8 ff ff       	call   24b0 <__printf_chk@plt>
    2bfc:	41 83 ff 01          	cmp    $0x1,%r15d
    2c00:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2c05:	0f 8f a0 10 00 00    	jg     3cab <main+0x163b>
    2c0b:	48 63 44 24 78       	movslq 0x78(%rsp),%rax
    2c10:	48 89 c7             	mov    %rax,%rdi
    2c13:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2c19:	77 12                	ja     2c2d <main+0x5bd>
    2c1b:	48 c1 e8 06          	shr    $0x6,%rax
    2c1f:	ba 01 00 00 00       	mov    $0x1,%edx
    2c24:	89 f9                	mov    %edi,%ecx
    2c26:	48 d3 e2             	shl    %cl,%rdx
    2c29:	48 09 14 c3          	or     %rdx,(%rbx,%rax,8)
    2c2d:	83 44 24 78 02       	addl   $0x2,0x78(%rsp)
    2c32:	45 89 79 08          	mov    %r15d,0x8(%r9)
    2c36:	be 10 00 00 00       	mov    $0x10,%esi
    2c3b:	bf 64 00 00 00       	mov    $0x64,%edi
    2c40:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    2c48:	49 89 99 b0 00 00 00 	mov    %rbx,0xb0(%r9)
    2c4f:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
    2c56:	48 8b 84 24 c8 00 00 00 	mov    0xc8(%rsp),%rax
    2c5e:	49 89 69 18          	mov    %rbp,0x18(%r9)
    2c62:	31 ed                	xor    %ebp,%ebp
    2c64:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
    2c6b:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2c70:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
    2c77:	49 89 41 20          	mov    %rax,0x20(%r9)
    2c7b:	48 8b 05 86 60 00 00 	mov    0x6086(%rip),%rax        # 8d08 <_IO_stdin_used+0xd08>
    2c82:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
    2c8a:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
    2c91:	48 8b 05 78 60 00 00 	mov    0x6078(%rip),%rax        # 8d10 <_IO_stdin_used+0xd10>
    2c98:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2c9d:	49 89 41 28          	mov    %rax,0x28(%r9)
    2ca1:	e8 5a f7 ff ff       	call   2400 <calloc@plt>
    2ca6:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2cab:	be 10 00 00 00       	mov    $0x10,%esi
    2cb0:	bf 64 00 00 00       	mov    $0x64,%edi
    2cb5:	49 89 41 68          	mov    %rax,0x68(%r9)
    2cb9:	e8 42 f7 ff ff       	call   2400 <calloc@plt>
    2cbe:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2cc3:	be 28 00 00 00       	mov    $0x28,%esi
    2cc8:	66 0f 6f 3d 00 60 00 00 	movdqa 0x6000(%rip),%xmm7        # 8cd0 <_IO_stdin_used+0xcd0>
    2cd0:	bf 64 00 00 00       	mov    $0x64,%edi
    2cd5:	49 89 41 70          	mov    %rax,0x70(%r9)
    2cd9:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
    2ce1:	e8 1a f7 ff ff       	call   2400 <calloc@plt>
    2ce6:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2ceb:	bf 03 00 00 00       	mov    $0x3,%edi
    2cf0:	66 0f 6f 35 d8 5f 00 00 	movdqa 0x5fd8(%rip),%xmm6        # 8cd0 <_IO_stdin_used+0xcd0>
    2cf8:	be 00 02 00 00       	mov    $0x200,%esi
    2cfd:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
    2d04:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
    2d0c:	e8 ef f6 ff ff       	call   2400 <calloc@plt>
    2d11:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2d16:	44 89 7c 24 18       	mov    %r15d,0x18(%rsp)
    2d1b:	45 89 ef             	mov    %r13d,%r15d
    2d1e:	48 63 bc 24 88 00 00 00 	movslq 0x88(%rsp),%rdi
    2d26:	48 89 c2             	mov    %rax,%rdx
    2d29:	49 89 41 38          	mov    %rax,0x38(%r9)
    2d2d:	48 89 fb             	mov    %rdi,%rbx
    2d30:	48 69 ff ab aa aa 2a 	imul   $0x2aaaaaab,%rdi,%rdi
    2d37:	4c 89 4c 24 48       	mov    %r9,0x48(%rsp)
    2d3c:	89 d8                	mov    %ebx,%eax
    2d3e:	c1 f8 1f             	sar    $0x1f,%eax
    2d41:	48 c1 ef 20          	shr    $0x20,%rdi
    2d45:	29 c7                	sub    %eax,%edi
    2d47:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2d4a:	01 c0                	add    %eax,%eax
    2d4c:	29 c3                	sub    %eax,%ebx
    2d4e:	89 9c 24 8c 00 00 00 	mov    %ebx,0x8c(%rsp)
    2d55:	48 63 c5             	movslq %ebp,%rax
    2d58:	be 00 01 00 00       	mov    $0x100,%esi
    2d5d:	bf 06 00 00 00       	mov    $0x6,%edi
    2d62:	45 31 ed             	xor    %r13d,%r13d
    2d65:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2d6a:	48 c1 e0 09          	shl    $0x9,%rax
    2d6e:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
    2d72:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2d77:	48 8d 05 42 18 00 00 	lea    0x1842(%rip),%rax        # 45c0 <do_protected_write>
    2d7e:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
    2d85:	e8 76 f6 ff ff       	call   2400 <calloc@plt>
    2d8a:	8b 74 24 58          	mov    0x58(%rsp),%esi
    2d8e:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
    2d95:	48 89 c1             	mov    %rax,%rcx
    2d98:	49 89 c4             	mov    %rax,%r12
    2d9b:	85 f6                	test   %esi,%esi
    2d9d:	0f 84 82 01 00 00    	je     2f25 <main+0x8b5>
    2da3:	8b 44 24 18          	mov    0x18(%rsp),%eax
    2da7:	48 89 8c 24 90 00 00 00 	mov    %rcx,0x90(%rsp)
    2daf:	48 89 cb             	mov    %rcx,%rbx
    2db2:	45 89 ec             	mov    %r13d,%r12d
    2db5:	83 e8 01             	sub    $0x1,%eax
    2db8:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2dbc:	eb 17                	jmp    2dd5 <main+0x765>
    2dbe:	66 90                	xchg   %ax,%ax
    2dc0:	41 83 c4 01          	add    $0x1,%r12d
    2dc4:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    2dcb:	41 83 fc 06          	cmp    $0x6,%r12d
    2dcf:	0f 84 d0 02 00 00    	je     30a5 <main+0xa35>
    2dd5:	45 89 e5             	mov    %r12d,%r13d
    2dd8:	31 c0                	xor    %eax,%eax
    2dda:	44 89 e2             	mov    %r12d,%edx
    2ddd:	bf 01 00 00 00       	mov    $0x1,%edi
    2de2:	41 d1 fd             	sar    %r13d
    2de5:	48 8d 35 ed 55 00 00 	lea    0x55ed(%rip),%rsi        # 83d9 <_IO_stdin_used+0x3d9>
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
    2e4b:	48 8d 35 6e 59 00 00 	lea    0x596e(%rip),%rsi        # 87c0 <_IO_stdin_used+0x7c0>
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
    2efd:	66 0f 6f 35 db 5d 00 00 	movdqa 0x5ddb(%rip),%xmm6        # 8ce0 <_IO_stdin_used+0xce0>
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
    2f52:	48 8d 35 80 54 00 00 	lea    0x5480(%rip),%rsi        # 83d9 <_IO_stdin_used+0x3d9>
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
    2fbc:	48 8d 35 fd 57 00 00 	lea    0x57fd(%rip),%rsi        # 87c0 <_IO_stdin_used+0x7c0>
    2fc3:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
    2fc9:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
    2fd3:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    2fd9:	41 8d 47 01          	lea    0x1(%r15),%eax
    2fdd:	41 89 85 98 08 00 00 	mov    %eax,0x898(%r13)
    2fe4:	49 8d 85 80 04 00 00 	lea    0x480(%r13),%rax
    2feb:	49 89 44 24 80       	mov    %rax,-0x80(%r12)
    2ff0:	8b 84 24 8c 00 00 00 	mov    0x8c(%rsp),%eax
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
    3072:	66 0f 6f 35 66 5c 00 00 	movdqa 0x5c66(%rip),%xmm6        # 8ce0 <_IO_stdin_used+0xce0>
    307a:	4d 89 5d 00          	mov    %r11,0x0(%r13)
    307e:	4d 89 95 80 04 00 00 	mov    %r10,0x480(%r13)
    3085:	41 0f 29 b5 80 00 00 00 	movaps %xmm6,0x80(%r13)
    308d:	41 0f 29 b5 00 05 00 00 	movaps %xmm6,0x500(%r13)
    3095:	83 fb 06             	cmp    $0x6,%ebx
    3098:	0f 85 a5 fe ff ff    	jne    2f43 <main+0x8d3>
    309e:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    30a3:	eb 08                	jmp    30ad <main+0xa3d>
    30a5:	48 8b 8c 24 90 00 00 00 	mov    0x90(%rsp),%rcx
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
    30ce:	48 8d 35 14 53 00 00 	lea    0x5314(%rip),%rsi        # 83e9 <_IO_stdin_used+0x3e9>
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
    313d:	66 0f 6f 35 9b 5b 00 00 	movdqa 0x5b9b(%rip),%xmm6        # 8ce0 <_IO_stdin_used+0xce0>
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
    329a:	44 8b 64 24 58       	mov    0x58(%rsp),%r12d
    329f:	ba 00 01 00 00       	mov    $0x100,%edx
    32a4:	31 c0                	xor    %eax,%eax
    32a6:	48 8d 0d 3b 55 00 00 	lea    0x553b(%rip),%rcx        # 87e8 <_IO_stdin_used+0x7e8>
    32ad:	be 01 00 00 00       	mov    $0x1,%esi
    32b2:	41 54                	push   %r12
    32b4:	44 8b 44 24 28       	mov    0x28(%rsp),%r8d
    32b9:	e8 e2 f2 ff ff       	call   25a0 <__sprintf_chk@plt>
    32be:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
    32c3:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    32c8:	44 89 e7             	mov    %r12d,%edi
    32cb:	be 20 00 00 00       	mov    $0x20,%esi
    32d0:	45 89 63 18          	mov    %r12d,0x18(%r11)
    32d4:	4c 8b 64 24 58       	mov    0x58(%rsp),%r12
    32d9:	49 89 43 10          	mov    %rax,0x10(%r11)
    32dd:	49 63 44 24 08       	movslq 0x8(%r12),%rax
    32e2:	49 8b 54 24 38       	mov    0x38(%r12),%rdx
    32e7:	49 89 1b             	mov    %rbx,(%r11)
    32ea:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    32ef:	49 89 43 08          	mov    %rax,0x8(%r11)
    32f3:	8b 44 24 30          	mov    0x30(%rsp),%eax
    32f7:	48 01 d3             	add    %rdx,%rbx
    32fa:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    32ff:	89 83 a0 01 00 00    	mov    %eax,0x1a0(%rbx)
    3305:	83 c0 01             	add    $0x1,%eax
    3308:	89 44 24 30          	mov    %eax,0x30(%rsp)
    330c:	8d 45 01             	lea    0x1(%rbp),%eax
    330f:	83 e0 01             	and    $0x1,%eax
    3312:	89 bb 9c 01 00 00    	mov    %edi,0x19c(%rbx)
    3318:	bf 63 00 00 00       	mov    $0x63,%edi
    331d:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
    3323:	89 83 98 01 00 00    	mov    %eax,0x198(%rbx)
    3329:	4c 89 9b 90 01 00 00 	mov    %r11,0x190(%rbx)
    3330:	c7 83 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbx)
    333a:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
    3345:	e8 b6 f0 ff ff       	call   2400 <calloc@plt>
    334a:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
    3355:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
    335c:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    3361:	48 8b 00             	mov    (%rax),%rax
    3364:	8b 48 04             	mov    0x4(%rax),%ecx
    3367:	49 39 c4             	cmp    %rax,%r12
    336a:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
    3371:	89 8b 30 01 00 00    	mov    %ecx,0x130(%rbx)
    3377:	5a                   	pop    %rdx
    3378:	59                   	pop    %rcx
    3379:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    337e:	0f 85 3b 11 00 00    	jne    44bf <main+0x1e4f>
    3384:	66 0f 6f 05 64 59 00 00 	movdqa 0x5964(%rip),%xmm0        # 8cf0 <_IO_stdin_used+0xcf0>
    338c:	89 6b 04             	mov    %ebp,0x4(%rbx)
    338f:	48 8b 05 6a 59 00 00 	mov    0x596a(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
    3396:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
    33a0:	c7 83 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rbx)
    33aa:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
    33b1:	0f 11 83 34 01 00 00 	movups %xmm0,0x134(%rbx)
    33b8:	83 fd 01             	cmp    $0x1,%ebp
    33bb:	0f 84 05 01 00 00    	je     34c6 <main+0xe56>
    33c1:	85 ed                	test   %ebp,%ebp
    33c3:	0f 84 e5 00 00 00    	je     34ae <main+0xe3e>
    33c9:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
    33ce:	48 8d 05 ab 37 00 00 	lea    0x37ab(%rip),%rax        # 6b80 <barriered_work>
    33d5:	be 08 00 00 00       	mov    $0x8,%esi
    33da:	45 89 fd             	mov    %r15d,%r13d
    33dd:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
    33e4:	bf 01 00 00 00       	mov    $0x1,%edi
    33e9:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    33f4:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
    33f9:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    33fe:	e8 fd ef ff ff       	call   2400 <calloc@plt>
    3403:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    3408:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
    340d:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    3412:	83 44 24 7c 01       	addl   $0x1,0x7c(%rsp)
    3417:	49 89 41 50          	mov    %rax,0x50(%r9)
    341b:	49 81 c1 00 01 00 00 	add    $0x100,%r9
    3422:	66 0f 6f bc 24 b0 00 00 00 	movdqa 0xb0(%rsp),%xmm7
    342b:	48 89 18             	mov    %rbx,(%rax)
    342e:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3433:	48 83 c3 10          	add    $0x10,%rbx
    3437:	48 89 5c 24 60       	mov    %rbx,0x60(%rsp)
    343c:	48 8b 00             	mov    (%rax),%rax
    343f:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
    3446:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
    3450:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
    3457:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
    3461:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
    346b:	41 8b 81 04 ff ff ff 	mov    -0xfc(%r9),%eax
    3472:	c7 82 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rdx)
    347c:	48 83 7c 24 68 08    	cmpq   $0x8,0x68(%rsp)
    3482:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
    3488:	48 8b 05 71 58 00 00 	mov    0x5871(%rip),%rax        # 8d00 <_IO_stdin_used+0xd00>
    348f:	48 89 82 44 05 00 00 	mov    %rax,0x544(%rdx)
    3496:	74 3c                	je     34d4 <main+0xe64>
    3498:	48 c7 44 24 68 08 00 00 00 	movq   $0x8,0x68(%rsp)
    34a1:	44 8b bc 24 88 00 00 00 	mov    0x88(%rsp),%r15d
    34a9:	e9 1b f6 ff ff       	jmp    2ac9 <main+0x459>
    34ae:	48 8d 05 3b 3c 00 00 	lea    0x3c3b(%rip),%rax        # 70f0 <barriered_work_ingest_andwork>
    34b5:	bd 01 00 00 00       	mov    $0x1,%ebp
    34ba:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
    34c1:	e9 8f f8 ff ff       	jmp    2d55 <main+0x6e5>
    34c6:	48 8d 05 b3 36 00 00 	lea    0x36b3(%rip),%rax        # 6b80 <barriered_work>
    34cd:	bd 02 00 00 00       	mov    $0x2,%ebp
    34d2:	eb e6                	jmp    34ba <main+0xe4a>
    34d4:	4d 89 f7             	mov    %r14,%r15
    34d7:	48 8b ac 24 d8 00 00 00 	mov    0xd8(%rsp),%rbp
    34df:	48 83 84 24 98 00 00 00 18 	addq   $0x18,0x98(%rsp)
    34e8:	49 83 c7 01          	add    $0x1,%r15
    34ec:	4c 8b b4 24 e8 00 00 00 	mov    0xe8(%rsp),%r14
    34f4:	49 83 ff 03          	cmp    $0x3,%r15
    34f8:	0f 85 1c f5 ff ff    	jne    2a1a <main+0x3aa>
    34fe:	bf 00 04 00 00       	mov    $0x400,%edi
    3503:	be 08 00 00 00       	mov    $0x8,%esi
    3508:	31 ed                	xor    %ebp,%ebp
    350a:	e8 f1 ee ff ff       	call   2400 <calloc@plt>
    350f:	4c 8b 54 24 38       	mov    0x38(%rsp),%r10
    3514:	bf 00 02 00 00       	mov    $0x200,%edi
    3519:	49 89 c7             	mov    %rax,%r15
    351c:	4c 8d 87 00 fe ff ff 	lea    -0x200(%rdi),%r8
    3523:	47 8b 4c 02 40       	mov    0x40(%r10,%r8,1),%r9d
    3528:	45 85 c9             	test   %r9d,%r9d
    352b:	0f 8e b0 00 00 00    	jle    35e1 <main+0xf71>
    3531:	4b 8b 4c 02 38       	mov    0x38(%r10,%r8,1),%rcx
    3536:	49 63 f1             	movslq %r9d,%rsi
    3539:	48 63 c5             	movslq %ebp,%rax
    353c:	48 c1 e6 09          	shl    $0x9,%rsi
    3540:	49 8d 14 c7          	lea    (%r15,%rax,8),%rdx
    3544:	48 01 ce             	add    %rcx,%rsi
    3547:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    3550:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    3557:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    355e:	48 83 c2 60          	add    $0x60,%rdx
    3562:	f3 0f 7e a0 00 01 00 00 	movq   0x100(%rax),%xmm4
    356a:	f3 0f 7e 28          	movq   (%rax),%xmm5
    356e:	f3 0f 7e 98 00 02 00 00 	movq   0x200(%rax),%xmm3
    3576:	f3 0f 7e 90 00 03 00 00 	movq   0x300(%rax),%xmm2
    357e:	f3 0f 7e 88 00 04 00 00 	movq   0x400(%rax),%xmm1
    3586:	0f 16 a0 80 01 00 00 	movhps 0x180(%rax),%xmm4
    358d:	f3 0f 7e 80 00 05 00 00 	movq   0x500(%rax),%xmm0
    3595:	0f 16 a8 80 00 00 00 	movhps 0x80(%rax),%xmm5
    359c:	0f 16 98 80 02 00 00 	movhps 0x280(%rax),%xmm3
    35a3:	0f 16 90 80 03 00 00 	movhps 0x380(%rax),%xmm2
    35aa:	0f 11 6a a0          	movups %xmm5,-0x60(%rdx)
    35ae:	0f 16 88 80 04 00 00 	movhps 0x480(%rax),%xmm1
    35b5:	0f 16 80 80 05 00 00 	movhps 0x580(%rax),%xmm0
    35bc:	0f 11 62 b0          	movups %xmm4,-0x50(%rdx)
    35c0:	0f 11 5a c0          	movups %xmm3,-0x40(%rdx)
    35c4:	0f 11 52 d0          	movups %xmm2,-0x30(%rdx)
    35c8:	0f 11 4a e0          	movups %xmm1,-0x20(%rdx)
    35cc:	0f 11 42 f0          	movups %xmm0,-0x10(%rdx)
    35d0:	48 39 ce             	cmp    %rcx,%rsi
    35d3:	0f 85 77 ff ff ff    	jne    3550 <main+0xee0>
    35d9:	43 8d 04 49          	lea    (%r9,%r9,2),%eax
    35dd:	8d 6c 85 00          	lea    0x0(%rbp,%rax,4),%ebp
    35e1:	49 81 c0 00 01 00 00 	add    $0x100,%r8
    35e8:	4c 39 c7             	cmp    %r8,%rdi
    35eb:	0f 85 32 ff ff ff    	jne    3523 <main+0xeb3>
    35f1:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    35f8:	48 81 ff 00 08 00 00 	cmp    $0x800,%rdi
    35ff:	0f 85 17 ff ff ff    	jne    351c <main+0xeac>
    3605:	48 8d 3d fb 4d 00 00 	lea    0x4dfb(%rip),%rdi        # 8407 <_IO_stdin_used+0x407>
    360c:	e8 1f ed ff ff       	call   2330 <puts@plt>
    3611:	48 8d 35 04 4e 00 00 	lea    0x4e04(%rip),%rsi        # 841c <_IO_stdin_used+0x41c>
    3618:	48 8d 3d ff 4d 00 00 	lea    0x4dff(%rip),%rdi        # 841e <_IO_stdin_used+0x41e>
    361f:	e8 cc ee ff ff       	call   24f0 <fopen@plt>
    3624:	49 89 c6             	mov    %rax,%r14
    3627:	85 ed                	test   %ebp,%ebp
    3629:	7e 6f                	jle    369a <main+0x102a>
    362b:	48 63 ed             	movslq %ebp,%rbp
    362e:	4c 8d 25 c6 4d 00 00 	lea    0x4dc6(%rip),%r12        # 83fb <_IO_stdin_used+0x3fb>
    3635:	4d 8d 2c ef          	lea    (%r15,%rbp,8),%r13
    3639:	48 8d 2d ff 4d 00 00 	lea    0x4dff(%rip),%rbp        # 843f <_IO_stdin_used+0x43f>
    3640:	be 01 00 00 00       	mov    $0x1,%esi
    3645:	bf fa 00 00 00       	mov    $0xfa,%edi
    364a:	49 83 c7 08          	add    $0x8,%r15
    364e:	e8 ad ed ff ff       	call   2400 <calloc@plt>
    3653:	4c 89 e1             	mov    %r12,%rcx
    3656:	ba fa 00 00 00       	mov    $0xfa,%edx
    365b:	be 01 00 00 00       	mov    $0x1,%esi
    3660:	48 89 c3             	mov    %rax,%rbx
    3663:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3667:	48 89 df             	mov    %rbx,%rdi
    366a:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3671:	31 c0                	xor    %eax,%eax
    3673:	e8 28 ef ff ff       	call   25a0 <__sprintf_chk@plt>
    3678:	48 89 da             	mov    %rbx,%rdx
    367b:	48 89 ee             	mov    %rbp,%rsi
    367e:	bf 01 00 00 00       	mov    $0x1,%edi
    3683:	31 c0                	xor    %eax,%eax
    3685:	e8 26 ee ff ff       	call   24b0 <__printf_chk@plt>
    368a:	4c 89 f6             	mov    %r14,%rsi
    368d:	48 89 df             	mov    %rbx,%rdi
    3690:	e8 2b ed ff ff       	call   23c0 <fputs@plt>
    3695:	4d 39 fd             	cmp    %r15,%r13
    3698:	75 a6                	jne    3640 <main+0xfd0>
    369a:	4c 89 f7             	mov    %r14,%rdi
    369d:	45 31 ff             	xor    %r15d,%r15d
    36a0:	4c 8d 25 c2 4d 00 00 	lea    0x4dc2(%rip),%r12        # 8469 <_IO_stdin_used+0x469>
    36a7:	e8 b4 ec ff ff       	call   2360 <fclose@plt>
    36ac:	48 8d 3d 74 4d 00 00 	lea    0x4d74(%rip),%rdi        # 8427 <_IO_stdin_used+0x427>
    36b3:	4c 89 fb             	mov    %r15,%rbx
    36b6:	e8 75 ec ff ff       	call   2330 <puts@plt>
    36bb:	89 da                	mov    %ebx,%edx
    36bd:	48 8d 35 7e 4d 00 00 	lea    0x4d7e(%rip),%rsi        # 8442 <_IO_stdin_used+0x442>
    36c4:	bf 01 00 00 00       	mov    $0x1,%edi
    36c9:	31 c0                	xor    %eax,%eax
    36cb:	e8 e0 ed ff ff       	call   24b0 <__printf_chk@plt>
    36d0:	49 89 dd             	mov    %rbx,%r13
    36d3:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    36d8:	8d 2c 1b             	lea    (%rbx,%rbx,1),%ebp
    36db:	49 c1 e5 09          	shl    $0x9,%r13
    36df:	45 31 ff             	xor    %r15d,%r15d
    36e2:	49 01 c5             	add    %rax,%r13
    36e5:	41 8d 0c 2f          	lea    (%r15,%rbp,1),%ecx
    36e9:	44 89 fa             	mov    %r15d,%edx
    36ec:	48 8d 35 59 4d 00 00 	lea    0x4d59(%rip),%rsi        # 844c <_IO_stdin_used+0x44c>
    36f3:	31 c0                	xor    %eax,%eax
    36f5:	bf 01 00 00 00       	mov    $0x1,%edi
    36fa:	45 31 f6             	xor    %r14d,%r14d
    36fd:	e8 ae ed ff ff       	call   24b0 <__printf_chk@plt>
    3702:	89 6c 24 10          	mov    %ebp,0x10(%rsp)
    3706:	4c 89 f1             	mov    %r14,%rcx
    3709:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    370e:	89 ca                	mov    %ecx,%edx
    3710:	48 8d 35 47 4d 00 00 	lea    0x4d47(%rip),%rsi        # 845e <_IO_stdin_used+0x45e>
    3717:	bf 01 00 00 00       	mov    $0x1,%edi
    371c:	31 c0                	xor    %eax,%eax
    371e:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    3723:	31 ed                	xor    %ebp,%ebp
    3725:	e8 86 ed ff ff       	call   24b0 <__printf_chk@plt>
    372a:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    372f:	48 c1 e3 09          	shl    $0x9,%rbx
    3733:	eb 2f                	jmp    3764 <main+0x10f4>
    3735:	0f 1f 00             	nopl   (%rax)
    3738:	83 fe 01             	cmp    $0x1,%esi
    373b:	0f 84 a6 00 00 00    	je     37e7 <main+0x1177>
    3741:	44 89 f2             	mov    %r14d,%edx
    3744:	4c 89 e6             	mov    %r12,%rsi
    3747:	bf 01 00 00 00       	mov    $0x1,%edi
    374c:	48 83 c5 01          	add    $0x1,%rbp
    3750:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    3757:	31 c0                	xor    %eax,%eax
    3759:	e8 52 ed ff ff       	call   24b0 <__printf_chk@plt>
    375e:	48 83 fd 06          	cmp    $0x6,%rbp
    3762:	74 50                	je     37b4 <main+0x1144>
    3764:	be 01 00 00 00       	mov    $0x1,%esi
    3769:	bf 64 00 00 00       	mov    $0x64,%edi
    376e:	41 89 ee             	mov    %ebp,%r14d
    3771:	e8 8a ec ff ff       	call   2400 <calloc@plt>
    3776:	4d 8b 45 38          	mov    0x38(%r13),%r8
    377a:	48 89 ef             	mov    %rbp,%rdi
    377d:	48 89 c1             	mov    %rax,%rcx
    3780:	48 c1 e7 08          	shl    $0x8,%rdi
    3784:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    378c:	48 01 f8             	add    %rdi,%rax
    378f:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    3795:	83 fe 02             	cmp    $0x2,%esi
    3798:	75 9e                	jne    3738 <main+0x10c8>
    379a:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    37a4:	48 89 01             	mov    %rax,(%rcx)
    37a7:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    37af:	48 01 f8             	add    %rdi,%rax
    37b2:	eb 8d                	jmp    3741 <main+0x10d1>
    37b4:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    37b9:	48 83 c1 01          	add    $0x1,%rcx
    37bd:	48 83 f9 03          	cmp    $0x3,%rcx
    37c1:	0f 85 47 ff ff ff    	jne    370e <main+0x109e>
    37c7:	8b 6c 24 10          	mov    0x10(%rsp),%ebp
    37cb:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    37d0:	49 81 c5 00 01 00 00 	add    $0x100,%r13
    37d7:	45 85 ff             	test   %r15d,%r15d
    37da:	75 28                	jne    3804 <main+0x1194>
    37dc:	41 bf 01 00 00 00    	mov    $0x1,%r15d
    37e2:	e9 fe fe ff ff       	jmp    36e5 <main+0x1075>
    37e7:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    37ed:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    37f4:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    37fc:	48 01 f8             	add    %rdi,%rax
    37ff:	e9 3d ff ff ff       	jmp    3741 <main+0x10d1>
    3804:	48 83 c3 01          	add    $0x1,%rbx
    3808:	48 83 fb 03          	cmp    $0x3,%rbx
    380c:	0f 85 a9 fe ff ff    	jne    36bb <main+0x104b>
    3812:	ba 07 00 00 00       	mov    $0x7,%edx
    3817:	48 8d 35 66 4c 00 00 	lea    0x4c66(%rip),%rsi        # 8484 <_IO_stdin_used+0x484>
    381e:	bf 01 00 00 00       	mov    $0x1,%edi
    3823:	31 c0                	xor    %eax,%eax
    3825:	e8 86 ec ff ff       	call   24b0 <__printf_chk@plt>
    382a:	be 08 00 00 00       	mov    $0x8,%esi
    382f:	bf 02 00 00 00       	mov    $0x2,%edi
    3834:	e8 c7 eb ff ff       	call   2400 <calloc@plt>
    3839:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
    383e:	be 38 00 00 00       	mov    $0x38,%esi
    3843:	bf 0a 00 00 00       	mov    $0xa,%edi
    3848:	4d 8d af 00 07 00 00 	lea    0x700(%r15),%r13
    384f:	4c 89 78 08          	mov    %r15,0x8(%rax)
    3853:	4d 8d a7 00 01 00 00 	lea    0x100(%r15),%r12
    385a:	49 89 87 18 07 00 00 	mov    %rax,0x718(%r15)
    3861:	4c 89 28             	mov    %r13,(%rax)
    3864:	49 8b 47 38          	mov    0x38(%r15),%rax
    3868:	41 c7 87 28 07 00 00 02 00 00 00 	movl   $0x2,0x728(%r15)
    3873:	41 c7 87 04 07 00 00 00 00 00 00 	movl   $0x0,0x704(%r15)
    387e:	41 c7 87 40 07 00 00 03 00 00 00 	movl   $0x3,0x740(%r15)
    3889:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3893:	49 8b 87 38 01 00 00 	mov    0x138(%r15),%rax
    389a:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    38a4:	e8 57 eb ff ff       	call   2400 <calloc@plt>
    38a9:	be 38 00 00 00       	mov    $0x38,%esi
    38ae:	bf 0a 00 00 00       	mov    $0xa,%edi
    38b3:	49 89 c6             	mov    %rax,%r14
    38b6:	e8 45 eb ff ff       	call   2400 <calloc@plt>
    38bb:	be 38 00 00 00       	mov    $0x38,%esi
    38c0:	bf 0a 00 00 00       	mov    $0xa,%edi
    38c5:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    38ca:	e8 31 eb ff ff       	call   2400 <calloc@plt>
    38cf:	be 38 00 00 00       	mov    $0x38,%esi
    38d4:	bf 0a 00 00 00       	mov    $0xa,%edi
    38d9:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    38de:	e8 1d eb ff ff       	call   2400 <calloc@plt>
    38e3:	be 08 00 00 00       	mov    $0x8,%esi
    38e8:	bf 0a 00 00 00       	mov    $0xa,%edi
    38ed:	48 89 c5             	mov    %rax,%rbp
    38f0:	e8 0b eb ff ff       	call   2400 <calloc@plt>
    38f5:	be 08 00 00 00       	mov    $0x8,%esi
    38fa:	bf 0a 00 00 00       	mov    $0xa,%edi
    38ff:	41 c7 87 0c 06 00 00 00 00 00 00 	movl   $0x0,0x60c(%r15)
    390a:	48 89 c3             	mov    %rax,%rbx
    390d:	48 8b 05 04 54 00 00 	mov    0x5404(%rip),%rax        # 8d18 <_IO_stdin_used+0xd18>
    3914:	49 89 87 40 06 00 00 	mov    %rax,0x640(%r15)
    391b:	e8 e0 ea ff ff       	call   2400 <calloc@plt>
    3920:	49 8d 97 00 02 00 00 	lea    0x200(%r15),%rdx
    3927:	4c 89 ff             	mov    %r15,%rdi
    392a:	49 8d 8f 00 06 00 00 	lea    0x600(%r15),%rcx
    3931:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3935:	49 8d 97 00 03 00 00 	lea    0x300(%r15),%rdx
    393c:	48 8d 35 50 4b 00 00 	lea    0x4b50(%rip),%rsi        # 8493 <_IO_stdin_used+0x493>
    3943:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3947:	49 8d 97 00 04 00 00 	lea    0x400(%r15),%rdx
    394e:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3952:	49 8d 97 00 05 00 00 	lea    0x500(%r15),%rdx
    3959:	4c 89 38             	mov    %r15,(%rax)
    395c:	4d 8d bf 00 08 00 00 	lea    0x800(%r15),%r15
    3963:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3967:	48 8d 97 00 09 00 00 	lea    0x900(%rdi),%rdx
    396e:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3972:	4c 89 68 38          	mov    %r13,0x38(%rax)
    3976:	4c 89 78 40          	mov    %r15,0x40(%rax)
    397a:	48 89 50 48          	mov    %rdx,0x48(%rax)
    397e:	ba 06 00 00 00       	mov    $0x6,%edx
    3983:	48 89 87 18 06 00 00 	mov    %rax,0x618(%rdi)
    398a:	4c 89 60 08          	mov    %r12,0x8(%rax)
    398e:	48 8b 05 8b 53 00 00 	mov    0x538b(%rip),%rax        # 8d20 <_IO_stdin_used+0xd20>
    3995:	c7 87 30 06 00 00 06 00 00 00 	movl   $0x6,0x630(%rdi)
    399f:	48 89 87 28 06 00 00 	mov    %rax,0x628(%rdi)
    39a6:	31 c0                	xor    %eax,%eax
    39a8:	c7 87 04 06 00 00 00 00 00 00 	movl   $0x0,0x604(%rdi)
    39b2:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
    39b7:	bf 01 00 00 00       	mov    $0x1,%edi
    39bc:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
    39c1:	e8 ea ea ff ff       	call   24b0 <__printf_chk@plt>
    39c6:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    39cb:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    39d0:	48 8d 15 d9 0d 00 00 	lea    0xdd9(%rip),%rdx        # 47b0 <timer_thread>
    39d7:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    39db:	48 81 c6 50 01 00 00 	add    $0x150,%rsi
    39e2:	e8 e9 ea ff ff       	call   24d0 <pthread_create@plt>
    39e7:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    39ec:	4c 89 f0             	mov    %r14,%rax
    39ef:	48 89 d9             	mov    %rbx,%rcx
    39f2:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    39f7:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    39fd:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3a02:	45 31 f6             	xor    %r14d,%r14d
    3a05:	4c 89 64 24 30       	mov    %r12,0x30(%rsp)
    3a0a:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    3a0f:	45 89 d5             	mov    %r10d,%r13d
    3a12:	4c 89 7c 24 40       	mov    %r15,0x40(%rsp)
    3a17:	49 89 c7             	mov    %rax,%r15
    3a1a:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    3a1f:	47 8d 24 36          	lea    (%r14,%r14,1),%r12d
    3a23:	48 89 cd             	mov    %rcx,%rbp
    3a26:	48 89 d3             	mov    %rdx,%rbx
    3a29:	48 89 4c 24 48       	mov    %rcx,0x48(%rsp)
    3a2e:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
    3a33:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    3a3a:	44 89 e2             	mov    %r12d,%edx
    3a3d:	44 89 f1             	mov    %r14d,%ecx
    3a40:	31 c0                	xor    %eax,%eax
    3a42:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    3a49:	48 8d 35 c8 4d 00 00 	lea    0x4dc8(%rip),%rsi        # 8818 <_IO_stdin_used+0x818>
    3a50:	bf 01 00 00 00       	mov    $0x1,%edi
    3a55:	41 83 c4 01          	add    $0x1,%r12d
    3a59:	e8 52 ea ff ff       	call   24b0 <__printf_chk@plt>
    3a5e:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3a63:	48 89 d9             	mov    %rbx,%rcx
    3a66:	48 89 ef             	mov    %rbp,%rdi
    3a69:	48 8d 15 c0 28 00 00 	lea    0x28c0(%rip),%rdx        # 6330 <barriered_thread>
    3a70:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    3a77:	48 83 c5 08          	add    $0x8,%rbp
    3a7b:	e8 50 ea ff ff       	call   24d0 <pthread_create@plt>
    3a80:	48 8b 53 b0          	mov    -0x50(%rbx),%rdx
    3a84:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
    3a88:	be 08 00 00 00       	mov    $0x8,%esi
    3a8d:	e8 8e e8 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    3a92:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3a98:	45 39 e5             	cmp    %r12d,%r13d
    3a9b:	75 96                	jne    3a33 <main+0x13c3>
    3a9d:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    3aa2:	41 83 c6 01          	add    $0x1,%r14d
    3aa6:	49 83 c7 70          	add    $0x70,%r15
    3aaa:	41 83 c5 02          	add    $0x2,%r13d
    3aae:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    3ab3:	48 83 c1 10          	add    $0x10,%rcx
    3ab7:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    3abe:	41 83 fe 03          	cmp    $0x3,%r14d
    3ac2:	0f 85 52 ff ff ff    	jne    3a1a <main+0x13aa>
    3ac8:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3acd:	be d8 00 00 00       	mov    $0xd8,%esi
    3ad2:	bf 01 00 00 00       	mov    $0x1,%edi
    3ad7:	48 8b 05 4a 52 00 00 	mov    0x524a(%rip),%rax        # 8d28 <_IO_stdin_used+0xd28>
    3ade:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    3ae3:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    3ae8:	41 c7 86 0c 07 00 00 02 00 00 00 	movl   $0x2,0x70c(%r14)
    3af3:	4c 8b 7c 24 40       	mov    0x40(%rsp),%r15
    3af8:	49 89 86 40 07 00 00 	mov    %rax,0x740(%r14)
    3aff:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    3b04:	4c 8b 64 24 30       	mov    0x30(%rsp),%r12
    3b09:	48 81 c5 c0 01 00 00 	add    $0x1c0,%rbp
    3b10:	e8 eb e8 ff ff       	call   2400 <calloc@plt>
    3b15:	be 00 08 00 00       	mov    $0x800,%esi
    3b1a:	31 ff                	xor    %edi,%edi
    3b1c:	49 89 86 58 07 00 00 	mov    %rax,0x758(%r14)
    3b23:	e8 f8 e9 ff ff       	call   2520 <eventfd@plt>
    3b28:	be 08 00 00 00       	mov    $0x8,%esi
    3b2d:	bf 02 00 00 00       	mov    $0x2,%edi
    3b32:	41 89 86 60 07 00 00 	mov    %eax,0x760(%r14)
    3b39:	e8 c2 e8 ff ff       	call   2400 <calloc@plt>
    3b3e:	ba 07 00 00 00       	mov    $0x7,%edx
    3b43:	bf 01 00 00 00       	mov    $0x1,%edi
    3b48:	41 c7 86 28 07 00 00 02 00 00 00 	movl   $0x2,0x728(%r14)
    3b53:	4c 89 30             	mov    %r14,(%rax)
    3b56:	48 8d 35 54 49 00 00 	lea    0x4954(%rip),%rsi        # 84b1 <_IO_stdin_used+0x4b1>
    3b5d:	49 89 86 18 07 00 00 	mov    %rax,0x718(%r14)
    3b64:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3b68:	31 c0                	xor    %eax,%eax
    3b6a:	41 c7 86 04 07 00 00 07 00 00 00 	movl   $0x7,0x704(%r14)
    3b75:	4d 89 fe             	mov    %r15,%r14
    3b78:	41 bf 08 00 00 00    	mov    $0x8,%r15d
    3b7e:	e8 2d e9 ff ff       	call   24b0 <__printf_chk@plt>
    3b83:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3b88:	4c 89 e9             	mov    %r13,%rcx
    3b8b:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3b8f:	48 8d 15 aa 1f 00 00 	lea    0x1faa(%rip),%rdx        # 5b40 <io_thread>
    3b96:	4c 8d 6b 40          	lea    0x40(%rbx),%r13
    3b9a:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3ba1:	e8 2a e9 ff ff       	call   24d0 <pthread_create@plt>
    3ba6:	ba 08 00 00 00       	mov    $0x8,%edx
    3bab:	48 8d 35 16 49 00 00 	lea    0x4916(%rip),%rsi        # 84c8 <_IO_stdin_used+0x4c8>
    3bb2:	31 c0                	xor    %eax,%eax
    3bb4:	bf 01 00 00 00       	mov    $0x1,%edi
    3bb9:	e8 f2 e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bbe:	44 89 fa             	mov    %r15d,%edx
    3bc1:	48 8d 35 16 49 00 00 	lea    0x4916(%rip),%rsi        # 84de <_IO_stdin_used+0x4de>
    3bc8:	bf 01 00 00 00       	mov    $0x1,%edi
    3bcd:	31 c0                	xor    %eax,%eax
    3bcf:	e8 dc e8 ff ff       	call   24b0 <__printf_chk@plt>
    3bd4:	be 08 00 00 00       	mov    $0x8,%esi
    3bd9:	bf 01 00 00 00       	mov    $0x1,%edi
    3bde:	48 8b 05 43 51 00 00 	mov    0x5143(%rip),%rax        # 8d28 <_IO_stdin_used+0xd28>
    3be5:	41 c7 46 0c 03 00 00 00 	movl   $0x3,0xc(%r14)
    3bed:	49 89 46 40          	mov    %rax,0x40(%r14)
    3bf1:	e8 0a e8 ff ff       	call   2400 <calloc@plt>
    3bf6:	48 8b bc 24 a8 00 00 00 	mov    0xa8(%rsp),%rdi
    3bfe:	be 08 00 00 00       	mov    $0x8,%esi
    3c03:	41 c7 86 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r14)
    3c0e:	49 89 46 50          	mov    %rax,0x50(%r14)
    3c12:	48 89 38             	mov    %rdi,(%rax)
    3c15:	bf 02 00 00 00       	mov    $0x2,%edi
    3c1a:	e8 e1 e7 ff ff       	call   2400 <calloc@plt>
    3c1f:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    3c24:	4c 89 f1             	mov    %r14,%rcx
    3c27:	4c 89 ef             	mov    %r13,%rdi
    3c2a:	49 89 46 18          	mov    %rax,0x18(%r14)
    3c2e:	48 8d 15 6b 0a 00 00 	lea    0xa6b(%rip),%rdx        # 46a0 <external_thread>
    3c35:	49 83 c5 08          	add    $0x8,%r13
    3c39:	49 81 c6 00 01 00 00 	add    $0x100,%r14
    3c40:	48 89 30             	mov    %rsi,(%rax)
    3c43:	48 89 ee             	mov    %rbp,%rsi
    3c46:	48 83 c5 38          	add    $0x38,%rbp
    3c4a:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3c4e:	48 8b 05 bb 50 00 00 	mov    0x50bb(%rip),%rax        # 8d10 <_IO_stdin_used+0xd10>
    3c55:	45 89 be 04 ff ff ff 	mov    %r15d,-0xfc(%r14)
    3c5c:	49 89 86 28 ff ff ff 	mov    %rax,-0xd8(%r14)
    3c63:	e8 68 e8 ff ff       	call   24d0 <pthread_create@plt>
    3c68:	48 83 84 24 a8 00 00 00 10 	addq   $0x10,0xa8(%rsp)
    3c71:	41 83 ff 08          	cmp    $0x8,%r15d
    3c75:	75 40                	jne    3cb7 <main+0x1647>
    3c77:	41 bf 09 00 00 00    	mov    $0x9,%r15d
    3c7d:	e9 3c ff ff ff       	jmp    3bbe <main+0x154e>
    3c82:	41 8d 47 01          	lea    0x1(%r15),%eax
    3c86:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3c8b:	4c 89 ca             	mov    %r9,%rdx
    3c8e:	45 31 c0             	xor    %r8d,%r8d
    3c91:	89 84 24 88 00 00 00 	mov    %eax,0x88(%rsp)
    3c98:	89 c1                	mov    %eax,%ecx
    3c9a:	48 c1 e0 08          	shl    $0x8,%rax
    3c9e:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    3ca3:	48 01 f8             	add    %rdi,%rax
    3ca6:	e9 eb ee ff ff       	jmp    2b96 <main+0x526>
    3cab:	48 81 0b ff 0f 00 00 	orq    $0xfff,(%rbx)
    3cb2:	e9 7b ef ff ff       	jmp    2c32 <main+0x5c2>
    3cb7:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3cbc:	48 8d 2d 38 48 00 00 	lea    0x4838(%rip),%rbp        # 84fb <_IO_stdin_used+0x4fb>
    3cc3:	4c 8d 68 04          	lea    0x4(%rax),%r13
    3cc7:	4c 8d a0 04 0a 00 00 	lea    0xa04(%rax),%r12
    3cce:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    3cd2:	41 8b 55 00          	mov    0x0(%r13),%edx
    3cd6:	48 89 ee             	mov    %rbp,%rsi
    3cd9:	bf 01 00 00 00       	mov    $0x1,%edi
    3cde:	31 c0                	xor    %eax,%eax
    3ce0:	49 81 c5 00 01 00 00 	add    $0x100,%r13
    3ce7:	e8 c4 e7 ff ff       	call   24b0 <__printf_chk@plt>
    3cec:	4d 39 ec             	cmp    %r13,%r12
    3cef:	75 dd                	jne    3cce <main+0x165e>
    3cf1:	48 8d 3d 16 48 00 00 	lea    0x4816(%rip),%rdi        # 850e <_IO_stdin_used+0x50e>
    3cf8:	45 31 ed             	xor    %r13d,%r13d
    3cfb:	4c 8d a4 24 f0 00 00 00 	lea    0xf0(%rsp),%r12
    3d03:	e8 28 e6 ff ff       	call   2330 <puts@plt>
    3d08:	48 8d 2d 1d 48 00 00 	lea    0x481d(%rip),%rbp        # 852c <_IO_stdin_used+0x52c>
    3d0f:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    3d13:	4c 89 e6             	mov    %r12,%rsi
    3d16:	e8 45 e8 ff ff       	call   2560 <pthread_join@plt>
    3d1b:	44 89 ea             	mov    %r13d,%edx
    3d1e:	48 89 ee             	mov    %rbp,%rsi
    3d21:	bf 01 00 00 00       	mov    $0x1,%edi
    3d26:	31 c0                	xor    %eax,%eax
    3d28:	49 83 c5 01          	add    $0x1,%r13
    3d2c:	e8 7f e7 ff ff       	call   24b0 <__printf_chk@plt>
    3d31:	49 83 fd 0a          	cmp    $0xa,%r13
    3d35:	75 d8                	jne    3d0f <main+0x169f>
    3d37:	be 08 00 00 00       	mov    $0x8,%esi
    3d3c:	bf 00 04 00 00       	mov    $0x400,%edi
    3d41:	31 db                	xor    %ebx,%ebx
    3d43:	e8 b8 e6 ff ff       	call   2400 <calloc@plt>
    3d48:	4c 8b 54 24 38       	mov    0x38(%rsp),%r10
    3d4d:	41 b9 00 02 00 00    	mov    $0x200,%r9d
    3d53:	49 89 c7             	mov    %rax,%r15
    3d56:	49 8d b9 00 fe ff ff 	lea    -0x200(%r9),%rdi
    3d5d:	45 8b 44 3a 40       	mov    0x40(%r10,%rdi,1),%r8d
    3d62:	45 85 c0             	test   %r8d,%r8d
    3d65:	0f 8e ad 00 00 00    	jle    3e18 <main+0x17a8>
    3d6b:	49 8b 4c 3a 38       	mov    0x38(%r10,%rdi,1),%rcx
    3d70:	49 63 f0             	movslq %r8d,%rsi
    3d73:	48 63 c3             	movslq %ebx,%rax
    3d76:	48 c1 e6 09          	shl    $0x9,%rsi
    3d7a:	49 8d 14 c7          	lea    (%r15,%rax,8),%rdx
    3d7e:	48 01 ce             	add    %rcx,%rsi
    3d81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3d88:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    3d8f:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    3d96:	48 83 c2 60          	add    $0x60,%rdx
    3d9a:	f3 0f 7e a0 00 01 00 00 	movq   0x100(%rax),%xmm4
    3da2:	f3 0f 7e 28          	movq   (%rax),%xmm5
    3da6:	f3 0f 7e 98 00 02 00 00 	movq   0x200(%rax),%xmm3
    3dae:	f3 0f 7e 90 00 03 00 00 	movq   0x300(%rax),%xmm2
    3db6:	f3 0f 7e 88 00 04 00 00 	movq   0x400(%rax),%xmm1
    3dbe:	0f 16 a0 80 01 00 00 	movhps 0x180(%rax),%xmm4
    3dc5:	f3 0f 7e 80 00 05 00 00 	movq   0x500(%rax),%xmm0
    3dcd:	0f 16 a8 80 00 00 00 	movhps 0x80(%rax),%xmm5
    3dd4:	0f 16 98 80 02 00 00 	movhps 0x280(%rax),%xmm3
    3ddb:	0f 16 90 80 03 00 00 	movhps 0x380(%rax),%xmm2
    3de2:	0f 11 6a a0          	movups %xmm5,-0x60(%rdx)
    3de6:	0f 16 88 80 04 00 00 	movhps 0x480(%rax),%xmm1
    3ded:	0f 16 80 80 05 00 00 	movhps 0x580(%rax),%xmm0
    3df4:	0f 11 62 b0          	movups %xmm4,-0x50(%rdx)
    3df8:	0f 11 5a c0          	movups %xmm3,-0x40(%rdx)
    3dfc:	0f 11 52 d0          	movups %xmm2,-0x30(%rdx)
    3e00:	0f 11 4a e0          	movups %xmm1,-0x20(%rdx)
    3e04:	0f 11 42 f0          	movups %xmm0,-0x10(%rdx)
    3e08:	48 39 f1             	cmp    %rsi,%rcx
    3e0b:	0f 85 77 ff ff ff    	jne    3d88 <main+0x1718>
    3e11:	43 8d 04 40          	lea    (%r8,%r8,2),%eax
    3e15:	8d 1c 83             	lea    (%rbx,%rax,4),%ebx
    3e18:	48 81 c7 00 01 00 00 	add    $0x100,%rdi
    3e1f:	4c 39 cf             	cmp    %r9,%rdi
    3e22:	0f 85 35 ff ff ff    	jne    3d5d <main+0x16ed>
    3e28:	4c 8d 8f 00 02 00 00 	lea    0x200(%rdi),%r9
    3e2f:	48 81 ff 00 06 00 00 	cmp    $0x600,%rdi
    3e36:	0f 85 1a ff ff ff    	jne    3d56 <main+0x16e6>
    3e3c:	48 8d 3d fd 46 00 00 	lea    0x46fd(%rip),%rdi        # 8540 <_IO_stdin_used+0x540>
    3e43:	e8 e8 e4 ff ff       	call   2330 <puts@plt>
    3e48:	48 8d 35 cd 45 00 00 	lea    0x45cd(%rip),%rsi        # 841c <_IO_stdin_used+0x41c>
    3e4f:	48 8d 3d 02 47 00 00 	lea    0x4702(%rip),%rdi        # 8558 <_IO_stdin_used+0x558>
    3e56:	e8 95 e6 ff ff       	call   24f0 <fopen@plt>
    3e5b:	49 89 c6             	mov    %rax,%r14
    3e5e:	85 db                	test   %ebx,%ebx
    3e60:	7e 6f                	jle    3ed1 <main+0x1861>
    3e62:	48 63 db             	movslq %ebx,%rbx
    3e65:	4c 8d 25 8f 45 00 00 	lea    0x458f(%rip),%r12        # 83fb <_IO_stdin_used+0x3fb>
    3e6c:	48 8d 2d cc 45 00 00 	lea    0x45cc(%rip),%rbp        # 843f <_IO_stdin_used+0x43f>
    3e73:	4d 8d 2c df          	lea    (%r15,%rbx,8),%r13
    3e77:	be 01 00 00 00       	mov    $0x1,%esi
    3e7c:	bf fa 00 00 00       	mov    $0xfa,%edi
    3e81:	49 83 c7 08          	add    $0x8,%r15
    3e85:	e8 76 e5 ff ff       	call   2400 <calloc@plt>
    3e8a:	4c 89 e1             	mov    %r12,%rcx
    3e8d:	ba fa 00 00 00       	mov    $0xfa,%edx
    3e92:	be 01 00 00 00       	mov    $0x1,%esi
    3e97:	48 89 c3             	mov    %rax,%rbx
    3e9a:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3e9e:	48 89 df             	mov    %rbx,%rdi
    3ea1:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3ea8:	31 c0                	xor    %eax,%eax
    3eaa:	e8 f1 e6 ff ff       	call   25a0 <__sprintf_chk@plt>
    3eaf:	48 89 da             	mov    %rbx,%rdx
    3eb2:	48 89 ee             	mov    %rbp,%rsi
    3eb5:	bf 01 00 00 00       	mov    $0x1,%edi
    3eba:	31 c0                	xor    %eax,%eax
    3ebc:	e8 ef e5 ff ff       	call   24b0 <__printf_chk@plt>
    3ec1:	4c 89 f6             	mov    %r14,%rsi
    3ec4:	48 89 df             	mov    %rbx,%rdi
    3ec7:	e8 f4 e4 ff ff       	call   23c0 <fputs@plt>
    3ecc:	4d 39 ef             	cmp    %r13,%r15
    3ecf:	75 a6                	jne    3e77 <main+0x1807>
    3ed1:	49 bc db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r12
    3edb:	4c 89 f7             	mov    %r14,%rdi
    3ede:	45 31 f6             	xor    %r14d,%r14d
    3ee1:	e8 7a e4 ff ff       	call   2360 <fclose@plt>
    3ee6:	4c 89 f3             	mov    %r14,%rbx
    3ee9:	48 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%rsp)
    3ef2:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
    3efb:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    3f04:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3f0d:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
    3f16:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3f1b:	49 89 da             	mov    %rbx,%r10
    3f1e:	44 8d 0c 1b          	lea    (%rbx,%rbx,1),%r9d
    3f22:	48 89 5c 24 58       	mov    %rbx,0x58(%rsp)
    3f27:	49 c1 e2 09          	shl    $0x9,%r10
    3f2b:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
    3f33:	44 89 4c 24 50       	mov    %r9d,0x50(%rsp)
    3f38:	41 8d 69 ff          	lea    -0x1(%r9),%ebp
    3f3c:	4e 8d 2c 10          	lea    (%rax,%r10,1),%r13
    3f40:	48 8d 04 5b          	lea    (%rbx,%rbx,2),%rax
    3f44:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    3f49:	48 c1 e0 04          	shl    $0x4,%rax
    3f4d:	48 01 f8             	add    %rdi,%rax
    3f50:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    3f55:	89 ef                	mov    %ebp,%edi
    3f57:	89 6c 24 48          	mov    %ebp,0x48(%rsp)
    3f5b:	83 c5 01             	add    $0x1,%ebp
    3f5e:	40 f6 c5 01          	test   $0x1,%bpl
    3f62:	8d 47 02             	lea    0x2(%rdi),%eax
    3f65:	0f 45 c7             	cmovne %edi,%eax
    3f68:	bf 0a 00 00 00       	mov    $0xa,%edi
    3f6d:	41 89 c6             	mov    %eax,%r14d
    3f70:	e8 9b e3 ff ff       	call   2310 <putchar@plt>
    3f75:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3f7a:	bf 01 00 00 00       	mov    $0x1,%edi
    3f7f:	48 8d 35 db 45 00 00 	lea    0x45db(%rip),%rsi        # 8561 <_IO_stdin_used+0x561>
    3f86:	48 8b 10             	mov    (%rax),%rdx
    3f89:	31 c0                	xor    %eax,%eax
    3f8b:	e8 20 e5 ff ff       	call   24b0 <__printf_chk@plt>
    3f90:	41 8b 55 40          	mov    0x40(%r13),%edx
    3f94:	85 d2                	test   %edx,%edx
    3f96:	0f 8e 1c 05 00 00    	jle    44b8 <main+0x1e48>
    3f9c:	48 63 ca             	movslq %edx,%rcx
    3f9f:	49 8b 45 38          	mov    0x38(%r13),%rax
    3fa3:	31 d2                	xor    %edx,%edx
    3fa5:	48 c1 e1 09          	shl    $0x9,%rcx
    3fa9:	48 01 c1             	add    %rax,%rcx
    3fac:	0f 1f 40 00          	nopl   0x0(%rax)
    3fb0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3fb7:	48 05 00 02 00 00    	add    $0x200,%rax
    3fbd:	48 39 c8             	cmp    %rcx,%rax
    3fc0:	75 ee                	jne    3fb0 <main+0x1940>
    3fc2:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3fc7:	49 63 c6             	movslq %r14d,%rax
    3fca:	48 c1 e0 08          	shl    $0x8,%rax
    3fce:	48 01 f8             	add    %rdi,%rax
    3fd1:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3fd5:	85 c9                	test   %ecx,%ecx
    3fd7:	7e 21                	jle    3ffa <main+0x198a>
    3fd9:	48 8b 40 38          	mov    0x38(%rax),%rax
    3fdd:	48 c1 e1 09          	shl    $0x9,%rcx
    3fe1:	48 01 c1             	add    %rax,%rcx
    3fe4:	0f 1f 40 00          	nopl   0x0(%rax)
    3fe8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
    3fef:	48 05 00 02 00 00    	add    $0x200,%rax
    3ff5:	48 39 c8             	cmp    %rcx,%rax
    3ff8:	75 ee                	jne    3fe8 <main+0x1978>
    3ffa:	48 8d 35 75 45 00 00 	lea    0x4575(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    4001:	bf 01 00 00 00       	mov    $0x1,%edi
    4006:	31 c0                	xor    %eax,%eax
    4008:	e8 a3 e4 ff ff       	call   24b0 <__printf_chk@plt>
    400d:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    4012:	bf 01 00 00 00       	mov    $0x1,%edi
    4017:	48 8d 35 2a 48 00 00 	lea    0x482a(%rip),%rsi        # 8848 <_IO_stdin_used+0x848>
    401e:	48 8b 08             	mov    (%rax),%rcx
    4021:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    402b:	48 f7 e9             	imul   %rcx
    402e:	48 c1 f9 3f          	sar    $0x3f,%rcx
    4032:	31 c0                	xor    %eax,%eax
    4034:	48 d1 fa             	sar    %rdx
    4037:	48 29 ca             	sub    %rcx,%rdx
    403a:	e8 71 e4 ff ff       	call   24b0 <__printf_chk@plt>
    403f:	bf 0a 00 00 00       	mov    $0xa,%edi
    4044:	e8 c7 e2 ff ff       	call   2310 <putchar@plt>
    4049:	45 8b 75 40          	mov    0x40(%r13),%r14d
    404d:	45 85 f6             	test   %r14d,%r14d
    4050:	0f 8e 3c 01 00 00    	jle    4192 <main+0x1b22>
    4056:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    405b:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    4060:	89 6c 24 08          	mov    %ebp,0x8(%rsp)
    4064:	31 d2                	xor    %edx,%edx
    4066:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    406b:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    4070:	49 8b 45 38          	mov    0x38(%r13),%rax
    4074:	49 89 d1             	mov    %rdx,%r9
    4077:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    407c:	89 d5                	mov    %edx,%ebp
    407e:	49 c1 e1 09          	shl    $0x9,%r9
    4082:	45 31 f6             	xor    %r14d,%r14d
    4085:	4c 01 c8             	add    %r9,%rax
    4088:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    408d:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
    4094:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
    409b:	48 03 b8 80 01 00 00 	add    0x180(%rax),%rdi
    40a2:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    40a7:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    40ac:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    40b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    40b8:	8b 54 24 08          	mov    0x8(%rsp),%edx
    40bc:	45 89 f0             	mov    %r14d,%r8d
    40bf:	89 e9                	mov    %ebp,%ecx
    40c1:	48 8d 35 bb 44 00 00 	lea    0x44bb(%rip),%rsi        # 8583 <_IO_stdin_used+0x583>
    40c8:	bf 01 00 00 00       	mov    $0x1,%edi
    40cd:	31 c0                	xor    %eax,%eax
    40cf:	e8 dc e3 ff ff       	call   24b0 <__printf_chk@plt>
    40d4:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    40d9:	4c 89 f0             	mov    %r14,%rax
    40dc:	45 89 f0             	mov    %r14d,%r8d
    40df:	49 8b 55 38          	mov    0x38(%r13),%rdx
    40e3:	48 c1 e0 08          	shl    $0x8,%rax
    40e7:	48 83 ec 08          	sub    $0x8,%rsp
    40eb:	49 83 c6 01          	add    $0x1,%r14
    40ef:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    40f7:	48 8b 38             	mov    (%rax),%rdi
    40fa:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
    4101:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
    4108:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
    410f:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
    4116:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    411d:	bf 01 00 00 00       	mov    $0x1,%edi
    4122:	48 01 c3             	add    %rax,%rbx
    4125:	48 01 f0             	add    %rsi,%rax
    4128:	49 01 cf             	add    %rcx,%r15
    412b:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
    412f:	48 01 f3             	add    %rsi,%rbx
    4132:	50                   	push   %rax
    4133:	49 01 d7             	add    %rdx,%r15
    4136:	8b 54 24 18          	mov    0x18(%rsp),%edx
    413a:	89 e9                	mov    %ebp,%ecx
    413c:	48 8d 35 25 47 00 00 	lea    0x4725(%rip),%rsi        # 8868 <_IO_stdin_used+0x868>
    4143:	31 c0                	xor    %eax,%eax
    4145:	e8 66 e3 ff ff       	call   24b0 <__printf_chk@plt>
    414a:	41 5a                	pop    %r10
    414c:	41 5b                	pop    %r11
    414e:	49 83 fe 06          	cmp    $0x6,%r14
    4152:	0f 85 60 ff ff ff    	jne    40b8 <main+0x1a48>
    4158:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    415d:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    4162:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    4167:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    416c:	48 83 c2 01          	add    $0x1,%rdx
    4170:	41 39 55 40          	cmp    %edx,0x40(%r13)
    4174:	0f 8f f6 fe ff ff    	jg     4070 <main+0x1a00>
    417a:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    417f:	8b 6c 24 08          	mov    0x8(%rsp),%ebp
    4183:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    4188:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    418d:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    4192:	45 31 ff             	xor    %r15d,%r15d
    4195:	49 83 bd a0 00 00 00 00 	cmpq   $0x0,0xa0(%r13)
    419d:	4c 8d 35 e4 46 00 00 	lea    0x46e4(%rip),%r14        # 8888 <_IO_stdin_used+0x888>
    41a4:	7e 62                	jle    4208 <main+0x1b98>
    41a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    41b0:	49 8b 85 90 00 00 00 	mov    0x90(%r13),%rax
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
    41de:	49 f7 e4             	mul    %r12
    41e1:	8b 49 20             	mov    0x20(%rcx),%ecx
    41e4:	56                   	push   %rsi
    41e5:	31 c0                	xor    %eax,%eax
    41e7:	4c 89 f6             	mov    %r14,%rsi
    41ea:	48 c1 ea 12          	shr    $0x12,%rdx
    41ee:	49 89 d1             	mov    %rdx,%r9
    41f1:	ba 02 00 00 00       	mov    $0x2,%edx
    41f6:	e8 b5 e2 ff ff       	call   24b0 <__printf_chk@plt>
    41fb:	41 58                	pop    %r8
    41fd:	41 59                	pop    %r9
    41ff:	4d 39 bd a0 00 00 00 	cmp    %r15,0xa0(%r13)
    4206:	7f a8                	jg     41b0 <main+0x1b40>
    4208:	41 8b 95 bc 00 00 00 	mov    0xbc(%r13),%edx
    420f:	85 d2                	test   %edx,%edx
    4211:	0f 8e 09 01 00 00    	jle    4320 <main+0x1cb0>
    4217:	48 89 5c 24 60       	mov    %rbx,0x60(%rsp)
    421c:	49 8b 7d 50          	mov    0x50(%r13),%rdi
    4220:	45 31 ff             	xor    %r15d,%r15d
    4223:	89 6c 24 68          	mov    %ebp,0x68(%rsp)
    4227:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4230:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    4234:	44 89 fb             	mov    %r15d,%ebx
    4237:	4a 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%rbp
    423f:	8b 30                	mov    (%rax),%esi
    4241:	85 f6                	test   %esi,%esi
    4243:	0f 8e c1 00 00 00    	jle    430a <main+0x1c9a>
    4249:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    424e:	31 d2                	xor    %edx,%edx
    4250:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4254:	49 89 f8             	mov    %rdi,%r8
    4257:	48 89 d7             	mov    %rdx,%rdi
    425a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4260:	49 89 fe             	mov    %rdi,%r14
    4263:	45 31 ff             	xor    %r15d,%r15d
    4266:	49 c1 e6 08          	shl    $0x8,%r14
    426a:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
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
    42ae:	49 f7 e4             	mul    %r12
    42b1:	89 d9                	mov    %ebx,%ecx
    42b3:	48 8d 35 1e 46 00 00 	lea    0x461e(%rip),%rsi        # 88d8 <_IO_stdin_used+0x8d8>
    42ba:	31 c0                	xor    %eax,%eax
    42bc:	48 c1 ea 12          	shr    $0x12,%rdx
    42c0:	49 89 d1             	mov    %rdx,%r9
    42c3:	ba 02 00 00 00       	mov    $0x2,%edx
    42c8:	e8 e3 e1 ff ff       	call   24b0 <__printf_chk@plt>
    42cd:	4d 8b 45 50          	mov    0x50(%r13),%r8
    42d1:	5e                   	pop    %rsi
    42d2:	5f                   	pop    %rdi
    42d3:	49 8b 14 28          	mov    (%r8,%rbp,1),%rdx
    42d7:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    42db:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    42df:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    42e6:	7f 98                	jg     4280 <main+0x1c10>
    42e8:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    42ed:	8b 32                	mov    (%rdx),%esi
    42ef:	48 83 c7 01          	add    $0x1,%rdi
    42f3:	39 fe                	cmp    %edi,%esi
    42f5:	0f 8f 65 ff ff ff    	jg     4260 <main+0x1bf0>
    42fb:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    4300:	41 8b 95 bc 00 00 00 	mov    0xbc(%r13),%edx
    4307:	4c 89 c7             	mov    %r8,%rdi
    430a:	49 83 c7 01          	add    $0x1,%r15
    430e:	44 39 fa             	cmp    %r15d,%edx
    4311:	0f 8f 19 ff ff ff    	jg     4230 <main+0x1bc0>
    4317:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
    431c:	8b 6c 24 68          	mov    0x68(%rsp),%ebp
    4320:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    4326:	8b 7c 24 48          	mov    0x48(%rsp),%edi
    432a:	49 81 c5 00 01 00 00 	add    $0x100,%r13
    4331:	39 7c 24 50          	cmp    %edi,0x50(%rsp)
    4335:	0f 85 1a fc ff ff    	jne    3f55 <main+0x18e5>
    433b:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    4340:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
    4345:	48 83 c3 01          	add    $0x1,%rbx
    4349:	48 83 fb 03          	cmp    $0x3,%rbx
    434d:	0f 85 c3 fb ff ff    	jne    3f16 <main+0x18a6>
    4353:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    4358:	48 8d 35 34 42 00 00 	lea    0x4234(%rip),%rsi        # 8593 <_IO_stdin_used+0x593>
    435f:	bf 01 00 00 00       	mov    $0x1,%edi
    4364:	31 c0                	xor    %eax,%eax
    4366:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4370:	4c 89 f2             	mov    %r14,%rdx
    4373:	e8 38 e1 ff ff       	call   24b0 <__printf_chk@plt>
    4378:	bf 0a 00 00 00       	mov    $0xa,%edi
    437d:	e8 8e df ff ff       	call   2310 <putchar@plt>
    4382:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    438a:	bf 01 00 00 00       	mov    $0x1,%edi
    438f:	48 8d 35 9a 45 00 00 	lea    0x459a(%rip),%rsi        # 8930 <_IO_stdin_used+0x930>
    4396:	48 8b 50 08          	mov    0x8(%rax),%rdx
    439a:	31 c0                	xor    %eax,%eax
    439c:	e8 0f e1 ff ff       	call   24b0 <__printf_chk@plt>
    43a1:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    43a6:	bf 01 00 00 00       	mov    $0x1,%edi
    43ab:	48 8d 35 a6 45 00 00 	lea    0x45a6(%rip),%rsi        # 8958 <_IO_stdin_used+0x958>
    43b2:	48 f7 eb             	imul   %rbx
    43b5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    43ba:	48 c1 f8 3f          	sar    $0x3f,%rax
    43be:	48 d1 fa             	sar    %rdx
    43c1:	48 29 c2             	sub    %rax,%rdx
    43c4:	31 c0                	xor    %eax,%eax
    43c6:	e8 e5 e0 ff ff       	call   24b0 <__printf_chk@plt>
    43cb:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    43d0:	bf 01 00 00 00       	mov    $0x1,%edi
    43d5:	48 8d 35 ac 45 00 00 	lea    0x45ac(%rip),%rsi        # 8988 <_IO_stdin_used+0x988>
    43dc:	48 f7 eb             	imul   %rbx
    43df:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    43e4:	48 c1 f8 3f          	sar    $0x3f,%rax
    43e8:	48 d1 fa             	sar    %rdx
    43eb:	48 29 c2             	sub    %rax,%rdx
    43ee:	31 c0                	xor    %eax,%eax
    43f0:	e8 bb e0 ff ff       	call   24b0 <__printf_chk@plt>
    43f5:	4c 89 f0             	mov    %r14,%rax
    43f8:	bf 01 00 00 00       	mov    $0x1,%edi
    43fd:	48 8d 35 b4 45 00 00 	lea    0x45b4(%rip),%rsi        # 89b8 <_IO_stdin_used+0x9b8>
    4404:	48 f7 eb             	imul   %rbx
    4407:	4c 89 f0             	mov    %r14,%rax
    440a:	48 c1 f8 3f          	sar    $0x3f,%rax
    440e:	48 d1 fa             	sar    %rdx
    4411:	48 29 c2             	sub    %rax,%rdx
    4414:	31 c0                	xor    %eax,%eax
    4416:	e8 95 e0 ff ff       	call   24b0 <__printf_chk@plt>
    441b:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4420:	bf 01 00 00 00       	mov    $0x1,%edi
    4425:	48 8d 35 7b 41 00 00 	lea    0x417b(%rip),%rsi        # 85a7 <_IO_stdin_used+0x5a7>
    442c:	48 f7 eb             	imul   %rbx
    442f:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4434:	48 c1 f8 3f          	sar    $0x3f,%rax
    4438:	48 d1 fa             	sar    %rdx
    443b:	48 29 c2             	sub    %rax,%rdx
    443e:	31 c0                	xor    %eax,%eax
    4440:	48 89 d5             	mov    %rdx,%rbp
    4443:	e8 68 e0 ff ff       	call   24b0 <__printf_chk@plt>
    4448:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    444d:	bf 01 00 00 00       	mov    $0x1,%edi
    4452:	48 8d 35 7f 45 00 00 	lea    0x457f(%rip),%rsi        # 89d8 <_IO_stdin_used+0x9d8>
    4459:	48 f7 eb             	imul   %rbx
    445c:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    4461:	48 c1 f8 3f          	sar    $0x3f,%rax
    4465:	48 89 d3             	mov    %rdx,%rbx
    4468:	48 d1 fb             	sar    %rbx
    446b:	48 29 c3             	sub    %rax,%rbx
    446e:	31 c0                	xor    %eax,%eax
    4470:	48 89 da             	mov    %rbx,%rdx
    4473:	48 29 eb             	sub    %rbp,%rbx
    4476:	e8 35 e0 ff ff       	call   24b0 <__printf_chk@plt>
    447b:	31 c0                	xor    %eax,%eax
    447d:	48 89 da             	mov    %rbx,%rdx
    4480:	bf 01 00 00 00       	mov    $0x1,%edi
    4485:	48 8d 35 37 41 00 00 	lea    0x4137(%rip),%rsi        # 85c3 <_IO_stdin_used+0x5c3>
    448c:	e8 1f e0 ff ff       	call   24b0 <__printf_chk@plt>
    4491:	48 8b 84 24 08 01 00 00 	mov    0x108(%rsp),%rax
    4499:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    44a2:	75 25                	jne    44c9 <main+0x1e59>
    44a4:	48 81 c4 18 01 00 00 	add    $0x118,%rsp
    44ab:	31 c0                	xor    %eax,%eax
    44ad:	5b                   	pop    %rbx
    44ae:	5d                   	pop    %rbp
    44af:	41 5c                	pop    %r12
    44b1:	41 5d                	pop    %r13
    44b3:	41 5e                	pop    %r14
    44b5:	41 5f                	pop    %r15
    44b7:	c3                   	ret
    44b8:	31 d2                	xor    %edx,%edx
    44ba:	e9 03 fb ff ff       	jmp    3fc2 <main+0x1952>
    44bf:	bf 01 00 00 00       	mov    $0x1,%edi
    44c4:	e8 47 e0 ff ff       	call   2510 <exit@plt>
    44c9:	e8 b2 de ff ff       	call   2380 <__stack_chk_fail@plt>
    44ce:	66 90                	xchg   %ax,%ax

00000000000044d0 <_start>:
    44d0:	f3 0f 1e fa          	endbr64
    44d4:	31 ed                	xor    %ebp,%ebp
    44d6:	49 89 d1             	mov    %rdx,%r9
    44d9:	5e                   	pop    %rsi
    44da:	48 89 e2             	mov    %rsp,%rdx
    44dd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    44e1:	50                   	push   %rax
    44e2:	54                   	push   %rsp
    44e3:	45 31 c0             	xor    %r8d,%r8d
    44e6:	31 c9                	xor    %ecx,%ecx
    44e8:	48 8d 3d 81 e1 ff ff 	lea    -0x1e7f(%rip),%rdi        # 2670 <main>
    44ef:	ff 15 e3 6a 00 00    	call   *0x6ae3(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    44f5:	f4                   	hlt
    44f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004500 <deregister_tm_clones>:
    4500:	48 8d 3d 19 6b 00 00 	lea    0x6b19(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4507:	48 8d 05 12 6b 00 00 	lea    0x6b12(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    450e:	48 39 f8             	cmp    %rdi,%rax
    4511:	74 15                	je     4528 <deregister_tm_clones+0x28>
    4513:	48 8b 05 c6 6a 00 00 	mov    0x6ac6(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    451a:	48 85 c0             	test   %rax,%rax
    451d:	74 09                	je     4528 <deregister_tm_clones+0x28>
    451f:	ff e0                	jmp    *%rax
    4521:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4528:	c3                   	ret
    4529:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004530 <register_tm_clones>:
    4530:	48 8d 3d e9 6a 00 00 	lea    0x6ae9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4537:	48 8d 35 e2 6a 00 00 	lea    0x6ae2(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    453e:	48 29 fe             	sub    %rdi,%rsi
    4541:	48 89 f0             	mov    %rsi,%rax
    4544:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4548:	48 c1 f8 03          	sar    $0x3,%rax
    454c:	48 01 c6             	add    %rax,%rsi
    454f:	48 d1 fe             	sar    %rsi
    4552:	74 14                	je     4568 <register_tm_clones+0x38>
    4554:	48 8b 05 95 6a 00 00 	mov    0x6a95(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    455b:	48 85 c0             	test   %rax,%rax
    455e:	74 08                	je     4568 <register_tm_clones+0x38>
    4560:	ff e0                	jmp    *%rax
    4562:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4568:	c3                   	ret
    4569:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004570 <__do_global_dtors_aux>:
    4570:	f3 0f 1e fa          	endbr64
    4574:	80 3d ad 6a 00 00 00 	cmpb   $0x0,0x6aad(%rip)        # b028 <completed.0>
    457b:	75 2b                	jne    45a8 <__do_global_dtors_aux+0x38>
    457d:	55                   	push   %rbp
    457e:	48 83 3d 72 6a 00 00 00 	cmpq   $0x0,0x6a72(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    4586:	48 89 e5             	mov    %rsp,%rbp
    4589:	74 0c                	je     4597 <__do_global_dtors_aux+0x27>
    458b:	48 8b 3d 76 6a 00 00 	mov    0x6a76(%rip),%rdi        # b008 <__dso_handle>
    4592:	e8 59 dd ff ff       	call   22f0 <__cxa_finalize@plt>
    4597:	e8 64 ff ff ff       	call   4500 <deregister_tm_clones>
    459c:	c6 05 85 6a 00 00 01 	movb   $0x1,0x6a85(%rip)        # b028 <completed.0>
    45a3:	5d                   	pop    %rbp
    45a4:	c3                   	ret
    45a5:	0f 1f 00             	nopl   (%rax)
    45a8:	c3                   	ret
    45a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000045b0 <frame_dummy>:
    45b0:	f3 0f 1e fa          	endbr64
    45b4:	e9 77 ff ff ff       	jmp    4530 <register_tm_clones>
    45b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000045c0 <do_protected_write>:
    45c0:	f3 0f 1e fa          	endbr64
    45c4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    45cb:	48 8b 40 48          	mov    0x48(%rax),%rax
    45cf:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
    45d7:	48 8b 48 08          	mov    0x8(%rax),%rcx
    45db:	48 83 00 01          	addq   $0x1,(%rax)
    45df:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    45e6:	48 85 c9             	test   %rcx,%rcx
    45e9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    45f0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    45f4:	48 89 50 08          	mov    %rdx,0x8(%rax)
    45f8:	31 c0                	xor    %eax,%eax
    45fa:	c3                   	ret
    45fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004600 <barriered_reset>:
    4600:	f3 0f 1e fa          	endbr64
    4604:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    460b:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    4612:	85 c9                	test   %ecx,%ecx
    4614:	7e 48                	jle    465e <barriered_reset+0x5e>
    4616:	48 63 97 30 01 00 00 	movslq 0x130(%rdi),%rdx
    461d:	49 8b 40 18          	mov    0x18(%r8),%rax
    4621:	48 c1 e1 09          	shl    $0x9,%rcx
    4625:	49 8b 70 38          	mov    0x38(%r8),%rsi
    4629:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    462d:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4631:	31 c0                	xor    %eax,%eax
    4633:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4638:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
    4640:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
    4648:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    4653:	48 05 00 02 00 00    	add    $0x200,%rax
    4659:	48 39 c1             	cmp    %rax,%rcx
    465c:	75 da                	jne    4638 <barriered_reset+0x38>
    465e:	49 8b 88 f0 00 00 00 	mov    0xf0(%r8),%rcx
    4665:	8b 01                	mov    (%rcx),%eax
    4667:	83 f8 ff             	cmp    $0xffffffff,%eax
    466a:	74 0e                	je     467a <barriered_reset+0x7a>
    466c:	41 8b b8 c0 00 00 00 	mov    0xc0(%r8),%edi
    4673:	8d 57 ff             	lea    -0x1(%rdi),%edx
    4676:	39 d0                	cmp    %edx,%eax
    4678:	74 06                	je     4680 <barriered_reset+0x80>
    467a:	0f ae f8             	sfence
    467d:	31 c0                	xor    %eax,%eax
    467f:	c3                   	ret
    4680:	41 83 78 04 01       	cmpl   $0x1,0x4(%r8)
    4685:	75 f3                	jne    467a <barriered_reset+0x7a>
    4687:	49 8b 80 d8 00 00 00 	mov    0xd8(%r8),%rax
    468e:	83 00 01             	addl   $0x1,(%rax)
    4691:	c7 01 ff ff ff ff    	movl   $0xffffffff,(%rcx)
    4697:	eb e1                	jmp    467a <barriered_reset+0x7a>
    4699:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000046a0 <external_thread>:
    46a0:	f3 0f 1e fa          	endbr64
    46a4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    46a8:	0f 85 fb 00 00 00    	jne    47a9 <external_thread+0x109>
    46ae:	41 57                	push   %r15
    46b0:	49 89 ff             	mov    %rdi,%r15
    46b3:	41 56                	push   %r14
    46b5:	41 55                	push   %r13
    46b7:	4c 8d 2d 46 39 00 00 	lea    0x3946(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
    46be:	41 54                	push   %r12
    46c0:	55                   	push   %rbp
    46c1:	53                   	push   %rbx
    46c2:	48 83 ec 08          	sub    $0x8,%rsp
    46c6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    46cc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    46d0:	85 c9                	test   %ecx,%ecx
    46d2:	7e 6e                	jle    4742 <external_thread+0xa2>
    46d4:	45 31 e4             	xor    %r12d,%r12d
    46d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    46e0:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    46e8:	31 db                	xor    %ebx,%ebx
    46ea:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    46ee:	48 8b 06             	mov    (%rsi),%rax
    46f1:	8b 10                	mov    (%rax),%edx
    46f3:	85 d2                	test   %edx,%edx
    46f5:	7e 2a                	jle    4721 <external_thread+0x81>
    46f7:	48 8b 48 08          	mov    0x8(%rax),%rcx
    46fb:	48 89 dd             	mov    %rbx,%rbp
    46fe:	48 c1 e5 08          	shl    $0x8,%rbp
    4702:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4706:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    470d:	45 85 c0             	test   %r8d,%r8d
    4710:	74 36                	je     4748 <external_thread+0xa8>
    4712:	48 83 c3 01          	add    $0x1,%rbx
    4716:	39 da                	cmp    %ebx,%edx
    4718:	7f e1                	jg     46fb <external_thread+0x5b>
    471a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4721:	49 83 c4 01          	add    $0x1,%r12
    4725:	44 39 e1             	cmp    %r12d,%ecx
    4728:	7f b6                	jg     46e0 <external_thread+0x40>
    472a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    472f:	74 9f                	je     46d0 <external_thread+0x30>
    4731:	48 83 c4 08          	add    $0x8,%rsp
    4735:	31 c0                	xor    %eax,%eax
    4737:	5b                   	pop    %rbx
    4738:	5d                   	pop    %rbp
    4739:	41 5c                	pop    %r12
    473b:	41 5d                	pop    %r13
    473d:	41 5e                	pop    %r14
    473f:	41 5f                	pop    %r15
    4741:	c3                   	ret
    4742:	eb fe                	jmp    4742 <external_thread+0xa2>
    4744:	0f 1f 40 00          	nopl   0x0(%rax)
    4748:	4c 89 28             	mov    %r13,(%rax)
    474b:	48 8b 06             	mov    (%rsi),%rax
    474e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4752:	48 01 ef             	add    %rbp,%rdi
    4755:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    475c:	48 c1 e6 05          	shl    $0x5,%rsi
    4760:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4767:	bf 04 00 00 00       	mov    $0x4,%edi
    476c:	e8 df db ff ff       	call   2350 <clock_gettime@plt>
    4771:	49 8b 47 50          	mov    0x50(%r15),%rax
    4775:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    4779:	48 8b 40 08          	mov    0x8(%rax),%rax
    477d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
    4788:	0f ae f8             	sfence
    478b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    478f:	48 83 c3 01          	add    $0x1,%rbx
    4793:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4797:	48 8b 06             	mov    (%rsi),%rax
    479a:	8b 10                	mov    (%rax),%edx
    479c:	39 da                	cmp    %ebx,%edx
    479e:	0f 8f 53 ff ff ff    	jg     46f7 <external_thread+0x57>
    47a4:	e9 71 ff ff ff       	jmp    471a <external_thread+0x7a>
    47a9:	31 c0                	xor    %eax,%eax
    47ab:	c3                   	ret
    47ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000047b0 <timer_thread>:
    47b0:	f3 0f 1e fa          	endbr64
    47b4:	41 57                	push   %r15
    47b6:	48 8d 35 53 38 00 00 	lea    0x3853(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    47bd:	49 89 ff             	mov    %rdi,%r15
    47c0:	41 56                	push   %r14
    47c2:	41 55                	push   %r13
    47c4:	41 54                	push   %r12
    47c6:	55                   	push   %rbp
    47c7:	53                   	push   %rbx
    47c8:	48 83 ec 58          	sub    $0x58,%rsp
    47cc:	8b 57 04             	mov    0x4(%rdi),%edx
    47cf:	bf 01 00 00 00       	mov    $0x1,%edi
    47d4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    47dd:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    47e2:	31 c0                	xor    %eax,%eax
    47e4:	e8 c7 dc ff ff       	call   24b0 <__printf_chk@plt>
    47e9:	66 0f 6f 05 ff 43 00 00 	movdqa 0x43ff(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    47f1:	ba 88 13 00 00       	mov    $0x1388,%edx
    47f6:	31 c0                	xor    %eax,%eax
    47f8:	48 8d 35 23 38 00 00 	lea    0x3823(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    47ff:	bf 01 00 00 00       	mov    $0x1,%edi
    4804:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4809:	e8 a2 dc ff ff       	call   24b0 <__printf_chk@plt>
    480e:	41 8b 47 44          	mov    0x44(%r15),%eax
    4812:	89 c3                	mov    %eax,%ebx
    4814:	85 c0                	test   %eax,%eax
    4816:	0f 84 9a 00 00 00    	je     48b6 <timer_thread+0x106>
    481c:	45 31 f6             	xor    %r14d,%r14d
    481f:	31 db                	xor    %ebx,%ebx
    4821:	49 89 e5             	mov    %rsp,%r13
    4824:	31 ed                	xor    %ebp,%ebp
    4826:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    482b:	4c 89 e7             	mov    %r12,%rdi
    482e:	4c 89 ee             	mov    %r13,%rsi
    4831:	41 83 c6 01          	add    $0x1,%r14d
    4835:	e8 66 db ff ff       	call   23a0 <nanosleep@plt>
    483a:	49 63 47 30          	movslq 0x30(%r15),%rax
    483e:	8d 7b 01             	lea    0x1(%rbx),%edi
    4841:	85 c0                	test   %eax,%eax
    4843:	7e 4a                	jle    488f <timer_thread+0xdf>
    4845:	49 8b 4f 18          	mov    0x18(%r15),%rcx
    4849:	4c 63 c3             	movslq %ebx,%r8
    484c:	49 c1 e0 09          	shl    $0x9,%r8
    4850:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4854:	0f 1f 40 00          	nopl   0x0(%rax)
    4858:	48 8b 19             	mov    (%rcx),%rbx
    485b:	89 f8                	mov    %edi,%eax
    485d:	48 83 c1 08          	add    $0x8,%rcx
    4861:	99                   	cltd
    4862:	f7 7b 40             	idivl  0x40(%rbx)
    4865:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4869:	83 ea 01             	sub    $0x1,%edx
    486c:	48 63 d2             	movslq %edx,%rdx
    486f:	48 c1 e2 09          	shl    $0x9,%rdx
    4873:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    487e:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    488a:	49 39 c9             	cmp    %rcx,%r9
    488d:	75 c9                	jne    4858 <timer_thread+0xa8>
    488f:	0f ae f0             	mfence
    4892:	49 8b 47 18          	mov    0x18(%r15),%rax
    4896:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    489a:	89 fb                	mov    %edi,%ebx
    489c:	48 8b 00             	mov    (%rax),%rax
    489f:	39 78 40             	cmp    %edi,0x40(%rax)
    48a2:	0f 4e dd             	cmovle %ebp,%ebx
    48a5:	85 c9                	test   %ecx,%ecx
    48a7:	74 0d                	je     48b6 <timer_thread+0x106>
    48a9:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    48b0:	0f 85 75 ff ff ff    	jne    482b <timer_thread+0x7b>
    48b6:	48 8d 3d 7b 37 00 00 	lea    0x377b(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    48bd:	e8 6e da ff ff       	call   2330 <puts@plt>
    48c2:	49 63 57 30          	movslq 0x30(%r15),%rdx
    48c6:	85 d2                	test   %edx,%edx
    48c8:	7e 6b                	jle    4935 <timer_thread+0x185>
    48ca:	49 63 47 40          	movslq 0x40(%r15),%rax
    48ce:	85 c0                	test   %eax,%eax
    48d0:	7e 63                	jle    4935 <timer_thread+0x185>
    48d2:	48 c1 e0 09          	shl    $0x9,%rax
    48d6:	4d 8b 47 18          	mov    0x18(%r15),%r8
    48da:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    48e2:	31 c9                	xor    %ecx,%ecx
    48e4:	48 89 c6             	mov    %rax,%rsi
    48e7:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    48eb:	48 8b 40 38          	mov    0x38(%rax),%rax
    48ef:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    48f3:	f7 c6 00 02 00 00    	test   $0x200,%esi
    48f9:	74 15                	je     4910 <timer_thread+0x160>
    48fb:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    4905:	48 05 00 02 00 00    	add    $0x200,%rax
    490b:	48 39 c2             	cmp    %rax,%rdx
    490e:	74 1c                	je     492c <timer_thread+0x17c>
    4910:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    491a:	48 05 00 04 00 00    	add    $0x400,%rax
    4920:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    4927:	48 39 c2             	cmp    %rax,%rdx
    492a:	75 e4                	jne    4910 <timer_thread+0x160>
    492c:	48 83 c1 08          	add    $0x8,%rcx
    4930:	48 39 cf             	cmp    %rcx,%rdi
    4933:	75 b2                	jne    48e7 <timer_thread+0x137>
    4935:	0f ae f0             	mfence
    4938:	66 0f 6f 05 c0 42 00 00 	movdqa 0x42c0(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4940:	41 89 dc             	mov    %ebx,%r12d
    4943:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    4948:	49 63 47 28          	movslq 0x28(%r15),%rax
    494c:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    4951:	85 c0                	test   %eax,%eax
    4953:	7e 46                	jle    499b <timer_thread+0x1eb>
    4955:	49 8b 4f 18          	mov    0x18(%r15),%rcx
    4959:	49 63 ec             	movslq %r12d,%rbp
    495c:	48 c1 e5 09          	shl    $0x9,%rbp
    4960:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4964:	0f 1f 40 00          	nopl   0x0(%rax)
    4968:	48 8b 19             	mov    (%rcx),%rbx
    496b:	89 f8                	mov    %edi,%eax
    496d:	48 83 c1 08          	add    $0x8,%rcx
    4971:	99                   	cltd
    4972:	f7 7b 40             	idivl  0x40(%rbx)
    4975:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4979:	48 63 d2             	movslq %edx,%rdx
    497c:	48 c1 e2 09          	shl    $0x9,%rdx
    4980:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
    498b:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    4996:	49 39 c8             	cmp    %rcx,%r8
    4999:	75 cd                	jne    4968 <timer_thread+0x1b8>
    499b:	0f ae f0             	mfence
    499e:	49 8b 77 18          	mov    0x18(%r15),%rsi
    49a2:	45 31 e4             	xor    %r12d,%r12d
    49a5:	48 8b 06             	mov    (%rsi),%rax
    49a8:	39 78 40             	cmp    %edi,0x40(%rax)
    49ab:	44 0f 4f e7          	cmovg  %edi,%r12d
    49af:	41 8b 7f 30          	mov    0x30(%r15),%edi
    49b3:	85 ff                	test   %edi,%edi
    49b5:	0f 8e a9 01 00 00    	jle    4b64 <timer_thread+0x3b4>
    49bb:	45 31 f6             	xor    %r14d,%r14d
    49be:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    49c4:	4c 89 f5             	mov    %r14,%rbp
    49c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    49d0:	89 eb                	mov    %ebp,%ebx
    49d2:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    49da:	45 31 f6             	xor    %r14d,%r14d
    49dd:	85 ff                	test   %edi,%edi
    49df:	7e 77                	jle    4a58 <timer_thread+0x2a8>
    49e1:	4c 89 f6             	mov    %r14,%rsi
    49e4:	48 63 cf             	movslq %edi,%rcx
    49e7:	45 31 c0             	xor    %r8d,%r8d
    49ea:	48 c1 e6 09          	shl    $0x9,%rsi
    49ee:	66 90                	xchg   %ax,%ax
    49f0:	41 39 e8             	cmp    %ebp,%r8d
    49f3:	74 45                	je     4a3a <timer_thread+0x28a>
    49f5:	49 8b 47 18          	mov    0x18(%r15),%rax
    49f9:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    49fd:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4a01:	4c 89 c0             	mov    %r8,%rax
    4a04:	48 c1 e0 08          	shl    $0x8,%rax
    4a08:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4a10:	48 8b 10             	mov    (%rax),%rdx
    4a13:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    4a1a:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4a21:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4a28:	4d 85 c9             	test   %r9,%r9
    4a2b:	0f 8f 97 00 00 00    	jg     4ac8 <timer_thread+0x318>
    4a31:	4d 85 db             	test   %r11,%r11
    4a34:	0f 8f 8e 00 00 00    	jg     4ac8 <timer_thread+0x318>
    4a3a:	49 83 c0 01          	add    $0x1,%r8
    4a3e:	4c 39 c1             	cmp    %r8,%rcx
    4a41:	75 ad                	jne    49f0 <timer_thread+0x240>
    4a43:	49 83 fe 01          	cmp    $0x1,%r14
    4a47:	74 0f                	je     4a58 <timer_thread+0x2a8>
    4a49:	41 be 01 00 00 00    	mov    $0x1,%r14d
    4a4f:	85 ff                	test   %edi,%edi
    4a51:	7f 8e                	jg     49e1 <timer_thread+0x231>
    4a53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4a58:	48 83 c5 01          	add    $0x1,%rbp
    4a5c:	39 ef                	cmp    %ebp,%edi
    4a5e:	0f 8f 6c ff ff ff    	jg     49d0 <timer_thread+0x220>
    4a64:	44 89 d5             	mov    %r10d,%ebp
    4a67:	85 ff                	test   %edi,%edi
    4a69:	7e 3b                	jle    4aa6 <timer_thread+0x2f6>
    4a6b:	31 db                	xor    %ebx,%ebx
    4a6d:	bf 01 00 00 00       	mov    $0x1,%edi
    4a72:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4a76:	41 8b 57 40          	mov    0x40(%r15),%edx
    4a7a:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4a7e:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a82:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    4a88:	39 d1                	cmp    %edx,%ecx
    4a8a:	0f 8c a8 00 00 00    	jl     4b38 <timer_thread+0x388>
    4a90:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    4a96:	39 d0                	cmp    %edx,%eax
    4a98:	7c 6e                	jl     4b08 <timer_thread+0x358>
    4a9a:	48 83 c3 01          	add    $0x1,%rbx
    4a9e:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4aa2:	7f d6                	jg     4a7a <timer_thread+0x2ca>
    4aa4:	21 fd                	and    %edi,%ebp
    4aa6:	85 ed                	test   %ebp,%ebp
    4aa8:	0f 85 b6 00 00 00    	jne    4b64 <timer_thread+0x3b4>
    4aae:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4ab3:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4ab8:	e8 e3 d8 ff ff       	call   23a0 <nanosleep@plt>
    4abd:	e9 86 fe ff ff       	jmp    4948 <timer_thread+0x198>
    4ac2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4ac8:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    4ace:	48 83 ec 08          	sub    $0x8,%rsp
    4ad2:	bf 01 00 00 00       	mov    $0x1,%edi
    4ad7:	44 89 f1             	mov    %r14d,%ecx
    4ada:	48 8d 35 7c 35 00 00 	lea    0x357c(%rip),%rsi        # 805d <_IO_stdin_used+0x5d>
    4ae1:	50                   	push   %rax
    4ae2:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    4ae8:	89 da                	mov    %ebx,%edx
    4aea:	50                   	push   %rax
    4aeb:	31 c0                	xor    %eax,%eax
    4aed:	41 53                	push   %r11
    4aef:	e8 bc d9 ff ff       	call   24b0 <__printf_chk@plt>
    4af4:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4af8:	48 83 c4 20          	add    $0x20,%rsp
    4afc:	45 31 d2             	xor    %r10d,%r10d
    4aff:	e9 3f ff ff ff       	jmp    4a43 <timer_thread+0x293>
    4b04:	0f 1f 40 00          	nopl   0x0(%rax)
    4b08:	89 c2                	mov    %eax,%edx
    4b0a:	bf 01 00 00 00       	mov    $0x1,%edi
    4b0f:	31 c0                	xor    %eax,%eax
    4b11:	48 83 c3 01          	add    $0x1,%rbx
    4b15:	48 8d 35 06 38 00 00 	lea    0x3806(%rip),%rsi        # 8322 <_IO_stdin_used+0x322>
    4b1c:	e8 8f d9 ff ff       	call   24b0 <__printf_chk@plt>
    4b21:	31 ff                	xor    %edi,%edi
    4b23:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4b27:	0f 8f 45 ff ff ff    	jg     4a72 <timer_thread+0x2c2>
    4b2d:	e9 72 ff ff ff       	jmp    4aa4 <timer_thread+0x2f4>
    4b32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b38:	89 ca                	mov    %ecx,%edx
    4b3a:	48 8d 35 e1 37 00 00 	lea    0x37e1(%rip),%rsi        # 8322 <_IO_stdin_used+0x322>
    4b41:	bf 01 00 00 00       	mov    $0x1,%edi
    4b46:	31 c0                	xor    %eax,%eax
    4b48:	e8 63 d9 ff ff       	call   24b0 <__printf_chk@plt>
    4b4d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4b51:	41 8b 57 40          	mov    0x40(%r15),%edx
    4b55:	31 ff                	xor    %edi,%edi
    4b57:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4b5b:	48 8b 40 38          	mov    0x38(%rax),%rax
    4b5f:	e9 2c ff ff ff       	jmp    4a90 <timer_thread+0x2e0>
    4b64:	48 8d 3d e9 34 00 00 	lea    0x34e9(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4b6b:	e8 c0 d7 ff ff       	call   2330 <puts@plt>
    4b70:	41 8b 57 44          	mov    0x44(%r15),%edx
    4b74:	85 d2                	test   %edx,%edx
    4b76:	0f 84 eb 00 00 00    	je     4c67 <timer_thread+0x4b7>
    4b7c:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4b80:	31 db                	xor    %ebx,%ebx
    4b82:	48 8d 2d f1 34 00 00 	lea    0x34f1(%rip),%rbp        # 807a <_IO_stdin_used+0x7a>
    4b89:	4c 8d 25 05 35 00 00 	lea    0x3505(%rip),%r12        # 8095 <_IO_stdin_used+0x95>
    4b90:	85 c0                	test   %eax,%eax
    4b92:	7e 38                	jle    4bcc <timer_thread+0x41c>
    4b94:	0f 1f 40 00          	nopl   0x0(%rax)
    4b98:	31 c0                	xor    %eax,%eax
    4b9a:	89 da                	mov    %ebx,%edx
    4b9c:	48 89 ee             	mov    %rbp,%rsi
    4b9f:	bf 01 00 00 00       	mov    $0x1,%edi
    4ba4:	e8 07 d9 ff ff       	call   24b0 <__printf_chk@plt>
    4ba9:	49 8b 47 18          	mov    0x18(%r15),%rax
    4bad:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4bb1:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
    4bb5:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
    4bbc:	0f 84 d2 00 00 00    	je     4c94 <timer_thread+0x4e4>
    4bc2:	48 83 c3 01          	add    $0x1,%rbx
    4bc6:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4bca:	7f cc                	jg     4b98 <timer_thread+0x3e8>
    4bcc:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4bd0:	85 d2                	test   %edx,%edx
    4bd2:	7e 7c                	jle    4c50 <timer_thread+0x4a0>
    4bd4:	41 8b 47 40          	mov    0x40(%r15),%eax
    4bd8:	85 c0                	test   %eax,%eax
    4bda:	7e 74                	jle    4c50 <timer_thread+0x4a0>
    4bdc:	48 63 f0             	movslq %eax,%rsi
    4bdf:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4be3:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4beb:	31 c9                	xor    %ecx,%ecx
    4bed:	48 c1 e6 09          	shl    $0x9,%rsi
    4bf1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4bf8:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4bfc:	48 8b 40 38          	mov    0x38(%rax),%rax
    4c00:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4c04:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4c0a:	74 1c                	je     4c28 <timer_thread+0x478>
    4c0c:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4c16:	48 05 00 02 00 00    	add    $0x200,%rax
    4c1c:	48 39 d0             	cmp    %rdx,%rax
    4c1f:	74 26                	je     4c47 <timer_thread+0x497>
    4c21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c28:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
    4c32:	48 05 00 04 00 00    	add    $0x400,%rax
    4c38:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
    4c42:	48 39 d0             	cmp    %rdx,%rax
    4c45:	75 e1                	jne    4c28 <timer_thread+0x478>
    4c47:	48 83 c1 08          	add    $0x8,%rcx
    4c4b:	48 39 cf             	cmp    %rcx,%rdi
    4c4e:	75 a8                	jne    4bf8 <timer_thread+0x448>
    4c50:	0f ae f0             	mfence
    4c53:	48 8d 3d 4d 34 00 00 	lea    0x344d(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4c5a:	e8 d1 d6 ff ff       	call   2330 <puts@plt>
    4c5f:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4c67:	48 8d 3d 40 34 00 00 	lea    0x3440(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4c6e:	e8 bd d6 ff ff       	call   2330 <puts@plt>
    4c73:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4c78:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4c81:	75 41                	jne    4cc4 <timer_thread+0x514>
    4c83:	48 83 c4 58          	add    $0x58,%rsp
    4c87:	31 c0                	xor    %eax,%eax
    4c89:	5b                   	pop    %rbx
    4c8a:	5d                   	pop    %rbp
    4c8b:	41 5c                	pop    %r12
    4c8d:	41 5d                	pop    %r13
    4c8f:	41 5e                	pop    %r14
    4c91:	41 5f                	pop    %r15
    4c93:	c3                   	ret
    4c94:	4c 89 e7             	mov    %r12,%rdi
    4c97:	e8 94 d6 ff ff       	call   2330 <puts@plt>
    4c9c:	49 8b 47 18          	mov    0x18(%r15),%rax
    4ca0:	be 01 00 00 00       	mov    $0x1,%esi
    4ca5:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    4ca9:	48 83 c3 01          	add    $0x1,%rbx
    4cad:	8b 78 60             	mov    0x60(%rax),%edi
    4cb0:	e8 ab d7 ff ff       	call   2460 <eventfd_write@plt>
    4cb5:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4cb9:	0f 8f d9 fe ff ff    	jg     4b98 <timer_thread+0x3e8>
    4cbf:	e9 08 ff ff ff       	jmp    4bcc <timer_thread+0x41c>
    4cc4:	e8 b7 d6 ff ff       	call   2380 <__stack_chk_fail@plt>
    4cc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004cd0 <minf>:
    4cd0:	f3 0f 1e fa          	endbr64
    4cd4:	39 f7                	cmp    %esi,%edi
    4cd6:	89 f0                	mov    %esi,%eax
    4cd8:	0f 4e c7             	cmovle %edi,%eax
    4cdb:	c3                   	ret
    4cdc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004ce0 <maxf>:
    4ce0:	f3 0f 1e fa          	endbr64
    4ce4:	39 f7                	cmp    %esi,%edi
    4ce6:	89 f0                	mov    %esi,%eax
    4ce8:	0f 4d c7             	cmovge %edi,%eax
    4ceb:	c3                   	ret
    4cec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004cf0 <strtolower>:
    4cf0:	f3 0f 1e fa          	endbr64
    4cf4:	55                   	push   %rbp
    4cf5:	53                   	push   %rbx
    4cf6:	48 83 ec 08          	sub    $0x8,%rsp
    4cfa:	48 0f be 1f          	movsbq (%rdi),%rbx
    4cfe:	84 db                	test   %bl,%bl
    4d00:	74 24                	je     4d26 <strtolower+0x36>
    4d02:	48 89 fd             	mov    %rdi,%rbp
    4d05:	e8 86 d8 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4d0a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d10:	48 8b 10             	mov    (%rax),%rdx
    4d13:	48 83 c5 01          	add    $0x1,%rbp
    4d17:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4d1a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    4d1d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4d22:	84 db                	test   %bl,%bl
    4d24:	75 ea                	jne    4d10 <strtolower+0x20>
    4d26:	48 83 c4 08          	add    $0x8,%rsp
    4d2a:	5b                   	pop    %rbx
    4d2b:	5d                   	pop    %rbp
    4d2c:	c3                   	ret
    4d2d:	0f 1f 00             	nopl   (%rax)

0000000000004d30 <zh_malloc>:
    4d30:	f3 0f 1e fa          	endbr64
    4d34:	48 83 ec 08          	sub    $0x8,%rsp
    4d38:	e8 33 d7 ff ff       	call   2470 <malloc@plt>
    4d3d:	48 85 c0             	test   %rax,%rax
    4d40:	74 05                	je     4d47 <zh_malloc+0x17>
    4d42:	48 83 c4 08          	add    $0x8,%rsp
    4d46:	c3                   	ret
    4d47:	48 8b 0d d2 62 00 00 	mov    0x62d2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4d4e:	ba 28 00 00 00       	mov    $0x28,%edx
    4d53:	be 01 00 00 00       	mov    $0x1,%esi
    4d58:	48 8d 3d 79 38 00 00 	lea    0x3879(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    4d5f:	e8 cc d7 ff ff       	call   2530 <fwrite@plt>
    4d64:	bf 01 00 00 00       	mov    $0x1,%edi
    4d69:	e8 a2 d7 ff ff       	call   2510 <exit@plt>
    4d6e:	66 90                	xchg   %ax,%ax

0000000000004d70 <get_filename_ext>:
    4d70:	f3 0f 1e fa          	endbr64
    4d74:	53                   	push   %rbx
    4d75:	be 2e 00 00 00       	mov    $0x2e,%esi
    4d7a:	48 89 fb             	mov    %rdi,%rbx
    4d7d:	e8 2e d6 ff ff       	call   23b0 <strrchr@plt>
    4d82:	48 85 c0             	test   %rax,%rax
    4d85:	74 11                	je     4d98 <get_filename_ext+0x28>
    4d87:	48 39 c3             	cmp    %rax,%rbx
    4d8a:	74 0c                	je     4d98 <get_filename_ext+0x28>
    4d8c:	48 83 c0 01          	add    $0x1,%rax
    4d90:	5b                   	pop    %rbx
    4d91:	c3                   	ret
    4d92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4d98:	48 8d 05 57 33 00 00 	lea    0x3357(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
    4d9f:	5b                   	pop    %rbx
    4da0:	c3                   	ret
    4da1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4dac:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004db0 <send_headers>:
    4db0:	f3 0f 1e fa          	endbr64
    4db4:	41 55                	push   %r13
    4db6:	49 89 f5             	mov    %rsi,%r13
    4db9:	48 89 fe             	mov    %rdi,%rsi
    4dbc:	41 54                	push   %r12
    4dbe:	55                   	push   %rbp
    4dbf:	48 89 d5             	mov    %rdx,%rbp
    4dc2:	ba 00 04 00 00       	mov    $0x400,%edx
    4dc7:	53                   	push   %rbx
    4dc8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4dcf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4dd8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4de0:	31 c0                	xor    %eax,%eax
    4de2:	49 89 e4             	mov    %rsp,%r12
    4de5:	4c 89 e7             	mov    %r12,%rdi
    4de8:	e8 a3 d6 ff ff       	call   2490 <__strcpy_chk@plt>
    4ded:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4df2:	84 db                	test   %bl,%bl
    4df4:	74 24                	je     4e1a <send_headers+0x6a>
    4df6:	e8 95 d7 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4dfb:	48 8b 08             	mov    (%rax),%rcx
    4dfe:	4c 89 e0             	mov    %r12,%rax
    4e01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4e08:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    4e0b:	48 83 c0 01          	add    $0x1,%rax
    4e0f:	88 50 ff             	mov    %dl,-0x1(%rax)
    4e12:	48 0f be 18          	movsbq (%rax),%rbx
    4e16:	84 db                	test   %bl,%bl
    4e18:	75 ee                	jne    4e08 <send_headers+0x58>
    4e1a:	bf 11 00 00 00       	mov    $0x11,%edi
    4e1f:	e8 4c d6 ff ff       	call   2470 <malloc@plt>
    4e24:	48 85 c0             	test   %rax,%rax
    4e27:	0f 84 7e 04 00 00    	je     52ab <send_headers+0x4fb>
    4e2d:	66 0f 6f 05 db 3d 00 00 	movdqa 0x3ddb(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4e35:	48 89 45 00          	mov    %rax,0x0(%rbp)
    4e39:	bf 17 00 00 00       	mov    $0x17,%edi
    4e3e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4e46:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4e4a:	0f 11 00             	movups %xmm0,(%rax)
    4e4d:	e8 1e d6 ff ff       	call   2470 <malloc@plt>
    4e52:	48 85 c0             	test   %rax,%rax
    4e55:	0f 84 50 04 00 00    	je     52ab <send_headers+0x4fb>
    4e5b:	66 0f 6f 05 bd 3d 00 00 	movdqa 0x3dbd(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4e63:	48 89 45 10          	mov    %rax,0x10(%rbp)
    4e67:	4c 89 e7             	mov    %r12,%rdi
    4e6a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    4e74:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4e7c:	0f 11 00             	movups %xmm0,(%rax)
    4e7f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    4e83:	be 2e 00 00 00       	mov    $0x2e,%esi
    4e88:	e8 23 d5 ff ff       	call   23b0 <strrchr@plt>
    4e8d:	48 85 c0             	test   %rax,%rax
    4e90:	0f 84 ea 02 00 00    	je     5180 <send_headers+0x3d0>
    4e96:	4c 39 e0             	cmp    %r12,%rax
    4e99:	0f 84 e1 02 00 00    	je     5180 <send_headers+0x3d0>
    4e9f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    4ea3:	48 8d 3d 1a 32 00 00 	lea    0x321a(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4eaa:	48 89 de             	mov    %rbx,%rsi
    4ead:	e8 5e d5 ff ff       	call   2410 <strcmp@plt>
    4eb2:	85 c0                	test   %eax,%eax
    4eb4:	75 20                	jne    4ed6 <send_headers+0x126>
    4eb6:	66 0f 6f 05 72 3d 00 00 	movdqa 0x3d72(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4ebe:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ec6:	66 0f 6f 05 72 3d 00 00 	movdqa 0x3d72(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4ece:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4ed6:	48 89 de             	mov    %rbx,%rsi
    4ed9:	48 8d 3d e8 31 00 00 	lea    0x31e8(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4ee0:	e8 2b d5 ff ff       	call   2410 <strcmp@plt>
    4ee5:	85 c0                	test   %eax,%eax
    4ee7:	75 20                	jne    4f09 <send_headers+0x159>
    4ee9:	66 0f 6f 05 3f 3d 00 00 	movdqa 0x3d3f(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4ef1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ef9:	66 0f 6f 05 3f 3d 00 00 	movdqa 0x3d3f(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4f01:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4f09:	48 89 de             	mov    %rbx,%rsi
    4f0c:	48 8d 3d ba 31 00 00 	lea    0x31ba(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4f13:	e8 f8 d4 ff ff       	call   2410 <strcmp@plt>
    4f18:	85 c0                	test   %eax,%eax
    4f1a:	0f 84 10 02 00 00    	je     5130 <send_headers+0x380>
    4f20:	48 89 de             	mov    %rbx,%rsi
    4f23:	48 8d 3d a7 31 00 00 	lea    0x31a7(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4f2a:	e8 e1 d4 ff ff       	call   2410 <strcmp@plt>
    4f2f:	85 c0                	test   %eax,%eax
    4f31:	0f 84 a9 02 00 00    	je     51e0 <send_headers+0x430>
    4f37:	48 89 de             	mov    %rbx,%rsi
    4f3a:	48 8d 3d 94 31 00 00 	lea    0x3194(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4f41:	e8 ca d4 ff ff       	call   2410 <strcmp@plt>
    4f46:	85 c0                	test   %eax,%eax
    4f48:	0f 84 6a 02 00 00    	je     51b8 <send_headers+0x408>
    4f4e:	48 89 de             	mov    %rbx,%rsi
    4f51:	48 8d 3d c0 31 00 00 	lea    0x31c0(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4f58:	e8 b3 d4 ff ff       	call   2410 <strcmp@plt>
    4f5d:	85 c0                	test   %eax,%eax
    4f5f:	0f 84 2b 02 00 00    	je     5190 <send_headers+0x3e0>
    4f65:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4f68:	0f 84 52 01 00 00    	je     50c0 <send_headers+0x310>
    4f6e:	48 89 de             	mov    %rbx,%rsi
    4f71:	48 8d 3d 61 31 00 00 	lea    0x3161(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4f78:	e8 93 d4 ff ff       	call   2410 <strcmp@plt>
    4f7d:	85 c0                	test   %eax,%eax
    4f7f:	0f 84 ab 02 00 00    	je     5230 <send_headers+0x480>
    4f85:	48 89 de             	mov    %rbx,%rsi
    4f88:	48 8d 3d 4e 31 00 00 	lea    0x314e(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4f8f:	e8 7c d4 ff ff       	call   2410 <strcmp@plt>
    4f94:	85 c0                	test   %eax,%eax
    4f96:	0f 84 6c 02 00 00    	je     5208 <send_headers+0x458>
    4f9c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4fa4:	4c 89 e7             	mov    %r12,%rdi
    4fa7:	e8 c4 d3 ff ff       	call   2370 <strlen@plt>
    4fac:	48 89 c7             	mov    %rax,%rdi
    4faf:	48 89 c3             	mov    %rax,%rbx
    4fb2:	e8 b9 d4 ff ff       	call   2470 <malloc@plt>
    4fb7:	48 85 c0             	test   %rax,%rax
    4fba:	0f 84 eb 02 00 00    	je     52ab <send_headers+0x4fb>
    4fc0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    4fc4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
    4fc8:	83 fb 08             	cmp    $0x8,%ebx
    4fcb:	0f 83 3f 01 00 00    	jae    5110 <send_headers+0x360>
    4fd1:	f6 c3 04             	test   $0x4,%bl
    4fd4:	0f 85 7b 02 00 00    	jne    5255 <send_headers+0x4a5>
    4fda:	85 db                	test   %ebx,%ebx
    4fdc:	74 13                	je     4ff1 <send_headers+0x241>
    4fde:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4fe6:	88 10                	mov    %dl,(%rax)
    4fe8:	f6 c3 02             	test   $0x2,%bl
    4feb:	0f 85 96 02 00 00    	jne    5287 <send_headers+0x4d7>
    4ff1:	4d 89 e8             	mov    %r13,%r8
    4ff4:	48 8d 0d e6 30 00 00 	lea    0x30e6(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4ffb:	4c 89 e7             	mov    %r12,%rdi
    4ffe:	31 c0                	xor    %eax,%eax
    5000:	ba 00 04 00 00       	mov    $0x400,%edx
    5005:	be 01 00 00 00       	mov    $0x1,%esi
    500a:	e8 91 d5 ff ff       	call   25a0 <__sprintf_chk@plt>
    500f:	4c 89 e7             	mov    %r12,%rdi
    5012:	e8 59 d3 ff ff       	call   2370 <strlen@plt>
    5017:	48 89 c7             	mov    %rax,%rdi
    501a:	48 89 c3             	mov    %rax,%rbx
    501d:	e8 4e d4 ff ff       	call   2470 <malloc@plt>
    5022:	48 85 c0             	test   %rax,%rax
    5025:	0f 84 80 02 00 00    	je     52ab <send_headers+0x4fb>
    502b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    502f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    5033:	83 fb 08             	cmp    $0x8,%ebx
    5036:	0f 83 1c 01 00 00    	jae    5158 <send_headers+0x3a8>
    503c:	f6 c3 04             	test   $0x4,%bl
    503f:	0f 85 29 02 00 00    	jne    526e <send_headers+0x4be>
    5045:	85 db                	test   %ebx,%ebx
    5047:	74 13                	je     505c <send_headers+0x2ac>
    5049:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    5051:	88 10                	mov    %dl,(%rax)
    5053:	f6 c3 02             	test   $0x2,%bl
    5056:	0f 85 3d 02 00 00    	jne    5299 <send_headers+0x4e9>
    505c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    5061:	bf 02 00 00 00       	mov    $0x2,%edi
    5066:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    506e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    5076:	e8 f5 d3 ff ff       	call   2470 <malloc@plt>
    507b:	48 85 c0             	test   %rax,%rax
    507e:	0f 84 27 02 00 00    	je     52ab <send_headers+0x4fb>
    5084:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    508c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    5090:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    5098:	66 89 10             	mov    %dx,(%rax)
    509b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    50a3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    50ac:	0f 85 20 02 00 00    	jne    52d2 <send_headers+0x522>
    50b2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    50b9:	5b                   	pop    %rbx
    50ba:	5d                   	pop    %rbp
    50bb:	41 5c                	pop    %r12
    50bd:	41 5d                	pop    %r13
    50bf:	c3                   	ret
    50c0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    50c4:	0f 85 a4 fe ff ff    	jne    4f6e <send_headers+0x1be>
    50ca:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    50ce:	0f 85 9a fe ff ff    	jne    4f6e <send_headers+0x1be>
    50d4:	66 0f 6f 05 b4 3b 00 00 	movdqa 0x3bb4(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
    50dc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    50e6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    50ee:	66 0f 6f 05 aa 3b 00 00 	movdqa 0x3baa(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
    50f6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    50fe:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    5106:	e9 63 fe ff ff       	jmp    4f6e <send_headers+0x1be>
    510b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5110:	89 da                	mov    %ebx,%edx
    5112:	48 89 c7             	mov    %rax,%rdi
    5115:	4c 89 e6             	mov    %r12,%rsi
    5118:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    511d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5122:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5125:	c1 e9 03             	shr    $0x3,%ecx
    5128:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    512b:	e9 c1 fe ff ff       	jmp    4ff1 <send_headers+0x241>
    5130:	66 0f 6f 05 f8 3a 00 00 	movdqa 0x3af8(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    5138:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5140:	66 0f 6f 05 08 3b 00 00 	movdqa 0x3b08(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    5148:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5150:	e9 cb fd ff ff       	jmp    4f20 <send_headers+0x170>
    5155:	0f 1f 00             	nopl   (%rax)
    5158:	89 da                	mov    %ebx,%edx
    515a:	48 89 c7             	mov    %rax,%rdi
    515d:	4c 89 e6             	mov    %r12,%rsi
    5160:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    5165:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    516a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    516d:	c1 e9 03             	shr    $0x3,%ecx
    5170:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    5173:	e9 e4 fe ff ff       	jmp    505c <send_headers+0x2ac>
    5178:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5180:	48 8d 1d 6f 2f 00 00 	lea    0x2f6f(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    5187:	e9 94 fd ff ff       	jmp    4f20 <send_headers+0x170>
    518c:	0f 1f 40 00          	nopl   0x0(%rax)
    5190:	66 0f 6f 05 d8 3a 00 00 	movdqa 0x3ad8(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    5198:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    51a0:	66 0f 6f 05 d8 3a 00 00 	movdqa 0x3ad8(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    51a8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    51b0:	e9 b0 fd ff ff       	jmp    4f65 <send_headers+0x1b5>
    51b5:	0f 1f 00             	nopl   (%rax)
    51b8:	66 0f 6f 05 b0 3a 00 00 	movdqa 0x3ab0(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    51c0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    51c8:	66 0f 6f 05 b0 3a 00 00 	movdqa 0x3ab0(%rip),%xmm0        # 8c80 <_IO_stdin_used+0xc80>
    51d0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    51d8:	e9 71 fd ff ff       	jmp    4f4e <send_headers+0x19e>
    51dd:	0f 1f 00             	nopl   (%rax)
    51e0:	66 0f 6f 05 48 3a 00 00 	movdqa 0x3a48(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    51e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    51f0:	66 0f 6f 05 68 3a 00 00 	movdqa 0x3a68(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    51f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5200:	e9 32 fd ff ff       	jmp    4f37 <send_headers+0x187>
    5205:	0f 1f 00             	nopl   (%rax)
    5208:	66 0f 6f 05 60 3a 00 00 	movdqa 0x3a60(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    5210:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5218:	66 0f 6f 05 a0 3a 00 00 	movdqa 0x3aa0(%rip),%xmm0        # 8cc0 <_IO_stdin_used+0xcc0>
    5220:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5228:	e9 6f fd ff ff       	jmp    4f9c <send_headers+0x1ec>
    522d:	0f 1f 00             	nopl   (%rax)
    5230:	66 0f 6f 05 38 3a 00 00 	movdqa 0x3a38(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    5238:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5240:	66 0f 6f 05 68 3a 00 00 	movdqa 0x3a68(%rip),%xmm0        # 8cb0 <_IO_stdin_used+0xcb0>
    5248:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5250:	e9 30 fd ff ff       	jmp    4f85 <send_headers+0x1d5>
    5255:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    525c:	89 db                	mov    %ebx,%ebx
    525e:	89 10                	mov    %edx,(%rax)
    5260:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5265:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5269:	e9 83 fd ff ff       	jmp    4ff1 <send_headers+0x241>
    526e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5275:	89 db                	mov    %ebx,%ebx
    5277:	89 10                	mov    %edx,(%rax)
    5279:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    527e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5282:	e9 d5 fd ff ff       	jmp    505c <send_headers+0x2ac>
    5287:	89 db                	mov    %ebx,%ebx
    5289:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    528f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5294:	e9 58 fd ff ff       	jmp    4ff1 <send_headers+0x241>
    5299:	89 db                	mov    %ebx,%ebx
    529b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    52a1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    52a6:	e9 b1 fd ff ff       	jmp    505c <send_headers+0x2ac>
    52ab:	48 8b 0d 6e 5d 00 00 	mov    0x5d6e(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    52b2:	ba 28 00 00 00       	mov    $0x28,%edx
    52b7:	be 01 00 00 00       	mov    $0x1,%esi
    52bc:	48 8d 3d 15 33 00 00 	lea    0x3315(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    52c3:	e8 68 d2 ff ff       	call   2530 <fwrite@plt>
    52c8:	bf 01 00 00 00       	mov    $0x1,%edi
    52cd:	e8 3e d2 ff ff       	call   2510 <exit@plt>
    52d2:	e8 a9 d0 ff ff       	call   2380 <__stack_chk_fail@plt>
    52d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000052e0 <copy_file_contents>:
    52e0:	f3 0f 1e fa          	endbr64
    52e4:	41 55                	push   %r13
    52e6:	49 89 d5             	mov    %rdx,%r13
    52e9:	41 54                	push   %r12
    52eb:	49 89 fc             	mov    %rdi,%r12
    52ee:	48 89 f7             	mov    %rsi,%rdi
    52f1:	55                   	push   %rbp
    52f2:	53                   	push   %rbx
    52f3:	48 89 f3             	mov    %rsi,%rbx
    52f6:	48 83 ec 08          	sub    $0x8,%rsp
    52fa:	e8 71 d1 ff ff       	call   2470 <malloc@plt>
    52ff:	48 85 c0             	test   %rax,%rax
    5302:	74 6b                	je     536f <copy_file_contents+0x8f>
    5304:	4c 89 e7             	mov    %r12,%rdi
    5307:	48 89 c5             	mov    %rax,%rbp
    530a:	31 f6                	xor    %esi,%esi
    530c:	31 c0                	xor    %eax,%eax
    530e:	e8 cd d1 ff ff       	call   24e0 <open@plt>
    5313:	41 89 c4             	mov    %eax,%r12d
    5316:	85 c0                	test   %eax,%eax
    5318:	0f 88 b8 d2 ff ff    	js     25d6 <copy_file_contents.cold>
    531e:	48 89 da             	mov    %rbx,%rdx
    5321:	48 89 ee             	mov    %rbp,%rsi
    5324:	89 c7                	mov    %eax,%edi
    5326:	e8 c5 d0 ff ff       	call   23f0 <read@plt>
    532b:	48 98                	cltq
    532d:	48 39 d8             	cmp    %rbx,%rax
    5330:	7c 1e                	jl     5350 <copy_file_contents+0x70>
    5332:	44 89 e7             	mov    %r12d,%edi
    5335:	e8 96 d0 ff ff       	call   23d0 <close@plt>
    533a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    533e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
    5342:	48 83 c4 08          	add    $0x8,%rsp
    5346:	5b                   	pop    %rbx
    5347:	5d                   	pop    %rbp
    5348:	41 5c                	pop    %r12
    534a:	41 5d                	pop    %r13
    534c:	c3                   	ret
    534d:	0f 1f 00             	nopl   (%rax)
    5350:	48 8b 0d c9 5c 00 00 	mov    0x5cc9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5357:	ba 1a 00 00 00       	mov    $0x1a,%edx
    535c:	be 01 00 00 00       	mov    $0x1,%esi
    5361:	48 8d 3d 8f 2d 00 00 	lea    0x2d8f(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    5368:	e8 c3 d1 ff ff       	call   2530 <fwrite@plt>
    536d:	eb c3                	jmp    5332 <copy_file_contents+0x52>
    536f:	48 8b 0d aa 5c 00 00 	mov    0x5caa(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5376:	ba 28 00 00 00       	mov    $0x28,%edx
    537b:	be 01 00 00 00       	mov    $0x1,%esi
    5380:	48 8d 3d 51 32 00 00 	lea    0x3251(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    5387:	e8 a4 d1 ff ff       	call   2530 <fwrite@plt>
    538c:	bf 01 00 00 00       	mov    $0x1,%edi
    5391:	e8 7a d1 ff ff       	call   2510 <exit@plt>
    5396:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000053a0 <add_write_request>:
    53a0:	f3 0f 1e fa          	endbr64
    53a4:	8b 46 44             	mov    0x44(%rsi),%eax
    53a7:	48 89 fa             	mov    %rdi,%rdx
    53aa:	48 89 f7             	mov    %rsi,%rdi
    53ad:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
    53b3:	8d 70 01             	lea    0x1(%rax),%esi
    53b6:	48 8b 07             	mov    (%rdi),%rax
    53b9:	44 8b 00             	mov    (%rax),%r8d
    53bc:	f6 c1 02             	test   $0x2,%cl
    53bf:	74 00                	je     53c1 <add_write_request+0x21>
    53c1:	89 f0                	mov    %esi,%eax
    53c3:	44 29 c0             	sub    %r8d,%eax
    53c6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    53c9:	0f 82 13 d2 ff ff    	jb     25e2 <add_write_request.cold>
    53cf:	c1 e9 0a             	shr    $0xa,%ecx
    53d2:	48 83 ec 08          	sub    $0x8,%rsp
    53d6:	8b 47 44             	mov    0x44(%rdi),%eax
    53d9:	23 47 58             	and    0x58(%rdi),%eax
    53dc:	83 e1 01             	and    $0x1,%ecx
    53df:	89 77 44             	mov    %esi,0x44(%rdi)
    53e2:	8b 72 08             	mov    0x8(%rdx),%esi
    53e5:	66 0f ef c0          	pxor   %xmm0,%xmm0
    53e9:	d3 e0                	shl    %cl,%eax
    53eb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    53ee:	48 c1 e0 06          	shl    $0x6,%rax
    53f2:	48 03 47 38          	add    0x38(%rdi),%rax
    53f6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
    53fc:	89 70 04             	mov    %esi,0x4(%rax)
    53ff:	48 8d 72 10          	lea    0x10(%rdx),%rsi
    5403:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    5409:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5411:	48 89 70 10          	mov    %rsi,0x10(%rax)
    5415:	89 48 18             	mov    %ecx,0x18(%rax)
    5418:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    541f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5427:	48 89 50 20          	mov    %rdx,0x20(%rax)
    542b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    542f:	e8 5c cf ff ff       	call   2390 <io_uring_submit@plt>
    5434:	31 c0                	xor    %eax,%eax
    5436:	48 83 c4 08          	add    $0x8,%rsp
    543a:	c3                   	ret
    543b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005440 <add_read_request>:
    5440:	f3 0f 1e fa          	endbr64
    5444:	41 55                	push   %r13
    5446:	41 89 fd             	mov    %edi,%r13d
    5449:	41 54                	push   %r12
    544b:	55                   	push   %rbp
    544c:	53                   	push   %rbx
    544d:	48 89 f3             	mov    %rsi,%rbx
    5450:	48 83 ec 08          	sub    $0x8,%rsp
    5454:	8b 46 44             	mov    0x44(%rsi),%eax
    5457:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
    545d:	48 8b 16             	mov    (%rsi),%rdx
    5460:	83 c0 01             	add    $0x1,%eax
    5463:	8b 32                	mov    (%rdx),%esi
    5465:	f6 c1 02             	test   $0x2,%cl
    5468:	74 00                	je     546a <add_read_request+0x2a>
    546a:	89 c2                	mov    %eax,%edx
    546c:	29 f2                	sub    %esi,%edx
    546e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5471:	0f 82 7b d1 ff ff    	jb     25f2 <add_read_request.cold>
    5477:	8b 6b 44             	mov    0x44(%rbx),%ebp
    547a:	c1 e9 0a             	shr    $0xa,%ecx
    547d:	89 43 44             	mov    %eax,0x44(%rbx)
    5480:	bf 20 00 00 00       	mov    $0x20,%edi
    5485:	83 e1 01             	and    $0x1,%ecx
    5488:	23 6b 58             	and    0x58(%rbx),%ebp
    548b:	d3 e5                	shl    %cl,%ebp
    548d:	48 c1 e5 06          	shl    $0x6,%rbp
    5491:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5495:	e8 d6 cf ff ff       	call   2470 <malloc@plt>
    549a:	be 01 00 00 00       	mov    $0x1,%esi
    549f:	bf 00 20 00 00       	mov    $0x2000,%edi
    54a4:	49 89 c4             	mov    %rax,%r12
    54a7:	e8 54 cf ff ff       	call   2400 <calloc@plt>
    54ac:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
    54b1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    54b5:	48 89 df             	mov    %rbx,%rdi
    54b8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    54bd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    54c2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    54cb:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
    54d3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
    54d7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
    54db:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
    54e2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    54ea:	48 89 45 10          	mov    %rax,0x10(%rbp)
    54ee:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
    54f6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    54fe:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5502:	e8 89 ce ff ff       	call   2390 <io_uring_submit@plt>
    5507:	48 83 c4 08          	add    $0x8,%rsp
    550b:	31 c0                	xor    %eax,%eax
    550d:	5b                   	pop    %rbx
    550e:	5d                   	pop    %rbp
    550f:	41 5c                	pop    %r12
    5511:	41 5d                	pop    %r13
    5513:	c3                   	ret
    5514:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    551f:	90                   	nop

0000000000005520 <_send_static_string_content>:
    5520:	f3 0f 1e fa          	endbr64
    5524:	41 56                	push   %r14
    5526:	41 89 f6             	mov    %esi,%r14d
    5529:	41 55                	push   %r13
    552b:	49 89 fd             	mov    %rdi,%r13
    552e:	bf 20 00 00 00       	mov    $0x20,%edi
    5533:	41 54                	push   %r12
    5535:	55                   	push   %rbp
    5536:	48 89 d5             	mov    %rdx,%rbp
    5539:	53                   	push   %rbx
    553a:	e8 31 cf ff ff       	call   2470 <malloc@plt>
    553f:	48 85 c0             	test   %rax,%rax
    5542:	0f 84 dd 00 00 00    	je     5625 <_send_static_string_content+0x105>
    5548:	48 89 c3             	mov    %rax,%rbx
    554b:	4c 89 ef             	mov    %r13,%rdi
    554e:	e8 1d ce ff ff       	call   2370 <strlen@plt>
    5553:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    555a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    555e:	48 89 c7             	mov    %rax,%rdi
    5561:	49 89 c4             	mov    %rax,%r12
    5564:	e8 07 cf ff ff       	call   2470 <malloc@plt>
    5569:	48 89 c7             	mov    %rax,%rdi
    556c:	48 85 c0             	test   %rax,%rax
    556f:	0f 84 b0 00 00 00    	je     5625 <_send_static_string_content+0x105>
    5575:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5579:	4c 89 e2             	mov    %r12,%rdx
    557c:	4c 89 ee             	mov    %r13,%rsi
    557f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5583:	e8 b8 ce ff ff       	call   2440 <memcpy@plt>
    5588:	8b 45 44             	mov    0x44(%rbp),%eax
    558b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
    5591:	8d 50 01             	lea    0x1(%rax),%edx
    5594:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5598:	8b 30                	mov    (%rax),%esi
    559a:	f6 c1 02             	test   $0x2,%cl
    559d:	0f 85 7d 00 00 00    	jne    5620 <_send_static_string_content+0x100>
    55a3:	89 d0                	mov    %edx,%eax
    55a5:	29 f0                	sub    %esi,%eax
    55a7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    55aa:	0f 82 4c d0 ff ff    	jb     25fc <_send_static_string_content.cold>
    55b0:	c1 e9 0a             	shr    $0xa,%ecx
    55b3:	8b 45 44             	mov    0x44(%rbp),%eax
    55b6:	23 45 58             	and    0x58(%rbp),%eax
    55b9:	89 55 44             	mov    %edx,0x44(%rbp)
    55bc:	83 e1 01             	and    $0x1,%ecx
    55bf:	8b 53 04             	mov    0x4(%rbx),%edx
    55c2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    55c8:	66 0f ef c0          	pxor   %xmm0,%xmm0
    55cc:	d3 e0                	shl    %cl,%eax
    55ce:	8b 4b 08             	mov    0x8(%rbx),%ecx
    55d1:	48 89 ef             	mov    %rbp,%rdi
    55d4:	48 c1 e0 06          	shl    $0x6,%rax
    55d8:	48 03 45 38          	add    0x38(%rbp),%rax
    55dc:	89 48 04             	mov    %ecx,0x4(%rax)
    55df:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
    55e3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
    55e9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    55f1:	48 89 48 10          	mov    %rcx,0x10(%rax)
    55f5:	89 50 18             	mov    %edx,0x18(%rax)
    55f8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
    55ff:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5607:	48 89 58 20          	mov    %rbx,0x20(%rax)
    560b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    560f:	5b                   	pop    %rbx
    5610:	5d                   	pop    %rbp
    5611:	41 5c                	pop    %r12
    5613:	41 5d                	pop    %r13
    5615:	41 5e                	pop    %r14
    5617:	e9 74 cd ff ff       	jmp    2390 <io_uring_submit@plt>
    561c:	0f 1f 40 00          	nopl   0x0(%rax)
    5620:	e9 7e ff ff ff       	jmp    55a3 <_send_static_string_content+0x83>
    5625:	48 8b 0d f4 59 00 00 	mov    0x59f4(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    562c:	ba 28 00 00 00       	mov    $0x28,%edx
    5631:	be 01 00 00 00       	mov    $0x1,%esi
    5636:	48 8d 3d 9b 2f 00 00 	lea    0x2f9b(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    563d:	e8 ee ce ff ff       	call   2530 <fwrite@plt>
    5642:	bf 01 00 00 00       	mov    $0x1,%edi
    5647:	e8 c4 ce ff ff       	call   2510 <exit@plt>
    564c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005650 <handle_unimplemented_method>:
    5650:	f3 0f 1e fa          	endbr64
    5654:	48 89 f2             	mov    %rsi,%rdx
    5657:	89 fe                	mov    %edi,%esi
    5659:	48 8b 3d b8 59 00 00 	mov    0x59b8(%rip),%rdi        # b018 <unimplemented_content>
    5660:	e9 bb fe ff ff       	jmp    5520 <_send_static_string_content>
    5665:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005670 <handle_http_404>:
    5670:	f3 0f 1e fa          	endbr64
    5674:	48 89 f2             	mov    %rsi,%rdx
    5677:	89 fe                	mov    %edi,%esi
    5679:	48 8b 3d 90 59 00 00 	mov    0x5990(%rip),%rdi        # b010 <http_404_content>
    5680:	e9 9b fe ff ff       	jmp    5520 <_send_static_string_content>
    5685:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005690 <handle_get_method>:
    5690:	f3 0f 1e fa          	endbr64
    5694:	41 56                	push   %r14
    5696:	41 55                	push   %r13
    5698:	49 89 d5             	mov    %rdx,%r13
    569b:	41 54                	push   %r12
    569d:	41 89 f4             	mov    %esi,%r12d
    56a0:	55                   	push   %rbp
    56a1:	48 89 fd             	mov    %rdi,%rbp
    56a4:	53                   	push   %rbx
    56a5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    56ac:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    56b5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    56bd:	31 c0                	xor    %eax,%eax
    56bf:	e8 ac cc ff ff       	call   2370 <strlen@plt>
    56c4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    56c9:	48 89 c3             	mov    %rax,%rbx
    56cc:	0f 84 b6 00 00 00    	je     5788 <handle_get_method+0xf8>
    56d2:	b8 69 63 00 00       	mov    $0x6369,%eax
    56d7:	48 89 ee             	mov    %rbp,%rsi
    56da:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    56de:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    56e3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    56eb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    56f3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    56fe:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
    5706:	e8 15 cd ff ff       	call   2420 <__memcpy_chk@plt>
    570b:	48 89 e6             	mov    %rsp,%rsi
    570e:	4c 89 f7             	mov    %r14,%rdi
    5711:	e8 1a cd ff ff       	call   2430 <stat@plt>
    5716:	83 f8 ff             	cmp    $0xffffffff,%eax
    5719:	0f 84 d3 00 00 00    	je     57f2 <handle_get_method+0x162>
    571f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5723:	25 00 f0 00 00       	and    $0xf000,%eax
    5728:	3d 00 80 00 00       	cmp    $0x8000,%eax
    572d:	0f 84 f5 00 00 00    	je     5828 <handle_get_method+0x198>
    5733:	48 8b 3d d6 58 00 00 	mov    0x58d6(%rip),%rdi        # b010 <http_404_content>
    573a:	4c 89 ea             	mov    %r13,%rdx
    573d:	44 89 e6             	mov    %r12d,%esi
    5740:	e8 db fd ff ff       	call   5520 <_send_static_string_content>
    5745:	4c 89 f2             	mov    %r14,%rdx
    5748:	bf 01 00 00 00       	mov    $0x1,%edi
    574d:	31 c0                	xor    %eax,%eax
    574f:	48 8d 35 f1 29 00 00 	lea    0x29f1(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5756:	e8 55 cd ff ff       	call   24b0 <__printf_chk@plt>
    575b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5763:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    576c:	0f 85 20 01 00 00    	jne    5892 <handle_get_method+0x202>
    5772:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5779:	5b                   	pop    %rbx
    577a:	5d                   	pop    %rbp
    577b:	41 5c                	pop    %r12
    577d:	41 5d                	pop    %r13
    577f:	41 5e                	pop    %r14
    5781:	c3                   	ret
    5782:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5788:	ba 69 63 00 00       	mov    $0x6369,%edx
    578d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5795:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    579a:	48 89 ee             	mov    %rbp,%rsi
    579d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
    57a5:	48 89 c2             	mov    %rax,%rdx
    57a8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    57b0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    57bb:	e8 60 cc ff ff       	call   2420 <__memcpy_chk@plt>
    57c0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    57c5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    57ca:	48 8d 35 41 29 00 00 	lea    0x2941(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    57d1:	48 29 d9             	sub    %rbx,%rcx
    57d4:	ba 0b 00 00 00       	mov    $0xb,%edx
    57d9:	e8 42 cc ff ff       	call   2420 <__memcpy_chk@plt>
    57de:	48 89 e6             	mov    %rsp,%rsi
    57e1:	4c 89 f7             	mov    %r14,%rdi
    57e4:	e8 47 cc ff ff       	call   2430 <stat@plt>
    57e9:	83 f8 ff             	cmp    $0xffffffff,%eax
    57ec:	0f 85 2d ff ff ff    	jne    571f <handle_get_method+0x8f>
    57f2:	4c 89 f2             	mov    %r14,%rdx
    57f5:	48 89 e9             	mov    %rbp,%rcx
    57f8:	48 8d 35 1e 29 00 00 	lea    0x291e(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    57ff:	31 c0                	xor    %eax,%eax
    5801:	bf 01 00 00 00       	mov    $0x1,%edi
    5806:	e8 a5 cc ff ff       	call   24b0 <__printf_chk@plt>
    580b:	48 8b 3d fe 57 00 00 	mov    0x57fe(%rip),%rdi        # b010 <http_404_content>
    5812:	4c 89 ea             	mov    %r13,%rdx
    5815:	44 89 e6             	mov    %r12d,%esi
    5818:	e8 03 fd ff ff       	call   5520 <_send_static_string_content>
    581d:	e9 39 ff ff ff       	jmp    575b <handle_get_method+0xcb>
    5822:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5828:	bf 70 00 00 00       	mov    $0x70,%edi
    582d:	e8 3e cc ff ff       	call   2470 <malloc@plt>
    5832:	48 89 c3             	mov    %rax,%rbx
    5835:	48 85 c0             	test   %rax,%rax
    5838:	74 5d                	je     5897 <handle_get_method+0x207>
    583a:	44 89 60 08          	mov    %r12d,0x8(%rax)
    583e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5843:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5847:	4c 89 f7             	mov    %r14,%rdi
    584a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
    5851:	e8 5a f5 ff ff       	call   4db0 <send_headers>
    5856:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    585b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    585f:	4c 89 f7             	mov    %r14,%rdi
    5862:	e8 79 fa ff ff       	call   52e0 <copy_file_contents>
    5867:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    586c:	4c 89 f2             	mov    %r14,%rdx
    586f:	31 c0                	xor    %eax,%eax
    5871:	48 8d 35 bd 28 00 00 	lea    0x28bd(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    5878:	bf 01 00 00 00       	mov    $0x1,%edi
    587d:	e8 2e cc ff ff       	call   24b0 <__printf_chk@plt>
    5882:	4c 89 ee             	mov    %r13,%rsi
    5885:	48 89 df             	mov    %rbx,%rdi
    5888:	e8 13 fb ff ff       	call   53a0 <add_write_request>
    588d:	e9 c9 fe ff ff       	jmp    575b <handle_get_method+0xcb>
    5892:	e8 e9 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    5897:	48 8b 0d 82 57 00 00 	mov    0x5782(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    589e:	ba 28 00 00 00       	mov    $0x28,%edx
    58a3:	be 01 00 00 00       	mov    $0x1,%esi
    58a8:	48 8d 3d 29 2d 00 00 	lea    0x2d29(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    58af:	e8 7c cc ff ff       	call   2530 <fwrite@plt>
    58b4:	bf 01 00 00 00       	mov    $0x1,%edi
    58b9:	e8 52 cc ff ff       	call   2510 <exit@plt>
    58be:	66 90                	xchg   %ax,%ax

00000000000058c0 <handle_http_method>:
    58c0:	f3 0f 1e fa          	endbr64
    58c4:	41 57                	push   %r15
    58c6:	41 56                	push   %r14
    58c8:	4c 8d 35 dd 27 00 00 	lea    0x27dd(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
    58cf:	41 55                	push   %r13
    58d1:	49 89 d5             	mov    %rdx,%r13
    58d4:	41 54                	push   %r12
    58d6:	41 89 f4             	mov    %esi,%r12d
    58d9:	4c 89 f6             	mov    %r14,%rsi
    58dc:	55                   	push   %rbp
    58dd:	53                   	push   %rbx
    58de:	48 83 ec 18          	sub    $0x18,%rsp
    58e2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    58eb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    58f0:	31 c0                	xor    %eax,%eax
    58f2:	49 89 e7             	mov    %rsp,%r15
    58f5:	4c 89 fa             	mov    %r15,%rdx
    58f8:	e8 e3 ca ff ff       	call   23e0 <strtok_r@plt>
    58fd:	48 0f be 18          	movsbq (%rax),%rbx
    5901:	48 89 c5             	mov    %rax,%rbp
    5904:	84 db                	test   %bl,%bl
    5906:	74 1d                	je     5925 <handle_http_method+0x65>
    5908:	e8 83 cc ff ff       	call   2590 <__ctype_tolower_loc@plt>
    590d:	48 89 ea             	mov    %rbp,%rdx
    5910:	48 8b 08             	mov    (%rax),%rcx
    5913:	48 83 c2 01          	add    $0x1,%rdx
    5917:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    591a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    591d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5921:	84 db                	test   %bl,%bl
    5923:	75 eb                	jne    5910 <handle_http_method+0x50>
    5925:	4c 89 fa             	mov    %r15,%rdx
    5928:	4c 89 f6             	mov    %r14,%rsi
    592b:	31 ff                	xor    %edi,%edi
    592d:	e8 ae ca ff ff       	call   23e0 <strtok_r@plt>
    5932:	48 8d 35 21 28 00 00 	lea    0x2821(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    5939:	48 89 ef             	mov    %rbp,%rdi
    593c:	48 89 c3             	mov    %rax,%rbx
    593f:	e8 cc ca ff ff       	call   2410 <strcmp@plt>
    5944:	4c 89 ea             	mov    %r13,%rdx
    5947:	44 89 e6             	mov    %r12d,%esi
    594a:	85 c0                	test   %eax,%eax
    594c:	75 2a                	jne    5978 <handle_http_method+0xb8>
    594e:	48 89 df             	mov    %rbx,%rdi
    5951:	e8 3a fd ff ff       	call   5690 <handle_get_method>
    5956:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    595b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5964:	75 20                	jne    5986 <handle_http_method+0xc6>
    5966:	48 83 c4 18          	add    $0x18,%rsp
    596a:	5b                   	pop    %rbx
    596b:	5d                   	pop    %rbp
    596c:	41 5c                	pop    %r12
    596e:	41 5d                	pop    %r13
    5970:	41 5e                	pop    %r14
    5972:	41 5f                	pop    %r15
    5974:	c3                   	ret
    5975:	0f 1f 00             	nopl   (%rax)
    5978:	48 8b 3d 99 56 00 00 	mov    0x5699(%rip),%rdi        # b018 <unimplemented_content>
    597f:	e8 9c fb ff ff       	call   5520 <_send_static_string_content>
    5984:	eb d0                	jmp    5956 <handle_http_method+0x96>
    5986:	e8 f5 c9 ff ff       	call   2380 <__stack_chk_fail@plt>
    598b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005990 <get_line>:
    5990:	f3 0f 1e fa          	endbr64
    5994:	85 d2                	test   %edx,%edx
    5996:	7e 38                	jle    59d0 <get_line+0x40>
    5998:	48 63 d2             	movslq %edx,%rdx
    599b:	48 83 c7 01          	add    $0x1,%rdi
    599f:	48 01 f2             	add    %rsi,%rdx
    59a2:	eb 11                	jmp    59b5 <get_line+0x25>
    59a4:	0f 1f 40 00          	nopl   0x0(%rax)
    59a8:	48 83 c6 01          	add    $0x1,%rsi
    59ac:	48 83 c7 01          	add    $0x1,%rdi
    59b0:	48 39 d6             	cmp    %rdx,%rsi
    59b3:	74 1b                	je     59d0 <get_line+0x40>
    59b5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    59b9:	88 06                	mov    %al,(%rsi)
    59bb:	3c 0d                	cmp    $0xd,%al
    59bd:	75 e9                	jne    59a8 <get_line+0x18>
    59bf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    59c2:	75 e4                	jne    59a8 <get_line+0x18>
    59c4:	c6 06 00             	movb   $0x0,(%rsi)
    59c7:	31 c0                	xor    %eax,%eax
    59c9:	c3                   	ret
    59ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    59d0:	b8 01 00 00 00       	mov    $0x1,%eax
    59d5:	c3                   	ret
    59d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000059e0 <handle_client_request>:
    59e0:	f3 0f 1e fa          	endbr64
    59e4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    59eb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    59ef:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    59f8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5a00:	31 c0                	xor    %eax,%eax
    5a02:	49 89 e2             	mov    %rsp,%r10
    5a05:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    5a0d:	4c 89 d0             	mov    %r10,%rax
    5a10:	eb 13                	jmp    5a25 <handle_client_request+0x45>
    5a12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5a18:	48 83 c0 01          	add    $0x1,%rax
    5a1c:	48 83 c1 01          	add    $0x1,%rcx
    5a20:	4c 39 c8             	cmp    %r9,%rax
    5a23:	74 4b                	je     5a70 <handle_client_request+0x90>
    5a25:	44 0f b6 01          	movzbl (%rcx),%r8d
    5a29:	44 88 00             	mov    %r8b,(%rax)
    5a2c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5a30:	75 e6                	jne    5a18 <handle_client_request+0x38>
    5a32:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5a36:	75 e0                	jne    5a18 <handle_client_request+0x38>
    5a38:	c6 00 00             	movb   $0x0,(%rax)
    5a3b:	8b 47 08             	mov    0x8(%rdi),%eax
    5a3e:	48 89 f2             	mov    %rsi,%rdx
    5a41:	4c 89 d7             	mov    %r10,%rdi
    5a44:	89 c6                	mov    %eax,%esi
    5a46:	e8 75 fe ff ff       	call   58c0 <handle_http_method>
    5a4b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5a53:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5a5c:	75 39                	jne    5a97 <handle_client_request+0xb7>
    5a5e:	31 c0                	xor    %eax,%eax
    5a60:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5a67:	c3                   	ret
    5a68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5a70:	48 8b 0d a9 55 00 00 	mov    0x55a9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5a77:	ba 12 00 00 00       	mov    $0x12,%edx
    5a7c:	be 01 00 00 00       	mov    $0x1,%esi
    5a81:	48 8d 3d d6 26 00 00 	lea    0x26d6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5a88:	e8 a3 ca ff ff       	call   2530 <fwrite@plt>
    5a8d:	bf 01 00 00 00       	mov    $0x1,%edi
    5a92:	e8 79 ca ff ff       	call   2510 <exit@plt>
    5a97:	e8 e4 c8 ff ff       	call   2380 <__stack_chk_fail@plt>
    5a9c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005aa0 <add_accept_request>:
    5aa0:	f3 0f 1e fa          	endbr64
    5aa4:	55                   	push   %rbp
    5aa5:	53                   	push   %rbx
    5aa6:	48 89 cb             	mov    %rcx,%rbx
    5aa9:	48 83 ec 08          	sub    $0x8,%rsp
    5aad:	8b 41 44             	mov    0x44(%rcx),%eax
    5ab0:	4c 8b 03             	mov    (%rbx),%r8
    5ab3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
    5ab9:	83 c0 01             	add    $0x1,%eax
    5abc:	45 8b 08             	mov    (%r8),%r9d
    5abf:	f6 c1 02             	test   $0x2,%cl
    5ac2:	74 00                	je     5ac4 <add_accept_request+0x24>
    5ac4:	41 89 c0             	mov    %eax,%r8d
    5ac7:	45 29 c8             	sub    %r9d,%r8d
    5aca:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    5ace:	0f 82 38 cb ff ff    	jb     260c <add_accept_request.cold>
    5ad4:	c1 e9 0a             	shr    $0xa,%ecx
    5ad7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    5ada:	23 6b 58             	and    0x58(%rbx),%ebp
    5add:	89 43 44             	mov    %eax,0x44(%rbx)
    5ae0:	83 e1 01             	and    $0x1,%ecx
    5ae3:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5ae7:	d3 e5                	shl    %cl,%ebp
    5ae9:	48 c1 e5 06          	shl    $0x6,%rbp
    5aed:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5af1:	89 7d 04             	mov    %edi,0x4(%rbp)
    5af4:	bf 10 00 00 00       	mov    $0x10,%edi
    5af9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
    5b00:	48 89 55 08          	mov    %rdx,0x8(%rbp)
    5b04:	48 89 75 10          	mov    %rsi,0x10(%rbp)
    5b08:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
    5b10:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
    5b18:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5b1c:	e8 4f c9 ff ff       	call   2470 <malloc@plt>
    5b21:	48 89 df             	mov    %rbx,%rdi
    5b24:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
    5b2a:	48 89 45 20          	mov    %rax,0x20(%rbp)
    5b2e:	48 83 c4 08          	add    $0x8,%rsp
    5b32:	5b                   	pop    %rbx
    5b33:	5d                   	pop    %rbp
    5b34:	e9 57 c8 ff ff       	jmp    2390 <io_uring_submit@plt>
    5b39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005b40 <io_thread>:
    5b40:	f3 0f 1e fa          	endbr64
    5b44:	41 57                	push   %r15
    5b46:	31 d2                	xor    %edx,%edx
    5b48:	41 56                	push   %r14
    5b4a:	41 55                	push   %r13
    5b4c:	41 54                	push   %r12
    5b4e:	55                   	push   %rbp
    5b4f:	48 89 fd             	mov    %rdi,%rbp
    5b52:	53                   	push   %rbx
    5b53:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
    5b5a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5b63:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    5b6b:	48 8b 47 58          	mov    0x58(%rdi),%rax
    5b6f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5b74:	bf 00 01 00 00       	mov    $0x100,%edi
    5b79:	48 89 de             	mov    %rbx,%rsi
    5b7c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5b80:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5b85:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5b8a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    5b8f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5b94:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    5b9c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5ba1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5ba9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5bae:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5bb6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5bbb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5bc3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5bc8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5bd0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5bd5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    5bdd:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5be5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    5bed:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5bf5:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5bfd:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5c05:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5c0d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5c15:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5c1d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5c25:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5c2d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5c34:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
    5c3c:	e8 0f c8 ff ff       	call   2450 <io_uring_queue_init@plt>
    5c41:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5c45:	31 f6                	xor    %esi,%esi
    5c47:	e8 04 c9 ff ff       	call   2550 <io_uring_register_eventfd@plt>
    5c4c:	31 d2                	xor    %edx,%edx
    5c4e:	be 01 00 00 00       	mov    $0x1,%esi
    5c53:	bf 02 00 00 00       	mov    $0x2,%edi
    5c58:	e8 53 c9 ff ff       	call   25b0 <socket@plt>
    5c5d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5c60:	0f 84 e8 c9 ff ff    	je     264e <io_thread.cold+0x38>
    5c66:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5c6b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5c71:	89 c7                	mov    %eax,%edi
    5c73:	41 89 c4             	mov    %eax,%r12d
    5c76:	ba 02 00 00 00       	mov    $0x2,%edx
    5c7b:	be 01 00 00 00       	mov    $0x1,%esi
    5c80:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
    5c88:	e8 b3 c6 ff ff       	call   2340 <setsockopt@plt>
    5c8d:	85 c0                	test   %eax,%eax
    5c8f:	0f 88 8d c9 ff ff    	js     2622 <io_thread.cold+0xc>
    5c95:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
    5c9a:	ba 10 00 00 00       	mov    $0x10,%edx
    5c9f:	44 89 e7             	mov    %r12d,%edi
    5ca2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5cab:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
    5cb3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
    5cbb:	e8 00 c8 ff ff       	call   24c0 <bind@plt>
    5cc0:	85 c0                	test   %eax,%eax
    5cc2:	0f 88 92 c9 ff ff    	js     265a <io_thread.cold+0x44>
    5cc8:	be 0a 00 00 00       	mov    $0xa,%esi
    5ccd:	44 89 e7             	mov    %r12d,%edi
    5cd0:	e8 ab c7 ff ff       	call   2480 <listen@plt>
    5cd5:	85 c0                	test   %eax,%eax
    5cd7:	0f 88 51 c9 ff ff    	js     262e <io_thread.cold+0x18>
    5cdd:	ba db 18 00 00       	mov    $0x18db,%edx
    5ce2:	48 8d 35 ba 24 00 00 	lea    0x24ba(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5ce9:	bf 01 00 00 00       	mov    $0x1,%edi
    5cee:	31 c0                	xor    %eax,%eax
    5cf0:	e8 bb c7 ff ff       	call   24b0 <__printf_chk@plt>
    5cf5:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5cfa:	48 89 d9             	mov    %rbx,%rcx
    5cfd:	44 89 e7             	mov    %r12d,%edi
    5d00:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5d05:	48 89 c6             	mov    %rax,%rsi
    5d08:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5d0d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    5d12:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
    5d1a:	e8 81 fd ff ff       	call   5aa0 <add_accept_request>
    5d1f:	bf 01 00 00 00       	mov    $0x1,%edi
    5d24:	be 10 00 00 00       	mov    $0x10,%esi
    5d29:	e8 d2 c6 ff ff       	call   2400 <calloc@plt>
    5d2e:	bf 0a 00 00 00       	mov    $0xa,%edi
    5d33:	49 89 c5             	mov    %rax,%r13
    5d36:	e8 35 c7 ff ff       	call   2470 <malloc@plt>
    5d3b:	48 85 c0             	test   %rax,%rax
    5d3e:	0f 84 ae 04 00 00    	je     61f2 <io_thread+0x6b2>
    5d44:	49 89 45 00          	mov    %rax,0x0(%r13)
    5d48:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5d4f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5d56:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
    5d5e:	8d 50 01             	lea    0x1(%rax),%edx
    5d61:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5d66:	8b 30                	mov    (%rax),%esi
    5d68:	f6 c1 02             	test   $0x2,%cl
    5d6b:	0f 85 0f 04 00 00    	jne    6180 <io_thread+0x640>
    5d71:	89 d0                	mov    %edx,%eax
    5d73:	29 f0                	sub    %esi,%eax
    5d75:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5d7c:	0f 82 c2 c8 ff ff    	jb     2644 <io_thread.cold+0x2e>
    5d82:	c1 e9 0a             	shr    $0xa,%ecx
    5d85:	48 8d 75 60          	lea    0x60(%rbp),%rsi
    5d89:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5d8d:	48 89 df             	mov    %rbx,%rdi
    5d90:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5d97:	83 e1 01             	and    $0x1,%ecx
    5d9a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5da1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5da8:	d3 e0                	shl    %cl,%eax
    5daa:	8b 55 60             	mov    0x60(%rbp),%edx
    5dad:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5db2:	48 c1 e0 06          	shl    $0x6,%rax
    5db6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5dbe:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5dc4:	89 50 04             	mov    %edx,0x4(%rax)
    5dc7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5dcf:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5dd3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5ddb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5de3:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5de7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5deb:	e8 a0 c5 ff ff       	call   2390 <io_uring_submit@plt>
    5df0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5df4:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5df9:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5e01:	0f 85 d7 01 00 00    	jne    5fde <io_thread+0x49e>
    5e07:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5e0c:	4d 89 ce             	mov    %r9,%r14
    5e0f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5e14:	0f 1f 40 00          	nopl   0x0(%rax)
    5e18:	48 8d 3d 9a 23 00 00 	lea    0x239a(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5e1f:	e8 0c c5 ff ff       	call   2330 <puts@plt>
    5e24:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5e2b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
    5e32:	c1 e9 0b             	shr    $0xb,%ecx
    5e35:	83 e1 01             	and    $0x1,%ecx
    5e38:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5e40:	8b 00                	mov    (%rax),%eax
    5e42:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5e4a:	8b 16                	mov    (%rsi),%edx
    5e4c:	39 d0                	cmp    %edx,%eax
    5e4e:	74 36                	je     5e86 <io_thread+0x346>
    5e50:	89 f8                	mov    %edi,%eax
    5e52:	21 d0                	and    %edx,%eax
    5e54:	d3 e0                	shl    %cl,%eax
    5e56:	48 c1 e0 04          	shl    $0x4,%rax
    5e5a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
    5e62:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5e6a:	0f 85 a8 01 00 00    	jne    6018 <io_thread+0x4d8>
    5e70:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5e74:	0f 85 0e 03 00 00    	jne    6188 <io_thread+0x648>
    5e7a:	8b 40 08             	mov    0x8(%rax),%eax
    5e7d:	83 c2 01             	add    $0x1,%edx
    5e80:	89 16                	mov    %edx,(%rsi)
    5e82:	85 c0                	test   %eax,%eax
    5e84:	79 b2                	jns    5e38 <io_thread+0x2f8>
    5e86:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
    5e8f:	90                   	nop
    5e90:	45 31 c0             	xor    %r8d,%r8d
    5e93:	31 d2                	xor    %edx,%edx
    5e95:	b9 01 00 00 00       	mov    $0x1,%ecx
    5e9a:	4c 89 f6             	mov    %r14,%rsi
    5e9d:	48 89 df             	mov    %rbx,%rdi
    5ea0:	e8 fb c5 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    5ea5:	41 89 c7             	mov    %eax,%r15d
    5ea8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5ead:	48 83 38 01          	cmpq   $0x1,(%rax)
    5eb1:	0f 84 e1 02 00 00    	je     6198 <io_thread+0x658>
    5eb7:	48 8d 3d 21 23 00 00 	lea    0x2321(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5ebe:	e8 6d c4 ff ff       	call   2330 <puts@plt>
    5ec3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5ec8:	4c 8b 22             	mov    (%rdx),%r12
    5ecb:	45 85 ff             	test   %r15d,%r15d
    5ece:	0f 88 42 c7 ff ff    	js     2616 <io_thread.cold>
    5ed4:	8b 42 08             	mov    0x8(%rdx),%eax
    5ed7:	45 8b 04 24          	mov    (%r12),%r8d
    5edb:	85 c0                	test   %eax,%eax
    5edd:	0f 88 d5 02 00 00    	js     61b8 <io_thread+0x678>
    5ee3:	41 83 f8 01          	cmp    $0x1,%r8d
    5ee7:	0f 84 7b 01 00 00    	je     6068 <io_thread+0x528>
    5eed:	41 83 f8 02          	cmp    $0x2,%r8d
    5ef1:	0f 84 a1 01 00 00    	je     6098 <io_thread+0x558>
    5ef7:	45 85 c0             	test   %r8d,%r8d
    5efa:	0f 85 50 01 00 00    	jne    6050 <io_thread+0x510>
    5f00:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5f05:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5f0a:	48 89 d9             	mov    %rbx,%rcx
    5f0d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5f11:	e8 8a fb ff ff       	call   5aa0 <add_accept_request>
    5f16:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f1b:	48 89 de             	mov    %rbx,%rsi
    5f1e:	8b 78 08             	mov    0x8(%rax),%edi
    5f21:	e8 1a f5 ff ff       	call   5440 <add_read_request>
    5f26:	4c 89 e7             	mov    %r12,%rdi
    5f29:	e8 d2 c3 ff ff       	call   2300 <free@plt>
    5f2e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5f33:	48 85 c0             	test   %rax,%rax
    5f36:	0f 85 14 01 00 00    	jne    6050 <io_thread+0x510>
    5f3c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5f43:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
    5f4a:	8d 50 01             	lea    0x1(%rax),%edx
    5f4d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5f52:	8b 30                	mov    (%rax),%esi
    5f54:	f6 c1 02             	test   $0x2,%cl
    5f57:	74 00                	je     5f59 <io_thread+0x419>
    5f59:	89 d0                	mov    %edx,%eax
    5f5b:	29 f0                	sub    %esi,%eax
    5f5d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5f64:	0f 82 d0 c6 ff ff    	jb     263a <io_thread.cold+0x24>
    5f6a:	c1 e9 0a             	shr    $0xa,%ecx
    5f6d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5f72:	66 0f ef c0          	pxor   %xmm0,%xmm0
    5f76:	48 89 df             	mov    %rbx,%rdi
    5f79:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
    5f80:	83 e1 01             	and    $0x1,%ecx
    5f83:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
    5f8a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
    5f91:	d3 e0                	shl    %cl,%eax
    5f93:	8b 55 60             	mov    0x60(%rbp),%edx
    5f96:	48 c1 e0 06          	shl    $0x6,%rax
    5f9a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
    5fa2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
    5fa8:	89 50 04             	mov    %edx,0x4(%rax)
    5fab:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5fb3:	4c 89 68 10          	mov    %r13,0x10(%rax)
    5fb7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
    5fbf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    5fc7:	48 89 70 20          	mov    %rsi,0x20(%rax)
    5fcb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    5fcf:	e8 bc c3 ff ff       	call   2390 <io_uring_submit@plt>
    5fd4:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5fd8:	0f 84 3a fe ff ff    	je     5e18 <io_thread+0x2d8>
    5fde:	48 8d 3d 33 22 00 00 	lea    0x2233(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5fe5:	e8 46 c3 ff ff       	call   2330 <puts@plt>
    5fea:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5ff2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5ffb:	0f 85 18 02 00 00    	jne    6219 <io_thread+0x6d9>
    6001:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    6008:	31 c0                	xor    %eax,%eax
    600a:	5b                   	pop    %rbx
    600b:	5d                   	pop    %rbp
    600c:	41 5c                	pop    %r12
    600e:	41 5d                	pop    %r13
    6010:	41 5e                	pop    %r14
    6012:	41 5f                	pop    %r15
    6014:	c3                   	ret
    6015:	0f 1f 00             	nopl   (%rax)
    6018:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    601d:	48 85 c0             	test   %rax,%rax
    6020:	0f 84 6a fe ff ff    	je     5e90 <io_thread+0x350>
    6026:	48 83 38 01          	cmpq   $0x1,(%rax)
    602a:	0f 84 68 01 00 00    	je     6198 <io_thread+0x658>
    6030:	48 8d 3d a8 21 00 00 	lea    0x21a8(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    6037:	e8 f4 c2 ff ff       	call   2330 <puts@plt>
    603c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    6041:	4c 8b 22             	mov    (%rdx),%r12
    6044:	e9 8b fe ff ff       	jmp    5ed4 <io_thread+0x394>
    6049:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6050:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    6058:	8b 02                	mov    (%rdx),%eax
    605a:	83 c0 01             	add    $0x1,%eax
    605d:	89 02                	mov    %eax,(%rdx)
    605f:	e9 d8 fe ff ff       	jmp    5f3c <io_thread+0x3fc>
    6064:	0f 1f 40 00          	nopl   0x0(%rax)
    6068:	85 c0                	test   %eax,%eax
    606a:	75 74                	jne    60e0 <io_thread+0x5a0>
    606c:	48 8b 0d ad 4f 00 00 	mov    0x4fad(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6073:	ba 0f 00 00 00       	mov    $0xf,%edx
    6078:	be 01 00 00 00       	mov    $0x1,%esi
    607d:	48 8d 3d 84 21 00 00 	lea    0x2184(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    6084:	e8 a7 c4 ff ff       	call   2530 <fwrite@plt>
    6089:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    608e:	e9 a0 fe ff ff       	jmp    5f33 <io_thread+0x3f3>
    6093:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6098:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    609d:	45 31 ff             	xor    %r15d,%r15d
    60a0:	85 c0                	test   %eax,%eax
    60a2:	7e 20                	jle    60c4 <io_thread+0x584>
    60a4:	0f 1f 40 00          	nopl   0x0(%rax)
    60a8:	4c 89 f8             	mov    %r15,%rax
    60ab:	49 83 c7 01          	add    $0x1,%r15
    60af:	48 c1 e0 04          	shl    $0x4,%rax
    60b3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    60b8:	e8 43 c2 ff ff       	call   2300 <free@plt>
    60bd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    60c2:	7f e4                	jg     60a8 <io_thread+0x568>
    60c4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    60c9:	e8 02 c3 ff ff       	call   23d0 <close@plt>
    60ce:	4c 89 e7             	mov    %r12,%rdi
    60d1:	e8 2a c2 ff ff       	call   2300 <free@plt>
    60d6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    60db:	e9 53 fe ff ff       	jmp    5f33 <io_thread+0x3f3>
    60e0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    60e5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    60ea:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    60f2:	eb 11                	jmp    6105 <io_thread+0x5c5>
    60f4:	0f 1f 40 00          	nopl   0x0(%rax)
    60f8:	48 83 c0 01          	add    $0x1,%rax
    60fc:	48 83 c2 01          	add    $0x1,%rdx
    6100:	48 39 c6             	cmp    %rax,%rsi
    6103:	74 4b                	je     6150 <io_thread+0x610>
    6105:	0f b6 0a             	movzbl (%rdx),%ecx
    6108:	88 08                	mov    %cl,(%rax)
    610a:	80 f9 0d             	cmp    $0xd,%cl
    610d:	75 e9                	jne    60f8 <io_thread+0x5b8>
    610f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    6113:	75 e3                	jne    60f8 <io_thread+0x5b8>
    6115:	c6 00 00             	movb   $0x0,(%rax)
    6118:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    611d:	48 89 da             	mov    %rbx,%rdx
    6120:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    6125:	e8 96 f7 ff ff       	call   58c0 <handle_http_method>
    612a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    612f:	e8 cc c1 ff ff       	call   2300 <free@plt>
    6134:	4c 89 e7             	mov    %r12,%rdi
    6137:	e8 c4 c1 ff ff       	call   2300 <free@plt>
    613c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    6141:	e9 ed fd ff ff       	jmp    5f33 <io_thread+0x3f3>
    6146:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6150:	48 8b 0d c9 4e 00 00 	mov    0x4ec9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6157:	ba 12 00 00 00       	mov    $0x12,%edx
    615c:	be 01 00 00 00       	mov    $0x1,%esi
    6161:	48 8d 3d f6 1f 00 00 	lea    0x1ff6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    6168:	e8 c3 c3 ff ff       	call   2530 <fwrite@plt>
    616d:	bf 01 00 00 00       	mov    $0x1,%edi
    6172:	e8 99 c3 ff ff       	call   2510 <exit@plt>
    6177:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6180:	e9 ec fb ff ff       	jmp    5d71 <io_thread+0x231>
    6185:	0f 1f 00             	nopl   (%rax)
    6188:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    618d:	e9 94 fe ff ff       	jmp    6026 <io_thread+0x4e6>
    6192:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6198:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    61a0:	48 8d 3d 24 20 00 00 	lea    0x2024(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    61a7:	8b 02                	mov    (%rdx),%eax
    61a9:	83 c0 01             	add    $0x1,%eax
    61ac:	89 02                	mov    %eax,(%rdx)
    61ae:	e8 7d c1 ff ff       	call   2330 <puts@plt>
    61b3:	e9 26 fe ff ff       	jmp    5fde <io_thread+0x49e>
    61b8:	f7 d8                	neg    %eax
    61ba:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    61bf:	89 c7                	mov    %eax,%edi
    61c1:	e8 aa c3 ff ff       	call   2570 <strerror@plt>
    61c6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    61cb:	be 01 00 00 00       	mov    $0x1,%esi
    61d0:	48 8b 3d 49 4e 00 00 	mov    0x4e49(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    61d7:	48 89 c1             	mov    %rax,%rcx
    61da:	48 8d 15 27 24 00 00 	lea    0x2427(%rip),%rdx        # 8608 <_IO_stdin_used+0x608>
    61e1:	31 c0                	xor    %eax,%eax
    61e3:	e8 58 c3 ff ff       	call   2540 <__fprintf_chk@plt>
    61e8:	bf 01 00 00 00       	mov    $0x1,%edi
    61ed:	e8 1e c3 ff ff       	call   2510 <exit@plt>
    61f2:	48 8b 0d 27 4e 00 00 	mov    0x4e27(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    61f9:	ba 28 00 00 00       	mov    $0x28,%edx
    61fe:	be 01 00 00 00       	mov    $0x1,%esi
    6203:	48 8d 3d ce 23 00 00 	lea    0x23ce(%rip),%rdi        # 85d8 <_IO_stdin_used+0x5d8>
    620a:	e8 21 c3 ff ff       	call   2530 <fwrite@plt>
    620f:	bf 01 00 00 00       	mov    $0x1,%edi
    6214:	e8 f7 c2 ff ff       	call   2510 <exit@plt>
    6219:	e8 62 c1 ff ff       	call   2380 <__stack_chk_fail@plt>
    621e:	66 90                	xchg   %ax,%ax

0000000000006220 <barriered_work_ingest>:
    6220:	f3 0f 1e fa          	endbr64
    6224:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    622b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    6231:	85 c9                	test   %ecx,%ecx
    6233:	0f 8e ea 00 00 00    	jle    6323 <barriered_work_ingest+0x103>
    6239:	41 56                	push   %r14
    623b:	41 55                	push   %r13
    623d:	45 31 ed             	xor    %r13d,%r13d
    6240:	41 54                	push   %r12
    6242:	49 89 fc             	mov    %rdi,%r12
    6245:	55                   	push   %rbp
    6246:	53                   	push   %rbx
    6247:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    624b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6250:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    6254:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    625c:	31 db                	xor    %ebx,%ebx
    625e:	8b 10                	mov    (%rax),%edx
    6260:	85 d2                	test   %edx,%edx
    6262:	7e 26                	jle    628a <barriered_work_ingest+0x6a>
    6264:	48 8b 48 08          	mov    0x8(%rax),%rcx
    6268:	48 89 dd             	mov    %rbx,%rbp
    626b:	48 c1 e5 08          	shl    $0x8,%rbp
    626f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    6273:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    627a:	74 24                	je     62a0 <barriered_work_ingest+0x80>
    627c:	48 83 c3 01          	add    $0x1,%rbx
    6280:	39 da                	cmp    %ebx,%edx
    6282:	7f e4                	jg     6268 <barriered_work_ingest+0x48>
    6284:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    628a:	49 83 c5 01          	add    $0x1,%r13
    628e:	44 39 e9             	cmp    %r13d,%ecx
    6291:	7f bd                	jg     6250 <barriered_work_ingest+0x30>
    6293:	5b                   	pop    %rbx
    6294:	31 c0                	xor    %eax,%eax
    6296:	5d                   	pop    %rbp
    6297:	41 5c                	pop    %r12
    6299:	41 5d                	pop    %r13
    629b:	41 5e                	pop    %r14
    629d:	c3                   	ret
    629e:	66 90                	xchg   %ax,%ax
    62a0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
    62a9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    62b0:	bf 04 00 00 00       	mov    $0x4,%edi
    62b5:	48 c1 e6 05          	shl    $0x5,%rsi
    62b9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    62c0:	48 83 c6 10          	add    $0x10,%rsi
    62c4:	e8 87 c0 ff ff       	call   2350 <clock_gettime@plt>
    62c9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    62d1:	48 8b 40 50          	mov    0x50(%rax),%rax
    62d5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    62d9:	48 03 68 08          	add    0x8(%rax),%rbp
    62dd:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
    62e7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    62ed:	83 c0 01             	add    $0x1,%eax
    62f0:	99                   	cltd
    62f1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    62f7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
    62fd:	0f ae f8             	sfence
    6300:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    6308:	48 83 c3 01          	add    $0x1,%rbx
    630c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6310:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    6314:	8b 10                	mov    (%rax),%edx
    6316:	39 da                	cmp    %ebx,%edx
    6318:	0f 8f 46 ff ff ff    	jg     6264 <barriered_work_ingest+0x44>
    631e:	e9 61 ff ff ff       	jmp    6284 <barriered_work_ingest+0x64>
    6323:	31 c0                	xor    %eax,%eax
    6325:	c3                   	ret
    6326:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006330 <barriered_thread>:
    6330:	f3 0f 1e fa          	endbr64
    6334:	41 56                	push   %r14
    6336:	41 55                	push   %r13
    6338:	41 54                	push   %r12
    633a:	45 31 e4             	xor    %r12d,%r12d
    633d:	55                   	push   %rbp
    633e:	31 ed                	xor    %ebp,%ebp
    6340:	53                   	push   %rbx
    6341:	48 89 fb             	mov    %rdi,%rbx
    6344:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6348:	0f 85 74 02 00 00    	jne    65c2 <barriered_thread+0x292>
    634e:	8b 43 40             	mov    0x40(%rbx),%eax
    6351:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6358:	41 39 c4             	cmp    %eax,%r12d
    635b:	0f 8d 6f 01 00 00    	jge    64d0 <barriered_thread+0x1a0>
    6361:	49 63 fc             	movslq %r12d,%rdi
    6364:	48 c1 e7 09          	shl    $0x9,%rdi
    6368:	49 89 fd             	mov    %rdi,%r13
    636b:	eb 32                	jmp    639f <barriered_thread+0x6f>
    636d:	0f 1f 00             	nopl   (%rax)
    6370:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6374:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6378:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    637c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6380:	4c 01 ef             	add    %r13,%rdi
    6383:	e8 98 fe ff ff       	call   6220 <barriered_work_ingest>
    6388:	8b 43 40             	mov    0x40(%rbx),%eax
    638b:	41 83 c4 01          	add    $0x1,%r12d
    638f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    6396:	44 39 e0             	cmp    %r12d,%eax
    6399:	0f 8e 19 02 00 00    	jle    65b8 <barriered_thread+0x288>
    639f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    63a3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    63a7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    63ae:	75 c0                	jne    6370 <barriered_thread+0x40>
    63b0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
    63b4:	83 e8 01             	sub    $0x1,%eax
    63b7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    63bc:	45 85 e4             	test   %r12d,%r12d
    63bf:	0f 4f c1             	cmovg  %ecx,%eax
    63c2:	45 85 c0             	test   %r8d,%r8d
    63c5:	0f 8e 2d 01 00 00    	jle    64f8 <barriered_thread+0x1c8>
    63cb:	48 63 c8             	movslq %eax,%rcx
    63ce:	48 8b 43 18          	mov    0x18(%rbx),%rax
    63d2:	49 63 d0             	movslq %r8d,%rdx
    63d5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
    63db:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    63e2:	48 c1 e1 09          	shl    $0x9,%rcx
    63e6:	45 31 d2             	xor    %r10d,%r10d
    63e9:	45 31 f6             	xor    %r14d,%r14d
    63ec:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    63f0:	48 8b 10             	mov    (%rax),%rdx
    63f3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    63f7:	49 01 cb             	add    %rcx,%r11
    63fa:	4c 89 da             	mov    %r11,%rdx
    63fd:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6404:	75 04                	jne    640a <barriered_thread+0xda>
    6406:	41 83 c6 01          	add    $0x1,%r14d
    640a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6410:	75 04                	jne    6416 <barriered_thread+0xe6>
    6412:	41 83 c2 01          	add    $0x1,%r10d
    6416:	48 83 c0 08          	add    $0x8,%rax
    641a:	48 39 c6             	cmp    %rax,%rsi
    641d:	75 d1                	jne    63f0 <barriered_thread+0xc0>
    641f:	45 85 d2             	test   %r10d,%r10d
    6422:	0f 84 c0 00 00 00    	je     64e8 <barriered_thread+0x1b8>
    6428:	45 39 d0             	cmp    %r10d,%r8d
    642b:	0f 84 b7 00 00 00    	je     64e8 <barriered_thread+0x1b8>
    6431:	45 85 f6             	test   %r14d,%r14d
    6434:	74 0a                	je     6440 <barriered_thread+0x110>
    6436:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    643a:	0f 85 ae 01 00 00    	jne    65ee <barriered_thread+0x2be>
    6440:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6444:	4c 01 ea             	add    %r13,%rdx
    6447:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
    644e:	45 85 e4             	test   %r12d,%r12d
    6451:	75 14                	jne    6467 <barriered_thread+0x137>
    6453:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    645a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6461:	0f 8c 69 01 00 00    	jl     65d0 <barriered_thread+0x2a0>
    6467:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    646b:	48 8b 43 18          	mov    0x18(%rbx),%rax
    646f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
    6479:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    647d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6481:	4c 01 ef             	add    %r13,%rdi
    6484:	ff 92 18 01 00 00    	call   *0x118(%rdx)
    648a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    648e:	4c 01 e8             	add    %r13,%rax
    6491:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
    6498:	8b 43 40             	mov    0x40(%rbx),%eax
    649b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
    64a0:	83 e8 01             	sub    $0x1,%eax
    64a3:	44 39 e0             	cmp    %r12d,%eax
    64a6:	0f 84 a4 00 00 00    	je     6550 <barriered_thread+0x220>
    64ac:	0f ae f8             	sfence
    64af:	85 ed                	test   %ebp,%ebp
    64b1:	0f 84 d1 00 00 00    	je     6588 <barriered_thread+0x258>
    64b7:	bd 01 00 00 00       	mov    $0x1,%ebp
    64bc:	e9 c7 fe ff ff       	jmp    6388 <barriered_thread+0x58>
    64c1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    64c5:	0f 85 f7 00 00 00    	jne    65c2 <barriered_thread+0x292>
    64cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    64d0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    64d8:	85 c0                	test   %eax,%eax
    64da:	7e e5                	jle    64c1 <barriered_thread+0x191>
    64dc:	45 31 e4             	xor    %r12d,%r12d
    64df:	e9 7d fe ff ff       	jmp    6361 <barriered_thread+0x31>
    64e4:	0f 1f 40 00          	nopl   0x0(%rax)
    64e8:	83 fd 01             	cmp    $0x1,%ebp
    64eb:	74 1b                	je     6508 <barriered_thread+0x1d8>
    64ed:	31 ed                	xor    %ebp,%ebp
    64ef:	e9 3d ff ff ff       	jmp    6431 <barriered_thread+0x101>
    64f4:	0f 1f 40 00          	nopl   0x0(%rax)
    64f8:	83 fd 01             	cmp    $0x1,%ebp
    64fb:	0f 85 43 ff ff ff    	jne    6444 <barriered_thread+0x114>
    6501:	45 31 f6             	xor    %r14d,%r14d
    6504:	0f 1f 40 00          	nopl   0x0(%rax)
    6508:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    650f:	bf 04 00 00 00       	mov    $0x4,%edi
    6514:	31 ed                	xor    %ebp,%ebp
    6516:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    651a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6521:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6526:	e8 25 be ff ff       	call   2350 <clock_gettime@plt>
    652b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6532:	48 83 c0 01          	add    $0x1,%rax
    6536:	48 99                	cqto
    6538:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    653f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
    6546:	e9 e6 fe ff ff       	jmp    6431 <barriered_thread+0x101>
    654b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6550:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6557:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    655e:	0f 8d 48 ff ff ff    	jge    64ac <barriered_thread+0x17c>
    6564:	48 c1 e6 04          	shl    $0x4,%rsi
    6568:	bf 04 00 00 00       	mov    $0x4,%edi
    656d:	48 03 73 70          	add    0x70(%rbx),%rsi
    6571:	e8 da bd ff ff       	call   2350 <clock_gettime@plt>
    6576:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    657e:	e9 29 ff ff ff       	jmp    64ac <barriered_thread+0x17c>
    6583:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6588:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    658f:	bf 04 00 00 00       	mov    $0x4,%edi
    6594:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6598:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    659f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    65a3:	44 89 66 20          	mov    %r12d,0x20(%rsi)
    65a7:	e8 a4 bd ff ff       	call   2350 <clock_gettime@plt>
    65ac:	e9 06 ff ff ff       	jmp    64b7 <barriered_thread+0x187>
    65b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    65b8:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    65bc:	0f 84 96 fd ff ff    	je     6358 <barriered_thread+0x28>
    65c2:	5b                   	pop    %rbx
    65c3:	31 c0                	xor    %eax,%eax
    65c5:	5d                   	pop    %rbp
    65c6:	41 5c                	pop    %r12
    65c8:	41 5d                	pop    %r13
    65ca:	41 5e                	pop    %r14
    65cc:	c3                   	ret
    65cd:	0f 1f 00             	nopl   (%rax)
    65d0:	48 c1 e6 04          	shl    $0x4,%rsi
    65d4:	bf 04 00 00 00       	mov    $0x4,%edi
    65d9:	48 03 73 68          	add    0x68(%rbx),%rsi
    65dd:	e8 6e bd ff ff       	call   2350 <clock_gettime@plt>
    65e2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    65e6:	4c 01 ea             	add    %r13,%rdx
    65e9:	e9 79 fe ff ff       	jmp    6467 <barriered_thread+0x137>
    65ee:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    65f2:	48 8b 43 18          	mov    0x18(%rbx),%rax
    65f6:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    65fa:	48 8b 78 38          	mov    0x38(%rax),%rdi
    65fe:	4c 01 ef             	add    %r13,%rdi
    6601:	e8 1a fc ff ff       	call   6220 <barriered_work_ingest>
    6606:	e9 39 fd ff ff       	jmp    6344 <barriered_thread+0x14>
    660b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006610 <receive>:
    6610:	f3 0f 1e fa          	endbr64
    6614:	41 56                	push   %r14
    6616:	41 55                	push   %r13
    6618:	41 54                	push   %r12
    661a:	55                   	push   %rbp
    661b:	53                   	push   %rbx
    661c:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    6623:	45 85 e4             	test   %r12d,%r12d
    6626:	0f 8e 27 01 00 00    	jle    6753 <receive+0x143>
    662c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    6633:	48 89 fe             	mov    %rdi,%rsi
    6636:	31 db                	xor    %ebx,%ebx
    6638:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    663c:	49 89 ed             	mov    %rbp,%r13
    663f:	90                   	nop
    6640:	41 39 dd             	cmp    %ebx,%r13d
    6643:	0f 84 fd 00 00 00    	je     6746 <receive+0x136>
    6649:	48 89 d8             	mov    %rbx,%rax
    664c:	48 c1 e0 08          	shl    $0x8,%rax
    6650:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    6657:	48 8b 10             	mov    (%rax),%rdx
    665a:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    6660:	83 f8 01             	cmp    $0x1,%eax
    6663:	74 11                	je     6676 <receive+0x66>
    6665:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    666c:	75 08                	jne    6676 <receive+0x66>
    666e:	85 c0                	test   %eax,%eax
    6670:	0f 84 d0 00 00 00    	je     6746 <receive+0x136>
    6676:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    667d:	48 85 ff             	test   %rdi,%rdi
    6680:	0f 8e a2 00 00 00    	jle    6728 <receive+0x118>
    6686:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    668d:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    6694:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
    6698:	4c 8b 1a             	mov    (%rdx),%r11
    669b:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    669f:	49 01 f9             	add    %rdi,%r9
    66a2:	49 01 f8             	add    %rdi,%r8
    66a5:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    66ac:	eb 08                	jmp    66b6 <receive+0xa6>
    66ae:	66 90                	xchg   %ax,%ax
    66b0:	48 83 e8 01          	sub    $0x1,%rax
    66b4:	72 72                	jb     6728 <receive+0x118>
    66b6:	4c 89 c9             	mov    %r9,%rcx
    66b9:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
    66c0:	48 29 c1             	sub    %rax,%rcx
    66c3:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
    66ca:	4c 89 c1             	mov    %r8,%rcx
    66cd:	48 29 c1             	sub    %rax,%rcx
    66d0:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
    66d7:	48 89 f9             	mov    %rdi,%rcx
    66da:	48 29 c1             	sub    %rax,%rcx
    66dd:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
    66e4:	48 63 c8             	movslq %eax,%rcx
    66e7:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
    66eb:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    66ef:	75 bf                	jne    66b0 <receive+0xa0>
    66f1:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    66f5:	75 b9                	jne    66b0 <receive+0xa0>
    66f7:	49 63 46 04          	movslq 0x4(%r14),%rax
    66fb:	31 c9                	xor    %ecx,%ecx
    66fd:	bf 01 00 00 00       	mov    $0x1,%edi
    6702:	ba 01 00 00 00       	mov    $0x1,%edx
    6707:	48 8d 35 22 1f 00 00 	lea    0x1f22(%rip),%rsi        # 8630 <_IO_stdin_used+0x630>
    670e:	48 39 e8             	cmp    %rbp,%rax
    6711:	0f 94 c1             	sete   %cl
    6714:	31 c0                	xor    %eax,%eax
    6716:	e8 95 bd ff ff       	call   24b0 <__printf_chk@plt>
    671b:	bf 01 00 00 00       	mov    $0x1,%edi
    6720:	e8 eb bd ff ff       	call   2510 <exit@plt>
    6725:	0f 1f 00             	nopl   (%rax)
    6728:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
    6732:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
    673c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
    6746:	48 83 c3 01          	add    $0x1,%rbx
    674a:	49 39 dc             	cmp    %rbx,%r12
    674d:	0f 85 ed fe ff ff    	jne    6640 <receive+0x30>
    6753:	0f ae f8             	sfence
    6756:	31 c0                	xor    %eax,%eax
    6758:	5b                   	pop    %rbx
    6759:	5d                   	pop    %rbp
    675a:	41 5c                	pop    %r12
    675c:	41 5d                	pop    %r13
    675e:	41 5e                	pop    %r14
    6760:	c3                   	ret
    6761:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    676c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006770 <sendm>:
    6770:	f3 0f 1e fa          	endbr64
    6774:	41 57                	push   %r15
    6776:	41 56                	push   %r14
    6778:	41 55                	push   %r13
    677a:	41 54                	push   %r12
    677c:	55                   	push   %rbp
    677d:	53                   	push   %rbx
    677e:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    6784:	85 c0                	test   %eax,%eax
    6786:	0f 8e a1 00 00 00    	jle    682d <sendm+0xbd>
    678c:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    6793:	48 89 fe             	mov    %rdi,%rsi
    6796:	4c 63 e8             	movslq %eax,%r13
    6799:	31 d2                	xor    %edx,%edx
    679b:	45 8b 67 08          	mov    0x8(%r15),%r12d
    679f:	90                   	nop
    67a0:	41 39 d4             	cmp    %edx,%r12d
    67a3:	74 7b                	je     6820 <sendm+0xb0>
    67a5:	48 89 d0             	mov    %rdx,%rax
    67a8:	48 c1 e0 08          	shl    $0x8,%rax
    67ac:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    67b3:	48 8b 98 b8 00 00 00 	mov    0xb8(%rax),%rbx
    67ba:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
    67c1:	48 8d 7b 01          	lea    0x1(%rbx),%rdi
    67c5:	48 89 b8 b8 00 00 00 	mov    %rdi,0xb8(%rax)
    67cc:	48 85 ff             	test   %rdi,%rdi
    67cf:	7e 4f                	jle    6820 <sendm+0xb0>
    67d1:	48 8b b9 80 00 00 00 	mov    0x80(%rcx),%rdi
    67d8:	48 85 ff             	test   %rdi,%rdi
    67db:	7f 43                	jg     6820 <sendm+0xb0>
    67dd:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    67e4:	41 83 f8 01          	cmp    $0x1,%r8d
    67e8:	74 0e                	je     67f8 <sendm+0x88>
    67ea:	83 b9 08 04 00 00 02 	cmpl   $0x2,0x408(%rcx)
    67f1:	75 05                	jne    67f8 <sendm+0x88>
    67f3:	45 85 c0             	test   %r8d,%r8d
    67f6:	74 28                	je     6820 <sendm+0xb0>
    67f8:	83 be 88 01 00 00 01 	cmpl   $0x1,0x188(%rsi)
    67ff:	74 3f                	je     6840 <sendm+0xd0>
    6801:	83 b8 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax)
    6808:	75 16                	jne    6820 <sendm+0xb0>
    680a:	48 c7 80 b8 00 00 00 00 00 00 00 	movq   $0x0,0xb8(%rax)
    6815:	41 c7 87 f8 00 00 00 01 00 00 00 	movl   $0x1,0xf8(%r15)
    6820:	48 83 c2 01          	add    $0x1,%rdx
    6824:	49 39 d5             	cmp    %rdx,%r13
    6827:	0f 85 73 ff ff ff    	jne    67a0 <sendm+0x30>
    682d:	0f ae f8             	sfence
    6830:	31 c0                	xor    %eax,%eax
    6832:	5b                   	pop    %rbx
    6833:	5d                   	pop    %rbp
    6834:	41 5c                	pop    %r12
    6836:	41 5d                	pop    %r13
    6838:	41 5e                	pop    %r14
    683a:	41 5f                	pop    %r15
    683c:	c3                   	ret
    683d:	0f 1f 00             	nopl   (%rax)
    6840:	48 63 99 88 00 00 00 	movslq 0x88(%rcx),%rbx
    6847:	48 39 df             	cmp    %rbx,%rdi
    684a:	0f 8d ba 00 00 00    	jge    690a <sendm+0x19a>
    6850:	4c 8b b6 08 01 00 00 	mov    0x108(%rsi),%r14
    6857:	49 89 db             	mov    %rbx,%r11
    685a:	4c 8b 11             	mov    (%rcx),%r10
    685d:	49 29 fb             	sub    %rdi,%r11
    6860:	4c 89 74 24 e8       	mov    %r14,-0x18(%rsp)
    6865:	4c 8b b1 80 03 00 00 	mov    0x380(%rcx),%r14
    686c:	4d 8d 43 ff          	lea    -0x1(%r11),%r8
    6870:	4c 89 74 24 f0       	mov    %r14,-0x10(%rsp)
    6875:	49 83 f8 02          	cmp    $0x2,%r8
    6879:	0f 86 21 01 00 00    	jbe    69a0 <sendm+0x230>
    687f:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    6887:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    688f:	4f 8d 34 02          	lea    (%r10,%r8,1),%r14
    6893:	4b 8d 2c 0a          	lea    (%r10,%r9,1),%rbp
    6897:	4c 89 74 24 e0       	mov    %r14,-0x20(%rsp)
    689c:	4c 8d b6 90 01 00 00 	lea    0x190(%rsi),%r14
    68a3:	49 39 ee             	cmp    %rbp,%r14
    68a6:	0f 83 84 00 00 00    	jae    6930 <sendm+0x1c0>
    68ac:	48 8d ae 98 01 00 00 	lea    0x198(%rsi),%rbp
    68b3:	48 39 6c 24 e0       	cmp    %rbp,-0x20(%rsp)
    68b8:	73 76                	jae    6930 <sendm+0x1c0>
    68ba:	4d 01 d0             	add    %r10,%r8
    68bd:	4b 8d 3c 0a          	lea    (%r10,%r9,1),%rdi
    68c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    68c8:	4c 8b 8e 90 01 00 00 	mov    0x190(%rsi),%r9
    68cf:	49 83 c0 08          	add    $0x8,%r8
    68d3:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
    68d7:	4c 39 c7             	cmp    %r8,%rdi
    68da:	75 ec                	jne    68c8 <sendm+0x158>
    68dc:	0f 1f 40 00          	nopl   0x0(%rax)
    68e0:	48 8b 7c 24 e8       	mov    -0x18(%rsp),%rdi
    68e5:	4c 01 df             	add    %r11,%rdi
    68e8:	48 89 be 08 01 00 00 	mov    %rdi,0x108(%rsi)
    68ef:	48 8b 7c 24 f0       	mov    -0x10(%rsp),%rdi
    68f4:	48 89 99 80 00 00 00 	mov    %rbx,0x80(%rcx)
    68fb:	4c 01 df             	add    %r11,%rdi
    68fe:	48 89 b9 80 03 00 00 	mov    %rdi,0x380(%rcx)
    6905:	4d 89 4c da f8       	mov    %r9,-0x8(%r10,%rbx,8)
    690a:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
    6914:	c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rcx)
    691e:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    6928:	e9 d4 fe ff ff       	jmp    6801 <sendm+0x91>
    692d:	0f 1f 00             	nopl   (%rax)
    6930:	4c 89 dd             	mov    %r11,%rbp
    6933:	4c 8b 8e 90 01 00 00 	mov    0x190(%rsi),%r9
    693a:	4c 8b 44 24 e0       	mov    -0x20(%rsp),%r8
    693f:	48 d1 ed             	shr    %rbp
    6942:	48 c1 e5 04          	shl    $0x4,%rbp
    6946:	66 49 0f 6e c1       	movq   %r9,%xmm0
    694b:	4d 8d 34 28          	lea    (%r8,%rbp,1),%r14
    694f:	83 e5 10             	and    $0x10,%ebp
    6952:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    6956:	74 10                	je     6968 <sendm+0x1f8>
    6958:	41 0f 11 00          	movups %xmm0,(%r8)
    695c:	49 83 c0 10          	add    $0x10,%r8
    6960:	4d 39 f0             	cmp    %r14,%r8
    6963:	74 15                	je     697a <sendm+0x20a>
    6965:	0f 1f 00             	nopl   (%rax)
    6968:	41 0f 11 00          	movups %xmm0,(%r8)
    696c:	49 83 c0 20          	add    $0x20,%r8
    6970:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
    6975:	4d 39 f0             	cmp    %r14,%r8
    6978:	75 ee                	jne    6968 <sendm+0x1f8>
    697a:	4d 89 d8             	mov    %r11,%r8
    697d:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6981:	4c 01 c7             	add    %r8,%rdi
    6984:	41 f6 c3 01          	test   $0x1,%r11b
    6988:	0f 84 52 ff ff ff    	je     68e0 <sendm+0x170>
    698e:	4c 8b 8e 90 01 00 00 	mov    0x190(%rsi),%r9
    6995:	4d 89 0c fa          	mov    %r9,(%r10,%rdi,8)
    6999:	e9 42 ff ff ff       	jmp    68e0 <sendm+0x170>
    699e:	66 90                	xchg   %ax,%ax
    69a0:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    69a8:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    69b0:	e9 05 ff ff ff       	jmp    68ba <sendm+0x14a>
    69b5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000069c0 <mailboxkind>:
    69c0:	f3 0f 1e fa          	endbr64
    69c4:	85 f6                	test   %esi,%esi
    69c6:	74 18                	je     69e0 <mailboxkind+0x20>
    69c8:	31 c0                	xor    %eax,%eax
    69ca:	83 fe 01             	cmp    $0x1,%esi
    69cd:	74 01                	je     69d0 <mailboxkind+0x10>
    69cf:	c3                   	ret
    69d0:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
    69d7:	c3                   	ret
    69d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    69e0:	48 8b 07             	mov    (%rdi),%rax
    69e3:	c3                   	ret
    69e4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    69ef:	90                   	nop

00000000000069f0 <setmailboxkind>:
    69f0:	f3 0f 1e fa          	endbr64
    69f4:	85 d2                	test   %edx,%edx
    69f6:	75 08                	jne    6a00 <setmailboxkind+0x10>
    69f8:	48 89 37             	mov    %rsi,(%rdi)
    69fb:	31 c0                	xor    %eax,%eax
    69fd:	c3                   	ret
    69fe:	66 90                	xchg   %ax,%ax
    6a00:	83 fa 01             	cmp    $0x1,%edx
    6a03:	74 13                	je     6a18 <setmailboxkind+0x28>
    6a05:	83 fa 02             	cmp    $0x2,%edx
    6a08:	75 1e                	jne    6a28 <setmailboxkind+0x38>
    6a0a:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
    6a11:	31 c0                	xor    %eax,%eax
    6a13:	c3                   	ret
    6a14:	0f 1f 40 00          	nopl   0x0(%rax)
    6a18:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
    6a1f:	31 c0                	xor    %eax,%eax
    6a21:	c3                   	ret
    6a22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6a28:	83 fa 03             	cmp    $0x3,%edx
    6a2b:	75 ce                	jne    69fb <setmailboxkind+0xb>
    6a2d:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
    6a34:	31 c0                	xor    %eax,%eax
    6a36:	c3                   	ret
    6a37:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006a40 <fswap>:
    6a40:	f3 0f 1e fa          	endbr64
    6a44:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    6a4b:	8b 97 9c 01 00 00    	mov    0x19c(%rdi),%edx
    6a51:	44 8b 8f 30 01 00 00 	mov    0x130(%rdi),%r9d
    6a58:	48 63 4f 04          	movslq 0x4(%rdi),%rcx
    6a5c:	8b 86 c4 00 00 00    	mov    0xc4(%rsi),%eax
    6a62:	0f af d0             	imul   %eax,%edx
    6a65:	41 01 d1             	add    %edx,%r9d
    6a68:	85 c0                	test   %eax,%eax
    6a6a:	0f 8e 0d 01 00 00    	jle    6b7d <fswap+0x13d>
    6a70:	41 56                	push   %r14
    6a72:	4d 63 c9             	movslq %r9d,%r9
    6a75:	48 63 d2             	movslq %edx,%rdx
    6a78:	4c 63 d0             	movslq %eax,%r10
    6a7b:	41 55                	push   %r13
    6a7d:	49 c1 e1 08          	shl    $0x8,%r9
    6a81:	48 c1 e1 09          	shl    $0x9,%rcx
    6a85:	49 01 d2             	add    %rdx,%r10
    6a88:	41 54                	push   %r12
    6a8a:	49 c1 e2 08          	shl    $0x8,%r10
    6a8e:	55                   	push   %rbp
    6a8f:	53                   	push   %rbx
    6a90:	48 8b 6e 20          	mov    0x20(%rsi),%rbp
    6a94:	48 89 d6             	mov    %rdx,%rsi
    6a97:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
    6a9e:	48 c1 e6 08          	shl    $0x8,%rsi
    6aa2:	4e 8b 5c 0d 38       	mov    0x38(%rbp,%r9,1),%r11
    6aa7:	49 8b 9c 0b 70 01 00 00 	mov    0x170(%r11,%rcx,1),%rbx
    6aaf:	eb 17                	jmp    6ac8 <fswap+0x88>
    6ab1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6ab8:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    6abf:	49 39 f2             	cmp    %rsi,%r10
    6ac2:	0f 84 aa 00 00 00    	je     6b72 <fswap+0x132>
    6ac8:	83 bc 33 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbx,%rsi,1)
    6ad0:	75 e6                	jne    6ab8 <fswap+0x78>
    6ad2:	48 8b 7c 35 38       	mov    0x38(%rbp,%rsi,1),%rdi
    6ad7:	45 85 c0             	test   %r8d,%r8d
    6ada:	7e dc                	jle    6ab8 <fswap+0x78>
    6adc:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    6ae3:	31 c9                	xor    %ecx,%ecx
    6ae5:	eb 5e                	jmp    6b45 <fswap+0x105>
    6ae7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6af0:	48 63 d2             	movslq %edx,%rdx
    6af3:	48 c1 e2 09          	shl    $0x9,%rdx
    6af7:	4d 8b ac 13 70 01 00 00 	mov    0x170(%r11,%rdx,1),%r13
    6aff:	49 01 f5             	add    %rsi,%r13
    6b02:	4c 89 ea             	mov    %r13,%rdx
    6b05:	4d 8b 6d 00          	mov    0x0(%r13),%r13
    6b09:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    6b11:	75 22                	jne    6b35 <fswap+0xf5>
    6b13:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    6b1a:	4c 89 32             	mov    %r14,(%rdx)
    6b1d:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    6b24:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    6b2b:	4c 89 30             	mov    %r14,(%rax)
    6b2e:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
    6b35:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    6b3c:	41 39 c8             	cmp    %ecx,%r8d
    6b3f:	0f 84 73 ff ff ff    	je     6ab8 <fswap+0x78>
    6b45:	83 c1 01             	add    $0x1,%ecx
    6b48:	89 c8                	mov    %ecx,%eax
    6b4a:	99                   	cltd
    6b4b:	41 f7 f8             	idiv   %r8d
    6b4e:	48 8b 07             	mov    (%rdi),%rax
    6b51:	4c 01 c8             	add    %r9,%rax
    6b54:	4c 8b 20             	mov    (%rax),%r12
    6b57:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    6b60:	74 8e                	je     6af0 <fswap+0xb0>
    6b62:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    6b69:	49 39 f2             	cmp    %rsi,%r10
    6b6c:	0f 85 56 ff ff ff    	jne    6ac8 <fswap+0x88>
    6b72:	5b                   	pop    %rbx
    6b73:	31 c0                	xor    %eax,%eax
    6b75:	5d                   	pop    %rbp
    6b76:	41 5c                	pop    %r12
    6b78:	41 5d                	pop    %r13
    6b7a:	41 5e                	pop    %r14
    6b7c:	c3                   	ret
    6b7d:	31 c0                	xor    %eax,%eax
    6b7f:	c3                   	ret

0000000000006b80 <barriered_work>:
    6b80:	f3 0f 1e fa          	endbr64
    6b84:	41 57                	push   %r15
    6b86:	41 56                	push   %r14
    6b88:	41 55                	push   %r13
    6b8a:	41 54                	push   %r12
    6b8c:	55                   	push   %rbp
    6b8d:	53                   	push   %rbx
    6b8e:	48 89 fb             	mov    %rdi,%rbx
    6b91:	48 83 ec 78          	sub    $0x78,%rsp
    6b95:	66 0f 6f 05 53 20 00 00 	movdqa 0x2053(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    6b9d:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    6ba6:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    6bab:	31 c0                	xor    %eax,%eax
    6bad:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    6bb4:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    6bb9:	48 8b 88 f0 00 00 00 	mov    0xf0(%rax),%rcx
    6bc0:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
    6bc5:	8b 11                	mov    (%rcx),%edx
    6bc7:	83 fa ff             	cmp    $0xffffffff,%edx
    6bca:	0f 84 a0 02 00 00    	je     6e70 <barriered_work+0x2f0>
    6bd0:	3b 90 e8 00 00 00    	cmp    0xe8(%rax),%edx
    6bd6:	74 28                	je     6c00 <barriered_work+0x80>
    6bd8:	48 8b 44 24 68       	mov    0x68(%rsp),%rax
    6bdd:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    6be6:	0f 85 f2 04 00 00    	jne    70de <barriered_work+0x55e>
    6bec:	48 83 c4 78          	add    $0x78,%rsp
    6bf0:	31 c0                	xor    %eax,%eax
    6bf2:	5b                   	pop    %rbx
    6bf3:	5d                   	pop    %rbp
    6bf4:	41 5c                	pop    %r12
    6bf6:	41 5d                	pop    %r13
    6bf8:	41 5e                	pop    %r14
    6bfa:	41 5f                	pop    %r15
    6bfc:	c3                   	ret
    6bfd:	0f 1f 00             	nopl   (%rax)
    6c00:	8b af 30 01 00 00    	mov    0x130(%rdi),%ebp
    6c06:	8b 41 04             	mov    0x4(%rcx),%eax
    6c09:	85 ed                	test   %ebp,%ebp
    6c0b:	0f 85 4f 04 00 00    	jne    7060 <barriered_work+0x4e0>
    6c11:	85 c0                	test   %eax,%eax
    6c13:	0f 84 4f 04 00 00    	je     7068 <barriered_work+0x4e8>
    6c19:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6c20:	44 8b 63 04          	mov    0x4(%rbx),%r12d
    6c24:	48 89 df             	mov    %rbx,%rdi
    6c27:	41 39 ec             	cmp    %ebp,%r12d
    6c2a:	0f 85 90 03 00 00    	jne    6fc0 <barriered_work+0x440>
    6c30:	e8 db f9 ff ff       	call   6610 <receive>
    6c35:	4c 8b ab 28 01 00 00 	mov    0x128(%rbx),%r13
    6c3c:	41 83 bd f8 00 00 00 01 	cmpl   $0x1,0xf8(%r13)
    6c44:	0f 85 79 02 00 00    	jne    6ec3 <barriered_work+0x343>
    6c4a:	8b 83 40 01 00 00    	mov    0x140(%rbx),%eax
    6c50:	85 c0                	test   %eax,%eax
    6c52:	0f 8e 6b 02 00 00    	jle    6ec3 <barriered_work+0x343>
    6c58:	49 63 55 08          	movslq 0x8(%r13),%rdx
    6c5c:	8b b3 34 01 00 00    	mov    0x134(%rbx),%esi
    6c62:	4c 63 c5             	movslq %ebp,%r8
    6c65:	31 c9                	xor    %ecx,%ecx
    6c67:	49 c1 e0 09          	shl    $0x9,%r8
    6c6b:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6c70:	4c 63 f8             	movslq %eax,%r15
    6c73:	49 89 d6             	mov    %rdx,%r14
    6c76:	48 c1 e2 08          	shl    $0x8,%rdx
    6c7a:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    6c7f:	45 89 e0             	mov    %r12d,%r8d
    6c82:	89 74 24 24          	mov    %esi,0x24(%rsp)
    6c86:	49 89 d3             	mov    %rdx,%r11
    6c89:	eb 19                	jmp    6ca4 <barriered_work+0x124>
    6c8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6c90:	48 83 44 24 08 01    	addq   $0x1,0x8(%rsp)
    6c96:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    6c9b:	49 39 c7             	cmp    %rax,%r15
    6c9e:	0f 84 1c 02 00 00    	je     6ec0 <barriered_work+0x340>
    6ca4:	8b 44 24 08          	mov    0x8(%rsp),%eax
    6ca8:	41 39 c6             	cmp    %eax,%r14d
    6cab:	74 e3                	je     6c90 <barriered_work+0x110>
    6cad:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6cb2:	49 8b 45 20          	mov    0x20(%r13),%rax
    6cb6:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6cbb:	48 c1 e7 08          	shl    $0x8,%rdi
    6cbf:	48 8b 74 38 38       	mov    0x38(%rax,%rdi,1),%rsi
    6cc4:	48 8d 14 0e          	lea    (%rsi,%rcx,1),%rdx
    6cc8:	44 8b 8a a0 01 00 00 	mov    0x1a0(%rdx),%r9d
    6ccf:	45 85 c9             	test   %r9d,%r9d
    6cd2:	75 bc                	jne    6c90 <barriered_work+0x110>
    6cd4:	4e 8b 4c 18 38       	mov    0x38(%rax,%r11,1),%r9
    6cd9:	49 8d 04 09          	lea    (%r9,%rcx,1),%rax
    6cdd:	44 8b 90 a0 01 00 00 	mov    0x1a0(%rax),%r10d
    6ce4:	45 85 d2             	test   %r10d,%r10d
    6ce7:	75 a7                	jne    6c90 <barriered_work+0x110>
    6ce9:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    6cf0:	83 bc 38 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdi,1)
    6cf8:	75 96                	jne    6c90 <barriered_work+0x110>
    6cfa:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
    6d01:	42 83 bc 18 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%r11,1)
    6d0a:	75 84                	jne    6c90 <barriered_work+0x110>
    6d0c:	8b 54 24 24          	mov    0x24(%rsp),%edx
    6d10:	85 d2                	test   %edx,%edx
    6d12:	0f 8e 78 ff ff ff    	jle    6c90 <barriered_work+0x110>
    6d18:	48 63 c2             	movslq %edx,%rax
    6d1b:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    6d20:	bd 70 01 00 00       	mov    $0x170,%ebp
    6d25:	48 c1 e0 09          	shl    $0x9,%rax
    6d29:	44 89 74 24 34       	mov    %r14d,0x34(%rsp)
    6d2e:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    6d33:	4c 8d a0 a0 01 00 00 	lea    0x1a0(%rax),%r12
    6d3a:	44 89 44 24 30       	mov    %r8d,0x30(%rsp)
    6d3f:	41 89 d0             	mov    %edx,%r8d
    6d42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6d48:	41 83 c2 01          	add    $0x1,%r10d
    6d4c:	49 8b 0c 29          	mov    (%r9,%rbp,1),%rcx
    6d50:	44 89 d0             	mov    %r10d,%eax
    6d53:	99                   	cltd
    6d54:	48 01 f9             	add    %rdi,%rcx
    6d57:	41 f7 f8             	idiv   %r8d
    6d5a:	4c 8b 29             	mov    (%rcx),%r13
    6d5d:	4c 89 6c 24 18       	mov    %r13,0x18(%rsp)
    6d62:	4c 8b a9 80 00 00 00 	mov    0x80(%rcx),%r13
    6d69:	48 63 d2             	movslq %edx,%rdx
    6d6c:	48 c1 e2 09          	shl    $0x9,%rdx
    6d70:	48 8b 84 16 70 01 00 00 	mov    0x170(%rsi,%rdx,1),%rax
    6d78:	4c 01 d8             	add    %r11,%rax
    6d7b:	4c 8b 30             	mov    (%rax),%r14
    6d7e:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    6d85:	4c 89 28             	mov    %r13,(%rax)
    6d88:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    6d8d:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    6d94:	48 89 11             	mov    %rdx,(%rcx)
    6d97:	4c 89 b1 80 00 00 00 	mov    %r14,0x80(%rcx)
    6d9e:	b9 a0 01 00 00       	mov    $0x1a0,%ecx
    6da3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6da8:	41 c7 04 09 01 00 00 00 	movl   $0x1,(%r9,%rcx,1)
    6db0:	c7 04 0e 01 00 00 00 	movl   $0x1,(%rsi,%rcx,1)
    6db7:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    6dbe:	4c 39 e1             	cmp    %r12,%rcx
    6dc1:	75 e5                	jne    6da8 <barriered_work+0x228>
    6dc3:	48 8b 0c 2e          	mov    (%rsi,%rbp,1),%rcx
    6dc7:	48 8b 00             	mov    (%rax),%rax
    6dca:	41 c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r14)
    6dd5:	48 81 c5 00 02 00 00 	add    $0x200,%rbp
    6ddc:	4a 8b 8c 19 80 00 00 00 	mov    0x80(%rcx,%r11,1),%rcx
    6de4:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    6dee:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
    6df8:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
    6e02:	45 39 d0             	cmp    %r10d,%r8d
    6e05:	0f 85 3d ff ff ff    	jne    6d48 <barriered_work+0x1c8>
    6e0b:	48 8b 4c 24 38       	mov    0x38(%rsp),%rcx
    6e10:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    6e15:	b8 70 01 00 00       	mov    $0x170,%eax
    6e1a:	44 8b 44 24 30       	mov    0x30(%rsp),%r8d
    6e1f:	44 8b 74 24 34       	mov    0x34(%rsp),%r14d
    6e24:	48 8d a9 70 01 00 00 	lea    0x170(%rcx),%rbp
    6e2b:	eb 12                	jmp    6e3f <barriered_work+0x2bf>
    6e2d:	0f 1f 00             	nopl   (%rax)
    6e30:	48 05 00 02 00 00    	add    $0x200,%rax
    6e36:	48 39 e8             	cmp    %rbp,%rax
    6e39:	0f 84 51 fe ff ff    	je     6c90 <barriered_work+0x110>
    6e3f:	48 8b 14 06          	mov    (%rsi,%rax,1),%rdx
    6e43:	49 8b 0c 01          	mov    (%r9,%rax,1),%rcx
    6e47:	4a 8b 14 1a          	mov    (%rdx,%r11,1),%rdx
    6e4b:	48 39 14 39          	cmp    %rdx,(%rcx,%rdi,1)
    6e4f:	75 df                	jne    6e30 <barriered_work+0x2b0>
    6e51:	bf 01 00 00 00       	mov    $0x1,%edi
    6e56:	48 8d 35 eb 13 00 00 	lea    0x13eb(%rip),%rsi        # 8248 <_IO_stdin_used+0x248>
    6e5d:	31 c0                	xor    %eax,%eax
    6e5f:	e8 4c b6 ff ff       	call   24b0 <__printf_chk@plt>
    6e64:	bf 01 00 00 00       	mov    $0x1,%edi
    6e69:	e8 a2 b6 ff ff       	call   2510 <exit@plt>
    6e6e:	66 90                	xchg   %ax,%ax
    6e70:	8b af 30 01 00 00    	mov    0x130(%rdi),%ebp
    6e76:	85 ed                	test   %ebp,%ebp
    6e78:	0f 85 a2 fd ff ff    	jne    6c20 <barriered_work+0xa0>
    6e7e:	44 8b 90 e8 00 00 00 	mov    0xe8(%rax),%r10d
    6e85:	45 85 d2             	test   %r10d,%r10d
    6e88:	0f 85 92 fd ff ff    	jne    6c20 <barriered_work+0xa0>
    6e8e:	69 87 80 00 00 00 1d e6 cb 0b 	imul   $0xbcbe61d,0x80(%rdi),%eax
    6e98:	05 40 7c 0a 00       	add    $0xa7c40,%eax
    6e9d:	c1 c8 05             	ror    $0x5,%eax
    6ea0:	3d c4 a7 00 00       	cmp    $0xa7c4,%eax
    6ea5:	0f 87 75 fd ff ff    	ja     6c20 <barriered_work+0xa0>
    6eab:	48 c7 01 00 00 00 00 	movq   $0x0,(%rcx)
    6eb2:	e9 69 fd ff ff       	jmp    6c20 <barriered_work+0xa0>
    6eb7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6ec0:	45 89 c4             	mov    %r8d,%r12d
    6ec3:	48 89 df             	mov    %rbx,%rdi
    6ec6:	e8 75 fb ff ff       	call   6a40 <fswap>
    6ecb:	48 89 df             	mov    %rbx,%rdi
    6ece:	e8 3d f7 ff ff       	call   6610 <receive>
    6ed3:	0f ae f8             	sfence
    6ed6:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6edd:	31 ff                	xor    %edi,%edi
    6edf:	48 c1 e6 05          	shl    $0x5,%rsi
    6ee3:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6eea:	e8 61 b4 ff ff       	call   2350 <clock_gettime@plt>
    6eef:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6ef6:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6efd:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6f01:	8b 72 10             	mov    0x10(%rdx),%esi
    6f04:	8d 6e 01             	lea    0x1(%rsi),%ebp
    6f07:	89 6a 10             	mov    %ebp,0x10(%rdx)
    6f0a:	75 55                	jne    6f61 <barriered_work+0x3e1>
    6f0c:	0f 1f 40 00          	nopl   0x0(%rax)
    6f10:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    6f17:	48 8b 40 18          	mov    0x18(%rax),%rax
    6f1b:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
    6f1f:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6f27:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6f2b:	48 c1 e7 09          	shl    $0x9,%rdi
    6f2f:	48 03 78 38          	add    0x38(%rax),%rdi
    6f33:	ff 93 20 01 00 00    	call   *0x120(%rbx)
    6f39:	0f ae f8             	sfence
    6f3c:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6f43:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6f4a:	74 c4                	je     6f10 <barriered_work+0x390>
    6f4c:	48 8b 40 48          	mov    0x48(%rax),%rax
    6f50:	3b 68 10             	cmp    0x10(%rax),%ebp
    6f53:	74 0c                	je     6f61 <barriered_work+0x3e1>
    6f55:	48 8d 3d 07 13 00 00 	lea    0x1307(%rip),%rdi        # 8263 <_IO_stdin_used+0x263>
    6f5c:	e8 cf b3 ff ff       	call   2330 <puts@plt>
    6f61:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    6f68:	31 ff                	xor    %edi,%edi
    6f6a:	48 c1 e6 05          	shl    $0x5,%rsi
    6f6e:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6f75:	48 83 c6 10          	add    $0x10,%rsi
    6f79:	e8 d2 b3 ff ff       	call   2350 <clock_gettime@plt>
    6f7e:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6f85:	48 83 c0 01          	add    $0x1,%rax
    6f89:	48 99                	cqto
    6f8b:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6f92:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6f98:	83 e8 01             	sub    $0x1,%eax
    6f9b:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    6fa2:	44 39 e0             	cmp    %r12d,%eax
    6fa5:	74 53                	je     6ffa <barriered_work+0x47a>
    6fa7:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    6fb1:	0f ae f8             	sfence
    6fb4:	e9 1f fc ff ff       	jmp    6bd8 <barriered_work+0x58>
    6fb9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6fc0:	e8 4b f6 ff ff       	call   6610 <receive>
    6fc5:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6fcc:	75 16                	jne    6fe4 <barriered_work+0x464>
    6fce:	66 90                	xchg   %ax,%ax
    6fd0:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
    6fd8:	0f ae f8             	sfence
    6fdb:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6fe2:	74 ec                	je     6fd0 <barriered_work+0x450>
    6fe4:	48 89 df             	mov    %rbx,%rdi
    6fe7:	e8 84 f7 ff ff       	call   6770 <sendm>
    6fec:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    6ff2:	83 e8 01             	sub    $0x1,%eax
    6ff5:	44 39 e0             	cmp    %r12d,%eax
    6ff8:	75 ad                	jne    6fa7 <barriered_work+0x427>
    6ffa:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    7001:	85 d2                	test   %edx,%edx
    7003:	7e a2                	jle    6fa7 <barriered_work+0x427>
    7005:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    700c:	48 c1 e2 09          	shl    $0x9,%rdx
    7010:	48 63 41 08          	movslq 0x8(%rcx),%rax
    7014:	48 c1 e0 08          	shl    $0x8,%rax
    7018:	48 03 41 20          	add    0x20(%rcx),%rax
    701c:	48 8b 40 38          	mov    0x38(%rax),%rax
    7020:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    7024:	80 e6 02             	and    $0x2,%dh
    7027:	74 17                	je     7040 <barriered_work+0x4c0>
    7029:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    7030:	48 05 00 02 00 00    	add    $0x200,%rax
    7036:	48 39 c8             	cmp    %rcx,%rax
    7039:	0f 84 68 ff ff ff    	je     6fa7 <barriered_work+0x427>
    703f:	90                   	nop
    7040:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    7047:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
    704e:	48 05 00 04 00 00    	add    $0x400,%rax
    7054:	48 39 c8             	cmp    %rcx,%rax
    7057:	75 e7                	jne    7040 <barriered_work+0x4c0>
    7059:	e9 49 ff ff ff       	jmp    6fa7 <barriered_work+0x427>
    705e:	66 90                	xchg   %ax,%ax
    7060:	39 c5                	cmp    %eax,%ebp
    7062:	0f 85 b8 fb ff ff    	jne    6c20 <barriered_work+0xa0>
    7068:	48 8b 69 08          	mov    0x8(%rcx),%rbp
    706c:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
    7071:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    7076:	8b 45 10             	mov    0x10(%rbp),%eax
    7079:	48 83 45 00 01       	addq   $0x1,0x0(%rbp)
    707e:	44 8d 60 01          	lea    0x1(%rax),%r12d
    7082:	44 89 65 10          	mov    %r12d,0x10(%rbp)
    7086:	e8 15 b3 ff ff       	call   23a0 <nanosleep@plt>
    708b:	44 3b 65 10          	cmp    0x10(%rbp),%r12d
    708f:	74 0c                	je     709d <barriered_work+0x51d>
    7091:	48 8d 3d 93 11 00 00 	lea    0x1193(%rip),%rdi        # 822b <_IO_stdin_used+0x22b>
    7098:	e8 93 b2 ff ff       	call   2330 <puts@plt>
    709d:	8b ab 30 01 00 00    	mov    0x130(%rbx),%ebp
    70a3:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    70aa:	8d 45 01             	lea    0x1(%rbp),%eax
    70ad:	48 8b b1 f0 00 00 00 	mov    0xf0(%rcx),%rsi
    70b4:	99                   	cltd
    70b5:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    70bb:	89 56 04             	mov    %edx,0x4(%rsi)
    70be:	83 fd 01             	cmp    $0x1,%ebp
    70c1:	0f 85 59 fb ff ff    	jne    6c20 <barriered_work+0xa0>
    70c7:	8b 81 e8 00 00 00    	mov    0xe8(%rcx),%eax
    70cd:	83 c0 01             	add    $0x1,%eax
    70d0:	99                   	cltd
    70d1:	f7 b9 c0 00 00 00    	idivl  0xc0(%rcx)
    70d7:	89 16                	mov    %edx,(%rsi)
    70d9:	e9 42 fb ff ff       	jmp    6c20 <barriered_work+0xa0>
    70de:	e8 9d b2 ff ff       	call   2380 <__stack_chk_fail@plt>
    70e3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    70ee:	66 90                	xchg   %ax,%ax

00000000000070f0 <barriered_work_ingest_andwork>:
    70f0:	f3 0f 1e fa          	endbr64
    70f4:	53                   	push   %rbx
    70f5:	48 89 fb             	mov    %rdi,%rbx
    70f8:	e8 23 f1 ff ff       	call   6220 <barriered_work_ingest>
    70fd:	48 89 df             	mov    %rbx,%rdi
    7100:	5b                   	pop    %rbx
    7101:	e9 7a fa ff ff       	jmp    6b80 <barriered_work>
    7106:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000007110 <barriered_nulltask>:
    7110:	f3 0f 1e fa          	endbr64
    7114:	31 c0                	xor    %eax,%eax
    7116:	c3                   	ret
    7117:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007120 <barriered_steal>:
    7120:	f3 0f 1e fa          	endbr64
    7124:	31 c0                	xor    %eax,%eax
    7126:	c3                   	ret
    7127:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007130 <after>:
    7130:	f3 0f 1e fa          	endbr64
    7134:	31 c0                	xor    %eax,%eax
    7136:	48 39 d7             	cmp    %rdx,%rdi
    7139:	7e 08                	jle    7143 <after+0x13>
    713b:	31 c0                	xor    %eax,%eax
    713d:	48 39 ce             	cmp    %rcx,%rsi
    7140:	0f 9f c0             	setg   %al
    7143:	c3                   	ret
    7144:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    714f:	90                   	nop

0000000000007150 <within>:
    7150:	f3 0f 1e fa          	endbr64
    7154:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    7159:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    715e:	31 c0                	xor    %eax,%eax
    7160:	48 39 d7             	cmp    %rdx,%rdi
    7163:	7f 18                	jg     717d <within+0x2d>
    7165:	4d 39 d8             	cmp    %r11,%r8
    7168:	0f 9e c2             	setle  %dl
    716b:	48 39 ce             	cmp    %rcx,%rsi
    716e:	0f 9e c0             	setle  %al
    7171:	21 c2                	and    %eax,%edx
    7173:	31 c0                	xor    %eax,%eax
    7175:	4d 39 d1             	cmp    %r10,%r9
    7178:	0f 9e c0             	setle  %al
    717b:	21 d0                	and    %edx,%eax
    717d:	c3                   	ret
    717e:	66 90                	xchg   %ax,%ax

0000000000007180 <overlap>:
    7180:	f3 0f 1e fa          	endbr64
    7184:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    7189:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    718e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    7193:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    7198:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    719d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
    71a2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    71a7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    71ac:	48 39 fe             	cmp    %rdi,%rsi
    71af:	7d 2f                	jge    71e0 <overlap+0x60>
    71b1:	48 39 ca             	cmp    %rcx,%rdx
    71b4:	7d 62                	jge    7218 <overlap+0x98>
    71b6:	4d 39 da             	cmp    %r11,%r10
    71b9:	7d 0e                	jge    71c9 <overlap+0x49>
    71bb:	b8 01 00 00 00       	mov    $0x1,%eax
    71c0:	4d 39 c1             	cmp    %r8,%r9
    71c3:	0f 8c 7f 00 00 00    	jl     7248 <overlap+0xc8>
    71c9:	31 c0                	xor    %eax,%eax
    71cb:	4d 39 c1             	cmp    %r8,%r9
    71ce:	7f 4c                	jg     721c <overlap+0x9c>
    71d0:	31 c0                	xor    %eax,%eax
    71d2:	4d 39 da             	cmp    %r11,%r10
    71d5:	0f 9e c0             	setle  %al
    71d8:	c3                   	ret
    71d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    71e0:	7e 4e                	jle    7230 <overlap+0xb0>
    71e2:	48 39 ca             	cmp    %rcx,%rdx
    71e5:	7f 39                	jg     7220 <overlap+0xa0>
    71e7:	75 31                	jne    721a <overlap+0x9a>
    71e9:	4d 39 c1             	cmp    %r8,%r9
    71ec:	7c 2c                	jl     721a <overlap+0x9a>
    71ee:	b8 01 00 00 00       	mov    $0x1,%eax
    71f3:	4d 39 da             	cmp    %r11,%r10
    71f6:	7d 24                	jge    721c <overlap+0x9c>
    71f8:	48 39 ca             	cmp    %rcx,%rdx
    71fb:	0f 94 c2             	sete   %dl
    71fe:	48 39 fe             	cmp    %rdi,%rsi
    7201:	0f 94 c0             	sete   %al
    7204:	21 c2                	and    %eax,%edx
    7206:	31 c0                	xor    %eax,%eax
    7208:	4d 39 c1             	cmp    %r8,%r9
    720b:	0f 94 c0             	sete   %al
    720e:	21 d0                	and    %edx,%eax
    7210:	c3                   	ret
    7211:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7218:	74 af                	je     71c9 <overlap+0x49>
    721a:	31 c0                	xor    %eax,%eax
    721c:	c3                   	ret
    721d:	0f 1f 00             	nopl   (%rax)
    7220:	4d 39 da             	cmp    %r11,%r10
    7223:	7e c4                	jle    71e9 <overlap+0x69>
    7225:	b8 01 00 00 00       	mov    $0x1,%eax
    722a:	4d 39 c1             	cmp    %r8,%r9
    722d:	7e ba                	jle    71e9 <overlap+0x69>
    722f:	c3                   	ret
    7230:	48 39 ca             	cmp    %rcx,%rdx
    7233:	7c 94                	jl     71c9 <overlap+0x49>
    7235:	4d 39 c1             	cmp    %r8,%r9
    7238:	7d b4                	jge    71ee <overlap+0x6e>
    723a:	48 39 ca             	cmp    %rcx,%rdx
    723d:	74 91                	je     71d0 <overlap+0x50>
    723f:	eb d9                	jmp    721a <overlap+0x9a>
    7241:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7248:	c3                   	ret
    7249:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000007250 <verify>:
    7250:	f3 0f 1e fa          	endbr64
    7254:	85 f6                	test   %esi,%esi
    7256:	0f 8e 44 03 00 00    	jle    75a0 <verify+0x350>
    725c:	41 57                	push   %r15
    725e:	41 89 f7             	mov    %esi,%r15d
    7261:	41 56                	push   %r14
    7263:	45 31 f6             	xor    %r14d,%r14d
    7266:	41 55                	push   %r13
    7268:	41 54                	push   %r12
    726a:	55                   	push   %rbp
    726b:	53                   	push   %rbx
    726c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    7270:	48 83 ec 58          	sub    $0x58,%rsp
    7274:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    7279:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    727e:	45 31 e4             	xor    %r12d,%r12d
    7281:	45 39 e6             	cmp    %r12d,%r14d
    7284:	0f 84 4e 02 00 00    	je     74d8 <verify+0x288>
    728a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    728f:	8b 50 08             	mov    0x8(%rax),%edx
    7292:	85 d2                	test   %edx,%edx
    7294:	0f 8e 3e 02 00 00    	jle    74d8 <verify+0x288>
    729a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    729f:	31 c9                	xor    %ecx,%ecx
    72a1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    72a6:	31 c0                	xor    %eax,%eax
    72a8:	44 89 f2             	mov    %r14d,%edx
    72ab:	bf 01 00 00 00       	mov    $0x1,%edi
    72b0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    72b5:	48 8d 35 b7 0f 00 00 	lea    0xfb7(%rip),%rsi        # 8273 <_IO_stdin_used+0x273>
    72bc:	e8 ef b1 ff ff       	call   24b0 <__printf_chk@plt>
    72c1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    72c6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    72cb:	8b 40 08             	mov    0x8(%rax),%eax
    72ce:	85 c0                	test   %eax,%eax
    72d0:	0f 8e e6 01 00 00    	jle    74bc <verify+0x26c>
    72d6:	48 89 c8             	mov    %rcx,%rax
    72d9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    72de:	31 db                	xor    %ebx,%ebx
    72e0:	48 c1 e0 09          	shl    $0x9,%rax
    72e4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    72e9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    72ee:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    72f3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    72f8:	4c 8b 20             	mov    (%rax),%r12
    72fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7300:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    7305:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    730a:	49 89 de             	mov    %rbx,%r14
    730d:	48 8d 35 74 0f 00 00 	lea    0xf74(%rip),%rsi        # 8288 <_IO_stdin_used+0x288>
    7314:	49 c1 e6 09          	shl    $0x9,%r14
    7318:	bf 01 00 00 00       	mov    $0x1,%edi
    731d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    7321:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    7329:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    732e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    7336:	31 c0                	xor    %eax,%eax
    7338:	e8 73 b1 ff ff       	call   24b0 <__printf_chk@plt>
    733d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7342:	4c 8b 20             	mov    (%rax),%r12
    7345:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    734e:	0f 8e 47 01 00 00    	jle    749b <verify+0x24b>
    7354:	4c 03 75 00          	add    0x0(%rbp),%r14
    7358:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    735d:	ba 01 00 00 00       	mov    $0x1,%edx
    7362:	4d 89 f5             	mov    %r14,%r13
    7365:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    736c:	4d 85 f6             	test   %r14,%r14
    736f:	0f 8e 21 01 00 00    	jle    7496 <verify+0x246>
    7375:	0f 1f 00             	nopl   (%rax)
    7378:	48 89 d5             	mov    %rdx,%rbp
    737b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7380:	31 db                	xor    %ebx,%ebx
    7382:	4d 89 f2             	mov    %r14,%r10
    7385:	48 c1 e5 05          	shl    $0x5,%rbp
    7389:	48 83 ed 20          	sub    $0x20,%rbp
    738d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    7391:	49 89 ee             	mov    %rbp,%r14
    7394:	48 89 dd             	mov    %rbx,%rbp
    7397:	48 89 d3             	mov    %rdx,%rbx
    739a:	eb 31                	jmp    73cd <verify+0x17d>
    739c:	0f 1f 40 00          	nopl   0x0(%rax)
    73a0:	4c 39 c2             	cmp    %r8,%rdx
    73a3:	0f 8d 57 01 00 00    	jge    7500 <verify+0x2b0>
    73a9:	4c 39 df             	cmp    %r11,%rdi
    73ac:	7e 05                	jle    73b3 <verify+0x163>
    73ae:	49 39 c1             	cmp    %rax,%r9
    73b1:	7c 75                	jl     7428 <verify+0x1d8>
    73b3:	4c 39 df             	cmp    %r11,%rdi
    73b6:	0f 8d ab 01 00 00    	jge    7567 <verify+0x317>
    73bc:	0f 1f 40 00          	nopl   0x0(%rax)
    73c0:	48 83 c5 01          	add    $0x1,%rbp
    73c4:	49 39 ea             	cmp    %rbp,%r10
    73c7:	0f 8e a9 00 00 00    	jle    7476 <verify+0x226>
    73cd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    73d4:	48 89 e8             	mov    %rbp,%rax
    73d7:	48 c1 e0 05          	shl    $0x5,%rax
    73db:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    73e2:	4c 01 f2             	add    %r14,%rdx
    73e5:	48 8b 08             	mov    (%rax),%rcx
    73e8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    73ec:	48 8b 32             	mov    (%rdx),%rsi
    73ef:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    73f3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    73f7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    73fb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    73ff:	48 8b 40 18          	mov    0x18(%rax),%rax
    7403:	48 39 f1             	cmp    %rsi,%rcx
    7406:	7c 98                	jl     73a0 <verify+0x150>
    7408:	0f 8e 42 01 00 00    	jle    7550 <verify+0x300>
    740e:	4c 39 c2             	cmp    %r8,%rdx
    7411:	0f 8f f9 00 00 00    	jg     7510 <verify+0x2c0>
    7417:	75 a7                	jne    73c0 <verify+0x170>
    7419:	4c 39 df             	cmp    %r11,%rdi
    741c:	7f a2                	jg     73c0 <verify+0x170>
    741e:	49 39 c1             	cmp    %rax,%r9
    7421:	7c 9d                	jl     73c0 <verify+0x170>
    7423:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7428:	49 89 c1             	mov    %rax,%r9
    742b:	48 89 f9             	mov    %rdi,%rcx
    742e:	48 89 f2             	mov    %rsi,%rdx
    7431:	bf 01 00 00 00       	mov    $0x1,%edi
    7436:	48 8d 35 1b 12 00 00 	lea    0x121b(%rip),%rsi        # 8658 <_IO_stdin_used+0x658>
    743d:	31 c0                	xor    %eax,%eax
    743f:	48 83 c5 01          	add    $0x1,%rbp
    7443:	e8 68 b0 ff ff       	call   24b0 <__printf_chk@plt>
    7448:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    744d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    7452:	4c 03 28             	add    (%rax),%r13
    7455:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    745a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
    7461:	4c 8b 20             	mov    (%rax),%r12
    7464:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7469:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    746d:	49 39 ea             	cmp    %rbp,%r10
    7470:	0f 8f 57 ff ff ff    	jg     73cd <verify+0x17d>
    7476:	48 89 da             	mov    %rbx,%rdx
    7479:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7480:	7d 14                	jge    7496 <verify+0x246>
    7482:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7489:	48 83 c2 01          	add    $0x1,%rdx
    748d:	4d 85 f6             	test   %r14,%r14
    7490:	0f 8f e2 fe ff ff    	jg     7378 <verify+0x128>
    7496:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    749b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    74a0:	48 83 c3 01          	add    $0x1,%rbx
    74a4:	39 58 08             	cmp    %ebx,0x8(%rax)
    74a7:	0f 8f 53 fe ff ff    	jg     7300 <verify+0xb0>
    74ad:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    74b2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    74b7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
    74bc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    74c1:	48 83 c1 01          	add    $0x1,%rcx
    74c5:	39 48 08             	cmp    %ecx,0x8(%rax)
    74c8:	0f 8f d8 fd ff ff    	jg     72a6 <verify+0x56>
    74ce:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    74d3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    74d8:	48 81 44 24 10 00 01 00 00 	addq   $0x100,0x10(%rsp)
    74e1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    74e6:	41 39 c7             	cmp    %eax,%r15d
    74e9:	0f 84 86 00 00 00    	je     7575 <verify+0x325>
    74ef:	41 89 c4             	mov    %eax,%r12d
    74f2:	e9 8a fd ff ff       	jmp    7281 <verify+0x31>
    74f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    7500:	0f 85 ba fe ff ff    	jne    73c0 <verify+0x170>
    7506:	e9 a8 fe ff ff       	jmp    73b3 <verify+0x163>
    750b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7510:	49 39 c1             	cmp    %rax,%r9
    7513:	7e 09                	jle    751e <verify+0x2ce>
    7515:	4c 39 df             	cmp    %r11,%rdi
    7518:	0f 8c 0a ff ff ff    	jl     7428 <verify+0x1d8>
    751e:	4c 39 df             	cmp    %r11,%rdi
    7521:	0f 8f 99 fe ff ff    	jg     73c0 <verify+0x170>
    7527:	49 39 c1             	cmp    %rax,%r9
    752a:	0f 8d f8 fe ff ff    	jge    7428 <verify+0x1d8>
    7530:	48 39 f1             	cmp    %rsi,%rcx
    7533:	0f 85 87 fe ff ff    	jne    73c0 <verify+0x170>
    7539:	4c 39 c2             	cmp    %r8,%rdx
    753c:	0f 85 7e fe ff ff    	jne    73c0 <verify+0x170>
    7542:	4c 39 df             	cmp    %r11,%rdi
    7545:	0f 84 dd fe ff ff    	je     7428 <verify+0x1d8>
    754b:	e9 70 fe ff ff       	jmp    73c0 <verify+0x170>
    7550:	4c 39 c2             	cmp    %r8,%rdx
    7553:	0f 8c 5a fe ff ff    	jl     73b3 <verify+0x163>
    7559:	4c 39 df             	cmp    %r11,%rdi
    755c:	7e c9                	jle    7527 <verify+0x2d7>
    755e:	4c 39 c2             	cmp    %r8,%rdx
    7561:	0f 85 59 fe ff ff    	jne    73c0 <verify+0x170>
    7567:	49 39 c1             	cmp    %rax,%r9
    756a:	0f 8f 50 fe ff ff    	jg     73c0 <verify+0x170>
    7570:	e9 b3 fe ff ff       	jmp    7428 <verify+0x1d8>
    7575:	48 81 44 24 18 00 01 00 00 	addq   $0x100,0x18(%rsp)
    757e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7582:	45 39 e6             	cmp    %r12d,%r14d
    7585:	74 08                	je     758f <verify+0x33f>
    7587:	41 89 c6             	mov    %eax,%r14d
    758a:	e9 ea fc ff ff       	jmp    7279 <verify+0x29>
    758f:	48 83 c4 58          	add    $0x58,%rsp
    7593:	31 c0                	xor    %eax,%eax
    7595:	5b                   	pop    %rbx
    7596:	5d                   	pop    %rbp
    7597:	41 5c                	pop    %r12
    7599:	41 5d                	pop    %r13
    759b:	41 5e                	pop    %r14
    759d:	41 5f                	pop    %r15
    759f:	c3                   	ret
    75a0:	31 c0                	xor    %eax,%eax
    75a2:	c3                   	ret

Disassembly of section .fini:

00000000000075a4 <_fini>:
    75a4:	f3 0f 1e fa          	endbr64
    75a8:	48 83 ec 08          	sub    $0x8,%rsp
    75ac:	48 83 c4 08          	add    $0x8,%rsp
    75b0:	c3                   	ret
