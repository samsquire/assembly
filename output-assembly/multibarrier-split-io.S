
multibarrier-split-io:     file format elf64-x86-64


Disassembly of section .init:

0000000000002000 <_init>:
    2000:	f3 0f 1e fa          	endbr64
    2004:	48 83 ec 08          	sub    $0x8,%rsp
    2008:	48 8b 05 d9 9f 00 00 	mov    0x9fd9(%rip),%rax        # bfe8 <__gmon_start__@Base>
    200f:	48 85 c0             	test   %rax,%rax
    2012:	74 02                	je     2016 <_init+0x16>
    2014:	ff d0                	call   *%rax
    2016:	48 83 c4 08          	add    $0x8,%rsp
    201a:	c3                   	ret

Disassembly of section .plt:

0000000000002020 <.plt>:
    2020:	ff 35 42 9e 00 00    	push   0x9e42(%rip)        # be68 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 44 9e 00 00    	jmp    *0x9e44(%rip)        # be70 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    22f4:	ff 25 fe 9c 00 00    	jmp    *0x9cfe(%rip)        # bff8 <__cxa_finalize@GLIBC_2.2.5>
    22fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000002300 <free@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 6e 9b 00 00    	jmp    *0x9b6e(%rip)        # be78 <free@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <putchar@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 66 9b 00 00    	jmp    *0x9b66(%rip)        # be80 <putchar@GLIBC_2.2.5>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <pthread_setaffinity_np@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 5e 9b 00 00    	jmp    *0x9b5e(%rip)        # be88 <pthread_setaffinity_np@GLIBC_2.34>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <puts@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 56 9b 00 00    	jmp    *0x9b56(%rip)        # be90 <puts@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <setsockopt@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 4e 9b 00 00    	jmp    *0x9b4e(%rip)        # be98 <setsockopt@GLIBC_2.2.5>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <clock_gettime@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 46 9b 00 00    	jmp    *0x9b46(%rip)        # bea0 <clock_gettime@GLIBC_2.17>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <fclose@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 3e 9b 00 00    	jmp    *0x9b3e(%rip)        # bea8 <fclose@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <strlen@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 36 9b 00 00    	jmp    *0x9b36(%rip)        # beb0 <strlen@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <__stack_chk_fail@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 2e 9b 00 00    	jmp    *0x9b2e(%rip)        # beb8 <__stack_chk_fail@GLIBC_2.4>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <io_uring_submit@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 26 9b 00 00    	jmp    *0x9b26(%rip)        # bec0 <io_uring_submit@LIBURING_2.0>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <nanosleep@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 1e 9b 00 00    	jmp    *0x9b1e(%rip)        # bec8 <nanosleep@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <strrchr@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 16 9b 00 00    	jmp    *0x9b16(%rip)        # bed0 <strrchr@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <fputs@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 0e 9b 00 00    	jmp    *0x9b0e(%rip)        # bed8 <fputs@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <close@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 06 9b 00 00    	jmp    *0x9b06(%rip)        # bee0 <close@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <strtok_r@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 fe 9a 00 00    	jmp    *0x9afe(%rip)        # bee8 <strtok_r@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <read@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 f6 9a 00 00    	jmp    *0x9af6(%rip)        # bef0 <read@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <calloc@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 ee 9a 00 00    	jmp    *0x9aee(%rip)        # bef8 <calloc@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <strcmp@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 e6 9a 00 00    	jmp    *0x9ae6(%rip)        # bf00 <strcmp@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <__memcpy_chk@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 de 9a 00 00    	jmp    *0x9ade(%rip)        # bf08 <__memcpy_chk@GLIBC_2.3.4>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <stat@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 d6 9a 00 00    	jmp    *0x9ad6(%rip)        # bf10 <stat@GLIBC_2.33>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <memcpy@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 ce 9a 00 00    	jmp    *0x9ace(%rip)        # bf18 <memcpy@GLIBC_2.14>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <io_uring_queue_init@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 c6 9a 00 00    	jmp    *0x9ac6(%rip)        # bf20 <io_uring_queue_init@LIBURING_2.0>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <eventfd_write@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 be 9a 00 00    	jmp    *0x9abe(%rip)        # bf28 <eventfd_write@GLIBC_2.7>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <malloc@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 b6 9a 00 00    	jmp    *0x9ab6(%rip)        # bf30 <malloc@GLIBC_2.2.5>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <listen@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 ae 9a 00 00    	jmp    *0x9aae(%rip)        # bf38 <listen@GLIBC_2.2.5>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <__strcpy_chk@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 a6 9a 00 00    	jmp    *0x9aa6(%rip)        # bf40 <__strcpy_chk@GLIBC_2.3.4>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <__io_uring_get_cqe@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 9e 9a 00 00    	jmp    *0x9a9e(%rip)        # bf48 <__io_uring_get_cqe@LIBURING_2.0>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <__printf_chk@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 96 9a 00 00    	jmp    *0x9a96(%rip)        # bf50 <__printf_chk@GLIBC_2.3.4>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <bind@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 8e 9a 00 00    	jmp    *0x9a8e(%rip)        # bf58 <bind@GLIBC_2.2.5>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <pthread_create@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 86 9a 00 00    	jmp    *0x9a86(%rip)        # bf60 <pthread_create@GLIBC_2.34>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <open@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 7e 9a 00 00    	jmp    *0x9a7e(%rip)        # bf68 <open@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <fopen@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 76 9a 00 00    	jmp    *0x9a76(%rip)        # bf70 <fopen@GLIBC_2.2.5>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <perror@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 6e 9a 00 00    	jmp    *0x9a6e(%rip)        # bf78 <perror@GLIBC_2.2.5>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <exit@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 66 9a 00 00    	jmp    *0x9a66(%rip)        # bf80 <exit@GLIBC_2.2.5>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <eventfd@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 5e 9a 00 00    	jmp    *0x9a5e(%rip)        # bf88 <eventfd@GLIBC_2.7>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <fwrite@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 56 9a 00 00    	jmp    *0x9a56(%rip)        # bf90 <fwrite@GLIBC_2.2.5>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <__fprintf_chk@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 4e 9a 00 00    	jmp    *0x9a4e(%rip)        # bf98 <__fprintf_chk@GLIBC_2.3.4>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <io_uring_register_eventfd@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 46 9a 00 00    	jmp    *0x9a46(%rip)        # bfa0 <io_uring_register_eventfd@LIBURING_2.0>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <pthread_join@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 3e 9a 00 00    	jmp    *0x9a3e(%rip)        # bfa8 <pthread_join@GLIBC_2.34>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <strerror@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 36 9a 00 00    	jmp    *0x9a36(%rip)        # bfb0 <strerror@GLIBC_2.2.5>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <pthread_mutex_init@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 2e 9a 00 00    	jmp    *0x9a2e(%rip)        # bfb8 <pthread_mutex_init@GLIBC_2.2.5>
    258a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002590 <__ctype_tolower_loc@plt>:
    2590:	f3 0f 1e fa          	endbr64
    2594:	ff 25 26 9a 00 00    	jmp    *0x9a26(%rip)        # bfc0 <__ctype_tolower_loc@GLIBC_2.3>
    259a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025a0 <__sprintf_chk@plt>:
    25a0:	f3 0f 1e fa          	endbr64
    25a4:	ff 25 1e 9a 00 00    	jmp    *0x9a1e(%rip)        # bfc8 <__sprintf_chk@GLIBC_2.3.4>
    25aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025b0 <socket@plt>:
    25b0:	f3 0f 1e fa          	endbr64
    25b4:	ff 25 16 9a 00 00    	jmp    *0x9a16(%rip)        # bfd0 <socket@GLIBC_2.2.5>
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
    25d6:	48 8d 3d 67 6c 00 00 	lea    0x6c67(%rip),%rdi        # 9244 <_IO_stdin_used+0x244>
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

    sock = socket(PF_INET, SOCK_STREAM, 0);


    if (sock == -1)
        fatal_error("socket()");
    2616:	48 8d 3d 54 6b 00 00 	lea    0x6b54(%rip),%rdi        # 9171 <_IO_stdin_used+0x171>
    261d:	e8 9e ff ff ff       	call   25c0 <fatal_error>

    int enable = 1;
    if (setsockopt(sock,
                   SOL_SOCKET, SO_REUSEADDR,
                   &enable, sizeof(int)) < 0)
        fatal_error("setsockopt(SO_REUSEADDR)");
    2622:	48 8d 3d 51 6b 00 00 	lea    0x6b51(%rip),%rdi        # 917a <_IO_stdin_used+0x17a>
    2629:	e8 92 ff ff ff       	call   25c0 <fatal_error>
    262e:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2636:	0f 0b                	ud2
    2638:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2640:	0f 0b                	ud2
          break;
        }
        printf("Received wait finished\n");
        struct Request *req = (struct Request *) cqe->user_data;
        if (ret < 0)
            fatal_error("io_uring_wait_cqe");
    2642:	48 8d 3d b4 6b 00 00 	lea    0x6bb4(%rip),%rdi        # 91fd <_IO_stdin_used+0x1fd>
    2649:	e8 72 ff ff ff       	call   25c0 <fatal_error>
    264e:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2656:	0f 0b                	ud2
        fatal_error("bind()");
    2658:	48 8d 3d 34 6b 00 00 	lea    0x6b34(%rip),%rdi        # 9193 <_IO_stdin_used+0x193>
    265f:	e8 5c ff ff ff       	call   25c0 <fatal_error>
      fatal_error("listen()");
    2664:	48 8d 3d 2f 6b 00 00 	lea    0x6b2f(%rip),%rdi        # 919a <_IO_stdin_used+0x19a>
    266b:	e8 50 ff ff ff       	call   25c0 <fatal_error>
    2670:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2678:	0f 0b                	ud2
    printf("in send io read my identity %s my ring is %d other io is %d\n", data->identity, data->my_io, data->other_io);
    void * reply;
    
    void * _reply = bufferrecv(data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply); 
    struct Buffer *bufferreply = _reply;
    struct NewSocketMessage *msg = bufferreply->data;
    267a:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    2682:	0f 0b                	ud2
    2684:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    268e:	66 90                	xchg   %ax,%ax

0000000000002690 <main>:
    }


  return 0;
}
int main() {
    2690:	f3 0f 1e fa          	endbr64
    2694:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2696:	48 8d 3d 8b 71 00 00 	lea    0x718b(%rip),%rdi        # 9828 <_IO_stdin_used+0x828>
    269d:	41 56                	push   %r14
    269f:	41 55                	push   %r13
    26a1:	41 54                	push   %r12
    26a3:	4c 8d 25 0d 6d 00 00 	lea    0x6d0d(%rip),%r12        # 93b7 <_IO_stdin_used+0x3b7>
    26aa:	55                   	push   %rbp
    26ab:	53                   	push   %rbx
    26ac:	48 81 ec 38 01 00 00 	sub    $0x138,%rsp
    26b3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    26bc:	48 89 84 24 28 01 00 00 	mov    %rax,0x128(%rsp)
    26c4:	48 8d 05 05 23 00 00 	lea    0x2305(%rip),%rax        # 49d0 <barriered_reset>
    26cb:	66 48 0f 6e f0       	movq   %rax,%xmm6
    26d0:	0f 16 35 81 95 00 00 	movhps 0x9581(%rip),%xmm6        # bc58 <__do_global_dtors_aux_fini_array_entry+0x8>
    26d7:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    26df:	e8 4c fc ff ff       	call   2330 <puts@plt>
    26e4:	bf 0a 00 00 00       	mov    $0xa,%edi
    26e9:	e8 22 fc ff ff       	call   2310 <putchar@plt>
    26ee:	ba 01 00 00 00       	mov    $0x1,%edx
    26f3:	48 8d 35 b5 6b 00 00 	lea    0x6bb5(%rip),%rsi        # 92af <_IO_stdin_used+0x2af>
    26fa:	31 c0                	xor    %eax,%eax
    26fc:	bf 01 00 00 00       	mov    $0x1,%edi
    2701:	e8 aa fd ff ff       	call   24b0 <__printf_chk@plt>
    2706:	ba 06 00 00 00       	mov    $0x6,%edx
    270b:	48 8d 35 ad 6b 00 00 	lea    0x6bad(%rip),%rsi        # 92bf <_IO_stdin_used+0x2bf>
    2712:	31 c0                	xor    %eax,%eax
    2714:	bf 01 00 00 00       	mov    $0x1,%edi
    2719:	e8 92 fd ff ff       	call   24b0 <__printf_chk@plt>
    271e:	ba 03 00 00 00       	mov    $0x3,%edx
    2723:	48 8d 35 aa 6b 00 00 	lea    0x6baa(%rip),%rsi        # 92d4 <_IO_stdin_used+0x2d4>
    272a:	31 c0                	xor    %eax,%eax
    272c:	bf 01 00 00 00       	mov    $0x1,%edi
    2731:	e8 7a fd ff ff       	call   24b0 <__printf_chk@plt>
    2736:	ba 02 00 00 00       	mov    $0x2,%edx
    273b:	48 8d 35 a2 6b 00 00 	lea    0x6ba2(%rip),%rsi        # 92e4 <_IO_stdin_used+0x2e4>
    2742:	31 c0                	xor    %eax,%eax
    2744:	bf 01 00 00 00       	mov    $0x1,%edi
    2749:	e8 62 fd ff ff       	call   24b0 <__printf_chk@plt>
    274e:	48 8d 3d a5 6b 00 00 	lea    0x6ba5(%rip),%rdi        # 92fa <_IO_stdin_used+0x2fa>
    2755:	e8 d6 fb ff ff       	call   2330 <puts@plt>
    275a:	ba 02 00 00 00       	mov    $0x2,%edx
    275f:	48 8d 35 b0 6b 00 00 	lea    0x6bb0(%rip),%rsi        # 9316 <_IO_stdin_used+0x316>
    2766:	31 c0                	xor    %eax,%eax
    2768:	bf 01 00 00 00       	mov    $0x1,%edi
    276d:	e8 3e fd ff ff       	call   24b0 <__printf_chk@plt>
    2772:	ba 0b 00 00 00       	mov    $0xb,%edx
    2777:	48 8d 35 b2 6b 00 00 	lea    0x6bb2(%rip),%rsi        # 9330 <_IO_stdin_used+0x330>
    277e:	31 c0                	xor    %eax,%eax
    2780:	bf 01 00 00 00       	mov    $0x1,%edi
    2785:	e8 26 fd ff ff       	call   24b0 <__printf_chk@plt>
    278a:	ba 02 00 00 00       	mov    $0x2,%edx
    278f:	48 8d 35 ae 6b 00 00 	lea    0x6bae(%rip),%rsi        # 9344 <_IO_stdin_used+0x344>
    2796:	31 c0                	xor    %eax,%eax
    2798:	bf 01 00 00 00       	mov    $0x1,%edi
    279d:	e8 0e fd ff ff       	call   24b0 <__printf_chk@plt>
    27a2:	ba 01 00 00 00       	mov    $0x1,%edx
    27a7:	48 8d 35 a7 6b 00 00 	lea    0x6ba7(%rip),%rsi        # 9355 <_IO_stdin_used+0x355>
    27ae:	31 c0                	xor    %eax,%eax
    27b0:	bf 01 00 00 00       	mov    $0x1,%edi
    27b5:	e8 f6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27ba:	ba 02 00 00 00       	mov    $0x2,%edx
    27bf:	48 8d 35 a7 6b 00 00 	lea    0x6ba7(%rip),%rsi        # 936d <_IO_stdin_used+0x36d>
    27c6:	31 c0                	xor    %eax,%eax
    27c8:	bf 01 00 00 00       	mov    $0x1,%edi
    27cd:	e8 de fc ff ff       	call   24b0 <__printf_chk@plt>
    27d2:	ba 01 00 00 00       	mov    $0x1,%edx
    27d7:	48 8d 35 b2 70 00 00 	lea    0x70b2(%rip),%rsi        # 9890 <_IO_stdin_used+0x890>
    27de:	31 c0                	xor    %eax,%eax
    27e0:	bf 01 00 00 00       	mov    $0x1,%edi
    27e5:	e8 c6 fc ff ff       	call   24b0 <__printf_chk@plt>
    27ea:	ba 01 00 00 00       	mov    $0x1,%edx
    27ef:	48 8d 35 ca 70 00 00 	lea    0x70ca(%rip),%rsi        # 98c0 <_IO_stdin_used+0x8c0>
    27f6:	31 c0                	xor    %eax,%eax
    27f8:	bf 01 00 00 00       	mov    $0x1,%edi
    27fd:	e8 ae fc ff ff       	call   24b0 <__printf_chk@plt>
    2802:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2807:	48 8d 35 7b 6b 00 00 	lea    0x6b7b(%rip),%rsi        # 9389 <_IO_stdin_used+0x389>
    280e:	31 c0                	xor    %eax,%eax
    2810:	bf 01 00 00 00       	mov    $0x1,%edi
    2815:	e8 96 fc ff ff       	call   24b0 <__printf_chk@plt>
    281a:	ba 05 00 00 00       	mov    $0x5,%edx
    281f:	48 8d 35 7d 6b 00 00 	lea    0x6b7d(%rip),%rsi        # 93a3 <_IO_stdin_used+0x3a3>
    2826:	31 c0                	xor    %eax,%eax
    2828:	bf 01 00 00 00       	mov    $0x1,%edi
    282d:	e8 7e fc ff ff       	call   24b0 <__printf_chk@plt>
    2832:	48 8d 3d bc 68 00 00 	lea    0x68bc(%rip),%rdi        # 90f5 <_IO_stdin_used+0xf5>
    2839:	e8 f2 fa ff ff       	call   2330 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
    283e:	be 18 00 00 00       	mov    $0x18,%esi
    2843:	bf 01 00 00 00       	mov    $0x1,%edi
    2848:	e8 b3 fb ff ff       	call   2400 <calloc@plt>
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    284d:	be 18 00 00 00       	mov    $0x18,%esi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
    2852:	45 31 ff             	xor    %r15d,%r15d
  int cc = 0; 
    2855:	45 31 f6             	xor    %r14d,%r14d
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2858:	bf 03 00 00 00       	mov    $0x3,%edi
  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
    285d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2862:	e8 99 fb ff ff       	call   2400 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2867:	be 20 01 00 00       	mov    $0x120,%esi
    286c:	bf 0b 00 00 00       	mov    $0xb,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2871:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2879:	e8 82 fb ff ff       	call   2400 <calloc@plt>
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    287e:	be 28 00 00 00       	mov    $0x28,%esi
    2883:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2888:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    288d:	e8 6e fb ff ff       	call   2400 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    2892:	be 28 00 00 00       	mov    $0x28,%esi
    2897:	bf 79 00 00 00       	mov    $0x79,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    289c:	48 89 84 24 e8 00 00 00 	mov    %rax,0xe8(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28a4:	e8 57 fb ff ff       	call   2400 <calloc@plt>
    28a9:	48 89 84 24 f0 00 00 00 	mov    %rax,0xf0(%rsp)
  for (int x = 0 ; x < total_threads; x++) {
    28b1:	48 89 c3             	mov    %rax,%rbx
int main() {
    28b4:	49 89 dd             	mov    %rbx,%r13
    for (int y = 0 ; y < total_threads; y++) {
    28b7:	31 ed                	xor    %ebp,%ebp
    28b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    28c0:	41 8d 14 2e          	lea    (%r14,%rbp,1),%edx
    28c4:	41 89 e8             	mov    %ebp,%r8d
    28c7:	44 89 f9             	mov    %r15d,%ecx
    28ca:	4c 89 e6             	mov    %r12,%rsi
    28cd:	bf 01 00 00 00       	mov    $0x1,%edi
    28d2:	31 c0                	xor    %eax,%eax
    28d4:	83 c5 01             	add    $0x1,%ebp
    28d7:	e8 d4 fb ff ff       	call   24b0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    28dc:	4c 89 ef             	mov    %r13,%rdi
    28df:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    28e1:	49 83 c5 28          	add    $0x28,%r13
      pthread_mutex_init(&swapmutex[cc++], NULL);
    28e5:	e8 96 fc ff ff       	call   2580 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    28ea:	83 fd 0b             	cmp    $0xb,%ebp
    28ed:	75 d1                	jne    28c0 <main+0x230>
    28ef:	41 83 c6 0b          	add    $0xb,%r14d
  for (int x = 0 ; x < total_threads; x++) {
    28f3:	41 83 c7 01          	add    $0x1,%r15d
    28f7:	48 81 c3 b8 01 00 00 	add    $0x1b8,%rbx
    28fe:	41 83 fe 79          	cmp    $0x79,%r14d
    2902:	75 b0                	jne    28b4 <main+0x224>
    2904:	ba 06 00 00 00       	mov    $0x6,%edx
    2909:	48 8d 35 b7 6a 00 00 	lea    0x6ab7(%rip),%rsi        # 93c7 <_IO_stdin_used+0x3c7>
    2910:	bf 01 00 00 00       	mov    $0x1,%edi
    2915:	31 c0                	xor    %eax,%eax
    2917:	e8 94 fb ff ff       	call   24b0 <__printf_chk@plt>
    291c:	ba 0c 00 00 00       	mov    $0xc,%edx
    2921:	48 8d 35 b5 6a 00 00 	lea    0x6ab5(%rip),%rsi        # 93dd <_IO_stdin_used+0x3dd>
    2928:	31 c0                	xor    %eax,%eax
    292a:	bf 01 00 00 00       	mov    $0x1,%edi
    292f:	e8 7c fb ff ff       	call   24b0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2934:	be 10 00 00 00       	mov    $0x10,%esi
    2939:	bf 0c 00 00 00       	mov    $0xc,%edi
    293e:	e8 bd fa ff ff       	call   2400 <calloc@plt>
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2943:	be 10 00 00 00       	mov    $0x10,%esi
    2948:	bf 02 00 00 00       	mov    $0x2,%edi
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    294d:	48 89 c5             	mov    %rax,%rbp
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2950:	e8 ab fa ff ff       	call   2400 <calloc@plt>


  int snapshot_limit = 100;
  for (int x = 0 ; x < io_threads; x++) {
    iobuffers[x].count = buffer_size;
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2955:	be 00 01 00 00       	mov    $0x100,%esi
    295a:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int y = 0 ; y < buffer_size; y++) {
      iobuffers[x].buffer[y].available = 0;
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    295f:	49 89 ee             	mov    %rbp,%r14
    iobuffers[x].count = buffer_size;
    2962:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2968:	49 89 c4             	mov    %rax,%r12
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    296b:	e8 90 fa ff ff       	call   2400 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2970:	be 20 00 00 00       	mov    $0x20,%esi
    2975:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    297a:	49 89 44 24 08       	mov    %rax,0x8(%r12)
    297f:	49 89 c5             	mov    %rax,%r13
      iobuffers[x].buffer[y].available = 0;
    2982:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    298c:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2996:	e8 65 fa ff ff       	call   2400 <calloc@plt>
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    299b:	be 00 01 00 00       	mov    $0x100,%esi
    29a0:	bf 01 00 00 00       	mov    $0x1,%edi
    iobuffers[x].count = buffer_size;
    29a5:	41 c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%r12)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29ae:	49 89 85 88 00 00 00 	mov    %rax,0x88(%r13)
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29b5:	e8 46 fa ff ff       	call   2400 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29ba:	be 20 00 00 00       	mov    $0x20,%esi
    29bf:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29c4:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    29c9:	49 89 c5             	mov    %rax,%r13
    29cc:	4c 8d a5 c0 00 00 00 	lea    0xc0(%rbp),%r12
      iobuffers[x].buffer[y].available = 0;
    29d3:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    29dd:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29e7:	e8 14 fa ff ff       	call   2400 <calloc@plt>
    29ec:	48 89 ac 24 c8 00 00 00 	mov    %rbp,0xc8(%rsp)
    29f4:	49 89 85 88 00 00 00 	mov    %rax,0x88(%r13)
    }
  }
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    29fb:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a02:	be 00 01 00 00       	mov    $0x100,%esi
    2a07:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2a0c:	49 83 c6 10          	add    $0x10,%r14
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a10:	e8 eb f9 ff ff       	call   2400 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a15:	be 20 00 00 00       	mov    $0x20,%esi
    2a1a:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a1f:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    2a23:	48 89 c3             	mov    %rax,%rbx
      buffers[x].buffer[y].available = 0;
    2a26:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2a30:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a3a:	e8 c1 f9 ff ff       	call   2400 <calloc@plt>
    2a3f:	48 89 83 88 00 00 00 	mov    %rax,0x88(%rbx)
  for (int x = 0 ; x < buffers_required; x++) {
    2a46:	4d 39 f4             	cmp    %r14,%r12
    2a49:	75 b0                	jne    29fb <main+0x36b>
  int iocur_buffer = 0;
  int swap = 0;
  int groupcount = 0;
  int seq = 0;
  int seqs[] = {1, 3, 6};
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a4b:	be 08 00 00 00       	mov    $0x8,%esi
    2a50:	bf 64 00 00 00       	mov    $0x64,%edi
  struct Global *global = calloc(1, sizeof(struct Global));
  global->request_group_sync = -1;
  global->protected_state = global_protected_state;
    2a55:	45 31 ff             	xor    %r15d,%r15d
  int dataid = 0;
    2a58:	31 db                	xor    %ebx,%ebx
  int seqs[] = {1, 3, 6};
    2a5a:	48 8b 05 4f 74 00 00 	mov    0x744f(%rip),%rax        # 9eb0 <_IO_stdin_used+0xeb0>
              }
              printf("Creating friend mailbox %d other is %d\n", b, mailboxes[b].other);
              data[0].messages = messages;
              data[1].messages = messages2;
              data[0].messages_limit = messages_limit;
              data[0].messages_count = 0;
    2a61:	4d 89 fd             	mov    %r15,%r13
  int seqs[] = {1, 3, 6};
    2a64:	c7 84 24 20 01 00 00 06 00 00 00 	movl   $0x6,0x120(%rsp)
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a6f:	4c 8d b4 24 18 01 00 00 	lea    0x118(%rsp),%r14
              data[0].messages_count = 0;
    2a77:	41 89 df             	mov    %ebx,%r15d
  int seqs[] = {1, 3, 6};
    2a7a:	48 89 84 24 18 01 00 00 	mov    %rax,0x118(%rsp)
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a82:	e8 79 f9 ff ff       	call   2400 <calloc@plt>
  struct Global *global = calloc(1, sizeof(struct Global));
    2a87:	be 10 00 00 00       	mov    $0x10,%esi
    2a8c:	bf 01 00 00 00       	mov    $0x1,%edi
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a91:	48 89 84 24 c0 00 00 00 	mov    %rax,0xc0(%rsp)
  struct Global *global = calloc(1, sizeof(struct Global));
    2a99:	e8 62 f9 ff ff       	call   2400 <calloc@plt>
  int swap = 0;
    2a9e:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  struct Global *global = calloc(1, sizeof(struct Global));
    2aa6:	49 89 c3             	mov    %rax,%r11
  global->request_group_sync = -1;
    2aa9:	c7 00 ff ff ff ff    	movl   $0xffffffff,(%rax)
  global->protected_state = global_protected_state;
    2aaf:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  int iocur_buffer = 0;
    2ab4:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
  global->protected_state = global_protected_state;
    2abc:	49 89 43 08          	mov    %rax,0x8(%r11)
  for (int k = 0 ; k < group_count ; k++) {
    2ac0:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
  int cur_buffer = 0;
    2ac8:	c7 84 24 84 00 00 00 00 00 00 00 	movl   $0x0,0x84(%rsp)
    2ad3:	48 89 84 24 d8 00 00 00 	mov    %rax,0xd8(%rsp)
  global->protected_state = global_protected_state;
    2adb:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  int curcpu = 0;
    2ae3:	c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rsp)
              data[0].messages_count = 0;
    2aee:	4c 89 9c 24 e0 00 00 00 	mov    %r11,0xe0(%rsp)
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2af6:	be 00 01 00 00       	mov    $0x100,%esi
    2afb:	bf 01 00 00 00       	mov    $0x1,%edi
    2b00:	44 89 6c 24 50       	mov    %r13d,0x50(%rsp)
    2b05:	e8 f6 f8 ff ff       	call   2400 <calloc@plt>
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2b0a:	be 08 00 00 00       	mov    $0x8,%esi
    2b0f:	bf 64 00 00 00       	mov    $0x64,%edi
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2b14:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2b19:	e8 e2 f8 ff ff       	call   2400 <calloc@plt>
    all_groups[groupcount++] = group_data;
    2b1e:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2b23:	48 8b 9c 24 c0 00 00 00 	mov    0xc0(%rsp),%rbx
        thread_data[x].protected_state = &protected_state[k];
    2b2b:	48 c7 44 24 68 00 00 00 00 	movq   $0x0,0x68(%rsp)
    2b34:	48 89 ac 24 f8 00 00 00 	mov    %rbp,0xf8(%rsp)
    group_data->threads = group_threads;
    2b3c:	48 89 82 88 00 00 00 	mov    %rax,0x88(%rdx)
    group_data->global = global;
    2b43:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
    all_groups[groupcount++] = group_data;
    2b4b:	4a 89 14 eb          	mov    %rdx,(%rbx,%r13,8)
    group_data->thread_count = threads_per_group * group_count;
    2b4f:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    group_data->global = global;
    2b54:	48 89 82 98 00 00 00 	mov    %rax,0x98(%rdx)
    group_data->seq = seqs[seq++ % 3];
    2b5b:	43 8b 04 ae          	mov    (%r14,%r13,4),%eax
    group_data->thread_count = threads_per_group * group_count;
    2b5f:	c7 82 90 00 00 00 06 00 00 00 	movl   $0x6,0x90(%rdx)
    group_data->seq = seqs[seq++ % 3];
    2b69:	89 82 a0 00 00 00    	mov    %eax,0xa0(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2b6f:	4b 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%rax
    2b74:	48 c1 e0 06          	shl    $0x6,%rax
    2b78:	48 89 94 24 00 01 00 00 	mov    %rdx,0x100(%rsp)
    2b80:	4c 8d 0c 18          	lea    (%rax,%rbx,1),%r9
    2b84:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2b89:	48 89 9c 24 d0 00 00 00 	mov    %rbx,0xd0(%rsp)
    2b91:	43 8d 5c 2d 00       	lea    0x0(%r13,%r13,1),%ebx
    2b96:	4c 89 b4 24 08 01 00 00 	mov    %r14,0x108(%rsp)
    2b9e:	4d 89 ee             	mov    %r13,%r14
    2ba1:	41 89 dd             	mov    %ebx,%r13d
    2ba4:	48 c1 e0 04          	shl    $0x4,%rax
    2ba8:	48 01 e8             	add    %rbp,%rax
    2bab:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2bb0:	48 63 84 24 84 00 00 00 	movslq 0x84(%rsp),%rax
    2bb8:	48 c1 e0 04          	shl    $0x4,%rax
    2bbc:	48 01 e8             	add    %rbp,%rax
    2bbf:	48 89 84 24 a0 00 00 00 	mov    %rax,0xa0(%rsp)
      thread_data[x].all_groups = all_groups;
    2bc7:	48 8b 84 24 c0 00 00 00 	mov    0xc0(%rsp),%rax
      thread_data[x].group = k;
    2bcf:	8b 54 24 50          	mov    0x50(%rsp),%edx
    2bd3:	44 89 e9             	mov    %r13d,%ecx
    2bd6:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].group_data = group_data;
    2bdb:	48 8b 9c 24 00 01 00 00 	mov    0x100(%rsp),%rbx
    2be3:	48 8d 35 fe 6c 00 00 	lea    0x6cfe(%rip),%rsi        # 98e8 <_IO_stdin_used+0x8e8>
      thread_data[x].global = global;
    2bea:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].all_groups = all_groups;
    2bef:	49 89 81 e8 00 00 00 	mov    %rax,0xe8(%r9)
      thread_data[x].global = global;
    2bf6:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
      thread_data[x].group_data = group_data;
    2bfe:	49 89 99 e0 00 00 00 	mov    %rbx,0xe0(%r9)
      thread_data[x].group = k;
    2c05:	41 89 91 f0 00 00 00 	mov    %edx,0xf0(%r9)
      thread_data[x].global = global;
    2c0c:	49 89 81 f8 00 00 00 	mov    %rax,0xf8(%r9)
    2c13:	31 c0                	xor    %eax,%eax
    2c15:	e8 96 f8 ff ff       	call   24b0 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c1a:	be 08 00 00 00       	mov    $0x8,%esi
    2c1f:	bf 02 00 00 00       	mov    $0x2,%edi
    2c24:	e8 d7 f7 ff ff       	call   2400 <calloc@plt>
      group_data->threads[group_thread_count++] = &thread_data[x];  
    2c29:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2c2e:	be 80 00 00 00       	mov    $0x80,%esi
    2c33:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c38:	48 89 c5             	mov    %rax,%rbp
      group_data->threads[group_thread_count++] = &thread_data[x];  
    2c3b:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    2c42:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    2c47:	4c 89 0c 18          	mov    %r9,(%rax,%rbx,1)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2c4b:	e8 b0 f7 ff ff       	call   2400 <calloc@plt>
      if (x % 2 == 1) {
    2c50:	45 89 e8             	mov    %r13d,%r8d
    2c53:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2c58:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2c5c:	48 89 c3             	mov    %rax,%rbx
      if (x % 2 == 1) {
    2c5f:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2c64:	0f 84 cc 0a 00 00    	je     3736 <main+0x10a6>
        other = abs(x - 1) % total_threads;
    2c6a:	41 8d 45 ff          	lea    -0x1(%r13),%eax
    2c6e:	41 8d 7d 01          	lea    0x1(%r13),%edi
        my_thread_data[0] = &thread_data[other]; 
    2c72:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
        other = abs(x - 1) % total_threads;
    2c76:	48 89 c1             	mov    %rax,%rcx
        my_thread_data[0] = &thread_data[other]; 
    2c79:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    2c7e:	89 bc 24 88 00 00 00 	mov    %edi,0x88(%rsp)
    2c85:	48 c1 e2 05          	shl    $0x5,%rdx
    2c89:	48 01 c2             	add    %rax,%rdx
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2c8c:	48 8d 45 08          	lea    0x8(%rbp),%rax
    2c90:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2c95:	4c 89 c8             	mov    %r9,%rax
        my_thread_data[1] = &thread_data[x]; 
    2c98:	48 89 45 08          	mov    %rax,0x8(%rbp)
        thread_data[x].protected_state = &protected_state[k];
    2c9c:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    2ca4:	48 8d 35 6d 6c 00 00 	lea    0x6c6d(%rip),%rsi        # 9918 <_IO_stdin_used+0x918>
    2cab:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].thread_index = 1;
    2cb0:	45 89 41 04          	mov    %r8d,0x4(%r9)
        thread_data[x].protected_state = &protected_state[k];
    2cb4:	49 89 41 48          	mov    %rax,0x48(%r9)
    2cb8:	31 c0                	xor    %eax,%eax
        my_thread_data[0] = &thread_data[other]; 
    2cba:	48 89 55 00          	mov    %rdx,0x0(%rbp)
    2cbe:	44 89 ea             	mov    %r13d,%edx
        thread_data[x].protected_state = &protected_state[k];
    2cc1:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2cc6:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2cca:	e8 e1 f7 ff ff       	call   24b0 <__printf_chk@plt>
      thread_data[x].other = other;
    2ccf:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2cd3:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2cd8:	31 c0                	xor    %eax,%eax
    2cda:	44 89 ea             	mov    %r13d,%edx
    2cdd:	48 8d 35 64 6c 00 00 	lea    0x6c64(%rip),%rsi        # 9948 <_IO_stdin_used+0x948>
    2ce4:	bf 01 00 00 00       	mov    $0x1,%edi
    2ce9:	41 89 89 c0 00 00 00 	mov    %ecx,0xc0(%r9)
    2cf0:	8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%ecx
    2cf7:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2cfc:	e8 af f7 ff ff       	call   24b0 <__printf_chk@plt>
        if (x < thread_count) {
    2d01:	41 83 fd 01          	cmp    $0x1,%r13d
    2d05:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2d0a:	0f 8f 7a 13 00 00    	jg     408a <main+0x19fa>
          CPU_SET(curcpu, sendercpu);
    2d10:	48 63 84 24 80 00 00 00 	movslq 0x80(%rsp),%rax
    2d18:	48 89 c7             	mov    %rax,%rdi
    2d1b:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2d21:	77 12                	ja     2d35 <main+0x6a5>
    2d23:	48 c1 e8 06          	shr    $0x6,%rax
    2d27:	ba 01 00 00 00       	mov    $0x1,%edx
    2d2c:	89 f9                	mov    %edi,%ecx
    2d2e:	48 d3 e2             	shl    %cl,%rdx
    2d31:	48 09 14 c3          	or     %rdx,(%rbx,%rax,8)
          curcpu += 2;
    2d35:	83 84 24 80 00 00 00 02 	addl   $0x2,0x80(%rsp)
      thread_data[x].real_thread_index = x;
    2d3d:	45 89 69 08          	mov    %r13d,0x8(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2d41:	be 10 00 00 00       	mov    $0x10,%esi
    2d46:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].swapmutex = swapmutex;
    2d4b:	48 8b 84 24 f0 00 00 00 	mov    0xf0(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    2d53:	49 89 99 b8 00 00 00 	mov    %rbx,0xb8(%r9)
      thread_data[x].swapmutex = swapmutex;
    2d5a:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2d61:	48 8b 84 24 e8 00 00 00 	mov    0xe8(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2d69:	49 89 69 18          	mov    %rbp,0x18(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2d6d:	31 ed                	xor    %ebp,%ebp
      thread_data[x].mswapmutex = mswapmutex;
    2d6f:	49 89 81 d8 00 00 00 	mov    %rax,0xd8(%r9)
      thread_data[x].all_threads = thread_data;
    2d76:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
      thread_data[x].kind = KERNEL_THREAD;
    2d7b:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].all_threads = thread_data;
    2d82:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2d86:	48 8b 05 2b 71 00 00 	mov    0x712b(%rip),%rax        # 9eb8 <_IO_stdin_used+0xeb8>
      thread_data[x].task_count = total_barrier_count;
    2d8d:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].group_count = group_count;
    2d95:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].thread_count = 2;
    2d9c:	48 8b 05 1d 71 00 00 	mov    0x711d(%rip),%rax        # 9ec0 <_IO_stdin_used+0xec0>
      thread_data[x].task_count = total_barrier_count;
    2da3:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].thread_count = 2;
    2da8:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2dac:	e8 4f f6 ff ff       	call   2400 <calloc@plt>
    2db1:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2db6:	be 10 00 00 00       	mov    $0x10,%esi
    2dbb:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2dc0:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2dc4:	e8 37 f6 ff ff       	call   2400 <calloc@plt>
    2dc9:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2dce:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2dd3:	66 0f 6f 3d a5 70 00 00 	movdqa 0x70a5(%rip),%xmm7        # 9e80 <_IO_stdin_used+0xe80>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2ddb:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2de0:	49 89 41 78          	mov    %rax,0x78(%r9)
      thread_data[x].timestamp_count = 0;
    2de4:	41 0f 11 b9 88 00 00 00 	movups %xmm7,0x88(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2dec:	e8 0f f6 ff ff       	call   2400 <calloc@plt>
    2df1:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2df6:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2dfb:	66 0f 6f 35 7d 70 00 00 	movdqa 0x707d(%rip),%xmm6        # 9e80 <_IO_stdin_used+0xe80>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e03:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2e08:	49 89 81 98 00 00 00 	mov    %rax,0x98(%r9)
      thread_data[x].task_timestamp_count = 0;
    2e0f:	41 0f 11 b1 a0 00 00 00 	movups %xmm6,0xa0(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e17:	e8 e4 f5 ff ff       	call   2400 <calloc@plt>
        thread_data[x].tasks = barriers;
    2e1c:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
            data[0].messages_count = 0;
    2e21:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
    2e26:	45 89 fd             	mov    %r15d,%r13d
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2e29:	48 63 bc 24 88 00 00 00 	movslq 0x88(%rsp),%rdi
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e31:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2e34:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2e38:	48 89 fb             	mov    %rdi,%rbx
    2e3b:	48 69 ff ab aa aa 2a 	imul   $0x2aaaaaab,%rdi,%rdi
            data[0].messages_count = 0;
    2e42:	4c 89 4c 24 48       	mov    %r9,0x48(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2e47:	89 d8                	mov    %ebx,%eax
    2e49:	c1 f8 1f             	sar    $0x1f,%eax
    2e4c:	48 c1 ef 20          	shr    $0x20,%rdi
    2e50:	29 c7                	sub    %eax,%edi
    2e52:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2e55:	01 c0                	add    %eax,%eax
    2e57:	29 c3                	sub    %eax,%ebx
            data[0].messages_count = 0;
    2e59:	89 9c 24 8c 00 00 00 	mov    %ebx,0x8c(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2e60:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2e63:	be 00 01 00 00       	mov    $0x100,%esi
    2e68:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e6d:	45 31 ff             	xor    %r15d,%r15d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2e70:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2e75:	48 c1 e0 09          	shl    $0x9,%rax
    2e79:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
    2e7d:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2e82:	48 8d 05 07 1b 00 00 	lea    0x1b07(%rip),%rax        # 4990 <do_protected_write>
    2e89:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2e90:	e8 6b f5 ff ff       	call   2400 <calloc@plt>
    2e95:	8b 74 24 58          	mov    0x58(%rsp),%esi
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2e99:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ea0:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ea3:	85 f6                	test   %esi,%esi
    2ea5:	0f 84 89 01 00 00    	je     3034 <main+0x9a4>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2eab:	8b 44 24 18          	mov    0x18(%rsp),%eax
    2eaf:	48 89 8c 24 90 00 00 00 	mov    %rcx,0x90(%rsp)
    2eb7:	48 89 cb             	mov    %rcx,%rbx
    2eba:	45 89 fc             	mov    %r15d,%r12d
    2ebd:	83 e8 01             	sub    $0x1,%eax
    2ec0:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2ec4:	eb 1f                	jmp    2ee5 <main+0x855>
    2ec6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ed0:	41 83 c4 01          	add    $0x1,%r12d
    2ed4:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    2edb:	41 83 fc 06          	cmp    $0x6,%r12d
    2edf:	0f 84 ca 02 00 00    	je     31af <main+0xb1f>
            int group_of = b / threads_per_group;
    2ee5:	45 89 e7             	mov    %r12d,%r15d
    2ee8:	31 c0                	xor    %eax,%eax
    2eea:	44 89 e2             	mov    %r12d,%edx
    2eed:	bf 01 00 00 00       	mov    $0x1,%edi
    2ef2:	41 d1 ff             	sar    %r15d
    2ef5:	48 8d 35 fb 64 00 00 	lea    0x64fb(%rip),%rsi        # 93f7 <_IO_stdin_used+0x3f7>
    2efc:	44 89 f9             	mov    %r15d,%ecx
    2eff:	e8 ac f5 ff ff       	call   24b0 <__printf_chk@plt>
            if (k == group_of) {
    2f04:	45 39 f7             	cmp    %r14d,%r15d
    2f07:	75 c7                	jne    2ed0 <main+0x840>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f09:	be 08 00 00 00       	mov    $0x8,%esi
    2f0e:	bf 01 00 00 00       	mov    $0x1,%edi
    2f13:	e8 e8 f4 ff ff       	call   2400 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f18:	be 08 00 00 00       	mov    $0x8,%esi
    2f1d:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f22:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f27:	e8 d4 f4 ff ff       	call   2400 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2f2c:	be 80 04 00 00       	mov    $0x480,%esi
    2f31:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f36:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2f3b:	e8 c0 f4 ff ff       	call   2400 <calloc@plt>
              data[0].a = x;
    2f40:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    2f44:	44 89 e2             	mov    %r12d,%edx
              mailboxes[b].pending_lower = NULL;
    2f47:	48 c7 83 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%rbx)
              struct Data *data = calloc(3, sizeof(struct Data));
    2f52:	49 89 c7             	mov    %rax,%r15
              data[0].b = y;
    2f55:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    2f5b:	48 8d 35 06 6a 00 00 	lea    0x6a06(%rip),%rsi        # 9968 <_IO_stdin_used+0x968>
              data[0].a = x;
    2f62:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
              data[0].kind = MAILBOX_LOWER;
    2f68:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
              data[0].c = b;
    2f72:	44 89 a0 14 04 00 00 	mov    %r12d,0x414(%rax)
              data[0].id = dataid++;
    2f79:	41 8d 45 01          	lea    0x1(%r13),%eax
              data[1].id = dataid++;
    2f7d:	41 89 87 98 08 00 00 	mov    %eax,0x898(%r15)
              mailboxes[b].higher = &data[1];
    2f84:	49 8d 87 80 04 00 00 	lea    0x480(%r15),%rax
    2f8b:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
    2f92:	8b 44 24 70          	mov    0x70(%rsp),%eax
              data[0].id = dataid++;
    2f96:	45 89 af 18 04 00 00 	mov    %r13d,0x418(%r15)
              data[1].id = dataid++;
    2f9d:	41 83 c5 02          	add    $0x2,%r13d
              data[1].a = x;
    2fa1:	41 89 bf 8c 08 00 00 	mov    %edi,0x88c(%r15)
    2fa8:	89 c1                	mov    %eax,%ecx
    2faa:	bf 01 00 00 00       	mov    $0x1,%edi
    2faf:	89 83 b4 00 00 00    	mov    %eax,0xb4(%rbx)
    2fb5:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    2fb7:	41 c7 87 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r15)
              data[1].b = y;
    2fc2:	41 89 af 90 08 00 00 	mov    %ebp,0x890(%r15)
              data[1].c = b;
    2fc9:	45 89 a7 94 08 00 00 	mov    %r12d,0x894(%r15)
              mailboxes[b].lower = &data[0];
    2fd0:	4c 89 3b             	mov    %r15,(%rbx)
              mailboxes[b].pending_higher = NULL;
    2fd3:	48 c7 83 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%rbx)
              data[0].finished_reading = 1;
    2fde:	41 c7 87 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r15)
              data[1].finished_reading = 1;
    2fe9:	41 c7 87 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r15)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2ff4:	c7 83 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%rbx)
    2ffe:	e8 ad f4 ff ff       	call   24b0 <__printf_chk@plt>
              data[0].messages = messages;
    3003:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
              data[1].messages = messages2;
    3008:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
              data[0].messages_count = 0;
    300d:	66 0f 6f 35 7b 6e 00 00 	movdqa 0x6e7b(%rip),%xmm6        # 9e90 <_IO_stdin_used+0xe90>
              data[0].messages = messages;
    3015:	4d 89 1f             	mov    %r11,(%r15)
              data[1].messages = messages2;
    3018:	4d 89 97 80 04 00 00 	mov    %r10,0x480(%r15)
              data[0].messages_count = 0;
    301f:	41 0f 29 b7 80 00 00 00 	movaps %xmm6,0x80(%r15)
              data[1].messages_count = 0;
    3027:	41 0f 29 b7 00 05 00 00 	movaps %xmm6,0x500(%r15)
    302f:	e9 9c fe ff ff       	jmp    2ed0 <main+0x840>
    3034:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
    3039:	48 89 c3             	mov    %rax,%rbx
    303c:	45 89 fc             	mov    %r15d,%r12d
    303f:	eb 1c                	jmp    305d <main+0x9cd>
    3041:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3048:	41 83 c4 01          	add    $0x1,%r12d
    304c:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    3053:	41 83 fc 06          	cmp    $0x6,%r12d
    3057:	0f 84 91 05 00 00    	je     35ee <main+0xf5e>
            int group_of = b / threads_per_group;
    305d:	45 89 e7             	mov    %r12d,%r15d
    3060:	31 c0                	xor    %eax,%eax
    3062:	44 89 e2             	mov    %r12d,%edx
    3065:	bf 01 00 00 00       	mov    $0x1,%edi
    306a:	41 d1 ff             	sar    %r15d
    306d:	48 8d 35 83 63 00 00 	lea    0x6383(%rip),%rsi        # 93f7 <_IO_stdin_used+0x3f7>
    3074:	44 89 f9             	mov    %r15d,%ecx
    3077:	e8 34 f4 ff ff       	call   24b0 <__printf_chk@plt>
            if (k == group_of) {
    307c:	45 39 f7             	cmp    %r14d,%r15d
    307f:	75 c7                	jne    3048 <main+0x9b8>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3081:	be 08 00 00 00       	mov    $0x8,%esi
    3086:	bf 01 00 00 00       	mov    $0x1,%edi
    308b:	e8 70 f3 ff ff       	call   2400 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3090:	be 08 00 00 00       	mov    $0x8,%esi
    3095:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    309a:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    309f:	e8 5c f3 ff ff       	call   2400 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    30a4:	be 80 04 00 00       	mov    $0x480,%esi
    30a9:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30ae:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    30b3:	e8 48 f3 ff ff       	call   2400 <calloc@plt>
              data[0].a = x;
    30b8:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    30bc:	44 89 e2             	mov    %r12d,%edx
              mailboxes[b].pending_lower = NULL;
    30bf:	48 c7 83 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%rbx)
              struct Data *data = calloc(3, sizeof(struct Data));
    30ca:	49 89 c7             	mov    %rax,%r15
              data[0].b = y;
    30cd:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    30d3:	48 8d 35 8e 68 00 00 	lea    0x688e(%rip),%rsi        # 9968 <_IO_stdin_used+0x968>
              data[0].a = x;
    30da:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
              data[0].kind = MAILBOX_LOWER;
    30e0:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
              data[0].c = b;
    30ea:	44 89 a0 14 04 00 00 	mov    %r12d,0x414(%rax)
              data[0].id = dataid++;
    30f1:	41 8d 45 01          	lea    0x1(%r13),%eax
              data[1].id = dataid++;
    30f5:	41 89 87 98 08 00 00 	mov    %eax,0x898(%r15)
              mailboxes[b].higher = &data[1];
    30fc:	49 8d 87 80 04 00 00 	lea    0x480(%r15),%rax
    3103:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
    310a:	8b 84 24 8c 00 00 00 	mov    0x8c(%rsp),%eax
              data[0].id = dataid++;
    3111:	45 89 af 18 04 00 00 	mov    %r13d,0x418(%r15)
              data[1].id = dataid++;
    3118:	41 83 c5 02          	add    $0x2,%r13d
              data[1].a = x;
    311c:	41 89 bf 8c 08 00 00 	mov    %edi,0x88c(%r15)
    3123:	89 c1                	mov    %eax,%ecx
    3125:	bf 01 00 00 00       	mov    $0x1,%edi
    312a:	89 83 b4 00 00 00    	mov    %eax,0xb4(%rbx)
    3130:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    3132:	41 c7 87 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r15)
              data[1].b = y;
    313d:	41 89 af 90 08 00 00 	mov    %ebp,0x890(%r15)
              data[1].c = b;
    3144:	45 89 a7 94 08 00 00 	mov    %r12d,0x894(%r15)
              mailboxes[b].lower = &data[0];
    314b:	4c 89 3b             	mov    %r15,(%rbx)
              mailboxes[b].pending_higher = NULL;
    314e:	48 c7 83 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%rbx)
              data[0].finished_reading = 1;
    3159:	41 c7 87 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r15)
              data[1].finished_reading = 1;
    3164:	41 c7 87 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r15)
              mailboxes[b].kind = MAILBOX_FRIEND;
    316f:	c7 83 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%rbx)
    3179:	e8 32 f3 ff ff       	call   24b0 <__printf_chk@plt>
              data[0].messages = messages;
    317e:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
              data[1].messages = messages2;
    3183:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
              data[0].messages_count = 0;
    3188:	66 0f 6f 35 00 6d 00 00 	movdqa 0x6d00(%rip),%xmm6        # 9e90 <_IO_stdin_used+0xe90>
              data[0].messages = messages;
    3190:	4d 89 1f             	mov    %r11,(%r15)
              data[1].messages = messages2;
    3193:	4d 89 97 80 04 00 00 	mov    %r10,0x480(%r15)
              data[0].messages_count = 0;
    319a:	41 0f 29 b7 80 00 00 00 	movaps %xmm6,0x80(%r15)
              data[1].messages_count = 0;
    31a2:	41 0f 29 b7 00 05 00 00 	movaps %xmm6,0x500(%r15)
    31aa:	e9 99 fe ff ff       	jmp    3048 <main+0x9b8>
    31af:	48 8b 8c 24 90 00 00 00 	mov    0x90(%rsp),%rcx
    31b7:	49 89 cf             	mov    %rcx,%r15
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    31ba:	31 db                	xor    %ebx,%ebx
    31bc:	89 e9                	mov    %ebp,%ecx
    31be:	4c 89 f5             	mov    %r14,%rbp
    31c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            int group_of = b / threads_per_group;
    31c8:	89 d8                	mov    %ebx,%eax
    31ca:	d1 f8                	sar    %eax
            if (k == group_of) {
    31cc:	39 e8                	cmp    %ebp,%eax
    31ce:	0f 84 8a 01 00 00    	je     335e <main+0xcce>
    31d4:	89 da                	mov    %ebx,%edx
    31d6:	48 8d 35 2a 62 00 00 	lea    0x622a(%rip),%rsi        # 9407 <_IO_stdin_used+0x407>
    31dd:	bf 01 00 00 00       	mov    $0x1,%edi
    31e2:	31 c0                	xor    %eax,%eax
    31e4:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    31e8:	e8 c3 f2 ff ff       	call   24b0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    31ed:	be 08 00 00 00       	mov    $0x8,%esi
    31f2:	bf 01 00 00 00       	mov    $0x1,%edi
    31f7:	e8 04 f2 ff ff       	call   2400 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    31fc:	be 08 00 00 00       	mov    $0x8,%esi
    3201:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3206:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    320b:	e8 f0 f1 ff ff       	call   2400 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    3210:	be 80 04 00 00       	mov    $0x480,%esi
    3215:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    321a:	49 89 c6             	mov    %rax,%r14
            struct Data *data = calloc(3, sizeof(struct Data));
    321d:	e8 de f1 ff ff       	call   2400 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    3222:	be 80 04 00 00       	mov    $0x480,%esi
    3227:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    322c:	49 89 c4             	mov    %rax,%r12
            struct Data **stack = calloc(3, sizeof(struct Data));
    322f:	e8 cc f1 ff ff       	call   2400 <calloc@plt>
            data[0].a = x;
    3234:	8b 7c 24 18          	mov    0x18(%rsp),%edi
            data[0].b = y;
    3238:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
            mailboxes[b].lower = &data[0];
    323c:	4d 89 27             	mov    %r12,(%r15)
            data[0].id = dataid++;
    323f:	41 8d 75 01          	lea    0x1(%r13),%esi
            data[0].messages = messages;
    3243:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
            data[0].messages_count = 0;
    3248:	66 0f 6f 35 40 6c 00 00 	movdqa 0x6c40(%rip),%xmm6        # 9e90 <_IO_stdin_used+0xe90>
            data[0].id = dataid++;
    3250:	45 89 ac 24 18 04 00 00 	mov    %r13d,0x418(%r12)
            data[1].id = dataid++;
    3258:	41 89 b4 24 98 08 00 00 	mov    %esi,0x898(%r12)
            mailboxes[b].higher = &data[1];
    3260:	49 8d b4 24 80 04 00 00 	lea    0x480(%r12),%rsi
            data[1].id = dataid++;
    3268:	41 83 c5 02          	add    $0x2,%r13d
            data[0].kind = MAILBOX_LOWER;
    326c:	41 c7 84 24 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%r12)
            data[0].a = x;
    3278:	41 89 bc 24 0c 04 00 00 	mov    %edi,0x40c(%r12)
            data[0].b = y;
    3280:	41 89 8c 24 10 04 00 00 	mov    %ecx,0x410(%r12)
            data[0].c = b;
    3288:	41 89 9c 24 14 04 00 00 	mov    %ebx,0x414(%r12)
            data[1].kind = MAILBOX_HIGHER;
    3290:	41 c7 84 24 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r12)
            data[1].a = x;
    329c:	41 89 bc 24 8c 08 00 00 	mov    %edi,0x88c(%r12)
            data[1].b = y;
    32a4:	41 89 8c 24 90 08 00 00 	mov    %ecx,0x890(%r12)
            data[1].c = b;
    32ac:	41 89 9c 24 94 08 00 00 	mov    %ebx,0x894(%r12)
            mailboxes[b].my_lower = &data[0];
    32b4:	4d 89 a7 a0 00 00 00 	mov    %r12,0xa0(%r15)
            mailboxes[b].higher = &data[1];
    32bb:	49 89 b7 80 00 00 00 	mov    %rsi,0x80(%r15)
            mailboxes[b].pending_lower = NULL;
    32c2:	49 c7 87 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r15)
            mailboxes[b].pending_higher = NULL;
    32cd:	49 c7 87 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r15)
            data[0].finished_reading = 1;
    32d8:	41 c7 84 24 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r12)
            data[1].finished_reading = 1;
    32e4:	41 c7 84 24 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r12)
            mailboxes[b].my_higher = &data[1];
    32f0:	49 89 b7 a8 00 00 00 	mov    %rsi,0xa8(%r15)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    32f7:	41 c7 87 b0 00 00 00 02 00 00 00 	movl   $0x2,0xb0(%r15)
            stack[0] = mailboxes[b].lower;
    3302:	4c 89 20             	mov    %r12,(%rax)
            stack[1] = mailboxes[b].higher;
    3305:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    3309:	49 89 87 98 00 00 00 	mov    %rax,0x98(%r15)
            data[0].available_sending = 0;
    3310:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
            data[0].available_receiving = 0;
    331c:	41 c7 84 24 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r12)
            data[0].messages = messages;
    3328:	49 89 14 24          	mov    %rdx,(%r12)
            data[1].messages = messages2;
    332c:	4d 89 b4 24 80 04 00 00 	mov    %r14,0x480(%r12)
            data[1].available_sending = 1;
    3334:	41 c7 84 24 80 05 00 00 01 00 00 00 	movl   $0x1,0x580(%r12)
            data[1].available_receiving = 0;
    3340:	41 c7 84 24 00 06 00 00 00 00 00 00 	movl   $0x0,0x600(%r12)
            data[0].messages_count = 0;
    334c:	41 0f 29 b4 24 80 00 00 00 	movaps %xmm6,0x80(%r12)
            data[1].messages_count = 0;
    3355:	41 0f 29 b4 24 00 05 00 00 	movaps %xmm6,0x500(%r12)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    335e:	83 c3 01             	add    $0x1,%ebx
    3361:	49 81 c7 00 01 00 00 	add    $0x100,%r15
    3368:	83 fb 06             	cmp    $0x6,%ebx
    336b:	0f 85 57 fe ff ff    	jne    31c8 <main+0xb38>
          char *message = malloc(sizeof(char) * 256);
    3371:	be 01 00 00 00       	mov    $0x1,%esi
    3376:	bf 00 01 00 00       	mov    $0x100,%edi
    337b:	49 89 ee             	mov    %rbp,%r14
    337e:	89 cd                	mov    %ecx,%ebp
    3380:	e8 7b f0 ff ff       	call   2400 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    3385:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    338a:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
    338d:	e8 de f0 ff ff       	call   2470 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3392:	48 83 ec 08          	sub    $0x8,%rsp
    3396:	48 89 df             	mov    %rbx,%rdi
    3399:	41 89 e9             	mov    %ebp,%r9d
    339c:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    33a1:	44 8b 7c 24 58       	mov    0x58(%rsp),%r15d
    33a6:	ba 00 01 00 00       	mov    $0x100,%edx
    33ab:	31 c0                	xor    %eax,%eax
    33ad:	48 8d 0d dc 65 00 00 	lea    0x65dc(%rip),%rcx        # 9990 <_IO_stdin_used+0x990>
    33b4:	be 01 00 00 00       	mov    $0x1,%esi
    33b9:	41 57                	push   %r15
    33bb:	44 8b 44 24 28       	mov    0x28(%rsp),%r8d
    33c0:	e8 db f1 ff ff       	call   25a0 <__sprintf_chk@plt>
          messaged->message = message;
    33c5:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
          messaged->task_index = y;
    33ca:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
          messaged->group = k;
    33cf:	44 89 ff             	mov    %r15d,%edi
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    33d2:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->group = k;
    33d7:	45 89 7b 18          	mov    %r15d,0x18(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    33db:	4c 8b 7c 24 58       	mov    0x58(%rsp),%r15
          messaged->task_index = y;
    33e0:	49 89 43 10          	mov    %rax,0x10(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    33e4:	49 63 47 08          	movslq 0x8(%r15),%rax
          thread_data[x].tasks[y].swap = swap;
    33e8:	49 8b 57 38          	mov    0x38(%r15),%rdx
          messaged->message = message;
    33ec:	49 89 1b             	mov    %rbx,(%r11)
          thread_data[x].tasks[y].swap = swap;
    33ef:	48 8b 5c 24 40       	mov    0x40(%rsp),%rbx
          messaged->thread_index = thread_data[x].real_thread_index;
    33f4:	49 89 43 08          	mov    %rax,0x8(%r11)
          thread_data[x].tasks[y].swap = swap;
    33f8:	8b 44 24 38          	mov    0x38(%rsp),%eax
    33fc:	48 01 d3             	add    %rdx,%rbx
    33ff:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    3404:	89 83 a0 01 00 00    	mov    %eax,0x1a0(%rbx)
          swap += 1;
    340a:	83 c0 01             	add    $0x1,%eax
    340d:	89 44 24 38          	mov    %eax,0x38(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3411:	8d 45 01             	lea    0x1(%rbp),%eax
    3414:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].group = k;
    3417:	89 bb 9c 01 00 00    	mov    %edi,0x19c(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    341d:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    3422:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3428:	89 83 98 01 00 00    	mov    %eax,0x198(%rbx)
          thread_data[x].tasks[y].message = messaged;
    342e:	4c 89 9b 90 01 00 00 	mov    %r11,0x190(%rbx)
          thread_data[x].tasks[y].sending = 1;
    3435:	c7 83 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    343f:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    344a:	e8 b1 ef ff ff       	call   2400 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    344f:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    345a:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3461:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    3466:	48 8b 00             	mov    (%rax),%rax
    3469:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    346c:	49 39 c7             	cmp    %rax,%r15
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    346f:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3476:	89 8b 30 01 00 00    	mov    %ecx,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    347c:	41 5c                	pop    %r12
    347e:	5a                   	pop    %rdx
    347f:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    3484:	0f 85 00 14 00 00    	jne    488a <main+0x21fa>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    348a:	66 0f 6f 05 0e 6a 00 00 	movdqa 0x6a0e(%rip),%xmm0        # 9ea0 <_IO_stdin_used+0xea0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    3492:	89 6b 04             	mov    %ebp,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
    3495:	48 8b 05 14 6a 00 00 	mov    0x6a14(%rip),%rax        # 9eb0 <_IO_stdin_used+0xeb0>
          thread_data[x].tasks[y].arrived = 0;
    349c:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
    34a6:	c7 83 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rbx)
          thread_data[x].tasks[y].available = 1;
    34b0:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    34b7:	0f 11 83 34 01 00 00 	movups %xmm0,0x134(%rbx)
          if (y == barrier_count - 1) {
    34be:	83 fd 01             	cmp    $0x1,%ebp
    34c1:	0f 84 49 01 00 00    	je     3610 <main+0xf80>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    34c7:	85 ed                	test   %ebp,%ebp
    34c9:	0f 84 29 01 00 00    	je     35f8 <main+0xf68>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    34cf:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
    34d4:	48 8d 05 a5 44 00 00 	lea    0x44a5(%rip),%rax        # 7980 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    34db:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    34e0:	45 89 ef             	mov    %r13d,%r15d
    34e3:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    34ea:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
    34ef:	41 c7 81 c4 00 00 00 01 00 00 00 	movl   $0x1,0xc4(%r9)
               thread_data[x].tasks[y].run = barriered_work; 
    34fa:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
        thread_data[x].buffers_count = buffers_per_thread;
    34ff:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3504:	e8 f7 ee ff ff       	call   2400 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3509:	48 8b 6c 24 68       	mov    0x68(%rsp),%rbp
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    350e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        }
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3513:	be 08 00 00 00       	mov    $0x8,%esi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3518:	48 8b 9c 24 a0 00 00 00 	mov    0xa0(%rsp),%rbx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3520:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3525:	83 84 24 84 00 00 00 01 	addl   $0x1,0x84(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    352d:	49 89 41 50          	mov    %rax,0x50(%r9)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3531:	48 8d 0c 6b          	lea    (%rbx,%rbp,2),%rcx
    3535:	48 89 08             	mov    %rcx,(%rax)
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3538:	e8 c3 ee ff ff       	call   2400 <calloc@plt>
        for (int b = 0 ; b < io_threads; b++) {	
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    353d:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3542:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3547:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    354c:	83 44 24 7c 02       	addl   $0x2,0x7c(%rsp)
    3551:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3555:	49 89 41 58          	mov    %rax,0x58(%r9)
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3559:	66 0f 6f bc 24 b0 00 00 00 	movdqa 0xb0(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    3562:	49 81 c1 20 01 00 00 	add    $0x120,%r9
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    3569:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    356c:	48 83 c3 20          	add    $0x20,%rbx
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    3570:	48 89 48 08          	mov    %rcx,0x8(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3574:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    3579:	48 89 5c 24 60       	mov    %rbx,0x60(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    357e:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3581:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    3588:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3592:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    3599:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    35a3:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    35ad:	41 8b 81 e4 fe ff ff 	mov    -0x11c(%r9),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    35b4:	c7 82 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    35be:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
    35c4:	48 8b 05 e5 68 00 00 	mov    0x68e5(%rip),%rax        # 9eb0 <_IO_stdin_used+0xeb0>
    35cb:	48 89 82 44 05 00 00 	mov    %rax,0x544(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    35d2:	48 83 fd 08          	cmp    $0x8,%rbp
    35d6:	74 46                	je     361e <main+0xf8e>
    35d8:	48 c7 44 24 68 08 00 00 00 	movq   $0x8,0x68(%rsp)
    35e1:	44 8b ac 24 88 00 00 00 	mov    0x88(%rsp),%r13d
    35e9:	e9 d9 f5 ff ff       	jmp    2bc7 <main+0x537>
    35ee:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    35f3:	e9 bf fb ff ff       	jmp    31b7 <main+0xb27>
    35f8:	48 8d 05 41 49 00 00 	lea    0x4941(%rip),%rax        # 7f40 <barriered_work_ingest_andwork>
    35ff:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    3604:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    360b:	e9 50 f8 ff ff       	jmp    2e60 <main+0x7d0>
    3610:	48 8d 05 69 43 00 00 	lea    0x4369(%rip),%rax        # 7980 <barriered_work>
    3617:	bd 02 00 00 00       	mov    $0x2,%ebp
    361c:	eb e6                	jmp    3604 <main+0xf74>
    361e:	4d 89 f5             	mov    %r14,%r13
    3621:	48 8b ac 24 f8 00 00 00 	mov    0xf8(%rsp),%rbp
  for (int k = 0 ; k < group_count ; k++) {
    3629:	48 83 84 24 98 00 00 00 18 	addq   $0x18,0x98(%rsp)
    3632:	49 83 c5 01          	add    $0x1,%r13
    3636:	4c 8b b4 24 08 01 00 00 	mov    0x108(%rsp),%r14
    363e:	49 83 fd 03          	cmp    $0x3,%r13
    3642:	0f 85 ae f4 ff ff    	jne    2af6 <main+0x466>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3648:	be 08 00 00 00       	mov    $0x8,%esi
    364d:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    3652:	31 ed                	xor    %ebp,%ebp
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3654:	e8 a7 ed ff ff       	call   2400 <calloc@plt>
    3659:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
    365e:	49 89 c7             	mov    %rax,%r15
    3661:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3663:	49 89 d1             	mov    %rdx,%r9
    3666:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3668:	45 8b 51 40          	mov    0x40(%r9),%r10d
    366c:	45 85 d2             	test   %r10d,%r10d
    366f:	0f 8e ac 00 00 00    	jle    3721 <main+0x1091>
    3675:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3679:	4d 63 c2             	movslq %r10d,%r8
    367c:	48 63 cd             	movslq %ebp,%rcx
    367f:	49 c1 e0 09          	shl    $0x9,%r8
    3683:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    3687:	49 01 f8             	add    %rdi,%r8
    368a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3690:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3697:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    369e:	48 83 c6 60          	add    $0x60,%rsi
    36a2:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    36aa:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    36ae:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    36b6:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    36be:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    36c6:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    36cd:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    36d5:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    36dc:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    36e3:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    36ea:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    36ee:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    36f5:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    36fc:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3700:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3704:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3708:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    370c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3710:	49 39 f8             	cmp    %rdi,%r8
    3713:	0f 85 77 ff ff ff    	jne    3690 <main+0x1000>
    3719:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    371d:	8d 6c 8d 00          	lea    0x0(%rbp,%rcx,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3721:	49 81 c1 20 01 00 00 	add    $0x120,%r9
    3728:	85 db                	test   %ebx,%ebx
    372a:	75 37                	jne    3763 <main+0x10d3>
    372c:	bb 01 00 00 00       	mov    $0x1,%ebx
    3731:	e9 32 ff ff ff       	jmp    3668 <main+0xfd8>
        other = (x + 1) % total_threads;
    3736:	41 8d 45 01          	lea    0x1(%r13),%eax
        my_thread_data[1] = &thread_data[other]; 
    373a:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    373f:	4c 89 ca             	mov    %r9,%rdx
    3742:	45 31 c0             	xor    %r8d,%r8d
    3745:	89 84 24 88 00 00 00 	mov    %eax,0x88(%rsp)
        other = (x + 1) % total_threads;
    374c:	89 c1                	mov    %eax,%ecx
        my_thread_data[1] = &thread_data[other]; 
    374e:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3752:	48 c1 e0 05          	shl    $0x5,%rax
    3756:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    375b:	48 01 f8             	add    %rdi,%rax
        thread_data[x].protected_state = &protected_state[k];
    375e:	e9 35 f5 ff ff       	jmp    2c98 <main+0x608>
  for (int k = 0 ; k < group_count ; k++) {
    3763:	83 c0 02             	add    $0x2,%eax
    3766:	48 81 c2 40 02 00 00 	add    $0x240,%rdx
    376d:	83 f8 06             	cmp    $0x6,%eax
    3770:	0f 85 ed fe ff ff    	jne    3663 <main+0xfd3>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3776:	48 8d 3d a8 5c 00 00 	lea    0x5ca8(%rip),%rdi        # 9425 <_IO_stdin_used+0x425>
    377d:	e8 ae eb ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    3782:	48 8d 35 b1 5c 00 00 	lea    0x5cb1(%rip),%rsi        # 943a <_IO_stdin_used+0x43a>
    3789:	48 8d 3d ac 5c 00 00 	lea    0x5cac(%rip),%rdi        # 943c <_IO_stdin_used+0x43c>
    3790:	e8 5b ed ff ff       	call   24f0 <fopen@plt>
    3795:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas_size; x++) {
    3798:	85 ed                	test   %ebp,%ebp
    379a:	7e 76                	jle    3812 <main+0x1182>
    379c:	48 63 ed             	movslq %ebp,%rbp
    379f:	4c 8d 2d 73 5c 00 00 	lea    0x5c73(%rip),%r13        # 9419 <_IO_stdin_used+0x419>
    37a6:	4c 8d 25 b0 5c 00 00 	lea    0x5cb0(%rip),%r12        # 945d <_IO_stdin_used+0x45d>
    37ad:	49 8d 04 ef          	lea    (%r15,%rbp,8),%rax
    37b1:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    char * c = calloc(250, sizeof(char));
    37b6:	be 01 00 00 00       	mov    $0x1,%esi
    37bb:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    37c0:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    37c4:	e8 37 ec ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    37c9:	4c 89 e9             	mov    %r13,%rcx
    37cc:	ba fa 00 00 00       	mov    $0xfa,%edx
    37d1:	be 01 00 00 00       	mov    $0x1,%esi
    37d6:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    37d9:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    37dd:	48 89 ef             	mov    %rbp,%rdi
    37e0:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    37e7:	31 c0                	xor    %eax,%eax
    37e9:	e8 b2 ed ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    37ee:	48 89 ea             	mov    %rbp,%rdx
    37f1:	4c 89 e6             	mov    %r12,%rsi
    37f4:	bf 01 00 00 00       	mov    $0x1,%edi
    37f9:	31 c0                	xor    %eax,%eax
    37fb:	e8 b0 ec ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3800:	4c 89 f6             	mov    %r14,%rsi
    3803:	48 89 ef             	mov    %rbp,%rdi
    3806:	e8 b5 eb ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    380b:	4c 39 7c 24 08       	cmp    %r15,0x8(%rsp)
    3810:	75 a4                	jne    37b6 <main+0x1126>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    3812:	4c 89 f7             	mov    %r14,%rdi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3815:	45 31 f6             	xor    %r14d,%r14d
    3818:	4c 8d 25 68 5c 00 00 	lea    0x5c68(%rip),%r12        # 9487 <_IO_stdin_used+0x487>
    381f:	e8 3c eb ff ff       	call   2360 <fclose@plt>
    3824:	48 8d 3d 1a 5c 00 00 	lea    0x5c1a(%rip),%rdi        # 9445 <_IO_stdin_used+0x445>
    382b:	4c 89 f5             	mov    %r14,%rbp
    382e:	e8 fd ea ff ff       	call   2330 <puts@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    3833:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    3837:	89 ea                	mov    %ebp,%edx
    3839:	48 8d 35 20 5c 00 00 	lea    0x5c20(%rip),%rsi        # 9460 <_IO_stdin_used+0x460>
    3840:	bf 01 00 00 00       	mov    $0x1,%edi
    3845:	31 c0                	xor    %eax,%eax
    3847:	e8 64 ec ff ff       	call   24b0 <__printf_chk@plt>
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    384c:	48 8d 5c ed 00       	lea    0x0(%rbp,%rbp,8),%rbx
    3851:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3856:	45 31 ff             	xor    %r15d,%r15d
    3859:	48 c1 e3 06          	shl    $0x6,%rbx
    385d:	44 8d 6c 2d 00       	lea    0x0(%rbp,%rbp,1),%r13d
    3862:	48 01 c3             	add    %rax,%rbx
      int x = (k * threads_per_group) + d;
    3865:	43 8d 0c 2f          	lea    (%r15,%r13,1),%ecx
    3869:	44 89 fa             	mov    %r15d,%edx
    386c:	48 8d 35 f7 5b 00 00 	lea    0x5bf7(%rip),%rsi        # 946a <_IO_stdin_used+0x46a>
    3873:	31 c0                	xor    %eax,%eax
    3875:	bf 01 00 00 00       	mov    $0x1,%edi
    387a:	45 31 f6             	xor    %r14d,%r14d
    387d:	e8 2e ec ff ff       	call   24b0 <__printf_chk@plt>
    3882:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
    3887:	4c 89 f1             	mov    %r14,%rcx
    388a:	48 89 6c 24 28       	mov    %rbp,0x28(%rsp)
    388f:	48 89 dd             	mov    %rbx,%rbp
    3892:	89 ca                	mov    %ecx,%edx
    3894:	48 8d 35 e1 5b 00 00 	lea    0x5be1(%rip),%rsi        # 947c <_IO_stdin_used+0x47c>
    389b:	bf 01 00 00 00       	mov    $0x1,%edi
    38a0:	31 c0                	xor    %eax,%eax
    38a2:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    38a7:	45 31 ed             	xor    %r13d,%r13d
    38aa:	e8 01 ec ff ff       	call   24b0 <__printf_chk@plt>
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    38af:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    38b4:	48 c1 e3 09          	shl    $0x9,%rbx
    38b8:	eb 32                	jmp    38ec <main+0x125c>
    38ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    38c0:	83 fe 01             	cmp    $0x1,%esi
    38c3:	0f 84 a9 00 00 00    	je     3972 <main+0x12e2>
    38c9:	44 89 f2             	mov    %r14d,%edx
    38cc:	4c 89 e6             	mov    %r12,%rsi
    38cf:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    38d4:	49 83 c5 01          	add    $0x1,%r13
    38d8:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    38df:	31 c0                	xor    %eax,%eax
    38e1:	e8 ca eb ff ff       	call   24b0 <__printf_chk@plt>
    38e6:	49 83 fd 06          	cmp    $0x6,%r13
    38ea:	74 50                	je     393c <main+0x12ac>
          char * mailbox_kind = calloc(100, sizeof(char));
    38ec:	be 01 00 00 00       	mov    $0x1,%esi
    38f1:	bf 64 00 00 00       	mov    $0x64,%edi
    38f6:	45 89 ee             	mov    %r13d,%r14d
    38f9:	e8 02 eb ff ff       	call   2400 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    38fe:	4c 8b 45 38          	mov    0x38(%rbp),%r8
    3902:	4c 89 ef             	mov    %r13,%rdi
          char * mailbox_kind = calloc(100, sizeof(char));
    3905:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3908:	48 c1 e7 08          	shl    $0x8,%rdi
    390c:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3914:	48 01 f8             	add    %rdi,%rax
    3917:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    391d:	83 fe 02             	cmp    $0x2,%esi
    3920:	75 9e                	jne    38c0 <main+0x1230>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3922:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    392c:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    392f:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3937:	48 01 f8             	add    %rdi,%rax
    393a:	eb 8d                	jmp    38c9 <main+0x1239>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    393c:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    3941:	48 83 c1 01          	add    $0x1,%rcx
    3945:	48 83 f9 03          	cmp    $0x3,%rcx
    3949:	0f 85 43 ff ff ff    	jne    3892 <main+0x1202>
    for (int d = 0 ; d < threads_per_group ; d++) {
    394f:	48 89 eb             	mov    %rbp,%rbx
    3952:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    3957:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    395c:	48 81 c3 20 01 00 00 	add    $0x120,%rbx
    3963:	45 85 ff             	test   %r15d,%r15d
    3966:	75 27                	jne    398f <main+0x12ff>
    3968:	44 8b 7c 24 10       	mov    0x10(%rsp),%r15d
    396d:	e9 f3 fe ff ff       	jmp    3865 <main+0x11d5>
    3972:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3978:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    397f:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3987:	48 01 f8             	add    %rdi,%rax
    398a:	e9 3a ff ff ff       	jmp    38c9 <main+0x1239>
  for (int k = 0 ; k < group_count ; k++) {
    398f:	48 83 c5 01          	add    $0x1,%rbp
    3993:	48 83 fd 03          	cmp    $0x3,%rbp
    3997:	0f 85 9a fe ff ff    	jne    3837 <main+0x11a7>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    399d:	ba 07 00 00 00       	mov    $0x7,%edx
    39a2:	48 8d 35 f9 5a 00 00 	lea    0x5af9(%rip),%rsi        # 94a2 <_IO_stdin_used+0x4a2>
    39a9:	bf 01 00 00 00       	mov    $0x1,%edi
    39ae:	31 c0                	xor    %eax,%eax
    39b0:	e8 fb ea ff ff       	call   24b0 <__printf_chk@plt>
  

  printf("io index = %d\n", io_index);
  int io_mode = 0;
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    39b5:	be 08 00 00 00       	mov    $0x8,%esi
    39ba:	bf 02 00 00 00       	mov    $0x2,%edi
    39bf:	e8 3c ea ff ff       	call   2400 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    39c4:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    39c9:	be 08 00 00 00       	mov    $0x8,%esi
    39ce:	bf 02 00 00 00       	mov    $0x2,%edi
    my_thread_data[0] = &thread_data[x]; 
    39d3:	4c 8d b3 e0 07 00 00 	lea    0x7e0(%rbx),%r14
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    39da:	48 89 58 08          	mov    %rbx,0x8(%rax)
    39de:	4c 8d a3 20 01 00 00 	lea    0x120(%rbx),%r12

    io_mode = (io_mode + 1) % 2;
    thread_data[x].threads = my_thread_data;
    39e5:	48 89 83 f8 07 00 00 	mov    %rax,0x7f8(%rbx)
    thread_data[x].thread_count = 2;
    39ec:	c7 83 08 08 00 00 02 00 00 00 	movl   $0x2,0x808(%rbx)
    thread_data[x].thread_index = 0;
    39f6:	c7 83 e4 07 00 00 00 00 00 00 	movl   $0x0,0x7e4(%rbx)
    thread_data[x].task_count = total_barrier_count;
    3a00:	c7 83 20 08 00 00 03 00 00 00 	movl   $0x3,0x820(%rbx)
    my_thread_data[0] = &thread_data[x]; 
    3a0a:	4c 89 30             	mov    %r14,(%rax)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    3a0d:	e8 ee e9 ff ff       	call   2400 <calloc@plt>
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a12:	be 38 00 00 00       	mov    $0x38,%esi
    thread_data[n].tasks[0].scheduled = 1;
    3a17:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    my_thread_data[0] = &thread_data[x]; 
    3a1c:	48 8d bb 00 09 00 00 	lea    0x900(%rbx),%rdi
    thread_data[x].threads = my_thread_data;
    3a23:	48 89 83 18 09 00 00 	mov    %rax,0x918(%rbx)
    my_thread_data[0] = &thread_data[x]; 
    3a2a:	48 89 38             	mov    %rdi,(%rax)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3a2d:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3a31:	48 8b 43 38          	mov    0x38(%rbx),%rax
    thread_data[x].thread_count = 2;
    3a35:	c7 83 28 09 00 00 02 00 00 00 	movl   $0x2,0x928(%rbx)
    thread_data[x].thread_index = 0;
    3a3f:	c7 83 04 09 00 00 00 00 00 00 	movl   $0x0,0x904(%rbx)
    thread_data[x].task_count = total_barrier_count;
    3a49:	c7 83 40 09 00 00 03 00 00 00 	movl   $0x3,0x940(%rbx)
    thread_data[n].tasks[0].scheduled = 1;
    3a53:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3a5d:	48 8b 83 58 01 00 00 	mov    0x158(%rbx),%rax
    my_thread_data[0] = &thread_data[x]; 
    3a64:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a69:	bf 0b 00 00 00       	mov    $0xb,%edi
    thread_data[n].tasks[0].scheduled = 1;
    3a6e:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a78:	e8 83 e9 ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a7d:	be 38 00 00 00       	mov    $0x38,%esi
    3a82:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a87:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a8a:	e8 71 e9 ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a8f:	be 38 00 00 00       	mov    $0x38,%esi
    3a94:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a99:	48 89 c5             	mov    %rax,%rbp
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a9c:	e8 5f e9 ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3aa1:	be 38 00 00 00       	mov    $0x38,%esi
    3aa6:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3aab:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ab0:	e8 4b e9 ff ff       	call   2400 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3ab5:	be 08 00 00 00       	mov    $0x8,%esi
    3aba:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3abf:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3ac4:	e8 37 e9 ff ff       	call   2400 <calloc@plt>


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
    3ac9:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3ace:	be 08 00 00 00       	mov    $0x8,%esi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3ad3:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    3ad6:	48 8b 05 eb 63 00 00 	mov    0x63eb(%rip),%rax        # 9ec8 <_IO_stdin_used+0xec8>
  thread_data[timer_threadi].type = TIMER;
    3add:	c7 87 cc 06 00 00 00 00 00 00 	movl   $0x0,0x6cc(%rdi)
  thread_data[timer_threadi].task_count = total_barrier_count;
    3ae7:	48 89 87 00 07 00 00 	mov    %rax,0x700(%rdi)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3aee:	bf 0b 00 00 00       	mov    $0xb,%edi
    3af3:	e8 08 e9 ff ff       	call   2400 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3af8:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3afd:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3b02:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3b06:	48 8d 97 40 02 00 00 	lea    0x240(%rdi),%rdx
    3b0d:	48 8d 8f c0 06 00 00 	lea    0x6c0(%rdi),%rcx
    3b14:	48 89 70 40          	mov    %rsi,0x40(%rax)
    3b18:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3b1c:	48 8d 97 60 03 00 00 	lea    0x360(%rdi),%rdx
    3b23:	48 8d b7 20 0a 00 00 	lea    0xa20(%rdi),%rsi
    3b2a:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3b2e:	48 8d 97 80 04 00 00 	lea    0x480(%rdi),%rdx
    3b35:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3b39:	48 8d 97 a0 05 00 00 	lea    0x5a0(%rdi),%rdx
    3b40:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3b44:	48 8d 97 40 0b 00 00 	lea    0xb40(%rdi),%rdx
    3b4b:	48 89 38             	mov    %rdi,(%rax)
    3b4e:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3b52:	48 89 70 48          	mov    %rsi,0x48(%rax)
    3b56:	48 89 50 50          	mov    %rdx,0x50(%rax)
    3b5a:	ba 06 00 00 00       	mov    $0x6,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3b5f:	48 89 87 d8 06 00 00 	mov    %rax,0x6d8(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    3b66:	4c 89 70 38          	mov    %r14,0x38(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3b6a:	48 8b 05 5f 63 00 00 	mov    0x635f(%rip),%rax        # 9ed0 <_IO_stdin_used+0xed0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3b71:	c7 87 f0 06 00 00 06 00 00 00 	movl   $0x6,0x6f0(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3b7b:	48 89 87 e8 06 00 00 	mov    %rax,0x6e8(%rdi)
    3b82:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3b84:	c7 87 c4 06 00 00 00 00 00 00 	movl   $0x0,0x6c4(%rdi)
    3b8e:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    3b93:	48 89 74 24 30       	mov    %rsi,0x30(%rsp)
    3b98:	48 8d 35 12 59 00 00 	lea    0x5912(%rip),%rsi        # 94b1 <_IO_stdin_used+0x4b1>
    3b9f:	48 89 4c 24 10       	mov    %rcx,0x10(%rsp)
    3ba4:	e8 07 e9 ff ff       	call   24b0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3ba9:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    3bae:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    3bb2:	48 8d 15 c7 0f 00 00 	lea    0xfc7(%rip),%rdx        # 4b80 <timer_thread>
    3bb9:	48 8d b5 50 01 00 00 	lea    0x150(%rbp),%rsi
    3bc0:	e8 0b e9 ff ff       	call   24d0 <pthread_create@plt>
    3bc5:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
  for (int k = 0 ; k < group_count ; k++) {
    3bca:	45 31 c0             	xor    %r8d,%r8d
    3bcd:	48 89 d9             	mov    %rbx,%rcx
    3bd0:	4c 89 74 24 38       	mov    %r14,0x38(%rsp)
    3bd5:	4c 89 e8             	mov    %r13,%rax
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3bd8:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3bde:	4c 89 64 24 40       	mov    %r12,0x40(%rsp)
    3be3:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    3be8:	44 89 c3             	mov    %r8d,%ebx
    3beb:	44 89 7c 24 48       	mov    %r15d,0x48(%rsp)
    3bf0:	49 89 d7             	mov    %rdx,%r15
    for (int d = 0 ; d < threads_per_group ; d++) {
    3bf3:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    3bf8:	4c 89 fd             	mov    %r15,%rbp
    3bfb:	44 8d 2c 1b          	lea    (%rbx,%rbx,1),%r13d
    3bff:	49 89 c6             	mov    %rax,%r14
    3c02:	48 89 4c 24 60       	mov    %rcx,0x60(%rsp)
    3c07:	49 89 cc             	mov    %rcx,%r12
    3c0a:	4c 89 7c 24 50       	mov    %r15,0x50(%rsp)
    3c0f:	45 89 d7             	mov    %r10d,%r15d
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3c12:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    3c19:	44 89 ea             	mov    %r13d,%edx
    3c1c:	89 d9                	mov    %ebx,%ecx
    3c1e:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    3c20:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    3c27:	48 8d 35 92 5d 00 00 	lea    0x5d92(%rip),%rsi        # 99c0 <_IO_stdin_used+0x9c0>
    3c2e:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c33:	41 83 c5 01          	add    $0x1,%r13d
    3c37:	e8 74 e8 ff ff       	call   24b0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3c3c:	48 89 e9             	mov    %rbp,%rcx
    3c3f:	4c 89 f6             	mov    %r14,%rsi
    3c42:	4c 89 e7             	mov    %r12,%rdi
    3c45:	48 8d 15 74 34 00 00 	lea    0x3474(%rip),%rdx        # 70c0 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c4c:	48 81 c5 20 01 00 00 	add    $0x120,%rbp
    3c53:	49 83 c4 08          	add    $0x8,%r12
    3c57:	49 83 c6 38          	add    $0x38,%r14
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3c5b:	e8 70 e8 ff ff       	call   24d0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3c60:	48 8b 55 98          	mov    -0x68(%rbp),%rdx
    3c64:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    3c69:	be 08 00 00 00       	mov    $0x8,%esi
    3c6e:	e8 ad e6 ff ff       	call   2320 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c73:	45 39 fd             	cmp    %r15d,%r13d
    3c76:	75 9a                	jne    3c12 <main+0x1582>
  for (int k = 0 ; k < group_count ; k++) {
    3c78:	4c 8b 7c 24 50       	mov    0x50(%rsp),%r15
    3c7d:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    3c82:	83 c3 01             	add    $0x1,%ebx
    3c85:	45 8d 55 02          	lea    0x2(%r13),%r10d
    3c89:	48 8b 4c 24 60       	mov    0x60(%rsp),%rcx
    3c8e:	49 81 c7 40 02 00 00 	add    $0x240,%r15
    3c95:	48 83 c0 70          	add    $0x70,%rax
    3c99:	48 83 c1 10          	add    $0x10,%rcx
    3c9d:	83 fb 03             	cmp    $0x3,%ebx
    3ca0:	0f 85 4d ff ff ff    	jne    3bf3 <main+0x1563>
    }
  }
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    3ca6:	be 08 00 00 00       	mov    $0x8,%esi
    3cab:	bf 02 00 00 00       	mov    $0x2,%edi
    3cb0:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    3cb5:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3cba:	4c 8b 64 24 40       	mov    0x40(%rsp),%r12
    3cbf:	44 8b 7c 24 48       	mov    0x48(%rsp),%r15d
    3cc4:	e8 37 e7 ff ff       	call   2400 <calloc@plt>

  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    3cc9:	be d8 00 00 00       	mov    $0xd8,%esi
    3cce:	bf 01 00 00 00       	mov    $0x1,%edi
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    3cd3:	48 89 c5             	mov    %rax,%rbp
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    3cd6:	e8 25 e7 ff ff       	call   2400 <calloc@plt>
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3cdb:	be d8 00 00 00       	mov    $0xd8,%esi
    3ce0:	bf 01 00 00 00       	mov    $0x1,%edi
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    3ce5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    3ce9:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3cee:	e8 0d e7 ff ff       	call   2400 <calloc@plt>

  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    3cf3:	be 10 00 00 00       	mov    $0x10,%esi
    3cf8:	bf 02 00 00 00       	mov    $0x2,%edi
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3cfd:	48 89 45 08          	mov    %rax,0x8(%rbp)
    3d01:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    3d06:	e8 f5 e6 ff ff       	call   2400 <calloc@plt>
  for (int x = 0 ; x < io_threads; x++) {
    iomailboxes[x].count = buffer_size;
    iomailboxes[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    3d0b:	be 00 01 00 00       	mov    $0x100,%esi
    3d10:	bf 01 00 00 00       	mov    $0x1,%edi
    iomailboxes[x].count = buffer_size;
    3d15:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    3d1b:	48 89 c5             	mov    %rax,%rbp
    iomailboxes[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    3d1e:	e8 dd e6 ff ff       	call   2400 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      iomailboxes[x].buffer[y].available = 0;
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3d23:	be 20 00 00 00       	mov    $0x20,%esi
    3d28:	bf 64 00 00 00       	mov    $0x64,%edi
    iomailboxes[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    3d2d:	48 89 45 08          	mov    %rax,0x8(%rbp)
    3d31:	49 89 c5             	mov    %rax,%r13
      iomailboxes[x].buffer[y].available = 0;
    3d34:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
    3d3e:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3d48:	e8 b3 e6 ff ff       	call   2400 <calloc@plt>
    iomailboxes[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    3d4d:	be 00 01 00 00       	mov    $0x100,%esi
    3d52:	bf 01 00 00 00       	mov    $0x1,%edi
    iomailboxes[x].count = buffer_size;
    3d57:	c7 45 10 01 00 00 00 	movl   $0x1,0x10(%rbp)
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3d5e:	49 89 85 88 00 00 00 	mov    %rax,0x88(%r13)
    iomailboxes[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    3d65:	e8 96 e6 ff ff       	call   2400 <calloc@plt>
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3d6a:	be 20 00 00 00       	mov    $0x20,%esi
    3d6f:	bf 64 00 00 00       	mov    $0x64,%edi
    iomailboxes[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    3d74:	48 89 45 18          	mov    %rax,0x18(%rbp)
    3d78:	49 89 c5             	mov    %rax,%r13
      iomailboxes[x].buffer[y].available = 0;
    3d7b:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
    3d85:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3d8f:	e8 6c e6 ff ff       	call   2400 <calloc@plt>
    }
  }
  char * send_identity = "send-thread";
  char * recv_identity = "recv-thread";
  char * unknown_identity = "unknown-thread";
  int sharedeventfd = eventfd(0, EFD_NONBLOCK);
    3d94:	be 00 08 00 00       	mov    $0x800,%esi
    3d99:	31 ff                	xor    %edi,%edi
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3d9b:	49 89 85 88 00 00 00 	mov    %rax,0x88(%r13)
  int sharedeventfd = eventfd(0, EFD_NONBLOCK);
    3da2:	e8 79 e7 ff ff       	call   2520 <eventfd@plt>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    3da7:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3dac:	45 31 c0             	xor    %r8d,%r8d
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    3daf:	4c 8b 2d 22 61 00 00 	mov    0x6122(%rip),%r13        # 9ed8 <_IO_stdin_used+0xed8>
    int myring = x % 2;
    int otherring = (myring + 1) % 2;
    if (myring == IO_MODE_SEND) {
      thread_data[x].identity = send_identity; 
    } else if (myring == IO_MODE_RECV) {
      thread_data[x].identity = recv_identity;
    3db6:	48 8d 35 12 57 00 00 	lea    0x5712(%rip),%rsi        # 94cf <_IO_stdin_used+0x4cf>
    3dbd:	4c 8d 1d 17 57 00 00 	lea    0x5717(%rip),%r11        # 94db <_IO_stdin_used+0x4db>
    3dc4:	b9 01 00 00 00       	mov    $0x1,%ecx
    3dc9:	ba 07 00 00 00       	mov    $0x7,%edx
    3dce:	48 89 b7 f8 08 00 00 	mov    %rsi,0x8f8(%rdi)
    3dd5:	4c 89 de             	mov    %r11,%rsi
      thread_data[x].identity = unknown_identity;
    }
    thread_data[x].io_mode = myring;
    thread_data[x].my_io = myring;
    thread_data[x].other_io = otherring;
    thread_data[x].iomailboxes = iomailboxes; 
    3dd8:	48 89 af e8 08 00 00 	mov    %rbp,0x8e8(%rdi)
    thread_data[x].type = IO;
    3ddf:	c7 87 ec 07 00 00 02 00 00 00 	movl   $0x2,0x7ec(%rdi)
    thread_data[x].task_count = 0;
    3de9:	4c 89 af 20 08 00 00 	mov    %r13,0x820(%rdi)
    thread_data[x].io_mode = myring;
    3df0:	c7 87 e4 08 00 00 01 00 00 00 	movl   $0x1,0x8e4(%rdi)
    thread_data[x].other_io = otherring;
    3dfa:	4c 89 af f0 08 00 00 	mov    %r13,0x8f0(%rdi)
    3e01:	bf 01 00 00 00       	mov    $0x1,%edi
  int sharedeventfd = eventfd(0, EFD_NONBLOCK);
    3e06:	89 44 24 10          	mov    %eax,0x10(%rsp)
    3e0a:	31 c0                	xor    %eax,%eax
    3e0c:	e8 9f e6 ff ff       	call   24b0 <__printf_chk@plt>
    printf("%d myring %d other is %d\n", x, myring, otherring);
    thread_data[x].ring = rings[myring]; 
    3e11:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3e16:	4c 8b 54 24 38       	mov    0x38(%rsp),%r10
    thread_data[x]._eventfd = sharedeventfd; 
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3e1b:	be 08 00 00 00       	mov    $0x8,%esi
    thread_data[x]._eventfd = sharedeventfd; 
    3e20:	8b 44 24 10          	mov    0x10(%rsp),%eax
    thread_data[x].ring = rings[myring]; 
    3e24:	4c 89 97 40 08 00 00 	mov    %r10,0x840(%rdi)
    thread_data[x]._eventfd = sharedeventfd; 
    3e2b:	89 87 48 08 00 00    	mov    %eax,0x848(%rdi)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3e31:	bf 02 00 00 00       	mov    $0x2,%edi
    3e36:	e8 c5 e5 ff ff       	call   2400 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3e3b:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3e40:	ba 07 00 00 00       	mov    $0x7,%edx
    3e45:	4c 8d 15 a9 56 00 00 	lea    0x56a9(%rip),%r10        # 94f5 <_IO_stdin_used+0x4f5>
    3e4c:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3e50:	4c 89 d6             	mov    %r10,%rsi
    3e53:	48 89 38             	mov    %rdi,(%rax)
    }
    thread_data[x].threads = my_thread_data;
    3e56:	48 89 87 f8 07 00 00 	mov    %rax,0x7f8(%rdi)
    3e5d:	31 c0                	xor    %eax,%eax
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3e5f:	c7 87 08 08 00 00 02 00 00 00 	movl   $0x2,0x808(%rdi)
    thread_data[x].thread_index = x;
    3e69:	c7 87 e4 07 00 00 07 00 00 00 	movl   $0x7,0x7e4(%rdi)
    3e73:	bf 01 00 00 00       	mov    $0x1,%edi
    3e78:	e8 33 e6 ff ff       	call   24b0 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3e7d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3e82:	4c 89 f1             	mov    %r14,%rcx
    3e85:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3e89:	4c 8d 35 80 20 00 00 	lea    0x2080(%rip),%r14        # 5f10 <io_thread>
    3e90:	4c 89 f2             	mov    %r14,%rdx
    3e93:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3e9a:	e8 31 e6 ff ff       	call   24d0 <pthread_create@plt>
    thread_data[x].type = IO;
    3e9f:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3ea4:	31 c9                	xor    %ecx,%ecx
    3ea6:	31 c0                	xor    %eax,%eax
      thread_data[x].identity = send_identity; 
    3ea8:	48 8d 15 5d 56 00 00 	lea    0x565d(%rip),%rdx        # 950c <_IO_stdin_used+0x50c>
    3eaf:	4c 8d 1d 25 56 00 00 	lea    0x5625(%rip),%r11        # 94db <_IO_stdin_used+0x4db>
    3eb6:	41 b8 01 00 00 00    	mov    $0x1,%r8d
    3ebc:	48 89 97 18 0a 00 00 	mov    %rdx,0xa18(%rdi)
    3ec3:	4c 89 de             	mov    %r11,%rsi
    3ec6:	ba 08 00 00 00       	mov    $0x8,%edx
    thread_data[x].iomailboxes = iomailboxes; 
    3ecb:	48 89 af 08 0a 00 00 	mov    %rbp,0xa08(%rdi)
    thread_data[x].type = IO;
    3ed2:	c7 87 0c 09 00 00 02 00 00 00 	movl   $0x2,0x90c(%rdi)
    thread_data[x].task_count = 0;
    3edc:	4c 89 af 40 09 00 00 	mov    %r13,0x940(%rdi)
    thread_data[x].io_mode = myring;
    3ee3:	c7 87 04 0a 00 00 00 00 00 00 	movl   $0x0,0xa04(%rdi)
    thread_data[x].other_io = otherring;
    3eed:	48 c7 87 10 0a 00 00 01 00 00 00 	movq   $0x1,0xa10(%rdi)
    3ef8:	bf 01 00 00 00       	mov    $0x1,%edi
    3efd:	e8 ae e5 ff ff       	call   24b0 <__printf_chk@plt>
    thread_data[x].ring = rings[myring]; 
    3f02:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    3f07:	4c 8b 4c 24 40       	mov    0x40(%rsp),%r9
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3f0c:	be 08 00 00 00       	mov    $0x8,%esi
    thread_data[x]._eventfd = sharedeventfd; 
    3f11:	8b 44 24 10          	mov    0x10(%rsp),%eax
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3f15:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x].ring = rings[myring]; 
    3f1a:	4c 89 8d 60 09 00 00 	mov    %r9,0x960(%rbp)
    thread_data[x]._eventfd = sharedeventfd; 
    3f21:	89 85 68 09 00 00    	mov    %eax,0x968(%rbp)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3f27:	e8 d4 e4 ff ff       	call   2400 <calloc@plt>
    3f2c:	ba 08 00 00 00       	mov    $0x8,%edx
    3f31:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].thread_count = thread_count;
    3f36:	c7 85 28 09 00 00 02 00 00 00 	movl   $0x2,0x928(%rbp)
      my_thread_data[n] = &thread_data[n]; 
    3f40:	48 89 28             	mov    %rbp,(%rax)
    3f43:	4c 8d 15 ab 55 00 00 	lea    0x55ab(%rip),%r10        # 94f5 <_IO_stdin_used+0x4f5>
    thread_data[x].threads = my_thread_data;
    3f4a:	48 89 85 18 09 00 00 	mov    %rax,0x918(%rbp)
    3f51:	4c 89 d6             	mov    %r10,%rsi
      my_thread_data[n] = &thread_data[n]; 
    3f54:	4c 89 60 08          	mov    %r12,0x8(%rax)
    3f58:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3f5a:	c7 85 04 09 00 00 08 00 00 00 	movl   $0x8,0x904(%rbp)
    3f64:	e8 47 e5 ff ff       	call   24b0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3f69:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3f6e:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3f73:	4c 89 f2             	mov    %r14,%rdx
    3f76:	48 8d 7b 40          	lea    0x40(%rbx),%rdi
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3f7a:	41 be 09 00 00 00    	mov    $0x9,%r14d
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3f80:	48 81 c6 c0 01 00 00 	add    $0x1c0,%rsi
    3f87:	e8 44 e5 ff ff       	call   24d0 <pthread_create@plt>
    3f8c:	ba 09 00 00 00       	mov    $0x9,%edx
    3f91:	48 8d 35 80 55 00 00 	lea    0x5580(%rip),%rsi        # 9518 <_IO_stdin_used+0x518>
    3f98:	31 c0                	xor    %eax,%eax
    3f9a:	bf 01 00 00 00       	mov    $0x1,%edi
    3f9f:	e8 0c e5 ff ff       	call   24b0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3fa4:	48 8d 43 48          	lea    0x48(%rbx),%rax
    3fa8:	48 8b 6c 24 30       	mov    0x30(%rsp),%rbp
    3fad:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3fb2:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3fb7:	48 05 f8 01 00 00    	add    $0x1f8,%rax
    3fbd:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3fc2:	44 89 f8             	mov    %r15d,%eax
    3fc5:	49 89 df             	mov    %rbx,%r15
    3fc8:	89 c3                	mov    %eax,%ebx
    3fca:	44 89 f2             	mov    %r14d,%edx
    3fcd:	48 8d 35 5a 55 00 00 	lea    0x555a(%rip),%rsi        # 952e <_IO_stdin_used+0x52e>
    3fd4:	bf 01 00 00 00       	mov    $0x1,%edi
    3fd9:	31 c0                	xor    %eax,%eax
    3fdb:	e8 d0 e4 ff ff       	call   24b0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    3fe0:	4c 89 6d 40          	mov    %r13,0x40(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3fe4:	be 08 00 00 00       	mov    $0x8,%esi
    3fe9:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = EXTERNAL;
    3fee:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3ff5:	e8 06 e4 ff ff       	call   2400 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3ffa:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    4002:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    4007:	c7 85 c4 00 00 00 01 00 00 00 	movl   $0x1,0xc4(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    4011:	48 89 45 50          	mov    %rax,0x50(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    4015:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    4018:	bf 02 00 00 00       	mov    $0x2,%edi
    401d:	e8 de e3 ff ff       	call   2400 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    4022:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    4027:	44 89 75 04          	mov    %r14d,0x4(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    402b:	48 89 e9             	mov    %rbp,%rcx
    thread_data[x].threads = my_thread_data;
    402e:	48 89 45 18          	mov    %rax,0x18(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    4032:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    4037:	48 8d 15 32 0a 00 00 	lea    0xa32(%rip),%rdx        # 4a70 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    403e:	48 81 c5 20 01 00 00 	add    $0x120,%rbp
      my_thread_data[n] = &thread_data[n]; 
    4045:	48 89 30             	mov    %rsi,(%rax)
    thread_data[x].thread_count = thread_count;
    4048:	48 8b 35 71 5e 00 00 	mov    0x5e71(%rip),%rsi        # 9ec0 <_IO_stdin_used+0xec0>
      my_thread_data[n] = &thread_data[n]; 
    404f:	4c 89 60 08          	mov    %r12,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    4053:	48 89 b5 08 ff ff ff 	mov    %rsi,-0xf8(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    405a:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    405f:	e8 6c e4 ff ff       	call   24d0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    4064:	48 83 44 24 10 08    	addq   $0x8,0x10(%rsp)
    406a:	48 83 84 24 c8 00 00 00 10 	addq   $0x10,0xc8(%rsp)
    4073:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    4079:	41 83 fe 09          	cmp    $0x9,%r14d
    407d:	75 17                	jne    4096 <main+0x1a06>
    407f:	41 be 0a 00 00 00    	mov    $0xa,%r14d
    4085:	e9 40 ff ff ff       	jmp    3fca <main+0x193a>
            CPU_SET(j, sendercpu);
    408a:	48 81 0b ff 0f 00 00 	orq    $0xfff,(%rbx)
          for (int j = 0 ; j < cores ; j++) {
    4091:	e9 a7 ec ff ff       	jmp    2d3d <main+0x6ad>
    4096:	89 d8                	mov    %ebx,%eax
    4098:	4c 89 fb             	mov    %r15,%rbx
    409b:	48 8d 2d a9 54 00 00 	lea    0x54a9(%rip),%rbp        # 954b <_IO_stdin_used+0x54b>
    40a2:	41 89 c7             	mov    %eax,%r15d
    40a5:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    40aa:	4c 8d 68 04          	lea    0x4(%rax),%r13
    40ae:	4c 8d a0 64 0c 00 00 	lea    0xc64(%rax),%r12
    40b5:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    40b9:	41 8b 55 00          	mov    0x0(%r13),%edx
    40bd:	48 89 ee             	mov    %rbp,%rsi
    40c0:	bf 01 00 00 00       	mov    $0x1,%edi
    40c5:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    40c7:	49 81 c5 20 01 00 00 	add    $0x120,%r13
    40ce:	e8 dd e3 ff ff       	call   24b0 <__printf_chk@plt>
    40d3:	4d 39 ec             	cmp    %r13,%r12
    40d6:	75 dd                	jne    40b5 <main+0x1a25>
    40d8:	48 8d 3d 7f 54 00 00 	lea    0x547f(%rip),%rdi        # 955e <_IO_stdin_used+0x55e>
    40df:	45 31 ed             	xor    %r13d,%r13d
    40e2:	4c 8d a4 24 10 01 00 00 	lea    0x110(%rsp),%r12
    40ea:	e8 41 e2 ff ff       	call   2330 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    40ef:	48 8d 2d 86 54 00 00 	lea    0x5486(%rip),%rbp        # 957c <_IO_stdin_used+0x57c>
    void * result; 
    pthread_join(thread[x], &result);
    40f6:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    40fa:	4c 89 e6             	mov    %r12,%rsi
    40fd:	e8 5e e4 ff ff       	call   2560 <pthread_join@plt>
    4102:	44 89 ea             	mov    %r13d,%edx
    4105:	48 89 ee             	mov    %rbp,%rsi
    4108:	bf 01 00 00 00       	mov    $0x1,%edi
    410d:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    410f:	49 83 c5 01          	add    $0x1,%r13
    4113:	e8 98 e3 ff ff       	call   24b0 <__printf_chk@plt>
    4118:	49 83 fd 0b          	cmp    $0xb,%r13
    411c:	75 d8                	jne    40f6 <main+0x1a66>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    411e:	be 08 00 00 00       	mov    $0x8,%esi
    4123:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    4128:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    412a:	e8 d1 e2 ff ff       	call   2400 <calloc@plt>
    412f:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
    4134:	48 89 c5             	mov    %rax,%rbp
    4137:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    4139:	49 89 d1             	mov    %rdx,%r9
    413c:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    413f:	45 8b 51 40          	mov    0x40(%r9),%r10d
    4143:	45 85 d2             	test   %r10d,%r10d
    4146:	0f 8e ac 00 00 00    	jle    41f8 <main+0x1b68>
    414c:	49 8b 79 38          	mov    0x38(%r9),%rdi
    4150:	4d 63 c2             	movslq %r10d,%r8
    4153:	48 63 cb             	movslq %ebx,%rcx
    4156:	49 c1 e0 09          	shl    $0x9,%r8
    415a:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    415f:	49 01 f8             	add    %rdi,%r8
    4162:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    4168:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    416f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    4176:	48 83 c6 60          	add    $0x60,%rsi
    417a:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    4182:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    4186:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    418e:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    4196:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    419e:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    41a5:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    41ad:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    41b4:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    41bb:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    41c2:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    41c6:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    41cd:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    41d4:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    41d8:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    41dc:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    41e0:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    41e4:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    41e8:	4c 39 c7             	cmp    %r8,%rdi
    41eb:	0f 85 77 ff ff ff    	jne    4168 <main+0x1ad8>
    41f1:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    41f5:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    41f8:	49 81 c1 20 01 00 00 	add    $0x120,%r9
    41ff:	45 85 db             	test   %r11d,%r11d
    4202:	75 08                	jne    420c <main+0x1b7c>
    4204:	45 89 fb             	mov    %r15d,%r11d
    4207:	e9 33 ff ff ff       	jmp    413f <main+0x1aaf>
  for (int k = 0 ; k < group_count ; k++) {
    420c:	83 c0 02             	add    $0x2,%eax
    420f:	48 81 c2 40 02 00 00 	add    $0x240,%rdx
    4216:	83 f8 06             	cmp    $0x6,%eax
    4219:	0f 85 1a ff ff ff    	jne    4139 <main+0x1aa9>
    421f:	48 8d 3d 6a 53 00 00 	lea    0x536a(%rip),%rdi        # 9590 <_IO_stdin_used+0x590>
    4226:	e8 05 e1 ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    422b:	48 8d 35 08 52 00 00 	lea    0x5208(%rip),%rsi        # 943a <_IO_stdin_used+0x43a>
    4232:	48 8d 3d 6f 53 00 00 	lea    0x536f(%rip),%rdi        # 95a8 <_IO_stdin_used+0x5a8>
    4239:	e8 b2 e2 ff ff       	call   24f0 <fopen@plt>
    423e:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas2_size; x++) {
    4241:	85 db                	test   %ebx,%ebx
    4243:	7e 73                	jle    42b8 <main+0x1c28>
    4245:	48 63 db             	movslq %ebx,%rbx
    4248:	49 89 ef             	mov    %rbp,%r15
    424b:	4c 8d 2d c7 51 00 00 	lea    0x51c7(%rip),%r13        # 9419 <_IO_stdin_used+0x419>
    4252:	48 8d 6c dd 00       	lea    0x0(%rbp,%rbx,8),%rbp
    4257:	4c 8d 25 ff 51 00 00 	lea    0x51ff(%rip),%r12        # 945d <_IO_stdin_used+0x45d>
    char * c = calloc(250, sizeof(char));
    425e:	be 01 00 00 00       	mov    $0x1,%esi
    4263:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    4268:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    426c:	e8 8f e1 ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4271:	4c 89 e9             	mov    %r13,%rcx
    4274:	ba fa 00 00 00       	mov    $0xfa,%edx
    4279:	be 01 00 00 00       	mov    $0x1,%esi
    427e:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    4281:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    4285:	48 89 df             	mov    %rbx,%rdi
    4288:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    428f:	31 c0                	xor    %eax,%eax
    4291:	e8 0a e3 ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4296:	48 89 da             	mov    %rbx,%rdx
    4299:	4c 89 e6             	mov    %r12,%rsi
    429c:	bf 01 00 00 00       	mov    $0x1,%edi
    42a1:	31 c0                	xor    %eax,%eax
    42a3:	e8 08 e2 ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    42a8:	4c 89 f6             	mov    %r14,%rsi
    42ab:	48 89 df             	mov    %rbx,%rdi
    42ae:	e8 0d e1 ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    42b3:	49 39 ef             	cmp    %rbp,%r15
    42b6:	75 a6                	jne    425e <main+0x1bce>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    42b8:	4c 89 f7             	mov    %r14,%rdi
    42bb:	bd ff ff ff ff       	mov    $0xffffffff,%ebp
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    42c0:	31 db                	xor    %ebx,%ebx
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    42c2:	49 bc db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r12
  fclose(m2);
    42cc:	e8 8f e0 ff ff       	call   2360 <fclose@plt>
  long sents = 0;
    42d1:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long sends = 0;
    42da:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long ingests = 0;
    42e3:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  long total = 0;
    42ec:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
  int datas2_size = 0; 
    42f5:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
    42fd:	4c 8b b4 24 d0 00 00 00 	mov    0xd0(%rsp),%r14
    4305:	41 89 ed             	mov    %ebp,%r13d
    4308:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    430d:	8d 45 02             	lea    0x2(%rbp),%eax
    4310:	89 44 24 48          	mov    %eax,0x48(%rsp)
      int x = (k * threads_per_group) + d;
    4314:	44 89 e8             	mov    %r13d,%eax
    4317:	41 83 c5 01          	add    $0x1,%r13d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    431b:	bf 0a 00 00 00       	mov    $0xa,%edi
        other = abs(x - 1) % total_threads;
    4320:	41 f6 c5 01          	test   $0x1,%r13b
    4324:	8d 50 02             	lea    0x2(%rax),%edx
    4327:	0f 44 c2             	cmove  %edx,%eax
    432a:	48 63 e8             	movslq %eax,%rbp
    432d:	e8 de df ff ff       	call   2310 <putchar@plt>
    4332:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    4337:	bf 01 00 00 00       	mov    $0x1,%edi
    433c:	48 8d 35 6e 52 00 00 	lea    0x526e(%rip),%rsi        # 95b1 <_IO_stdin_used+0x5b1>
    4343:	48 8b 10             	mov    (%rax),%rdx
    4346:	31 c0                	xor    %eax,%eax
    4348:	e8 63 e1 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    434d:	41 8b 56 40          	mov    0x40(%r14),%edx
    4351:	85 d2                	test   %edx,%edx
    4353:	0f 8e 2a 05 00 00    	jle    4883 <main+0x21f3>
    4359:	48 63 ca             	movslq %edx,%rcx
    435c:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    4360:	31 d2                	xor    %edx,%edx
    4362:	48 c1 e1 09          	shl    $0x9,%rcx
    4366:	48 01 c1             	add    %rax,%rcx
    4369:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        v += thread_data[me].tasks[n].v;
    4370:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    4377:	48 05 00 02 00 00    	add    $0x200,%rax
    437d:	48 39 c1             	cmp    %rax,%rcx
    4380:	75 ee                	jne    4370 <main+0x1ce0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    4382:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    4387:	48 8d 44 ed 00       	lea    0x0(%rbp,%rbp,8),%rax
    438c:	48 c1 e0 05          	shl    $0x5,%rax
    4390:	48 01 f8             	add    %rdi,%rax
    4393:	48 63 48 40          	movslq 0x40(%rax),%rcx
    4397:	85 c9                	test   %ecx,%ecx
    4399:	7e 27                	jle    43c2 <main+0x1d32>
    439b:	48 8b 40 38          	mov    0x38(%rax),%rax
    439f:	48 c1 e1 09          	shl    $0x9,%rcx
    43a3:	48 01 c1             	add    %rax,%rcx
    43a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    43b0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    43b7:	48 05 00 02 00 00    	add    $0x200,%rax
    43bd:	48 39 c1             	cmp    %rax,%rcx
    43c0:	75 ee                	jne    43b0 <main+0x1d20>
    43c2:	48 8d 35 fd 51 00 00 	lea    0x51fd(%rip),%rsi        # 95c6 <_IO_stdin_used+0x5c6>
    43c9:	bf 01 00 00 00       	mov    $0x1,%edi
    43ce:	31 c0                	xor    %eax,%eax
    43d0:	e8 db e0 ff ff       	call   24b0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    43d5:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    43da:	bf 01 00 00 00       	mov    $0x1,%edi
    43df:	48 8d 35 0a 56 00 00 	lea    0x560a(%rip),%rsi        # 99f0 <_IO_stdin_used+0x9f0>
    43e6:	48 8b 08             	mov    (%rax),%rcx
    43e9:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    43f3:	48 f7 e9             	imul   %rcx
    43f6:	48 c1 f9 3f          	sar    $0x3f,%rcx
    43fa:	31 c0                	xor    %eax,%eax
    43fc:	48 d1 fa             	sar    %rdx
    43ff:	48 29 ca             	sub    %rcx,%rdx
    4402:	e8 a9 e0 ff ff       	call   24b0 <__printf_chk@plt>
    4407:	bf 0a 00 00 00       	mov    $0xa,%edi
    440c:	e8 ff de ff ff       	call   2310 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    4411:	41 8b 6e 40          	mov    0x40(%r14),%ebp
    4415:	85 ed                	test   %ebp,%ebp
    4417:	0f 8e 3e 01 00 00    	jle    455b <main+0x1ecb>
    441d:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    4422:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    4427:	31 d2                	xor    %edx,%edx
    4429:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    442e:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    4433:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    4438:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        total += thread_data[x].tasks[n].n;
    4440:	49 8b 46 38          	mov    0x38(%r14),%rax
    4444:	49 89 d1             	mov    %rdx,%r9
        sends += thread_data[x].tasks[n].sends;
    4447:	48 89 54 24 38       	mov    %rdx,0x38(%rsp)
    444c:	41 89 d5             	mov    %edx,%r13d
        total += thread_data[x].tasks[n].n;
    444f:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    4453:	31 ed                	xor    %ebp,%ebp
        total += thread_data[x].tasks[n].n;
    4455:	4c 01 c8             	add    %r9,%rax
        sends += thread_data[x].tasks[n].sends;
    4458:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
        total += thread_data[x].tasks[n].n;
    445d:	48 03 b0 08 01 00 00 	add    0x108(%rax),%rsi
        ingests += thread_data[x].tasks[n].ingest_count;
    4464:	48 03 b8 68 01 00 00 	add    0x168(%rax),%rdi
        sends += thread_data[x].tasks[n].sends;
    446b:	4c 03 90 80 01 00 00 	add    0x180(%rax),%r10
    4472:	48 89 74 24 28       	mov    %rsi,0x28(%rsp)
    4477:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    447c:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
    4481:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4488:	8b 54 24 08          	mov    0x8(%rsp),%edx
    448c:	41 89 e8             	mov    %ebp,%r8d
    448f:	44 89 e9             	mov    %r13d,%ecx
    4492:	bf 01 00 00 00       	mov    $0x1,%edi
    4497:	48 8d 35 35 51 00 00 	lea    0x5135(%rip),%rsi        # 95d3 <_IO_stdin_used+0x5d3>
    449e:	31 c0                	xor    %eax,%eax
    44a0:	e8 0b e0 ff ff       	call   24b0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    44a5:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    44aa:	48 89 e8             	mov    %rbp,%rax
    44ad:	41 89 e8             	mov    %ebp,%r8d
    44b0:	49 8b 56 38          	mov    0x38(%r14),%rdx
    44b4:	48 c1 e0 08          	shl    $0x8,%rax
    44b8:	48 83 ec 08          	sub    $0x8,%rsp
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    44bc:	48 83 c5 01          	add    $0x1,%rbp
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    44c0:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    44c8:	48 8b 38             	mov    (%rax),%rdi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    44cb:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    44d2:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    44d9:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    44e0:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    44e7:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    44ee:	bf 01 00 00 00       	mov    $0x1,%edi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    44f3:	48 01 c3             	add    %rax,%rbx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    44f6:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    44f9:	49 01 cf             	add    %rcx,%r15
    44fc:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4500:	48 01 f3             	add    %rsi,%rbx
    4503:	50                   	push   %rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4504:	49 01 d7             	add    %rdx,%r15
    4507:	8b 54 24 18          	mov    0x18(%rsp),%edx
    450b:	44 89 e9             	mov    %r13d,%ecx
    450e:	48 8d 35 fb 54 00 00 	lea    0x54fb(%rip),%rsi        # 9a10 <_IO_stdin_used+0xa10>
    4515:	31 c0                	xor    %eax,%eax
    4517:	e8 94 df ff ff       	call   24b0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    451c:	41 5a                	pop    %r10
    451e:	41 5b                	pop    %r11
    4520:	48 83 fd 06          	cmp    $0x6,%rbp
    4524:	0f 85 5e ff ff ff    	jne    4488 <main+0x1df8>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    452a:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    452f:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    4534:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    4539:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    453e:	48 83 c2 01          	add    $0x1,%rdx
    4542:	41 39 56 40          	cmp    %edx,0x40(%r14)
    4546:	0f 8f f4 fe ff ff    	jg     4440 <main+0x1db0>
    454c:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    4551:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    4556:	48 89 74 24 38       	mov    %rsi,0x38(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    455b:	45 31 ff             	xor    %r15d,%r15d
    455e:	49 83 be a8 00 00 00 00 	cmpq   $0x0,0xa8(%r14)
    4566:	48 8d 2d c3 54 00 00 	lea    0x54c3(%rip),%rbp        # 9a30 <_IO_stdin_used+0xa30>
    456d:	7e 59                	jle    45c8 <main+0x1f38>
    456f:	90                   	nop
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4570:	49 8b 86 98 00 00 00 	mov    0x98(%r14),%rax
    4577:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    457b:	48 83 ec 08          	sub    $0x8,%rsp
    457f:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    4584:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4588:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    458c:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    4590:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    4594:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4597:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    459b:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    459e:	49 f7 e4             	mul    %r12
    45a1:	8b 49 20             	mov    0x20(%rcx),%ecx
    45a4:	56                   	push   %rsi
    45a5:	31 c0                	xor    %eax,%eax
    45a7:	48 89 ee             	mov    %rbp,%rsi
    45aa:	48 c1 ea 12          	shr    $0x12,%rdx
    45ae:	49 89 d1             	mov    %rdx,%r9
    45b1:	ba 02 00 00 00       	mov    $0x2,%edx
    45b6:	e8 f5 de ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    45bb:	41 58                	pop    %r8
    45bd:	41 59                	pop    %r9
    45bf:	4d 39 be a8 00 00 00 	cmp    %r15,0xa8(%r14)
    45c6:	7f a8                	jg     4570 <main+0x1ee0>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    45c8:	41 8b 96 c4 00 00 00 	mov    0xc4(%r14),%edx
    45cf:	85 d2                	test   %edx,%edx
    45d1:	0f 8e 0b 01 00 00    	jle    46e2 <main+0x2052>
    45d7:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    45dc:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    45e0:	45 31 ff             	xor    %r15d,%r15d
    45e3:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    45e8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    45f0:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    45f4:	45 89 fd             	mov    %r15d,%r13d
    45f7:	4a 8d 1c fd 00 00 00 00 	lea    0x0(,%r15,8),%rbx
    45ff:	8b 30                	mov    (%rax),%esi
    4601:	85 f6                	test   %esi,%esi
    4603:	0f 8e c2 00 00 00    	jle    46cb <main+0x203b>
    4609:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    460e:	31 d2                	xor    %edx,%edx
    4610:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4614:	49 89 f8             	mov    %rdi,%r8
    4617:	48 89 d7             	mov    %rdx,%rdi
    461a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4620:	48 89 fd             	mov    %rdi,%rbp
    4623:	45 31 ff             	xor    %r15d,%r15d
    4626:	48 c1 e5 08          	shl    $0x8,%rbp
    462a:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    462e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4634:	85 d2                	test   %edx,%edx
    4636:	7e 78                	jle    46b0 <main+0x2020>
    4638:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    463d:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4640:	4c 89 f9             	mov    %r15,%rcx
    4643:	48 83 ec 08          	sub    $0x8,%rsp
    4647:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    464c:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4650:	48 c1 e1 05          	shl    $0x5,%rcx
    4654:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    465b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    465f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    4663:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4666:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    466a:	4c 2b 01             	sub    (%rcx),%r8
    466d:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    466e:	49 f7 e4             	mul    %r12
    4671:	44 89 e9             	mov    %r13d,%ecx
    4674:	48 8d 35 05 54 00 00 	lea    0x5405(%rip),%rsi        # 9a80 <_IO_stdin_used+0xa80>
    467b:	31 c0                	xor    %eax,%eax
    467d:	48 c1 ea 12          	shr    $0x12,%rdx
    4681:	49 89 d1             	mov    %rdx,%r9
    4684:	ba 02 00 00 00       	mov    $0x2,%edx
    4689:	e8 22 de ff ff       	call   24b0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    468e:	4d 8b 46 50          	mov    0x50(%r14),%r8
    4692:	5e                   	pop    %rsi
    4693:	5f                   	pop    %rdi
    4694:	49 8b 14 18          	mov    (%r8,%rbx,1),%rdx
    4698:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    469c:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    46a0:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    46a7:	7f 97                	jg     4640 <main+0x1fb0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    46a9:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    46ae:	8b 32                	mov    (%rdx),%esi
    46b0:	48 83 c7 01          	add    $0x1,%rdi
    46b4:	39 fe                	cmp    %edi,%esi
    46b6:	0f 8f 64 ff ff ff    	jg     4620 <main+0x1f90>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    46bc:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    46c1:	41 8b 96 c4 00 00 00 	mov    0xc4(%r14),%edx
    46c8:	4c 89 c7             	mov    %r8,%rdi
    46cb:	49 83 c7 01          	add    $0x1,%r15
    46cf:	44 39 fa             	cmp    %r15d,%edx
    46d2:	0f 8f 18 ff ff ff    	jg     45f0 <main+0x1f60>
    46d8:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    46dd:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    46e2:	8b 44 24 48          	mov    0x48(%rsp),%eax
    46e6:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    46ec:	49 81 c6 20 01 00 00 	add    $0x120,%r14
    46f3:	41 39 c5             	cmp    %eax,%r13d
    46f6:	0f 85 18 fc ff ff    	jne    4314 <main+0x1c84>
  for (int k = 0 ; k < group_count ; k++) {
    46fc:	48 81 84 24 d0 00 00 00 40 02 00 00 	addq   $0x240,0xd0(%rsp)
    4708:	48 83 84 24 d8 00 00 00 30 	addq   $0x30,0xd8(%rsp)
    4711:	41 83 fd 05          	cmp    $0x5,%r13d
    4715:	74 08                	je     471f <main+0x208f>
    4717:	44 89 ed             	mov    %r13d,%ebp
    471a:	e9 d6 fb ff ff       	jmp    42f5 <main+0x1c65>
    471f:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    4724:	bf 01 00 00 00       	mov    $0x1,%edi
    4729:	31 c0                	xor    %eax,%eax
    472b:	49 89 df             	mov    %rbx,%r15
    472e:	48 8d 35 ae 4e 00 00 	lea    0x4eae(%rip),%rsi        # 95e3 <_IO_stdin_used+0x5e3>
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    4735:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    473f:	4c 89 f2             	mov    %r14,%rdx
    4742:	e8 69 dd ff ff       	call   24b0 <__printf_chk@plt>
    4747:	bf 0a 00 00 00       	mov    $0xa,%edi
    474c:	e8 bf db ff ff       	call   2310 <putchar@plt>
    4751:	48 8b bc 24 a8 00 00 00 	mov    0xa8(%rsp),%rdi
    4759:	48 8d 35 78 53 00 00 	lea    0x5378(%rip),%rsi        # 9ad8 <_IO_stdin_used+0xad8>
    4760:	31 c0                	xor    %eax,%eax
    4762:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    4766:	bf 01 00 00 00       	mov    $0x1,%edi
    476b:	e8 40 dd ff ff       	call   24b0 <__printf_chk@plt>
    4770:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    4775:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    477a:	48 8d 35 7f 53 00 00 	lea    0x537f(%rip),%rsi        # 9b00 <_IO_stdin_used+0xb00>
    4781:	48 f7 eb             	imul   %rbx
    4784:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4788:	31 c0                	xor    %eax,%eax
    478a:	48 d1 fa             	sar    %rdx
    478d:	48 29 fa             	sub    %rdi,%rdx
    4790:	bf 01 00 00 00       	mov    $0x1,%edi
    4795:	e8 16 dd ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    479a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    479f:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    47a4:	48 8d 35 85 53 00 00 	lea    0x5385(%rip),%rsi        # 9b30 <_IO_stdin_used+0xb30>
    47ab:	48 f7 eb             	imul   %rbx
    47ae:	48 c1 ff 3f          	sar    $0x3f,%rdi
    47b2:	31 c0                	xor    %eax,%eax
    47b4:	48 d1 fa             	sar    %rdx
    47b7:	48 29 fa             	sub    %rdi,%rdx
    47ba:	bf 01 00 00 00       	mov    $0x1,%edi
    47bf:	e8 ec dc ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    47c4:	4c 89 f0             	mov    %r14,%rax
    47c7:	bf 01 00 00 00       	mov    $0x1,%edi
    47cc:	48 8d 35 8d 53 00 00 	lea    0x538d(%rip),%rsi        # 9b60 <_IO_stdin_used+0xb60>
    47d3:	48 f7 eb             	imul   %rbx
    47d6:	4c 89 f0             	mov    %r14,%rax
    47d9:	48 c1 f8 3f          	sar    $0x3f,%rax
    47dd:	48 d1 fa             	sar    %rdx
    47e0:	48 29 c2             	sub    %rax,%rdx
    47e3:	31 c0                	xor    %eax,%eax
    47e5:	e8 c6 dc ff ff       	call   24b0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    47ea:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    47ef:	bf 01 00 00 00       	mov    $0x1,%edi
    47f4:	48 8d 35 fc 4d 00 00 	lea    0x4dfc(%rip),%rsi        # 95f7 <_IO_stdin_used+0x5f7>
    47fb:	48 f7 eb             	imul   %rbx
    47fe:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4803:	48 c1 f8 3f          	sar    $0x3f,%rax
    4807:	48 d1 fa             	sar    %rdx
    480a:	48 29 c2             	sub    %rax,%rdx
    480d:	31 c0                	xor    %eax,%eax
    480f:	48 89 d5             	mov    %rdx,%rbp
    4812:	e8 99 dc ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
    4817:	4c 89 f8             	mov    %r15,%rax
    481a:	bf 01 00 00 00       	mov    $0x1,%edi
    481f:	48 8d 35 5a 53 00 00 	lea    0x535a(%rip),%rsi        # 9b80 <_IO_stdin_used+0xb80>
    4826:	48 f7 eb             	imul   %rbx
    4829:	4c 89 f8             	mov    %r15,%rax
    482c:	48 c1 f8 3f          	sar    $0x3f,%rax
    4830:	48 89 d3             	mov    %rdx,%rbx
    4833:	48 d1 fb             	sar    %rbx
    4836:	48 29 c3             	sub    %rax,%rbx
    4839:	31 c0                	xor    %eax,%eax
    483b:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    483e:	48 29 eb             	sub    %rbp,%rbx
    4841:	e8 6a dc ff ff       	call   24b0 <__printf_chk@plt>
    4846:	31 c0                	xor    %eax,%eax
    4848:	48 89 da             	mov    %rbx,%rdx
    484b:	bf 01 00 00 00       	mov    $0x1,%edi
    4850:	48 8d 35 bc 4d 00 00 	lea    0x4dbc(%rip),%rsi        # 9613 <_IO_stdin_used+0x613>
    4857:	e8 54 dc ff ff       	call   24b0 <__printf_chk@plt>
  return 0;

}
    485c:	48 8b 84 24 28 01 00 00 	mov    0x128(%rsp),%rax
    4864:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    486d:	75 25                	jne    4894 <main+0x2204>
    486f:	48 81 c4 38 01 00 00 	add    $0x138,%rsp
    4876:	31 c0                	xor    %eax,%eax
    4878:	5b                   	pop    %rbx
    4879:	5d                   	pop    %rbp
    487a:	41 5c                	pop    %r12
    487c:	41 5d                	pop    %r13
    487e:	41 5e                	pop    %r14
    4880:	41 5f                	pop    %r15
    4882:	c3                   	ret
      long v = 0;
    4883:	31 d2                	xor    %edx,%edx
    4885:	e9 f8 fa ff ff       	jmp    4382 <main+0x1cf2>
            exit(1);
    488a:	bf 01 00 00 00       	mov    $0x1,%edi
    488f:	e8 7c dc ff ff       	call   2510 <exit@plt>
}
    4894:	e8 e7 da ff ff       	call   2380 <__stack_chk_fail@plt>
    4899:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000048a0 <_start>:
    48a0:	f3 0f 1e fa          	endbr64
    48a4:	31 ed                	xor    %ebp,%ebp
    48a6:	49 89 d1             	mov    %rdx,%r9
    48a9:	5e                   	pop    %rsi
    48aa:	48 89 e2             	mov    %rsp,%rdx
    48ad:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    48b1:	50                   	push   %rax
    48b2:	54                   	push   %rsp
    48b3:	45 31 c0             	xor    %r8d,%r8d
    48b6:	31 c9                	xor    %ecx,%ecx
    48b8:	48 8d 3d d1 dd ff ff 	lea    -0x222f(%rip),%rdi        # 2690 <main>
    48bf:	ff 15 13 77 00 00    	call   *0x7713(%rip)        # bfd8 <__libc_start_main@GLIBC_2.34>
    48c5:	f4                   	hlt
    48c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000048d0 <deregister_tm_clones>:
    48d0:	48 8d 3d 49 77 00 00 	lea    0x7749(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    48d7:	48 8d 05 42 77 00 00 	lea    0x7742(%rip),%rax        # c020 <stderr@GLIBC_2.2.5>
    48de:	48 39 f8             	cmp    %rdi,%rax
    48e1:	74 15                	je     48f8 <deregister_tm_clones+0x28>
    48e3:	48 8b 05 f6 76 00 00 	mov    0x76f6(%rip),%rax        # bfe0 <_ITM_deregisterTMCloneTable@Base>
    48ea:	48 85 c0             	test   %rax,%rax
    48ed:	74 09                	je     48f8 <deregister_tm_clones+0x28>
    48ef:	ff e0                	jmp    *%rax
    48f1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    48f8:	c3                   	ret
    48f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004900 <register_tm_clones>:
    4900:	48 8d 3d 19 77 00 00 	lea    0x7719(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4907:	48 8d 35 12 77 00 00 	lea    0x7712(%rip),%rsi        # c020 <stderr@GLIBC_2.2.5>
    490e:	48 29 fe             	sub    %rdi,%rsi
    4911:	48 89 f0             	mov    %rsi,%rax
    4914:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4918:	48 c1 f8 03          	sar    $0x3,%rax
    491c:	48 01 c6             	add    %rax,%rsi
    491f:	48 d1 fe             	sar    %rsi
    4922:	74 14                	je     4938 <register_tm_clones+0x38>
    4924:	48 8b 05 c5 76 00 00 	mov    0x76c5(%rip),%rax        # bff0 <_ITM_registerTMCloneTable@Base>
    492b:	48 85 c0             	test   %rax,%rax
    492e:	74 08                	je     4938 <register_tm_clones+0x38>
    4930:	ff e0                	jmp    *%rax
    4932:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4938:	c3                   	ret
    4939:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004940 <__do_global_dtors_aux>:
    4940:	f3 0f 1e fa          	endbr64
    4944:	80 3d dd 76 00 00 00 	cmpb   $0x0,0x76dd(%rip)        # c028 <completed.0>
    494b:	75 2b                	jne    4978 <__do_global_dtors_aux+0x38>
    494d:	55                   	push   %rbp
    494e:	48 83 3d a2 76 00 00 00 	cmpq   $0x0,0x76a2(%rip)        # bff8 <__cxa_finalize@GLIBC_2.2.5>
    4956:	48 89 e5             	mov    %rsp,%rbp
    4959:	74 0c                	je     4967 <__do_global_dtors_aux+0x27>
    495b:	48 8b 3d a6 76 00 00 	mov    0x76a6(%rip),%rdi        # c008 <__dso_handle>
    4962:	e8 89 d9 ff ff       	call   22f0 <__cxa_finalize@plt>
    4967:	e8 64 ff ff ff       	call   48d0 <deregister_tm_clones>
    496c:	c6 05 b5 76 00 00 01 	movb   $0x1,0x76b5(%rip)        # c028 <completed.0>
    4973:	5d                   	pop    %rbp
    4974:	c3                   	ret
    4975:	0f 1f 00             	nopl   (%rax)
    4978:	c3                   	ret
    4979:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004980 <frame_dummy>:
    4980:	f3 0f 1e fa          	endbr64
    4984:	e9 77 ff ff ff       	jmp    4900 <register_tm_clones>
    4989:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004990 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4990:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    4994:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    499b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    499f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    49a7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    49ab:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    49af:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    49b6:	48 85 c9             	test   %rcx,%rcx
    49b9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    49c0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    49c4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    49c8:	31 c0                	xor    %eax,%eax
    49ca:	c3                   	ret
    49cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000049d0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    49d0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    49d4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    49db:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    for (int x = 0 ; x < data->task_count ; x++) {
    49e2:	85 c9                	test   %ecx,%ecx
    49e4:	7e 48                	jle    4a2e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    49e6:	48 63 97 30 01 00 00 	movslq 0x130(%rdi),%rdx
    49ed:	49 8b 40 18          	mov    0x18(%r8),%rax
    49f1:	48 c1 e1 09          	shl    $0x9,%rcx
      data->thread->tasks[x].available = 1; 
    49f5:	49 8b 70 38          	mov    0x38(%r8),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    49f9:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    49fd:	48 8b 50 38          	mov    0x38(%rax),%rdx
      data->thread->tasks[x].available = 1; 
    4a01:	31 c0                	xor    %eax,%eax
    4a03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4a08:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4a10:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4a18:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    4a23:	48 05 00 02 00 00    	add    $0x200,%rax
    4a29:	48 39 c1             	cmp    %rax,%rcx
    4a2c:	75 da                	jne    4a08 <barriered_reset+0x38>
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    4a2e:	49 8b 88 f8 00 00 00 	mov    0xf8(%r8),%rcx
    4a35:	8b 01                	mov    (%rcx),%eax
    4a37:	83 f8 ff             	cmp    $0xffffffff,%eax
    4a3a:	74 0e                	je     4a4a <barriered_reset+0x7a>
    4a3c:	41 8b b8 c8 00 00 00 	mov    0xc8(%r8),%edi
    4a43:	8d 57 ff             	lea    -0x1(%rdi),%edx
    4a46:	39 d0                	cmp    %edx,%eax
    4a48:	74 06                	je     4a50 <barriered_reset+0x80>
}
    4a4a:	31 c0                	xor    %eax,%eax
    4a4c:	c3                   	ret
    4a4d:	0f 1f 00             	nopl   (%rax)
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    4a50:	41 83 78 04 01       	cmpl   $0x1,0x4(%r8)
    4a55:	75 f3                	jne    4a4a <barriered_reset+0x7a>
    data->thread->group_data->arrived++;
    4a57:	49 8b 80 e0 00 00 00 	mov    0xe0(%r8),%rax
    4a5e:	83 00 01             	addl   $0x1,(%rax)
    data->thread->global->request_group_sync = -1;
    4a61:	c7 01 ff ff ff ff    	movl   $0xffffffff,(%rcx)
    4a67:	eb e1                	jmp    4a4a <barriered_reset+0x7a>
    4a69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004a70 <external_thread>:
void * external_thread(void *arg) {
    4a70:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    4a74:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4a78:	0f 85 f8 00 00 00    	jne    4b76 <external_thread+0x106>
void * external_thread(void *arg) {
    4a7e:	41 57                	push   %r15
    4a80:	4c 8d 3d 7d 45 00 00 	lea    0x457d(%rip),%r15        # 9004 <_IO_stdin_used+0x4>
    4a87:	41 56                	push   %r14
    4a89:	49 89 fe             	mov    %rdi,%r14
    4a8c:	41 55                	push   %r13
    4a8e:	41 54                	push   %r12
    4a90:	55                   	push   %rbp
    4a91:	53                   	push   %rbx
    4a92:	48 83 ec 08          	sub    $0x8,%rsp
    4a96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int b = 0; b < data->buffers_count; b++) {
    4aa0:	41 8b 8e c4 00 00 00 	mov    0xc4(%r14),%ecx
    4aa7:	85 c9                	test   %ecx,%ecx
    4aa9:	7e 57                	jle    4b02 <external_thread+0x92>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4aab:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4aaf:	45 31 ed             	xor    %r13d,%r13d
    4ab2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4ab8:	4e 8d 24 ed 00 00 00 00 	lea    0x0(,%r13,8),%r12
    4ac0:	31 db                	xor    %ebx,%ebx
    4ac2:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    4ac6:	48 8b 06             	mov    (%rsi),%rax
    4ac9:	8b 10                	mov    (%rax),%edx
    4acb:	85 d2                	test   %edx,%edx
    4acd:	7e 2a                	jle    4af9 <external_thread+0x89>
    4acf:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    4ad3:	48 89 dd             	mov    %rbx,%rbp
    4ad6:	48 c1 e5 08          	shl    $0x8,%rbp
    4ada:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4ade:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    4ae5:	45 85 c0             	test   %r8d,%r8d
    4ae8:	74 36                	je     4b20 <external_thread+0xb0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4aea:	48 83 c3 01          	add    $0x1,%rbx
    4aee:	39 da                	cmp    %ebx,%edx
    4af0:	7f e1                	jg     4ad3 <external_thread+0x63>
    for (int b = 0; b < data->buffers_count; b++) {
    4af2:	41 8b 8e c4 00 00 00 	mov    0xc4(%r14),%ecx
    4af9:	49 83 c5 01          	add    $0x1,%r13
    4afd:	44 39 e9             	cmp    %r13d,%ecx
    4b00:	7f b6                	jg     4ab8 <external_thread+0x48>
  while (data->running == 1) {
    4b02:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    4b07:	74 97                	je     4aa0 <external_thread+0x30>
}
    4b09:	48 83 c4 08          	add    $0x8,%rsp
    4b0d:	31 c0                	xor    %eax,%eax
    4b0f:	5b                   	pop    %rbx
    4b10:	5d                   	pop    %rbp
    4b11:	41 5c                	pop    %r12
    4b13:	41 5d                	pop    %r13
    4b15:	41 5e                	pop    %r14
    4b17:	41 5f                	pop    %r15
    4b19:	c3                   	ret
    4b1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    4b20:	4c 89 38             	mov    %r15,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    4b23:	48 8b 06             	mov    (%rsi),%rax
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4b26:	48 83 c3 01          	add    $0x1,%rbx
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    4b2a:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4b2e:	48 01 ef             	add    %rbp,%rdi
    4b31:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    4b38:	48 c1 e6 05          	shl    $0x5,%rsi
    4b3c:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4b43:	bf 04 00 00 00       	mov    $0x4,%edi
    4b48:	e8 03 d8 ff ff       	call   2350 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4b4d:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4b51:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    4b55:	48 8b 06             	mov    (%rsi),%rax
    4b58:	48 8b 50 08          	mov    0x8(%rax),%rdx
    4b5c:	c7 84 2a 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rdx,%rbp,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4b67:	8b 10                	mov    (%rax),%edx
    4b69:	39 da                	cmp    %ebx,%edx
    4b6b:	0f 8f 5e ff ff ff    	jg     4acf <external_thread+0x5f>
    4b71:	e9 7c ff ff ff       	jmp    4af2 <external_thread+0x82>
}
    4b76:	31 c0                	xor    %eax,%eax
    4b78:	c3                   	ret
    4b79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004b80 <timer_thread>:
void* timer_thread(void *arg) {
    4b80:	f3 0f 1e fa          	endbr64
    4b84:	41 57                	push   %r15
    4b86:	48 8d 35 83 44 00 00 	lea    0x4483(%rip),%rsi        # 9010 <_IO_stdin_used+0x10>
    4b8d:	49 89 ff             	mov    %rdi,%r15
    4b90:	41 56                	push   %r14
    4b92:	41 55                	push   %r13
    4b94:	41 54                	push   %r12
    4b96:	55                   	push   %rbp
    4b97:	53                   	push   %rbx
    4b98:	48 83 ec 58          	sub    $0x58,%rsp
    4b9c:	8b 57 04             	mov    0x4(%rdi),%edx
    4b9f:	bf 01 00 00 00       	mov    $0x1,%edi
    4ba4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4bad:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    4bb2:	31 c0                	xor    %eax,%eax
    4bb4:	e8 f7 d8 ff ff       	call   24b0 <__printf_chk@plt>
  struct timespec preempt = {
    4bb9:	66 0f 6f 05 df 51 00 00 	movdqa 0x51df(%rip),%xmm0        # 9da0 <_IO_stdin_used+0xda0>
    4bc1:	ba 88 13 00 00       	mov    $0x1388,%edx
    4bc6:	31 c0                	xor    %eax,%eax
    4bc8:	48 8d 35 53 44 00 00 	lea    0x4453(%rip),%rsi        # 9022 <_IO_stdin_used+0x22>
    4bcf:	bf 01 00 00 00       	mov    $0x1,%edi
    4bd4:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4bd9:	e8 d2 d8 ff ff       	call   24b0 <__printf_chk@plt>
  while (data->running && n < times) {
    4bde:	41 8b 47 44          	mov    0x44(%r15),%eax
    4be2:	89 c3                	mov    %eax,%ebx
    4be4:	85 c0                	test   %eax,%eax
    4be6:	0f 84 97 00 00 00    	je     4c83 <timer_thread+0x103>
  int n = 0;
    4bec:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    4bef:	31 db                	xor    %ebx,%ebx
    4bf1:	49 89 e5             	mov    %rsp,%r13
    y++;
    4bf4:	31 ed                	xor    %ebp,%ebp
    4bf6:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    nanosleep(&preempt , &rem2);
    4bfb:	4c 89 e7             	mov    %r12,%rdi
    4bfe:	4c 89 ee             	mov    %r13,%rsi
    n++;
    4c01:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    4c05:	e8 96 d7 ff ff       	call   23a0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c0a:	49 63 47 30          	movslq 0x30(%r15),%rax
    y++;
    4c0e:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c11:	85 c0                	test   %eax,%eax
    4c13:	7e 4a                	jle    4c5f <timer_thread+0xdf>
    4c15:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4c19:	4c 63 c3             	movslq %ebx,%r8
    4c1c:	49 c1 e0 09          	shl    $0x9,%r8
    4c20:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4c24:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4c28:	48 8b 19             	mov    (%rcx),%rbx
    4c2b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c2d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4c31:	99                   	cltd
    4c32:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4c35:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4c39:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    4c3c:	48 63 d2             	movslq %edx,%rdx
    4c3f:	48 c1 e2 09          	shl    $0x9,%rdx
    4c43:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4c4e:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c5a:	49 39 c9             	cmp    %rcx,%r9
    4c5d:	75 c9                	jne    4c28 <timer_thread+0xa8>
    if (y >= data->threads[0]->task_count) {
    4c5f:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
    4c63:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    y++;
    4c67:	89 fb                	mov    %edi,%ebx
    if (y >= data->threads[0]->task_count) {
    4c69:	48 8b 00             	mov    (%rax),%rax
    y++;
    4c6c:	39 78 40             	cmp    %edi,0x40(%rax)
    4c6f:	0f 4e dd             	cmovle %ebp,%ebx
  while (data->running && n < times) {
    4c72:	85 c9                	test   %ecx,%ecx
    4c74:	74 0d                	je     4c83 <timer_thread+0x103>
    4c76:	41 81 fe 88 13 00 00 	cmp    $0x1388,%r14d
    4c7d:	0f 85 78 ff ff ff    	jne    4bfb <timer_thread+0x7b>
    4c83:	48 8d 3d ae 43 00 00 	lea    0x43ae(%rip),%rdi        # 9038 <_IO_stdin_used+0x38>
    4c8a:	e8 a1 d6 ff ff       	call   2330 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c8f:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4c93:	85 d2                	test   %edx,%edx
    4c95:	7e 6e                	jle    4d05 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    4c97:	49 63 47 40          	movslq 0x40(%r15),%rax
    4c9b:	85 c0                	test   %eax,%eax
    4c9d:	7e 66                	jle    4d05 <timer_thread+0x185>
    4c9f:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4ca3:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4ca7:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4caf:	31 c9                	xor    %ecx,%ecx
    4cb1:	48 89 c6             	mov    %rax,%rsi
    4cb4:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4cb8:	48 8b 40 38          	mov    0x38(%rax),%rax
    4cbc:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4cc0:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4cc6:	74 18                	je     4ce0 <timer_thread+0x160>
    4cc8:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4cd2:	48 05 00 02 00 00    	add    $0x200,%rax
    4cd8:	48 39 c2             	cmp    %rax,%rdx
    4cdb:	74 1f                	je     4cfc <timer_thread+0x17c>
    4cdd:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->tasks[y].sending = 0;
    4ce0:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4cea:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4cf0:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4cf7:	48 39 c2             	cmp    %rax,%rdx
    4cfa:	75 e4                	jne    4ce0 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    4cfc:	48 83 c1 08          	add    $0x8,%rcx
    4d00:	48 39 cf             	cmp    %rcx,%rdi
    4d03:	75 af                	jne    4cb4 <timer_thread+0x134>
  struct timespec drain = {
    4d05:	66 0f 6f 05 a3 50 00 00 	movdqa 0x50a3(%rip),%xmm0        # 9db0 <_IO_stdin_used+0xdb0>
    4d0d:	41 89 dc             	mov    %ebx,%r12d
    4d10:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4d15:	49 63 47 28          	movslq 0x28(%r15),%rax
    y++;
    4d19:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    4d1e:	85 c0                	test   %eax,%eax
    4d20:	7e 49                	jle    4d6b <timer_thread+0x1eb>
    4d22:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4d26:	49 63 ec             	movslq %r12d,%rbp
    4d29:	48 c1 e5 09          	shl    $0x9,%rbp
    4d2d:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4d31:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4d38:	48 8b 19             	mov    (%rcx),%rbx
    4d3b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    4d3d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4d41:	99                   	cltd
    4d42:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4d45:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4d49:	48 63 d2             	movslq %edx,%rdx
    4d4c:	48 c1 e2 09          	shl    $0x9,%rdx
    4d50:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4d5b:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4d66:	49 39 c8             	cmp    %rcx,%r8
    4d69:	75 cd                	jne    4d38 <timer_thread+0x1b8>
    if (y >= data->threads[0]->task_count) {
    4d6b:	49 8b 77 18          	mov    0x18(%r15),%rsi
    y++;
    4d6f:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    4d72:	48 8b 06             	mov    (%rsi),%rax
    y++;
    4d75:	39 78 40             	cmp    %edi,0x40(%rax)
    4d78:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4d7c:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4d80:	85 ff                	test   %edi,%edi
    4d82:	0f 8e ac 01 00 00    	jle    4f34 <timer_thread+0x3b4>
    4d88:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    4d8b:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    4d91:	4c 89 f5             	mov    %r14,%rbp
    4d94:	0f 1f 40 00          	nopl   0x0(%rax)
    4d98:	89 eb                	mov    %ebp,%ebx
      for (int y = 0 ; y < 2 ; y++) {
    4d9a:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    4da2:	45 31 f6             	xor    %r14d,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4da5:	85 ff                	test   %edi,%edi
    4da7:	7e 7f                	jle    4e28 <timer_thread+0x2a8>
    4da9:	4c 89 f6             	mov    %r14,%rsi
    4dac:	48 63 cf             	movslq %edi,%rcx
    4daf:	45 31 c0             	xor    %r8d,%r8d
    4db2:	48 c1 e6 09          	shl    $0x9,%rsi
    4db6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (x == k) { continue; }
    4dc0:	41 39 e8             	cmp    %ebp,%r8d
    4dc3:	74 45                	je     4e0a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4dc5:	49 8b 47 18          	mov    0x18(%r15),%rax
    4dc9:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    4dcd:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4dd1:	4c 89 c0             	mov    %r8,%rax
    4dd4:	48 c1 e0 08          	shl    $0x8,%rax
    4dd8:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4de0:	48 8b 10             	mov    (%rax),%rdx
    4de3:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    4dea:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4df1:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4df8:	4d 85 c9             	test   %r9,%r9
    4dfb:	0f 8f 97 00 00 00    	jg     4e98 <timer_thread+0x318>
    4e01:	4d 85 db             	test   %r11,%r11
    4e04:	0f 8f 8e 00 00 00    	jg     4e98 <timer_thread+0x318>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4e0a:	49 83 c0 01          	add    $0x1,%r8
    4e0e:	4c 39 c1             	cmp    %r8,%rcx
    4e11:	75 ad                	jne    4dc0 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    4e13:	49 83 fe 01          	cmp    $0x1,%r14
    4e17:	74 0f                	je     4e28 <timer_thread+0x2a8>
    4e19:	41 be 01 00 00 00    	mov    $0x1,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4e1f:	85 ff                	test   %edi,%edi
    4e21:	7f 86                	jg     4da9 <timer_thread+0x229>
    4e23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4e28:	48 83 c5 01          	add    $0x1,%rbp
    4e2c:	39 ef                	cmp    %ebp,%edi
    4e2e:	0f 8f 64 ff ff ff    	jg     4d98 <timer_thread+0x218>
    4e34:	44 89 d5             	mov    %r10d,%ebp
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4e37:	85 ff                	test   %edi,%edi
    4e39:	7e 3b                	jle    4e76 <timer_thread+0x2f6>
    4e3b:	31 db                	xor    %ebx,%ebx
    int all_waited = 1;
    4e3d:	bf 01 00 00 00       	mov    $0x1,%edi
    4e42:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4e46:	41 8b 57 40          	mov    0x40(%r15),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4e4a:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4e4e:	48 8b 40 38          	mov    0x38(%rax),%rax
    4e52:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    4e58:	39 d1                	cmp    %edx,%ecx
    4e5a:	0f 8c a8 00 00 00    	jl     4f08 <timer_thread+0x388>
    4e60:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    4e66:	39 d0                	cmp    %edx,%eax
    4e68:	7c 6e                	jl     4ed8 <timer_thread+0x358>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4e6a:	48 83 c3 01          	add    $0x1,%rbx
    4e6e:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4e72:	7f d6                	jg     4e4a <timer_thread+0x2ca>
    4e74:	21 fd                	and    %edi,%ebp
    if (all_empty == 1 && all_waited == 1) {
    4e76:	85 ed                	test   %ebp,%ebp
    4e78:	0f 85 b6 00 00 00    	jne    4f34 <timer_thread+0x3b4>
      nanosleep(&drain , &drainrem);
    4e7e:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4e83:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4e88:	e8 13 d5 ff ff       	call   23a0 <nanosleep@plt>
    4e8d:	e9 83 fe ff ff       	jmp    4d15 <timer_thread+0x195>
    4e92:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4e98:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    4e9e:	48 83 ec 08          	sub    $0x8,%rsp
    4ea2:	bf 01 00 00 00       	mov    $0x1,%edi
    4ea7:	44 89 f1             	mov    %r14d,%ecx
    4eaa:	48 8d 35 ac 41 00 00 	lea    0x41ac(%rip),%rsi        # 905d <_IO_stdin_used+0x5d>
    4eb1:	50                   	push   %rax
    4eb2:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    4eb8:	89 da                	mov    %ebx,%edx
    4eba:	50                   	push   %rax
    4ebb:	31 c0                	xor    %eax,%eax
    4ebd:	41 53                	push   %r11
    4ebf:	e8 ec d5 ff ff       	call   24b0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4ec4:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4ec8:	48 83 c4 20          	add    $0x20,%rsp
            all_empty = 0;
    4ecc:	45 31 d2             	xor    %r10d,%r10d
    4ecf:	e9 3f ff ff ff       	jmp    4e13 <timer_thread+0x293>
    4ed4:	0f 1f 40 00          	nopl   0x0(%rax)
    4ed8:	89 c2                	mov    %eax,%edx
    4eda:	bf 01 00 00 00       	mov    $0x1,%edi
    4edf:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4ee1:	48 83 c3 01          	add    $0x1,%rbx
    4ee5:	48 8d 35 54 44 00 00 	lea    0x4454(%rip),%rsi        # 9340 <_IO_stdin_used+0x340>
    4eec:	e8 bf d5 ff ff       	call   24b0 <__printf_chk@plt>
          all_waited = 0; 
    4ef1:	31 ff                	xor    %edi,%edi
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4ef3:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4ef7:	0f 8f 45 ff ff ff    	jg     4e42 <timer_thread+0x2c2>
    4efd:	e9 72 ff ff ff       	jmp    4e74 <timer_thread+0x2f4>
    4f02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4f08:	89 ca                	mov    %ecx,%edx
    4f0a:	48 8d 35 2f 44 00 00 	lea    0x442f(%rip),%rsi        # 9340 <_IO_stdin_used+0x340>
    4f11:	bf 01 00 00 00       	mov    $0x1,%edi
    4f16:	31 c0                	xor    %eax,%eax
    4f18:	e8 93 d5 ff ff       	call   24b0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4f1d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4f21:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    4f25:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4f27:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4f2b:	48 8b 40 38          	mov    0x38(%rax),%rax
    4f2f:	e9 2c ff ff ff       	jmp    4e60 <timer_thread+0x2e0>
    4f34:	48 8d 3d 19 41 00 00 	lea    0x4119(%rip),%rdi        # 9054 <_IO_stdin_used+0x54>
    4f3b:	e8 f0 d3 ff ff       	call   2330 <puts@plt>
  while (data->running) {
    4f40:	41 8b 57 44          	mov    0x44(%r15),%edx
    4f44:	85 d2                	test   %edx,%edx
    4f46:	0f 84 e8 00 00 00    	je     5034 <timer_thread+0x4b4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4f4c:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4f50:	31 db                	xor    %ebx,%ebx
    4f52:	48 8d 2d 21 41 00 00 	lea    0x4121(%rip),%rbp        # 907a <_IO_stdin_used+0x7a>
    4f59:	4c 8d 25 35 41 00 00 	lea    0x4135(%rip),%r12        # 9095 <_IO_stdin_used+0x95>
    4f60:	85 c0                	test   %eax,%eax
    4f62:	7e 38                	jle    4f9c <timer_thread+0x41c>
    4f64:	0f 1f 40 00          	nopl   0x0(%rax)
    4f68:	31 c0                	xor    %eax,%eax
    4f6a:	89 da                	mov    %ebx,%edx
    4f6c:	48 89 ee             	mov    %rbp,%rsi
    4f6f:	bf 01 00 00 00       	mov    $0x1,%edi
    4f74:	e8 37 d5 ff ff       	call   24b0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4f79:	49 8b 47 18          	mov    0x18(%r15),%rax
    4f7d:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4f81:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4f85:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4f8c:	0f 84 cf 00 00 00    	je     5061 <timer_thread+0x4e1>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4f92:	48 83 c3 01          	add    $0x1,%rbx
    4f96:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4f9a:	7f cc                	jg     4f68 <timer_thread+0x3e8>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4f9c:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4fa0:	85 d2                	test   %edx,%edx
    4fa2:	7e 7c                	jle    5020 <timer_thread+0x4a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    4fa4:	41 8b 47 40          	mov    0x40(%r15),%eax
    4fa8:	85 c0                	test   %eax,%eax
    4faa:	7e 74                	jle    5020 <timer_thread+0x4a0>
    4fac:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4faf:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4fb3:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4fbb:	31 c9                	xor    %ecx,%ecx
    4fbd:	48 c1 e6 09          	shl    $0x9,%rsi
    4fc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4fc8:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4fcc:	48 8b 40 38          	mov    0x38(%rax),%rax
    4fd0:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4fd4:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4fda:	74 1c                	je     4ff8 <timer_thread+0x478>
    4fdc:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4fe6:	48 05 00 02 00 00    	add    $0x200,%rax
    4fec:	48 39 d0             	cmp    %rdx,%rax
    4fef:	74 26                	je     5017 <timer_thread+0x497>
    4ff1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4ff8:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    5002:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    5008:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    5012:	48 39 d0             	cmp    %rdx,%rax
    5015:	75 e1                	jne    4ff8 <timer_thread+0x478>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    5017:	48 83 c1 08          	add    $0x8,%rcx
    501b:	48 39 cf             	cmp    %rcx,%rdi
    501e:	75 a8                	jne    4fc8 <timer_thread+0x448>
    5020:	48 8d 3d 80 40 00 00 	lea    0x4080(%rip),%rdi        # 90a7 <_IO_stdin_used+0xa7>
    5027:	e8 04 d3 ff ff       	call   2330 <puts@plt>
    data->running = 0;
    502c:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    5034:	48 8d 3d 73 40 00 00 	lea    0x4073(%rip),%rdi        # 90ae <_IO_stdin_used+0xae>
    503b:	e8 f0 d2 ff ff       	call   2330 <puts@plt>
}
    5040:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    5045:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    504e:	75 41                	jne    5091 <timer_thread+0x511>
    5050:	48 83 c4 58          	add    $0x58,%rsp
    5054:	31 c0                	xor    %eax,%eax
    5056:	5b                   	pop    %rbx
    5057:	5d                   	pop    %rbp
    5058:	41 5c                	pop    %r12
    505a:	41 5d                	pop    %r13
    505c:	41 5e                	pop    %r14
    505e:	41 5f                	pop    %r15
    5060:	c3                   	ret
    5061:	4c 89 e7             	mov    %r12,%rdi
    5064:	e8 c7 d2 ff ff       	call   2330 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    5069:	49 8b 47 18          	mov    0x18(%r15),%rax
    506d:	be 01 00 00 00       	mov    $0x1,%esi
    5072:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    5076:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    507a:	8b 78 68             	mov    0x68(%rax),%edi
    507d:	e8 de d3 ff ff       	call   2460 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    5082:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    5086:	0f 8f dc fe ff ff    	jg     4f68 <timer_thread+0x3e8>
    508c:	e9 0b ff ff ff       	jmp    4f9c <timer_thread+0x41c>
}
    5091:	e8 ea d2 ff ff       	call   2380 <__stack_chk_fail@plt>
    5096:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000050a0 <minf>:
int minf(int a, int b) {
    50a0:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    50a4:	39 f7                	cmp    %esi,%edi
    50a6:	89 f0                	mov    %esi,%eax
    50a8:	0f 4e c7             	cmovle %edi,%eax
}
    50ab:	c3                   	ret
    50ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000050b0 <maxf>:
int maxf(int a, int b) {
    50b0:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    50b4:	39 f7                	cmp    %esi,%edi
    50b6:	89 f0                	mov    %esi,%eax
    50b8:	0f 4d c7             	cmovge %edi,%eax
}
    50bb:	c3                   	ret
    50bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000050c0 <strtolower>:
void strtolower(char *str) {
    50c0:	f3 0f 1e fa          	endbr64
    50c4:	55                   	push   %rbp
    50c5:	53                   	push   %rbx
    50c6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    50ca:	48 0f be 1f          	movsbq (%rdi),%rbx
    50ce:	84 db                	test   %bl,%bl
    50d0:	74 24                	je     50f6 <strtolower+0x36>
    50d2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    50d5:	e8 b6 d4 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    50da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    50e0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    50e3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    50e7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    50ea:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    50ed:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    50f2:	84 db                	test   %bl,%bl
    50f4:	75 ea                	jne    50e0 <strtolower+0x20>
}
    50f6:	48 83 c4 08          	add    $0x8,%rsp
    50fa:	5b                   	pop    %rbx
    50fb:	5d                   	pop    %rbp
    50fc:	c3                   	ret
    50fd:	0f 1f 00             	nopl   (%rax)

0000000000005100 <zh_malloc>:
void *zh_malloc(size_t size) {
    5100:	f3 0f 1e fa          	endbr64
    5104:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    5108:	e8 63 d3 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    510d:	48 85 c0             	test   %rax,%rax
    5110:	74 05                	je     5117 <zh_malloc+0x17>
}
    5112:	48 83 c4 08          	add    $0x8,%rsp
    5116:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5117:	48 8b 0d 02 6f 00 00 	mov    0x6f02(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    511e:	ba 28 00 00 00       	mov    $0x28,%edx
    5123:	be 01 00 00 00       	mov    $0x1,%esi
    5128:	48 8d 3d f9 44 00 00 	lea    0x44f9(%rip),%rdi        # 9628 <_IO_stdin_used+0x628>
    512f:	e8 fc d3 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5134:	bf 01 00 00 00       	mov    $0x1,%edi
    5139:	e8 d2 d3 ff ff       	call   2510 <exit@plt>
    513e:	66 90                	xchg   %ax,%ax

0000000000005140 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    5140:	f3 0f 1e fa          	endbr64
    5144:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    5145:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    514a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    514d:	e8 5e d2 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    5152:	48 85 c0             	test   %rax,%rax
    5155:	74 11                	je     5168 <get_filename_ext+0x28>
    5157:	48 39 c3             	cmp    %rax,%rbx
    515a:	74 0c                	je     5168 <get_filename_ext+0x28>
    return dot + 1;
    515c:	48 83 c0 01          	add    $0x1,%rax
}
    5160:	5b                   	pop    %rbx
    5161:	c3                   	ret
    5162:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    5168:	48 8d 05 87 3f 00 00 	lea    0x3f87(%rip),%rax        # 90f6 <_IO_stdin_used+0xf6>
}
    516f:	5b                   	pop    %rbx
    5170:	c3                   	ret
    5171:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    517c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005180 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    5180:	f3 0f 1e fa          	endbr64
    5184:	41 55                	push   %r13
    5186:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5189:	48 89 fe             	mov    %rdi,%rsi
    518c:	41 54                	push   %r12
    518e:	55                   	push   %rbp
    518f:	48 89 d5             	mov    %rdx,%rbp
    5192:	ba 00 04 00 00       	mov    $0x400,%edx
    5197:	53                   	push   %rbx
    5198:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    519f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    51a8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    51b0:	31 c0                	xor    %eax,%eax
    51b2:	49 89 e4             	mov    %rsp,%r12
    51b5:	4c 89 e7             	mov    %r12,%rdi
    51b8:	e8 d3 d2 ff ff       	call   2490 <__strcpy_chk@plt>
    for (; *str; ++str)
    51bd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    51c2:	84 db                	test   %bl,%bl
    51c4:	74 24                	je     51ea <send_headers+0x6a>
        *str = (char)tolower(*str);
    51c6:	e8 c5 d3 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    51cb:	48 8b 08             	mov    (%rax),%rcx
    51ce:	4c 89 e0             	mov    %r12,%rax
    51d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    51d8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    51db:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    51df:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    51e2:	48 0f be 18          	movsbq (%rax),%rbx
    51e6:	84 db                	test   %bl,%bl
    51e8:	75 ee                	jne    51d8 <send_headers+0x58>
    void *buf = malloc(size);
    51ea:	bf 11 00 00 00       	mov    $0x11,%edi
    51ef:	e8 7c d2 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    51f4:	48 85 c0             	test   %rax,%rax
    51f7:	0f 84 7e 04 00 00    	je     567b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    51fd:	66 0f 6f 05 bb 4b 00 00 	movdqa 0x4bbb(%rip),%xmm0        # 9dc0 <_IO_stdin_used+0xdc0>
    iov[0].iov_base = zh_malloc(slen);
    5205:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    5209:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    520e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    5216:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    521a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    521d:	e8 4e d2 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5222:	48 85 c0             	test   %rax,%rax
    5225:	0f 84 50 04 00 00    	je     567b <send_headers+0x4fb>
    522b:	66 0f 6f 05 9d 4b 00 00 	movdqa 0x4b9d(%rip),%xmm0        # 9dd0 <_IO_stdin_used+0xdd0>
    iov[1].iov_base = zh_malloc(slen);
    5233:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    5237:	4c 89 e7             	mov    %r12,%rdi
    523a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    5244:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    524c:	0f 11 00             	movups %xmm0,(%rax)
    524f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    5253:	be 2e 00 00 00       	mov    $0x2e,%esi
    5258:	e8 53 d1 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    525d:	48 85 c0             	test   %rax,%rax
    5260:	0f 84 ea 02 00 00    	je     5550 <send_headers+0x3d0>
    5266:	4c 39 e0             	cmp    %r12,%rax
    5269:	0f 84 e1 02 00 00    	je     5550 <send_headers+0x3d0>
    return dot + 1;
    526f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    5273:	48 8d 3d 4a 3e 00 00 	lea    0x3e4a(%rip),%rdi        # 90c4 <_IO_stdin_used+0xc4>
    527a:	48 89 de             	mov    %rbx,%rsi
    527d:	e8 8e d1 ff ff       	call   2410 <strcmp@plt>
    5282:	85 c0                	test   %eax,%eax
    5284:	75 20                	jne    52a6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5286:	66 0f 6f 05 52 4b 00 00 	movdqa 0x4b52(%rip),%xmm0        # 9de0 <_IO_stdin_used+0xde0>
    528e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5296:	66 0f 6f 05 52 4b 00 00 	movdqa 0x4b52(%rip),%xmm0        # 9df0 <_IO_stdin_used+0xdf0>
    529e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    52a6:	48 89 de             	mov    %rbx,%rsi
    52a9:	48 8d 3d 18 3e 00 00 	lea    0x3e18(%rip),%rdi        # 90c8 <_IO_stdin_used+0xc8>
    52b0:	e8 5b d1 ff ff       	call   2410 <strcmp@plt>
    52b5:	85 c0                	test   %eax,%eax
    52b7:	75 20                	jne    52d9 <send_headers+0x159>
    52b9:	66 0f 6f 05 1f 4b 00 00 	movdqa 0x4b1f(%rip),%xmm0        # 9de0 <_IO_stdin_used+0xde0>
    52c1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    52c9:	66 0f 6f 05 1f 4b 00 00 	movdqa 0x4b1f(%rip),%xmm0        # 9df0 <_IO_stdin_used+0xdf0>
    52d1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    52d9:	48 89 de             	mov    %rbx,%rsi
    52dc:	48 8d 3d ea 3d 00 00 	lea    0x3dea(%rip),%rdi        # 90cd <_IO_stdin_used+0xcd>
    52e3:	e8 28 d1 ff ff       	call   2410 <strcmp@plt>
    52e8:	85 c0                	test   %eax,%eax
    52ea:	0f 84 10 02 00 00    	je     5500 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    52f0:	48 89 de             	mov    %rbx,%rsi
    52f3:	48 8d 3d d7 3d 00 00 	lea    0x3dd7(%rip),%rdi        # 90d1 <_IO_stdin_used+0xd1>
    52fa:	e8 11 d1 ff ff       	call   2410 <strcmp@plt>
    52ff:	85 c0                	test   %eax,%eax
    5301:	0f 84 a9 02 00 00    	je     55b0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    5307:	48 89 de             	mov    %rbx,%rsi
    530a:	48 8d 3d c4 3d 00 00 	lea    0x3dc4(%rip),%rdi        # 90d5 <_IO_stdin_used+0xd5>
    5311:	e8 fa d0 ff ff       	call   2410 <strcmp@plt>
    5316:	85 c0                	test   %eax,%eax
    5318:	0f 84 6a 02 00 00    	je     5588 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    531e:	48 89 de             	mov    %rbx,%rsi
    5321:	48 8d 3d f0 3d 00 00 	lea    0x3df0(%rip),%rdi        # 9118 <_IO_stdin_used+0x118>
    5328:	e8 e3 d0 ff ff       	call   2410 <strcmp@plt>
    532d:	85 c0                	test   %eax,%eax
    532f:	0f 84 2b 02 00 00    	je     5560 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    5335:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    5338:	0f 84 52 01 00 00    	je     5490 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    533e:	48 89 de             	mov    %rbx,%rsi
    5341:	48 8d 3d 91 3d 00 00 	lea    0x3d91(%rip),%rdi        # 90d9 <_IO_stdin_used+0xd9>
    5348:	e8 c3 d0 ff ff       	call   2410 <strcmp@plt>
    534d:	85 c0                	test   %eax,%eax
    534f:	0f 84 ab 02 00 00    	je     5600 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    5355:	48 89 de             	mov    %rbx,%rsi
    5358:	48 8d 3d 7e 3d 00 00 	lea    0x3d7e(%rip),%rdi        # 90dd <_IO_stdin_used+0xdd>
    535f:	e8 ac d0 ff ff       	call   2410 <strcmp@plt>
    5364:	85 c0                	test   %eax,%eax
    5366:	0f 84 6c 02 00 00    	je     55d8 <send_headers+0x458>
    slen = strlen(send_buffer);
    536c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    5374:	4c 89 e7             	mov    %r12,%rdi
    5377:	e8 f4 cf ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    537c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    537f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    5382:	e8 e9 d0 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5387:	48 85 c0             	test   %rax,%rax
    538a:	0f 84 eb 02 00 00    	je     567b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    5390:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    5394:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5398:	83 fb 08             	cmp    $0x8,%ebx
    539b:	0f 83 3f 01 00 00    	jae    54e0 <send_headers+0x360>
    53a1:	f6 c3 04             	test   $0x4,%bl
    53a4:	0f 85 7b 02 00 00    	jne    5625 <send_headers+0x4a5>
    53aa:	85 db                	test   %ebx,%ebx
    53ac:	74 13                	je     53c1 <send_headers+0x241>
    53ae:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    53b6:	88 10                	mov    %dl,(%rax)
    53b8:	f6 c3 02             	test   $0x2,%bl
    53bb:	0f 85 96 02 00 00    	jne    5657 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    53c1:	4d 89 e8             	mov    %r13,%r8
    53c4:	48 8d 0d 16 3d 00 00 	lea    0x3d16(%rip),%rcx        # 90e1 <_IO_stdin_used+0xe1>
    53cb:	4c 89 e7             	mov    %r12,%rdi
    53ce:	31 c0                	xor    %eax,%eax
    53d0:	ba 00 04 00 00       	mov    $0x400,%edx
    53d5:	be 01 00 00 00       	mov    $0x1,%esi
    53da:	e8 c1 d1 ff ff       	call   25a0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    53df:	4c 89 e7             	mov    %r12,%rdi
    53e2:	e8 89 cf ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    53e7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    53ea:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    53ed:	e8 7e d0 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    53f2:	48 85 c0             	test   %rax,%rax
    53f5:	0f 84 80 02 00 00    	je     567b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    53fb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    53ff:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    5403:	83 fb 08             	cmp    $0x8,%ebx
    5406:	0f 83 1c 01 00 00    	jae    5528 <send_headers+0x3a8>
    540c:	f6 c3 04             	test   $0x4,%bl
    540f:	0f 85 29 02 00 00    	jne    563e <send_headers+0x4be>
    5415:	85 db                	test   %ebx,%ebx
    5417:	74 13                	je     542c <send_headers+0x2ac>
    5419:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    5421:	88 10                	mov    %dl,(%rax)
    5423:	f6 c3 02             	test   $0x2,%bl
    5426:	0f 85 3d 02 00 00    	jne    5669 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    542c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    5431:	bf 02 00 00 00       	mov    $0x2,%edi
    5436:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    543e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    5446:	e8 25 d0 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    544b:	48 85 c0             	test   %rax,%rax
    544e:	0f 84 27 02 00 00    	je     567b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5454:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    545c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    5460:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    5468:	66 89 10             	mov    %dx,(%rax)
}
    546b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    5473:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    547c:	0f 85 20 02 00 00    	jne    56a2 <send_headers+0x522>
    5482:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    5489:	5b                   	pop    %rbx
    548a:	5d                   	pop    %rbp
    548b:	41 5c                	pop    %r12
    548d:	41 5d                	pop    %r13
    548f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    5490:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    5494:	0f 85 a4 fe ff ff    	jne    533e <send_headers+0x1be>
    549a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    549e:	0f 85 9a fe ff ff    	jne    533e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    54a4:	66 0f 6f 05 94 49 00 00 	movdqa 0x4994(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    54ac:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    54b6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    54be:	66 0f 6f 05 8a 49 00 00 	movdqa 0x498a(%rip),%xmm0        # 9e50 <_IO_stdin_used+0xe50>
    54c6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    54ce:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    54d6:	e9 63 fe ff ff       	jmp    533e <send_headers+0x1be>
    54db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    54e0:	89 da                	mov    %ebx,%edx
    54e2:	48 89 c7             	mov    %rax,%rdi
    54e5:	4c 89 e6             	mov    %r12,%rsi
    54e8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    54ed:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    54f2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    54f5:	c1 e9 03             	shr    $0x3,%ecx
    54f8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    54fb:	e9 c1 fe ff ff       	jmp    53c1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5500:	66 0f 6f 05 d8 48 00 00 	movdqa 0x48d8(%rip),%xmm0        # 9de0 <_IO_stdin_used+0xde0>
    5508:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5510:	66 0f 6f 05 e8 48 00 00 	movdqa 0x48e8(%rip),%xmm0        # 9e00 <_IO_stdin_used+0xe00>
    5518:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5520:	e9 cb fd ff ff       	jmp    52f0 <send_headers+0x170>
    5525:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5528:	89 da                	mov    %ebx,%edx
    552a:	48 89 c7             	mov    %rax,%rdi
    552d:	4c 89 e6             	mov    %r12,%rsi
    5530:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    5535:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    553a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    553d:	c1 e9 03             	shr    $0x3,%ecx
    5540:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    5543:	e9 e4 fe ff ff       	jmp    542c <send_headers+0x2ac>
    5548:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    5550:	48 8d 1d 9f 3b 00 00 	lea    0x3b9f(%rip),%rbx        # 90f6 <_IO_stdin_used+0xf6>
    5557:	e9 94 fd ff ff       	jmp    52f0 <send_headers+0x170>
    555c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5560:	66 0f 6f 05 b8 48 00 00 	movdqa 0x48b8(%rip),%xmm0        # 9e20 <_IO_stdin_used+0xe20>
    5568:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5570:	66 0f 6f 05 b8 48 00 00 	movdqa 0x48b8(%rip),%xmm0        # 9e30 <_IO_stdin_used+0xe30>
    5578:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5580:	e9 b0 fd ff ff       	jmp    5335 <send_headers+0x1b5>
    5585:	0f 1f 00             	nopl   (%rax)
    5588:	66 0f 6f 05 90 48 00 00 	movdqa 0x4890(%rip),%xmm0        # 9e20 <_IO_stdin_used+0xe20>
    5590:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5598:	66 0f 6f 05 90 48 00 00 	movdqa 0x4890(%rip),%xmm0        # 9e30 <_IO_stdin_used+0xe30>
    55a0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    55a8:	e9 71 fd ff ff       	jmp    531e <send_headers+0x19e>
    55ad:	0f 1f 00             	nopl   (%rax)
    55b0:	66 0f 6f 05 28 48 00 00 	movdqa 0x4828(%rip),%xmm0        # 9de0 <_IO_stdin_used+0xde0>
    55b8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    55c0:	66 0f 6f 05 48 48 00 00 	movdqa 0x4848(%rip),%xmm0        # 9e10 <_IO_stdin_used+0xe10>
    55c8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    55d0:	e9 32 fd ff ff       	jmp    5307 <send_headers+0x187>
    55d5:	0f 1f 00             	nopl   (%rax)
    55d8:	66 0f 6f 05 40 48 00 00 	movdqa 0x4840(%rip),%xmm0        # 9e20 <_IO_stdin_used+0xe20>
    55e0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    55e8:	66 0f 6f 05 80 48 00 00 	movdqa 0x4880(%rip),%xmm0        # 9e70 <_IO_stdin_used+0xe70>
    55f0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    55f8:	e9 6f fd ff ff       	jmp    536c <send_headers+0x1ec>
    55fd:	0f 1f 00             	nopl   (%rax)
    5600:	66 0f 6f 05 18 48 00 00 	movdqa 0x4818(%rip),%xmm0        # 9e20 <_IO_stdin_used+0xe20>
    5608:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5610:	66 0f 6f 05 48 48 00 00 	movdqa 0x4848(%rip),%xmm0        # 9e60 <_IO_stdin_used+0xe60>
    5618:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5620:	e9 30 fd ff ff       	jmp    5355 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5625:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    562c:	89 db                	mov    %ebx,%ebx
    562e:	89 10                	mov    %edx,(%rax)
    5630:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5635:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5639:	e9 83 fd ff ff       	jmp    53c1 <send_headers+0x241>
    563e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5645:	89 db                	mov    %ebx,%ebx
    5647:	89 10                	mov    %edx,(%rax)
    5649:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    564e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5652:	e9 d5 fd ff ff       	jmp    542c <send_headers+0x2ac>
    5657:	89 db                	mov    %ebx,%ebx
    5659:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    565f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5664:	e9 58 fd ff ff       	jmp    53c1 <send_headers+0x241>
    5669:	89 db                	mov    %ebx,%ebx
    566b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    5671:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5676:	e9 b1 fd ff ff       	jmp    542c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    567b:	48 8b 0d 9e 69 00 00 	mov    0x699e(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5682:	ba 28 00 00 00       	mov    $0x28,%edx
    5687:	be 01 00 00 00       	mov    $0x1,%esi
    568c:	48 8d 3d 95 3f 00 00 	lea    0x3f95(%rip),%rdi        # 9628 <_IO_stdin_used+0x628>
    5693:	e8 98 ce ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5698:	bf 01 00 00 00       	mov    $0x1,%edi
    569d:	e8 6e ce ff ff       	call   2510 <exit@plt>
}
    56a2:	e8 d9 cc ff ff       	call   2380 <__stack_chk_fail@plt>
    56a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000056b0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    56b0:	f3 0f 1e fa          	endbr64
    56b4:	41 55                	push   %r13
    56b6:	49 89 d5             	mov    %rdx,%r13
    56b9:	41 54                	push   %r12
    56bb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    56be:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    56c1:	55                   	push   %rbp
    56c2:	53                   	push   %rbx
    56c3:	48 89 f3             	mov    %rsi,%rbx
    56c6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    56ca:	e8 a1 cd ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    56cf:	48 85 c0             	test   %rax,%rax
    56d2:	74 6b                	je     573f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    56d4:	4c 89 e7             	mov    %r12,%rdi
    56d7:	48 89 c5             	mov    %rax,%rbp
    56da:	31 f6                	xor    %esi,%esi
    56dc:	31 c0                	xor    %eax,%eax
    56de:	e8 fd cd ff ff       	call   24e0 <open@plt>
    56e3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    56e6:	85 c0                	test   %eax,%eax
    56e8:	0f 88 e8 ce ff ff    	js     25d6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    56ee:	48 89 da             	mov    %rbx,%rdx
    56f1:	48 89 ee             	mov    %rbp,%rsi
    56f4:	89 c7                	mov    %eax,%edi
    56f6:	e8 f5 cc ff ff       	call   23f0 <read@plt>
    if (ret < file_size) {
    56fb:	48 98                	cltq
    56fd:	48 39 d8             	cmp    %rbx,%rax
    5700:	7c 1e                	jl     5720 <copy_file_contents+0x70>
    close(fd);
    5702:	44 89 e7             	mov    %r12d,%edi
    5705:	e8 c6 cc ff ff       	call   23d0 <close@plt>
    iov->iov_base = buf;
    570a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    570e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    5712:	48 83 c4 08          	add    $0x8,%rsp
    5716:	5b                   	pop    %rbx
    5717:	5d                   	pop    %rbp
    5718:	41 5c                	pop    %r12
    571a:	41 5d                	pop    %r13
    571c:	c3                   	ret
    571d:	0f 1f 00             	nopl   (%rax)
    5720:	48 8b 0d f9 68 00 00 	mov    0x68f9(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5727:	ba 1a 00 00 00       	mov    $0x1a,%edx
    572c:	be 01 00 00 00       	mov    $0x1,%esi
    5731:	48 8d 3d bf 39 00 00 	lea    0x39bf(%rip),%rdi        # 90f7 <_IO_stdin_used+0xf7>
    5738:	e8 f3 cd ff ff       	call   2530 <fwrite@plt>
    573d:	eb c3                	jmp    5702 <copy_file_contents+0x52>
    573f:	48 8b 0d da 68 00 00 	mov    0x68da(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5746:	ba 28 00 00 00       	mov    $0x28,%edx
    574b:	be 01 00 00 00       	mov    $0x1,%esi
    5750:	48 8d 3d d1 3e 00 00 	lea    0x3ed1(%rip),%rdi        # 9628 <_IO_stdin_used+0x628>
    5757:	e8 d4 cd ff ff       	call   2530 <fwrite@plt>
        exit(1);
    575c:	bf 01 00 00 00       	mov    $0x1,%edi
    5761:	e8 aa cd ff ff       	call   2510 <exit@plt>
    5766:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005770 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    5770:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    5774:	8b 46 44             	mov    0x44(%rsi),%eax
    5777:	48 89 fa             	mov    %rdi,%rdx
    577a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    577d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5783:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5786:	48 8b 07             	mov    (%rdi),%rax
    5789:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    578c:	f6 c1 02             	test   $0x2,%cl
    578f:	74 00                	je     5791 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    5791:	89 f0                	mov    %esi,%eax
    5793:	44 29 c0             	sub    %r8d,%eax
    5796:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5799:	0f 82 43 ce ff ff    	jb     25e2 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    579f:	c1 e9 0a             	shr    $0xa,%ecx
    57a2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    57a6:	8b 47 44             	mov    0x44(%rdi),%eax
    57a9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    57ac:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    57af:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    57b2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    57b5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    57b9:	d3 e0                	shl    %cl,%eax
    57bb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    57be:	48 c1 e0 06          	shl    $0x6,%rax
    57c2:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    57c6:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    57cc:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    57cf:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    57d3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    57d9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    57e1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    57e5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    57e8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    57ef:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    57f7:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    57fb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    57ff:	e8 8c cb ff ff       	call   2390 <io_uring_submit@plt>
}
    5804:	31 c0                	xor    %eax,%eax
    5806:	48 83 c4 08          	add    $0x8,%rsp
    580a:	c3                   	ret
    580b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005810 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    5810:	f3 0f 1e fa          	endbr64
    5814:	41 55                	push   %r13
    5816:	41 89 fd             	mov    %edi,%r13d
    5819:	41 54                	push   %r12
    581b:	55                   	push   %rbp
    581c:	53                   	push   %rbx
    581d:	48 89 f3             	mov    %rsi,%rbx
    5820:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    5824:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5827:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    582d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    5830:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5833:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5835:	f6 c1 02             	test   $0x2,%cl
    5838:	74 00                	je     583a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    583a:	89 c2                	mov    %eax,%edx
    583c:	29 f2                	sub    %esi,%edx
    583e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5841:	0f 82 ab cd ff ff    	jb     25f2 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5847:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    584a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    584d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5850:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    5855:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5858:	23 6b 58             	and    0x58(%rbx),%ebp
    585b:	d3 e5                	shl    %cl,%ebp
    585d:	48 c1 e5 06          	shl    $0x6,%rbp
    5861:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5865:	e8 06 cc ff ff       	call   2470 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    586a:	be 01 00 00 00       	mov    $0x1,%esi
    586f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5874:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    5877:	e8 84 cb ff ff       	call   2400 <calloc@plt>
    req->client_socket = client_socket;
    587c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5881:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5885:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5888:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    588d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    5892:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    589b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    58a3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    58a7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    58ab:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    58b2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    58ba:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    58be:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    58c6:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    58ce:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    58d2:	e8 b9 ca ff ff       	call   2390 <io_uring_submit@plt>
}
    58d7:	48 83 c4 08          	add    $0x8,%rsp
    58db:	31 c0                	xor    %eax,%eax
    58dd:	5b                   	pop    %rbx
    58de:	5d                   	pop    %rbp
    58df:	41 5c                	pop    %r12
    58e1:	41 5d                	pop    %r13
    58e3:	c3                   	ret
    58e4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    58ef:	90                   	nop

00000000000058f0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    58f0:	f3 0f 1e fa          	endbr64
    58f4:	41 56                	push   %r14
    58f6:	41 89 f6             	mov    %esi,%r14d
    58f9:	41 55                	push   %r13
    58fb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    58fe:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5903:	41 54                	push   %r12
    5905:	55                   	push   %rbp
    5906:	48 89 d5             	mov    %rdx,%rbp
    5909:	53                   	push   %rbx
    void *buf = malloc(size);
    590a:	e8 61 cb ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    590f:	48 85 c0             	test   %rax,%rax
    5912:	0f 84 dd 00 00 00    	je     59f5 <_send_static_string_content+0x105>
    5918:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    591b:	4c 89 ef             	mov    %r13,%rdi
    591e:	e8 4d ca ff ff       	call   2370 <strlen@plt>
    req->iovec_count = 1;
    5923:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    592a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    592e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    5931:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    5934:	e8 37 cb ff ff       	call   2470 <malloc@plt>
    5939:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    593c:	48 85 c0             	test   %rax,%rax
    593f:	0f 84 b0 00 00 00    	je     59f5 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    5945:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5949:	4c 89 e2             	mov    %r12,%rdx
    594c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    594f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5953:	e8 e8 ca ff ff       	call   2440 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5958:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    595b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5961:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5964:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5968:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    596a:	f6 c1 02             	test   $0x2,%cl
    596d:	0f 85 7d 00 00 00    	jne    59f0 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    5973:	89 d0                	mov    %edx,%eax
    5975:	29 f0                	sub    %esi,%eax
    5977:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    597a:	0f 82 7c cc ff ff    	jb     25fc <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5980:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5983:	8b 45 44             	mov    0x44(%rbp),%eax
    5986:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    5989:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    598c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    598f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    5992:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    5998:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    599c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    599e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    59a1:	48 89 ef             	mov    %rbp,%rdi
    59a4:	48 c1 e0 06          	shl    $0x6,%rax
    59a8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    59ac:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    59af:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    59b3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    59b9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    59c1:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    59c5:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    59c8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    59cf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    59d7:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    59db:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    59df:	5b                   	pop    %rbx
    59e0:	5d                   	pop    %rbp
    59e1:	41 5c                	pop    %r12
    59e3:	41 5d                	pop    %r13
    59e5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    59e7:	e9 a4 c9 ff ff       	jmp    2390 <io_uring_submit@plt>
    59ec:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    59f0:	e9 7e ff ff ff       	jmp    5973 <_send_static_string_content+0x83>
    59f5:	48 8b 0d 24 66 00 00 	mov    0x6624(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    59fc:	ba 28 00 00 00       	mov    $0x28,%edx
    5a01:	be 01 00 00 00       	mov    $0x1,%esi
    5a06:	48 8d 3d 1b 3c 00 00 	lea    0x3c1b(%rip),%rdi        # 9628 <_IO_stdin_used+0x628>
    5a0d:	e8 1e cb ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5a12:	bf 01 00 00 00       	mov    $0x1,%edi
    5a17:	e8 f4 ca ff ff       	call   2510 <exit@plt>
    5a1c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005a20 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    5a20:	f3 0f 1e fa          	endbr64
    5a24:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5a27:	89 fe                	mov    %edi,%esi
    5a29:	48 8b 3d e8 65 00 00 	mov    0x65e8(%rip),%rdi        # c018 <unimplemented_content>
    5a30:	e9 bb fe ff ff       	jmp    58f0 <_send_static_string_content>
    5a35:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005a40 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5a40:	f3 0f 1e fa          	endbr64
    5a44:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5a47:	89 fe                	mov    %edi,%esi
    5a49:	48 8b 3d c0 65 00 00 	mov    0x65c0(%rip),%rdi        # c010 <http_404_content>
    5a50:	e9 9b fe ff ff       	jmp    58f0 <_send_static_string_content>
    5a55:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005a60 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    5a60:	f3 0f 1e fa          	endbr64
    5a64:	41 56                	push   %r14
    5a66:	41 55                	push   %r13
    5a68:	49 89 d5             	mov    %rdx,%r13
    5a6b:	41 54                	push   %r12
    5a6d:	41 89 f4             	mov    %esi,%r12d
    5a70:	55                   	push   %rbp
    5a71:	48 89 fd             	mov    %rdi,%rbp
    5a74:	53                   	push   %rbx
    5a75:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    5a7c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5a85:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    5a8d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    5a8f:	e8 dc c8 ff ff       	call   2370 <strlen@plt>
    5a94:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    5a99:	48 89 c3             	mov    %rax,%rbx
    5a9c:	0f 84 b6 00 00 00    	je     5b58 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5aa2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5aa7:	48 89 ee             	mov    %rbp,%rsi
    5aaa:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    5aae:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5ab3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5abb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5ac3:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    5ace:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5ad6:	e8 45 c9 ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    5adb:	48 89 e6             	mov    %rsp,%rsi
    5ade:	4c 89 f7             	mov    %r14,%rdi
    5ae1:	e8 4a c9 ff ff       	call   2430 <stat@plt>
    5ae6:	83 f8 ff             	cmp    $0xffffffff,%eax
    5ae9:	0f 84 d3 00 00 00    	je     5bc2 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    5aef:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5af3:	25 00 f0 00 00       	and    $0xf000,%eax
    5af8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    5afd:	0f 84 f5 00 00 00    	je     5bf8 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    5b03:	48 8b 3d 06 65 00 00 	mov    0x6506(%rip),%rdi        # c010 <http_404_content>
    5b0a:	4c 89 ea             	mov    %r13,%rdx
    5b0d:	44 89 e6             	mov    %r12d,%esi
    5b10:	e8 db fd ff ff       	call   58f0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5b15:	4c 89 f2             	mov    %r14,%rdx
    5b18:	bf 01 00 00 00       	mov    $0x1,%edi
    5b1d:	31 c0                	xor    %eax,%eax
    5b1f:	48 8d 35 21 36 00 00 	lea    0x3621(%rip),%rsi        # 9147 <_IO_stdin_used+0x147>
    5b26:	e8 85 c9 ff ff       	call   24b0 <__printf_chk@plt>
}
    5b2b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5b33:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5b3c:	0f 85 20 01 00 00    	jne    5c62 <handle_get_method+0x202>
    5b42:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5b49:	5b                   	pop    %rbx
    5b4a:	5d                   	pop    %rbp
    5b4b:	41 5c                	pop    %r12
    5b4d:	41 5d                	pop    %r13
    5b4f:	41 5e                	pop    %r14
    5b51:	c3                   	ret
    5b52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5b58:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5b5d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5b65:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5b6a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5b6d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5b75:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5b78:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5b80:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5b8b:	e8 90 c8 ff ff       	call   2420 <__memcpy_chk@plt>
    5b90:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5b95:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    5b9a:	48 8d 35 71 35 00 00 	lea    0x3571(%rip),%rsi        # 9112 <_IO_stdin_used+0x112>
    5ba1:	48 29 d9             	sub    %rbx,%rcx
    5ba4:	ba 0b 00 00 00       	mov    $0xb,%edx
    5ba9:	e8 72 c8 ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    5bae:	48 89 e6             	mov    %rsp,%rsi
    5bb1:	4c 89 f7             	mov    %r14,%rdi
    5bb4:	e8 77 c8 ff ff       	call   2430 <stat@plt>
    5bb9:	83 f8 ff             	cmp    $0xffffffff,%eax
    5bbc:	0f 85 2d ff ff ff    	jne    5aef <handle_get_method+0x8f>
    5bc2:	4c 89 f2             	mov    %r14,%rdx
    5bc5:	48 89 e9             	mov    %rbp,%rcx
    5bc8:	48 8d 35 4e 35 00 00 	lea    0x354e(%rip),%rsi        # 911d <_IO_stdin_used+0x11d>
    5bcf:	31 c0                	xor    %eax,%eax
    5bd1:	bf 01 00 00 00       	mov    $0x1,%edi
    5bd6:	e8 d5 c8 ff ff       	call   24b0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    5bdb:	48 8b 3d 2e 64 00 00 	mov    0x642e(%rip),%rdi        # c010 <http_404_content>
    5be2:	4c 89 ea             	mov    %r13,%rdx
    5be5:	44 89 e6             	mov    %r12d,%esi
    5be8:	e8 03 fd ff ff       	call   58f0 <_send_static_string_content>
}
    5bed:	e9 39 ff ff ff       	jmp    5b2b <handle_get_method+0xcb>
    5bf2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5bf8:	bf 70 00 00 00       	mov    $0x70,%edi
    5bfd:	e8 6e c8 ff ff       	call   2470 <malloc@plt>
    5c02:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5c05:	48 85 c0             	test   %rax,%rax
    5c08:	74 5d                	je     5c67 <handle_get_method+0x207>
            req->client_socket = client_socket;
    5c0a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5c0e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5c13:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5c17:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    5c1a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5c21:	e8 5a f5 ff ff       	call   5180 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5c26:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5c2b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    5c2f:	4c 89 f7             	mov    %r14,%rdi
    5c32:	e8 79 fa ff ff       	call   56b0 <copy_file_contents>
    5c37:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    5c3c:	4c 89 f2             	mov    %r14,%rdx
    5c3f:	31 c0                	xor    %eax,%eax
    5c41:	48 8d 35 ed 34 00 00 	lea    0x34ed(%rip),%rsi        # 9135 <_IO_stdin_used+0x135>
    5c48:	bf 01 00 00 00       	mov    $0x1,%edi
    5c4d:	e8 5e c8 ff ff       	call   24b0 <__printf_chk@plt>
            add_write_request(req, ring);
    5c52:	4c 89 ee             	mov    %r13,%rsi
    5c55:	48 89 df             	mov    %rbx,%rdi
    5c58:	e8 13 fb ff ff       	call   5770 <add_write_request>
    5c5d:	e9 c9 fe ff ff       	jmp    5b2b <handle_get_method+0xcb>
}
    5c62:	e8 19 c7 ff ff       	call   2380 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5c67:	48 8b 0d b2 63 00 00 	mov    0x63b2(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5c6e:	ba 28 00 00 00       	mov    $0x28,%edx
    5c73:	be 01 00 00 00       	mov    $0x1,%esi
    5c78:	48 8d 3d a9 39 00 00 	lea    0x39a9(%rip),%rdi        # 9628 <_IO_stdin_used+0x628>
    5c7f:	e8 ac c8 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5c84:	bf 01 00 00 00       	mov    $0x1,%edi
    5c89:	e8 82 c8 ff ff       	call   2510 <exit@plt>
    5c8e:	66 90                	xchg   %ax,%ax

0000000000005c90 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5c90:	f3 0f 1e fa          	endbr64
    5c94:	41 57                	push   %r15
    5c96:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5c98:	4c 8d 35 0d 34 00 00 	lea    0x340d(%rip),%r14        # 90ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5c9f:	41 55                	push   %r13
    5ca1:	49 89 d5             	mov    %rdx,%r13
    5ca4:	41 54                	push   %r12
    5ca6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5ca9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5cac:	55                   	push   %rbp
    5cad:	53                   	push   %rbx
    5cae:	48 83 ec 18          	sub    $0x18,%rsp
    5cb2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5cbb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5cc0:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5cc2:	49 89 e7             	mov    %rsp,%r15
    5cc5:	4c 89 fa             	mov    %r15,%rdx
    5cc8:	e8 13 c7 ff ff       	call   23e0 <strtok_r@plt>
    for (; *str; ++str)
    5ccd:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5cd1:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5cd4:	84 db                	test   %bl,%bl
    5cd6:	74 1d                	je     5cf5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5cd8:	e8 b3 c8 ff ff       	call   2590 <__ctype_tolower_loc@plt>
    5cdd:	48 89 ea             	mov    %rbp,%rdx
    5ce0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    5ce3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    5ce7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    5cea:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    5ced:	48 0f be 1a          	movsbq (%rdx),%rbx
    5cf1:	84 db                	test   %bl,%bl
    5cf3:	75 eb                	jne    5ce0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5cf5:	4c 89 fa             	mov    %r15,%rdx
    5cf8:	4c 89 f6             	mov    %r14,%rsi
    5cfb:	31 ff                	xor    %edi,%edi
    5cfd:	e8 de c6 ff ff       	call   23e0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5d02:	48 8d 35 51 34 00 00 	lea    0x3451(%rip),%rsi        # 915a <_IO_stdin_used+0x15a>
    5d09:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    5d0c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    5d0f:	e8 fc c6 ff ff       	call   2410 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5d14:	4c 89 ea             	mov    %r13,%rdx
    5d17:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    5d1a:	85 c0                	test   %eax,%eax
    5d1c:	75 2a                	jne    5d48 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    5d1e:	48 89 df             	mov    %rbx,%rdi
    5d21:	e8 3a fd ff ff       	call   5a60 <handle_get_method>
}
    5d26:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    5d2b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5d34:	75 20                	jne    5d56 <handle_http_method+0xc6>
    5d36:	48 83 c4 18          	add    $0x18,%rsp
    5d3a:	5b                   	pop    %rbx
    5d3b:	5d                   	pop    %rbp
    5d3c:	41 5c                	pop    %r12
    5d3e:	41 5d                	pop    %r13
    5d40:	41 5e                	pop    %r14
    5d42:	41 5f                	pop    %r15
    5d44:	c3                   	ret
    5d45:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5d48:	48 8b 3d c9 62 00 00 	mov    0x62c9(%rip),%rdi        # c018 <unimplemented_content>
    5d4f:	e8 9c fb ff ff       	call   58f0 <_send_static_string_content>
}
    5d54:	eb d0                	jmp    5d26 <handle_http_method+0x96>
    5d56:	e8 25 c6 ff ff       	call   2380 <__stack_chk_fail@plt>
    5d5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005d60 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5d60:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5d64:	85 d2                	test   %edx,%edx
    5d66:	7e 38                	jle    5da0 <get_line+0x40>
    5d68:	48 63 d2             	movslq %edx,%rdx
    5d6b:	48 83 c7 01          	add    $0x1,%rdi
    5d6f:	48 01 f2             	add    %rsi,%rdx
    5d72:	eb 11                	jmp    5d85 <get_line+0x25>
    5d74:	0f 1f 40 00          	nopl   0x0(%rax)
    5d78:	48 83 c6 01          	add    $0x1,%rsi
    5d7c:	48 83 c7 01          	add    $0x1,%rdi
    5d80:	48 39 d6             	cmp    %rdx,%rsi
    5d83:	74 1b                	je     5da0 <get_line+0x40>
        dest[i] = src[i];
    5d85:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5d89:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5d8b:	3c 0d                	cmp    $0xd,%al
    5d8d:	75 e9                	jne    5d78 <get_line+0x18>
    5d8f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5d92:	75 e4                	jne    5d78 <get_line+0x18>
            dest[i] = '\0';
    5d94:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5d97:	31 c0                	xor    %eax,%eax
    5d99:	c3                   	ret
    5d9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5da0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5da5:	c3                   	ret
    5da6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005db0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5db0:	f3 0f 1e fa          	endbr64
    5db4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    5dbb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    5dbf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5dc8:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5dd0:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5dd2:	49 89 e2             	mov    %rsp,%r10
    5dd5:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    5ddd:	4c 89 d0             	mov    %r10,%rax
    5de0:	eb 13                	jmp    5df5 <handle_client_request+0x45>
    5de2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5de8:	48 83 c0 01          	add    $0x1,%rax
    5dec:	48 83 c1 01          	add    $0x1,%rcx
    5df0:	4c 39 c8             	cmp    %r9,%rax
    5df3:	74 4b                	je     5e40 <handle_client_request+0x90>
        dest[i] = src[i];
    5df5:	44 0f b6 01          	movzbl (%rcx),%r8d
    5df9:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5dfc:	41 80 f8 0d          	cmp    $0xd,%r8b
    5e00:	75 e6                	jne    5de8 <handle_client_request+0x38>
    5e02:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5e06:	75 e0                	jne    5de8 <handle_client_request+0x38>
            dest[i] = '\0';
    5e08:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5e0b:	8b 47 08             	mov    0x8(%rdi),%eax
    5e0e:	48 89 f2             	mov    %rsi,%rdx
    5e11:	4c 89 d7             	mov    %r10,%rdi
    5e14:	89 c6                	mov    %eax,%esi
    5e16:	e8 75 fe ff ff       	call   5c90 <handle_http_method>
}
    5e1b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5e23:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5e2c:	75 39                	jne    5e67 <handle_client_request+0xb7>
    5e2e:	31 c0                	xor    %eax,%eax
    5e30:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5e37:	c3                   	ret
    5e38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5e40:	48 8b 0d d9 61 00 00 	mov    0x61d9(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5e47:	ba 12 00 00 00       	mov    $0x12,%edx
    5e4c:	be 01 00 00 00       	mov    $0x1,%esi
    5e51:	48 8d 3d 06 33 00 00 	lea    0x3306(%rip),%rdi        # 915e <_IO_stdin_used+0x15e>
    5e58:	e8 d3 c6 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    5e5d:	bf 01 00 00 00       	mov    $0x1,%edi
    5e62:	e8 a9 c6 ff ff       	call   2510 <exit@plt>
}
    5e67:	e8 14 c5 ff ff       	call   2380 <__stack_chk_fail@plt>
    5e6c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005e70 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5e70:	f3 0f 1e fa          	endbr64
    5e74:	55                   	push   %rbp
    5e75:	53                   	push   %rbx
    5e76:	48 89 cb             	mov    %rcx,%rbx
    5e79:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    5e7d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5e80:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5e83:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5e89:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5e8c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5e8f:	f6 c1 02             	test   $0x2,%cl
    5e92:	74 00                	je     5e94 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5e94:	41 89 c0             	mov    %eax,%r8d
    5e97:	45 29 c8             	sub    %r9d,%r8d
    5e9a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    5e9e:	0f 82 68 c7 ff ff    	jb     260c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5ea4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5ea7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    5eaa:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    5ead:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5eb0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5eb3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5eb7:	d3 e5                	shl    %cl,%ebp
    5eb9:	48 c1 e5 06          	shl    $0x6,%rbp
    5ebd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5ec1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5ec4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5ec9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5ed0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5ed4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5ed8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5ee0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5ee8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5eec:	e8 7f c5 ff ff       	call   2470 <malloc@plt>
  io_uring_submit(ring);
    5ef1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5ef4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    5efa:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    5efe:	48 83 c4 08          	add    $0x8,%rsp
    5f02:	5b                   	pop    %rbx
    5f03:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5f04:	e9 87 c4 ff ff       	jmp    2390 <io_uring_submit@plt>
    5f09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005f10 <io_thread>:
void* io_thread(void *arg) {
    5f10:	f3 0f 1e fa          	endbr64
    5f14:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5f16:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5f18:	49 89 ff             	mov    %rdi,%r15
    5f1b:	41 56                	push   %r14
    5f1d:	41 55                	push   %r13
    5f1f:	41 54                	push   %r12
    5f21:	55                   	push   %rbp
    5f22:	53                   	push   %rbx
    5f23:	48 81 ec 78 05 00 00 	sub    $0x578,%rsp
  struct io_uring ring = *data->ring;
    5f2a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5f33:	48 89 84 24 68 05 00 00 	mov    %rax,0x568(%rsp)
    5f3b:	48 8b 47 60          	mov    0x60(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5f3f:	48 8d 9c 24 80 00 00 00 	lea    0x80(%rsp),%rbx
    5f47:	bf 00 01 00 00       	mov    $0x100,%edi
    5f4c:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    5f4f:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5f53:	0f 29 8c 24 80 00 00 00 	movaps %xmm1,0x80(%rsp)
    5f5b:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    5f60:	0f 29 94 24 90 00 00 00 	movaps %xmm2,0x90(%rsp)
    5f68:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5f6d:	0f 29 9c 24 a0 00 00 00 	movaps %xmm3,0xa0(%rsp)
    5f75:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5f7a:	0f 29 a4 24 b0 00 00 00 	movaps %xmm4,0xb0(%rsp)
    5f82:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    5f87:	0f 29 ac 24 c0 00 00 00 	movaps %xmm5,0xc0(%rsp)
    5f8f:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    5f94:	0f 29 b4 24 d0 00 00 00 	movaps %xmm6,0xd0(%rsp)
    5f9c:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5fa1:	0f 29 bc 24 e0 00 00 00 	movaps %xmm7,0xe0(%rsp)
    5fa9:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5fae:	0f 29 8c 24 f0 00 00 00 	movaps %xmm1,0xf0(%rsp)
    5fb6:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5fbe:	0f 29 94 24 00 01 00 00 	movaps %xmm2,0x100(%rsp)
    5fc6:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5fce:	0f 29 9c 24 10 01 00 00 	movaps %xmm3,0x110(%rsp)
    5fd6:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5fde:	0f 29 a4 24 20 01 00 00 	movaps %xmm4,0x120(%rsp)
    5fe6:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5fee:	0f 29 ac 24 30 01 00 00 	movaps %xmm5,0x130(%rsp)
    5ff6:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5ffe:	0f 29 b4 24 40 01 00 00 	movaps %xmm6,0x140(%rsp)
    6006:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    600d:	48 89 84 24 50 01 00 00 	mov    %rax,0x150(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    6015:	e8 36 c4 ff ff       	call   2450 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    601a:	49 8b 7f 60          	mov    0x60(%r15),%rdi
    601e:	31 f6                	xor    %esi,%esi
    6020:	e8 2b c5 ff ff       	call   2550 <io_uring_register_eventfd@plt>
  if (data->io_mode == IO_MODE_RECV) {
    6025:	41 8b 87 04 01 00 00 	mov    0x104(%r15),%eax
    602c:	83 f8 01             	cmp    $0x1,%eax
    602f:	0f 84 6b 06 00 00    	je     66a0 <io_thread+0x790>
  if (data->io_mode == IO_MODE_SEND) {
    6035:	85 c0                	test   %eax,%eax
    6037:	0f 85 b3 04 00 00    	jne    64f0 <io_thread+0x5e0>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    603d:	48 8d 3d ac 36 00 00 	lea    0x36ac(%rip),%rdi        # 96f0 <_IO_stdin_used+0x6f0>
    6044:	e8 e7 c2 ff ff       	call   2330 <puts@plt>
    6049:	41 8b 8f 14 01 00 00 	mov    0x114(%r15),%ecx
    6050:	49 8b 97 18 01 00 00 	mov    0x118(%r15),%rdx
    6057:	31 c0                	xor    %eax,%eax
    6059:	45 8b 87 10 01 00 00 	mov    0x110(%r15),%r8d
    6060:	48 8d 35 c1 36 00 00 	lea    0x36c1(%rip),%rsi        # 9728 <_IO_stdin_used+0x728>
    6067:	bf 01 00 00 00       	mov    $0x1,%edi
    606c:	e8 3f c4 ff ff       	call   24b0 <__printf_chk@plt>
    void * _reply = bufferrecv(data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply); 
    6071:	49 63 87 14 01 00 00 	movslq 0x114(%r15),%rax
    6078:	48 c1 e0 04          	shl    $0x4,%rax
    607c:	49 03 87 08 01 00 00 	add    0x108(%r15),%rax
  while (data->running == 1) {
    6083:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    void * _reply = bufferrecv(data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply); 
    6088:	49 89 c4             	mov    %rax,%r12
  while (data->running == 1) {
    608b:	0f 85 e9 c5 ff ff    	jne    267a <io_thread.cold+0x64>
      for (int x = 0 ; x < buffers->count ; x++) {
    6091:	48 63 00             	movslq (%rax),%rax
    6094:	85 c0                	test   %eax,%eax
    6096:	0f 8e c4 0c 00 00    	jle    6d60 <io_thread+0xe50>
        if (buffers->buffer[x].available == 1) {
    609c:	49 8b 54 24 08       	mov    0x8(%r12),%rdx
    60a1:	48 c1 e0 08          	shl    $0x8,%rax
                for (int i = 0; i < req->iovec_count; i++) {
    60a5:	31 ed                	xor    %ebp,%ebp
    60a7:	eb 13                	jmp    60bc <io_thread+0x1ac>
    60a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    60b0:	48 81 c5 00 01 00 00 	add    $0x100,%rbp
    60b7:	48 39 c5             	cmp    %rax,%rbp
    60ba:	74 e9                	je     60a5 <io_thread+0x195>
        if (buffers->buffer[x].available == 1) {
    60bc:	83 bc 2a 80 00 00 00 01 	cmpl   $0x1,0x80(%rdx,%rbp,1)
    60c4:	75 ea                	jne    60b0 <io_thread+0x1a0>
    60c6:	8b 8c 2a 98 00 00 00 	mov    0x98(%rdx,%rbp,1),%ecx
    60cd:	49 8b 97 18 01 00 00 	mov    0x118(%r15),%rdx
    60d4:	bf 01 00 00 00       	mov    $0x1,%edi
    60d9:	31 c0                	xor    %eax,%eax
    60db:	48 8d 35 cd 30 00 00 	lea    0x30cd(%rip),%rsi        # 91af <_IO_stdin_used+0x1af>
    60e2:	e8 c9 c3 ff ff       	call   24b0 <__printf_chk@plt>
          struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    60e7:	be 00 01 00 00       	mov    $0x100,%esi
    60ec:	bf 01 00 00 00       	mov    $0x1,%edi
    60f1:	e8 0a c3 ff ff       	call   2400 <calloc@plt>
          reply->data = buffers->buffer[x].data;
    60f6:	49 03 6c 24 08       	add    0x8(%r12),%rbp
          buffers->buffer[x].available = 0;
    60fb:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
          reply->data = buffers->buffer[x].data;
    6105:	48 8b 55 00          	mov    0x0(%rbp),%rdx
    6109:	48 89 10             	mov    %rdx,(%rax)
          reply->kind = buffers->buffer[x].kind;
    610c:	8b 95 98 00 00 00    	mov    0x98(%rbp),%edx
    6112:	89 90 98 00 00 00    	mov    %edx,0x98(%rax)
    struct NewSocketMessage *msg = bufferreply->data;
    6118:	4c 8b 28             	mov    (%rax),%r13
    611b:	49 8b 97 18 01 00 00 	mov    0x118(%r15),%rdx
    6122:	48 8d 35 3f 36 00 00 	lea    0x363f(%rip),%rsi        # 9768 <_IO_stdin_used+0x768>
    6129:	31 c0                	xor    %eax,%eax
    612b:	bf 01 00 00 00       	mov    $0x1,%edi
    6130:	41 8b 4d 00          	mov    0x0(%r13),%ecx
    6134:	e8 77 c3 ff ff       	call   24b0 <__printf_chk@plt>
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    6139:	be 04 00 00 00       	mov    $0x4,%esi
    613e:	bf 01 00 00 00       	mov    $0x1,%edi
    6143:	e8 b8 c2 ff ff       	call   2400 <calloc@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    6148:	4d 63 b7 10 01 00 00 	movslq 0x110(%r15),%r14
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    614f:	49 89 c4             	mov    %rax,%r12
    ourreply->nothing = msg->socket;
    6152:	41 8b 45 00          	mov    0x0(%r13),%eax
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    6156:	49 c1 e6 04          	shl    $0x4,%r14
    615a:	4d 03 b7 08 01 00 00 	add    0x108(%r15),%r14
  while (data->running == 1) {
    6161:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    ourreply->nothing = msg->socket;
    6166:	41 89 04 24          	mov    %eax,(%r12)
  while (data->running == 1) {
    616a:	75 74                	jne    61e0 <io_thread+0x2d0>
      for (int x = 0 ; x < buffers->count ; x++) {
    616c:	49 63 06             	movslq (%r14),%rax
    616f:	85 c0                	test   %eax,%eax
    6171:	0f 8e 89 04 00 00    	jle    6600 <io_thread+0x6f0>
        if (buffers->buffer[x].available == 0) {
    6177:	49 8b 56 08          	mov    0x8(%r14),%rdx
    617b:	48 c1 e0 08          	shl    $0x8,%rax
    617f:	31 ed                	xor    %ebp,%ebp
    6181:	eb 15                	jmp    6198 <io_thread+0x288>
    6183:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    6188:	48 81 c5 00 01 00 00 	add    $0x100,%rbp
    618f:	48 39 c5             	cmp    %rax,%rbp
    6192:	0f 84 68 04 00 00    	je     6600 <io_thread+0x6f0>
        if (buffers->buffer[x].available == 0) {
    6198:	8b 8c 2a 80 00 00 00 	mov    0x80(%rdx,%rbp,1),%ecx
    619f:	85 c9                	test   %ecx,%ecx
    61a1:	75 e5                	jne    6188 <io_thread+0x278>
    61a3:	8b 8c 2a 98 00 00 00 	mov    0x98(%rdx,%rbp,1),%ecx
    61aa:	49 8b 97 18 01 00 00 	mov    0x118(%r15),%rdx
    61b1:	bf 01 00 00 00       	mov    $0x1,%edi
    61b6:	31 c0                	xor    %eax,%eax
    61b8:	48 8d 35 e4 2f 00 00 	lea    0x2fe4(%rip),%rsi        # 91a3 <_IO_stdin_used+0x1a3>
    61bf:	e8 ec c2 ff ff       	call   24b0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    61c4:	49 03 6e 08          	add    0x8(%r14),%rbp
    61c8:	4c 89 65 00          	mov    %r12,0x0(%rbp)
          buffers->buffer[x].kind = kind;
    61cc:	c7 85 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%rbp)
          buffers->buffer[x].available = 1;
    61d6:	c7 85 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbp)
    61e0:	49 8b 97 18 01 00 00 	mov    0x118(%r15),%rdx
    61e7:	48 8d 35 b2 35 00 00 	lea    0x35b2(%rip),%rsi        # 97a0 <_IO_stdin_used+0x7a0>
    61ee:	bf 01 00 00 00       	mov    $0x1,%edi
    61f3:	31 c0                	xor    %eax,%eax
    61f5:	e8 b6 c2 ff ff       	call   24b0 <__printf_chk@plt>
    int sock = msg->socket;
    61fa:	41 8b 7d 00          	mov    0x0(%r13),%edi
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    61fe:	48 8d 44 24 70       	lea    0x70(%rsp),%rax
    6203:	48 89 d9             	mov    %rbx,%rcx
    6206:	48 8d 54 24 3c       	lea    0x3c(%rsp),%rdx
    620b:	48 89 c6             	mov    %rax,%rsi
    620e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    int sock = msg->socket;
    6213:	89 7c 24 10          	mov    %edi,0x10(%rsp)
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6217:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    socklen_t client_addr_len = sizeof(client_addr);
    621c:	c7 44 24 3c 10 00 00 00 	movl   $0x10,0x3c(%rsp)
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6224:	e8 47 fc ff ff       	call   5e70 <add_accept_request>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    6229:	bf 01 00 00 00       	mov    $0x1,%edi
    622e:	be 10 00 00 00       	mov    $0x10,%esi
    6233:	e8 c8 c1 ff ff       	call   2400 <calloc@plt>
    void *buf = malloc(size);
    6238:	bf 0a 00 00 00       	mov    $0xa,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    623d:	48 89 c5             	mov    %rax,%rbp
    void *buf = malloc(size);
    6240:	e8 2b c2 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    6245:	48 85 c0             	test   %rax,%rax
    6248:	0f 84 b8 0b 00 00    	je     6e06 <io_thread+0xef6>
    iov->iov_base = zh_malloc(10);
    624e:	48 89 45 00          	mov    %rax,0x0(%rbp)
	unsigned int head, next = sq->sqe_tail + 1;
    6252:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6259:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
    iov->iov_len = 10;
    6260:	48 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%rbp)
	unsigned int head, next = sq->sqe_tail + 1;
    6268:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    626b:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6273:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6275:	f6 c1 02             	test   $0x2,%cl
    6278:	74 00                	je     627a <io_thread+0x36a>
	if (next - head <= sq->ring_entries) {
    627a:	89 d0                	mov    %edx,%eax
    627c:	29 f0                	sub    %esi,%eax
    627e:	39 84 24 dc 00 00 00 	cmp    %eax,0xdc(%rsp)
    6285:	0f 82 c3 c3 ff ff    	jb     264e <io_thread.cold+0x38>
	if (ring->flags & IORING_SETUP_SQE128)
    628b:	c1 e9 0a             	shr    $0xa,%ecx
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
    628e:	49 8d 77 68          	lea    0x68(%r15),%rsi
	sqe->addr3 = 0;
    6292:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(&ring);
    6296:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6299:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    62a0:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    62a3:	23 84 24 d8 00 00 00 	and    0xd8(%rsp),%eax
		sq->sqe_tail = next;
    62aa:	89 94 24 c4 00 00 00 	mov    %edx,0xc4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    62b1:	d3 e0                	shl    %cl,%eax
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    62b3:	41 8b 57 68          	mov    0x68(%r15),%edx
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
    62b7:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    62bc:	4c 8d 25 5c 2f 00 00 	lea    0x2f5c(%rip),%r12        # 921f <_IO_stdin_used+0x21f>
    62c3:	48 c1 e0 06          	shl    $0x6,%rax
    62c7:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
	sqe->opcode = (__u8) op;
    62cf:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    62d5:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    62d8:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    62e0:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->len = len;
    62e4:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    62ec:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    62f4:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    62f8:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(&ring);
    62fc:	e8 8f c0 ff ff       	call   2390 <io_uring_submit@plt>
    while (data->running == 1) {
    6301:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    6306:	4c 8d 54 24 48       	lea    0x48(%rsp),%r10
    630b:	4c 8d 9c 24 60 01 00 00 	lea    0x160(%rsp),%r11
    6313:	0f 85 d7 01 00 00    	jne    64f0 <io_thread+0x5e0>
    6319:	4c 89 14 24          	mov    %r10,(%rsp)
    631d:	4c 89 5c 24 28       	mov    %r11,0x28(%rsp)
    6322:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6328:	4c 89 e7             	mov    %r12,%rdi
    632b:	e8 00 c0 ff ff       	call   2330 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    6330:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    6337:	8b bc 24 30 01 00 00 	mov    0x130(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    633e:	c1 e9 0b             	shr    $0xb,%ecx
    6341:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    6344:	48 8b 84 24 f0 00 00 00 	mov    0xf0(%rsp),%rax
    634c:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    634e:	48 8b b4 24 e8 00 00 00 	mov    0xe8(%rsp),%rsi
    6356:	8b 16                	mov    (%rsi),%edx
		if (!available)
    6358:	39 d0                	cmp    %edx,%eax
    635a:	74 36                	je     6392 <io_thread+0x482>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    635c:	89 f8                	mov    %edi,%eax
    635e:	21 d0                	and    %edx,%eax
    6360:	d3 e0                	shl    %cl,%eax
    6362:	48 c1 e0 04          	shl    $0x4,%rax
    6366:	48 03 84 24 18 01 00 00 	add    0x118(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    636e:	f6 84 24 49 01 00 00 01 	testb  $0x1,0x149(%rsp)
    6376:	0f 85 b4 01 00 00    	jne    6530 <io_thread+0x620>
    637c:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    6380:	0f 85 aa 09 00 00    	jne    6d30 <io_thread+0xe20>
			if (cqe->res < 0)
    6386:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6389:	83 c2 01             	add    $0x1,%edx
    638c:	89 16                	mov    %edx,(%rsi)
			if (!err)
    638e:	85 c0                	test   %eax,%eax
    6390:	79 b2                	jns    6344 <io_thread+0x434>
	*cqe_ptr = cqe;
    6392:	48 c7 44 24 48 00 00 00 00 	movq   $0x0,0x48(%rsp)
	return err;
    639b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    63a0:	48 8b 34 24          	mov    (%rsp),%rsi
    63a4:	45 31 c0             	xor    %r8d,%r8d
    63a7:	31 d2                	xor    %edx,%edx
    63a9:	b9 01 00 00 00       	mov    $0x1,%ecx
    63ae:	48 89 df             	mov    %rbx,%rdi
    63b1:	e8 ea c0 ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    63b6:	41 89 c5             	mov    %eax,%r13d
        if (cqe->user_data == 1) {
    63b9:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    63be:	48 83 38 01          	cmpq   $0x1,(%rax)
    63c2:	0f 84 78 09 00 00    	je     6d40 <io_thread+0xe30>
    63c8:	48 8d 3d 17 2e 00 00 	lea    0x2e17(%rip),%rdi        # 91e6 <_IO_stdin_used+0x1e6>
    63cf:	e8 5c bf ff ff       	call   2330 <puts@plt>
        struct Request *req = (struct Request *) cqe->user_data;
    63d4:	48 8b 54 24 48       	mov    0x48(%rsp),%rdx
    63d9:	4c 8b 32             	mov    (%rdx),%r14
        if (ret < 0)
    63dc:	45 85 ed             	test   %r13d,%r13d
    63df:	0f 88 5d c2 ff ff    	js     2642 <io_thread.cold+0x2c>
        if (cqe->res < 0) {
    63e5:	8b 42 08             	mov    0x8(%rdx),%eax
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    63e8:	41 8b 16             	mov    (%r14),%edx
        if (cqe->res < 0) {
    63eb:	85 c0                	test   %eax,%eax
    63ed:	0f 88 d7 09 00 00    	js     6dca <io_thread+0xeba>
        switch (req->event_type) {
    63f3:	83 fa 01             	cmp    $0x1,%edx
    63f6:	0f 84 d4 01 00 00    	je     65d0 <io_thread+0x6c0>
    63fc:	83 fa 02             	cmp    $0x2,%edx
    63ff:	0f 84 7b 01 00 00    	je     6580 <io_thread+0x670>
    6405:	85 d2                	test   %edx,%edx
    6407:	0f 85 5b 01 00 00    	jne    6568 <io_thread+0x658>
                add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    640d:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    6412:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    6417:	48 89 d9             	mov    %rbx,%rcx
    641a:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    641e:	e8 4d fa ff ff       	call   5e70 <add_accept_request>
                add_read_request(cqe->res, &ring);
    6423:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    6428:	48 89 de             	mov    %rbx,%rsi
    642b:	8b 78 08             	mov    0x8(%rax),%edi
    642e:	e8 dd f3 ff ff       	call   5810 <add_read_request>
                free(req);
    6433:	4c 89 f7             	mov    %r14,%rdi
    6436:	e8 c5 be ff ff       	call   2300 <free@plt>
        io_uring_cqe_seen(&ring, cqe);
    643b:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
	if (cqe)
    6440:	48 85 c0             	test   %rax,%rax
    6443:	0f 85 1f 01 00 00    	jne    6568 <io_thread+0x658>
	unsigned int head, next = sq->sqe_tail + 1;
    6449:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6450:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    6457:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    645a:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6462:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6464:	f6 c1 02             	test   $0x2,%cl
    6467:	74 00                	je     6469 <io_thread+0x559>
	if (next - head <= sq->ring_entries) {
    6469:	89 d0                	mov    %edx,%eax
    646b:	29 f0                	sub    %esi,%eax
    646d:	39 84 24 dc 00 00 00 	cmp    %eax,0xdc(%rsp)
    6474:	0f 82 f6 c1 ff ff    	jb     2670 <io_thread.cold+0x5a>
	if (ring->flags & IORING_SETUP_SQE128)
    647a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    647d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    6482:	66 0f ef c0          	pxor   %xmm0,%xmm0
        io_uring_submit(&ring);
    6486:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6489:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6490:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6493:	23 84 24 d8 00 00 00 	and    0xd8(%rsp),%eax
		sq->sqe_tail = next;
    649a:	89 94 24 c4 00 00 00 	mov    %edx,0xc4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    64a1:	d3 e0                	shl    %cl,%eax
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    64a3:	41 8b 57 68          	mov    0x68(%r15),%edx
    64a7:	48 c1 e0 06          	shl    $0x6,%rax
    64ab:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
	sqe->opcode = (__u8) op;
    64b3:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    64b9:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    64bc:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    64c4:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->len = len;
    64c8:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    64d0:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    64d8:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    64dc:	0f 11 40 30          	movups %xmm0,0x30(%rax)
        io_uring_submit(&ring);
    64e0:	e8 ab be ff ff       	call   2390 <io_uring_submit@plt>
    while (data->running == 1) {
    64e5:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    64ea:	0f 84 38 fe ff ff    	je     6328 <io_thread+0x418>
    64f0:	48 8d 3d 3f 2d 00 00 	lea    0x2d3f(%rip),%rdi        # 9236 <_IO_stdin_used+0x236>
    64f7:	e8 34 be ff ff       	call   2330 <puts@plt>
}
    64fc:	48 8b 84 24 68 05 00 00 	mov    0x568(%rsp),%rax
    6504:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    650d:	0f 85 ee 08 00 00    	jne    6e01 <io_thread+0xef1>
    6513:	48 81 c4 78 05 00 00 	add    $0x578,%rsp
    651a:	31 c0                	xor    %eax,%eax
    651c:	5b                   	pop    %rbx
    651d:	5d                   	pop    %rbp
    651e:	41 5c                	pop    %r12
    6520:	41 5d                	pop    %r13
    6522:	41 5e                	pop    %r14
    6524:	41 5f                	pop    %r15
    6526:	c3                   	ret
    6527:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    6530:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    6535:	48 85 c0             	test   %rax,%rax
    6538:	0f 84 62 fe ff ff    	je     63a0 <io_thread+0x490>
        if (cqe->user_data == 1) {
    653e:	48 83 38 01          	cmpq   $0x1,(%rax)
    6542:	0f 84 f8 07 00 00    	je     6d40 <io_thread+0xe30>
    6548:	48 8d 3d 97 2c 00 00 	lea    0x2c97(%rip),%rdi        # 91e6 <_IO_stdin_used+0x1e6>
    654f:	e8 dc bd ff ff       	call   2330 <puts@plt>
        struct Request *req = (struct Request *) cqe->user_data;
    6554:	48 8b 54 24 48       	mov    0x48(%rsp),%rdx
    6559:	4c 8b 32             	mov    (%rdx),%r14
        if (ret < 0)
    655c:	e9 84 fe ff ff       	jmp    63e5 <io_thread+0x4d5>
    6561:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6568:	48 8b 94 24 e8 00 00 00 	mov    0xe8(%rsp),%rdx
    6570:	8b 02                	mov    (%rdx),%eax
    6572:	83 c0 01             	add    $0x1,%eax
    6575:	89 02                	mov    %eax,(%rdx)
}
    6577:	e9 cd fe ff ff       	jmp    6449 <io_thread+0x539>
    657c:	0f 1f 40 00          	nopl   0x0(%rax)
                for (int i = 0; i < req->iovec_count; i++) {
    6580:	41 8b 46 04          	mov    0x4(%r14),%eax
    6584:	45 31 ed             	xor    %r13d,%r13d
    6587:	85 c0                	test   %eax,%eax
    6589:	7e 20                	jle    65ab <io_thread+0x69b>
    658b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                    free(req->iov[i].iov_base);
    6590:	4c 89 e8             	mov    %r13,%rax
                for (int i = 0; i < req->iovec_count; i++) {
    6593:	49 83 c5 01          	add    $0x1,%r13
                    free(req->iov[i].iov_base);
    6597:	48 c1 e0 04          	shl    $0x4,%rax
    659b:	49 8b 7c 06 10       	mov    0x10(%r14,%rax,1),%rdi
    65a0:	e8 5b bd ff ff       	call   2300 <free@plt>
                for (int i = 0; i < req->iovec_count; i++) {
    65a5:	45 39 6e 04          	cmp    %r13d,0x4(%r14)
    65a9:	7f e5                	jg     6590 <io_thread+0x680>
                close(req->client_socket);
    65ab:	41 8b 7e 08          	mov    0x8(%r14),%edi
    65af:	e8 1c be ff ff       	call   23d0 <close@plt>
                free(req);
    65b4:	4c 89 f7             	mov    %r14,%rdi
    65b7:	e8 44 bd ff ff       	call   2300 <free@plt>
        io_uring_cqe_seen(&ring, cqe);
    65bc:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
                break;
    65c1:	e9 7a fe ff ff       	jmp    6440 <io_thread+0x530>
    65c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
                if (!cqe->res) {
    65d0:	85 c0                	test   %eax,%eax
    65d2:	75 3c                	jne    6610 <io_thread+0x700>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    65d4:	48 8b 0d 45 5a 00 00 	mov    0x5a45(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    65db:	ba 0f 00 00 00       	mov    $0xf,%edx
    65e0:	be 01 00 00 00       	mov    $0x1,%esi
    65e5:	48 8d 3d 23 2c 00 00 	lea    0x2c23(%rip),%rdi        # 920f <_IO_stdin_used+0x20f>
    65ec:	e8 3f bf ff ff       	call   2530 <fwrite@plt>
        io_uring_cqe_seen(&ring, cqe);
    65f1:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    65f6:	e9 45 fe ff ff       	jmp    6440 <io_thread+0x530>
    65fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  while (data->running == 1) {
    6600:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    6605:	0f 84 61 fb ff ff    	je     616c <io_thread+0x25c>
    660b:	e9 d0 fb ff ff       	jmp    61e0 <io_thread+0x2d0>
    for (int i = 0; i < dest_sz; i++) {
    6610:	49 8b 56 10          	mov    0x10(%r14),%rdx
    6614:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    6619:	48 8d b4 24 60 05 00 00 	lea    0x560(%rsp),%rsi
    6621:	eb 12                	jmp    6635 <io_thread+0x725>
    6623:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6628:	48 83 c0 01          	add    $0x1,%rax
    662c:	48 83 c2 01          	add    $0x1,%rdx
    6630:	48 39 f0             	cmp    %rsi,%rax
    6633:	74 43                	je     6678 <io_thread+0x768>
        dest[i] = src[i];
    6635:	0f b6 0a             	movzbl (%rdx),%ecx
    6638:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    663a:	80 f9 0d             	cmp    $0xd,%cl
    663d:	75 e9                	jne    6628 <io_thread+0x718>
    663f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    6643:	75 e3                	jne    6628 <io_thread+0x718>
            dest[i] = '\0';
    6645:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    6648:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    664d:	48 89 da             	mov    %rbx,%rdx
    6650:	41 8b 76 08          	mov    0x8(%r14),%esi
    6654:	e8 37 f6 ff ff       	call   5c90 <handle_http_method>
                free(req->iov[0].iov_base);
    6659:	49 8b 7e 10          	mov    0x10(%r14),%rdi
    665d:	e8 9e bc ff ff       	call   2300 <free@plt>
                free(req);
    6662:	4c 89 f7             	mov    %r14,%rdi
    6665:	e8 96 bc ff ff       	call   2300 <free@plt>
        io_uring_cqe_seen(&ring, cqe);
    666a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
                break;
    666f:	e9 cc fd ff ff       	jmp    6440 <io_thread+0x530>
    6674:	0f 1f 40 00          	nopl   0x0(%rax)
    6678:	48 8b 0d a1 59 00 00 	mov    0x59a1(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    667f:	ba 12 00 00 00       	mov    $0x12,%edx
    6684:	be 01 00 00 00       	mov    $0x1,%esi
    6689:	48 8d 3d ce 2a 00 00 	lea    0x2ace(%rip),%rdi        # 915e <_IO_stdin_used+0x15e>
    6690:	e8 9b be ff ff       	call   2530 <fwrite@plt>
        exit(1);
    6695:	bf 01 00 00 00       	mov    $0x1,%edi
    669a:	e8 71 be ff ff       	call   2510 <exit@plt>
    669f:	90                   	nop
    sock = socket(PF_INET, SOCK_STREAM, 0);
    66a0:	31 d2                	xor    %edx,%edx
    66a2:	be 01 00 00 00       	mov    $0x1,%esi
    66a7:	bf 02 00 00 00       	mov    $0x2,%edi
    66ac:	e8 ff be ff ff       	call   25b0 <socket@plt>
    66b1:	89 c5                	mov    %eax,%ebp
    if (sock == -1)
    66b3:	83 f8 ff             	cmp    $0xffffffff,%eax
    66b6:	0f 84 5a bf ff ff    	je     2616 <io_thread.cold>
    if (setsockopt(sock,
    66bc:	48 8d 4c 24 34       	lea    0x34(%rsp),%rcx
    66c1:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    66c7:	ba 02 00 00 00       	mov    $0x2,%edx
    66cc:	89 c7                	mov    %eax,%edi
    66ce:	be 01 00 00 00       	mov    $0x1,%esi
    int enable = 1;
    66d3:	c7 44 24 34 01 00 00 00 	movl   $0x1,0x34(%rsp)
    if (setsockopt(sock,
    66db:	e8 60 bc ff ff       	call   2340 <setsockopt@plt>
    66e0:	85 c0                	test   %eax,%eax
    66e2:	0f 88 3a bf ff ff    	js     2622 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    66e8:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
    if (bind(sock,
    66ed:	ba 10 00 00 00       	mov    $0x10,%edx
    66f2:	89 ef                	mov    %ebp,%edi
    66f4:	48 c7 44 24 54 00 00 00 00 	movq   $0x0,0x54(%rsp)
    66fd:	c7 44 24 5c 00 00 00 00 	movl   $0x0,0x5c(%rsp)
    srv_addr.sin_family = AF_INET;
    6705:	c7 44 24 50 02 00 18 db 	movl   $0xdb180002,0x50(%rsp)
    if (bind(sock,
    670d:	e8 ae bd ff ff       	call   24c0 <bind@plt>
    6712:	85 c0                	test   %eax,%eax
    6714:	0f 88 3e bf ff ff    	js     2658 <io_thread.cold+0x42>
    if (listen(sock, 10) < 0) {
    671a:	be 0a 00 00 00       	mov    $0xa,%esi
    671f:	89 ef                	mov    %ebp,%edi
    6721:	e8 5a bd ff ff       	call   2480 <listen@plt>
    6726:	85 c0                	test   %eax,%eax
    6728:	0f 88 36 bf ff ff    	js     2664 <io_thread.cold+0x4e>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    672e:	89 e9                	mov    %ebp,%ecx
    6730:	ba db 18 00 00       	mov    $0x18db,%edx
    6735:	48 8d 35 1c 2f 00 00 	lea    0x2f1c(%rip),%rsi        # 9658 <_IO_stdin_used+0x658>
    673c:	31 c0                	xor    %eax,%eax
    673e:	bf 01 00 00 00       	mov    $0x1,%edi
    6743:	e8 68 bd ff ff       	call   24b0 <__printf_chk@plt>
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    6748:	be 04 00 00 00       	mov    $0x4,%esi
    674d:	bf 01 00 00 00       	mov    $0x1,%edi
    6752:	e8 a9 bc ff ff       	call   2400 <calloc@plt>
    6757:	49 8b 97 18 01 00 00 	mov    0x118(%r15),%rdx
    675e:	bf 01 00 00 00       	mov    $0x1,%edi
    6763:	48 8d 35 0e 2f 00 00 	lea    0x2f0e(%rip),%rsi        # 9678 <_IO_stdin_used+0x678>
    msg->socket = sock;
    676a:	89 28                	mov    %ebp,(%rax)
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    676c:	49 89 c5             	mov    %rax,%r13
    676f:	31 c0                	xor    %eax,%eax
    6771:	e8 3a bd ff ff       	call   24b0 <__printf_chk@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET, msg);
    6776:	4d 63 b7 10 01 00 00 	movslq 0x110(%r15),%r14
    677d:	49 c1 e6 04          	shl    $0x4,%r14
    6781:	4d 03 b7 08 01 00 00 	add    0x108(%r15),%r14
  while (data->running == 1) {
    6788:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    678d:	0f 85 22 01 00 00    	jne    68b5 <io_thread+0x9a5>
      for (int x = 0 ; x < buffers->count ; x++) {
    6793:	49 63 06             	movslq (%r14),%rax
    6796:	85 c0                	test   %eax,%eax
    6798:	7e ee                	jle    6788 <io_thread+0x878>
        if (buffers->buffer[x].available == 0) {
    679a:	49 8b 56 08          	mov    0x8(%r14),%rdx
    679e:	48 c1 e0 08          	shl    $0x8,%rax
    67a2:	45 31 e4             	xor    %r12d,%r12d
    67a5:	eb 15                	jmp    67bc <io_thread+0x8ac>
    67a7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    67b0:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    67b7:	4c 39 e0             	cmp    %r12,%rax
    67ba:	74 cc                	je     6788 <io_thread+0x878>
        if (buffers->buffer[x].available == 0) {
    67bc:	42 8b bc 22 80 00 00 00 	mov    0x80(%rdx,%r12,1),%edi
    67c4:	85 ff                	test   %edi,%edi
    67c6:	75 e8                	jne    67b0 <io_thread+0x8a0>
    67c8:	42 8b 8c 22 98 00 00 00 	mov    0x98(%rdx,%r12,1),%ecx
    67d0:	49 8b 97 18 01 00 00 	mov    0x118(%r15),%rdx
    67d7:	31 c0                	xor    %eax,%eax
    67d9:	48 8d 35 c3 29 00 00 	lea    0x29c3(%rip),%rsi        # 91a3 <_IO_stdin_used+0x1a3>
    67e0:	bf 01 00 00 00       	mov    $0x1,%edi
    67e5:	e8 c6 bc ff ff       	call   24b0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    67ea:	4d 03 66 08          	add    0x8(%r14),%r12
    67ee:	4d 89 2c 24          	mov    %r13,(%r12)
    bufferrecv(data,  &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply);
    67f2:	4d 63 af 14 01 00 00 	movslq 0x114(%r15),%r13
          buffers->buffer[x].kind = kind;
    67f9:	41 c7 84 24 98 00 00 00 00 00 00 00 	movl   $0x0,0x98(%r12)
          buffers->buffer[x].available = 1;
    6805:	41 c7 84 24 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r12)
    bufferrecv(data,  &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply);
    6811:	49 c1 e5 04          	shl    $0x4,%r13
    6815:	4d 03 af 08 01 00 00 	add    0x108(%r15),%r13
  while (data->running == 1) {
    681c:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    6821:	0f 85 8e 00 00 00    	jne    68b5 <io_thread+0x9a5>
      for (int x = 0 ; x < buffers->count ; x++) {
    6827:	49 63 45 00          	movslq 0x0(%r13),%rax
    682b:	85 c0                	test   %eax,%eax
    682d:	7f 09                	jg     6838 <io_thread+0x928>
    682f:	eb fe                	jmp    682f <io_thread+0x91f>
    6831:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        if (buffers->buffer[x].available == 1) {
    6838:	49 8b 55 08          	mov    0x8(%r13),%rdx
    683c:	48 c1 e0 08          	shl    $0x8,%rax
        if (buffers->buffer[x].available == 0) {
    6840:	45 31 e4             	xor    %r12d,%r12d
    6843:	eb 0f                	jmp    6854 <io_thread+0x944>
    6845:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    6848:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    684f:	4c 39 e0             	cmp    %r12,%rax
    6852:	74 ec                	je     6840 <io_thread+0x930>
        if (buffers->buffer[x].available == 1) {
    6854:	42 83 bc 22 80 00 00 00 01 	cmpl   $0x1,0x80(%rdx,%r12,1)
    685d:	75 e9                	jne    6848 <io_thread+0x938>
    685f:	42 8b 8c 22 98 00 00 00 	mov    0x98(%rdx,%r12,1),%ecx
    6867:	49 8b 97 18 01 00 00 	mov    0x118(%r15),%rdx
    686e:	bf 01 00 00 00       	mov    $0x1,%edi
    6873:	31 c0                	xor    %eax,%eax
    6875:	48 8d 35 33 29 00 00 	lea    0x2933(%rip),%rsi        # 91af <_IO_stdin_used+0x1af>
    687c:	e8 2f bc ff ff       	call   24b0 <__printf_chk@plt>
          struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6881:	be 00 01 00 00       	mov    $0x100,%esi
    6886:	bf 01 00 00 00       	mov    $0x1,%edi
    688b:	e8 70 bb ff ff       	call   2400 <calloc@plt>
          reply->data = buffers->buffer[x].data;
    6890:	4d 03 65 08          	add    0x8(%r13),%r12
          buffers->buffer[x].available = 0;
    6894:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
          reply->data = buffers->buffer[x].data;
    68a0:	49 8b 14 24          	mov    (%r12),%rdx
    68a4:	48 89 10             	mov    %rdx,(%rax)
          reply->kind = buffers->buffer[x].kind;
    68a7:	41 8b 94 24 98 00 00 00 	mov    0x98(%r12),%edx
    68af:	89 90 98 00 00 00    	mov    %edx,0x98(%rax)
    68b5:	49 8b 97 18 01 00 00 	mov    0x118(%r15),%rdx
    68bc:	48 8d 35 dd 2d 00 00 	lea    0x2ddd(%rip),%rsi        # 96a0 <_IO_stdin_used+0x6a0>
    68c3:	bf 01 00 00 00       	mov    $0x1,%edi
    68c8:	31 c0                	xor    %eax,%eax
    68ca:	e8 e1 bb ff ff       	call   24b0 <__printf_chk@plt>
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    68cf:	48 8d 44 24 60       	lea    0x60(%rsp),%rax
    68d4:	48 89 d9             	mov    %rbx,%rcx
    68d7:	89 ef                	mov    %ebp,%edi
    68d9:	48 8d 54 24 38       	lea    0x38(%rsp),%rdx
    68de:	48 89 c6             	mov    %rax,%rsi
    68e1:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    68e6:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    socklen_t client_addr_len = sizeof(client_addr);
    68eb:	c7 44 24 38 10 00 00 00 	movl   $0x10,0x38(%rsp)
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    68f3:	e8 78 f5 ff ff       	call   5e70 <add_accept_request>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    68f8:	bf 01 00 00 00       	mov    $0x1,%edi
    68fd:	be 10 00 00 00       	mov    $0x10,%esi
    6902:	e8 f9 ba ff ff       	call   2400 <calloc@plt>
    void *buf = malloc(size);
    6907:	bf 0a 00 00 00       	mov    $0xa,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    690c:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    690f:	e8 5c bb ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    6914:	48 85 c0             	test   %rax,%rax
    6917:	0f 84 10 05 00 00    	je     6e2d <io_thread+0xf1d>
    iov->iov_base = zh_malloc(10);
    691d:	49 89 04 24          	mov    %rax,(%r12)
	unsigned int head, next = sq->sqe_tail + 1;
    6921:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
    iov->iov_len = 10;
    6928:	49 c7 44 24 08 0a 00 00 00 	movq   $0xa,0x8(%r12)
	if (ring->flags & IORING_SETUP_SQE128)
    6931:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    6938:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    693b:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6943:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6945:	f6 c1 02             	test   $0x2,%cl
    6948:	0f 85 82 02 00 00    	jne    6bd0 <io_thread+0xcc0>
	if (next - head <= sq->ring_entries) {
    694e:	89 d0                	mov    %edx,%eax
    6950:	29 f0                	sub    %esi,%eax
    6952:	39 84 24 dc 00 00 00 	cmp    %eax,0xdc(%rsp)
    6959:	0f 82 d9 bc ff ff    	jb     2638 <io_thread.cold+0x22>
	if (ring->flags & IORING_SETUP_SQE128)
    695f:	c1 e9 0a             	shr    $0xa,%ecx
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
    6962:	4d 8d 77 68          	lea    0x68(%r15),%r14
	sqe->addr3 = 0;
    6966:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(&ring);
    696a:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    696d:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6974:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6977:	23 84 24 d8 00 00 00 	and    0xd8(%rsp),%eax
		sq->sqe_tail = next;
    697e:	89 94 24 c4 00 00 00 	mov    %edx,0xc4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6985:	d3 e0                	shl    %cl,%eax
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6987:	41 8b 57 68          	mov    0x68(%r15),%edx
    698b:	48 c1 e0 06          	shl    $0x6,%rax
    698f:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
	sqe->opcode = (__u8) op;
    6997:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    699d:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    69a0:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    69a8:	4c 89 60 10          	mov    %r12,0x10(%rax)
	sqe->len = len;
    69ac:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    69b4:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    69bc:	4c 89 70 20          	mov    %r14,0x20(%rax)
	sqe->addr3 = 0;
    69c0:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(&ring);
    69c4:	e8 c7 b9 ff ff       	call   2390 <io_uring_submit@plt>
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    69c9:	48 8d 44 24 40       	lea    0x40(%rsp),%rax
    while (data->running == 1) {
    69ce:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    69d3:	48 89 04 24          	mov    %rax,(%rsp)
    69d7:	48 8d 84 24 60 01 00 00 	lea    0x160(%rsp),%rax
    69df:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    69e4:	0f 85 d5 01 00 00    	jne    6bbf <io_thread+0xcaf>
    69ea:	89 6c 24 18          	mov    %ebp,0x18(%rsp)
    69ee:	66 90                	xchg   %ax,%ax
    69f0:	48 8d 3d c4 27 00 00 	lea    0x27c4(%rip),%rdi        # 91bb <_IO_stdin_used+0x1bb>
    69f7:	e8 34 b9 ff ff       	call   2330 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    69fc:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    6a03:	8b bc 24 30 01 00 00 	mov    0x130(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    6a0a:	c1 e9 0b             	shr    $0xb,%ecx
    6a0d:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    6a10:	48 8b 84 24 f0 00 00 00 	mov    0xf0(%rsp),%rax
    6a18:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    6a1a:	48 8b b4 24 e8 00 00 00 	mov    0xe8(%rsp),%rsi
    6a22:	8b 16                	mov    (%rsi),%edx
		if (!available)
    6a24:	39 d0                	cmp    %edx,%eax
    6a26:	74 36                	je     6a5e <io_thread+0xb4e>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    6a28:	89 f8                	mov    %edi,%eax
    6a2a:	21 d0                	and    %edx,%eax
    6a2c:	d3 e0                	shl    %cl,%eax
    6a2e:	48 c1 e0 04          	shl    $0x4,%rax
    6a32:	48 03 84 24 18 01 00 00 	add    0x118(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    6a3a:	f6 84 24 49 01 00 00 01 	testb  $0x1,0x149(%rsp)
    6a42:	0f 85 90 01 00 00    	jne    6bd8 <io_thread+0xcc8>
    6a48:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    6a4c:	0f 85 16 03 00 00    	jne    6d68 <io_thread+0xe58>
			if (cqe->res < 0)
    6a52:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6a55:	83 c2 01             	add    $0x1,%edx
    6a58:	89 16                	mov    %edx,(%rsi)
			if (!err)
    6a5a:	85 c0                	test   %eax,%eax
    6a5c:	79 b2                	jns    6a10 <io_thread+0xb00>
	*cqe_ptr = cqe;
    6a5e:	48 c7 44 24 40 00 00 00 00 	movq   $0x0,0x40(%rsp)
	return err;
    6a67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    6a70:	48 8b 34 24          	mov    (%rsp),%rsi
    6a74:	45 31 c0             	xor    %r8d,%r8d
    6a77:	31 d2                	xor    %edx,%edx
    6a79:	b9 01 00 00 00       	mov    $0x1,%ecx
    6a7e:	48 89 df             	mov    %rbx,%rdi
    6a81:	e8 1a ba ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    6a86:	41 89 c5             	mov    %eax,%r13d
        if (cqe->user_data == 1) {
    6a89:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6a8e:	48 83 38 01          	cmpq   $0x1,(%rax)
    6a92:	0f 84 da 02 00 00    	je     6d72 <io_thread+0xe62>
    6a98:	48 8d 3d 47 27 00 00 	lea    0x2747(%rip),%rdi        # 91e6 <_IO_stdin_used+0x1e6>
    6a9f:	e8 8c b8 ff ff       	call   2330 <puts@plt>
        struct Request *req = (struct Request *) cqe->user_data;
    6aa4:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    6aa9:	48 8b 2a             	mov    (%rdx),%rbp
        if (ret < 0)
    6aac:	45 85 ed             	test   %r13d,%r13d
    6aaf:	0f 88 8d bb ff ff    	js     2642 <io_thread.cold+0x2c>
        if (cqe->res < 0) {
    6ab5:	8b 42 08             	mov    0x8(%rdx),%eax
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    6ab8:	44 8b 45 00          	mov    0x0(%rbp),%r8d
        if (cqe->res < 0) {
    6abc:	85 c0                	test   %eax,%eax
    6abe:	0f 88 ce 02 00 00    	js     6d92 <io_thread+0xe82>
        switch (req->event_type) {
    6ac4:	41 83 f8 01          	cmp    $0x1,%r8d
    6ac8:	0f 84 a2 01 00 00    	je     6c70 <io_thread+0xd60>
    6ace:	41 83 f8 02          	cmp    $0x2,%r8d
    6ad2:	0f 84 50 01 00 00    	je     6c28 <io_thread+0xd18>
    6ad8:	45 85 c0             	test   %r8d,%r8d
    6adb:	0f 85 2f 01 00 00    	jne    6c10 <io_thread+0xd00>
                add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6ae1:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    6ae6:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    6aeb:	48 89 d9             	mov    %rbx,%rcx
    6aee:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    6af2:	e8 79 f3 ff ff       	call   5e70 <add_accept_request>
                add_read_request(cqe->res, &ring);
    6af7:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6afc:	48 89 de             	mov    %rbx,%rsi
    6aff:	8b 78 08             	mov    0x8(%rax),%edi
    6b02:	e8 09 ed ff ff       	call   5810 <add_read_request>
                free(req);
    6b07:	48 89 ef             	mov    %rbp,%rdi
    6b0a:	e8 f1 b7 ff ff       	call   2300 <free@plt>
        io_uring_cqe_seen(&ring, cqe);
    6b0f:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
	if (cqe)
    6b14:	48 85 c0             	test   %rax,%rax
    6b17:	0f 85 f3 00 00 00    	jne    6c10 <io_thread+0xd00>
	unsigned int head, next = sq->sqe_tail + 1;
    6b1d:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6b24:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    6b2b:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    6b2e:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6b36:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6b38:	f6 c1 02             	test   $0x2,%cl
    6b3b:	74 00                	je     6b3d <io_thread+0xc2d>
	if (next - head <= sq->ring_entries) {
    6b3d:	89 d0                	mov    %edx,%eax
    6b3f:	29 f0                	sub    %esi,%eax
    6b41:	39 84 24 dc 00 00 00 	cmp    %eax,0xdc(%rsp)
    6b48:	0f 82 e0 ba ff ff    	jb     262e <io_thread.cold+0x18>
	if (ring->flags & IORING_SETUP_SQE128)
    6b4e:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6b51:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
    6b58:	23 84 24 d8 00 00 00 	and    0xd8(%rsp),%eax
        io_uring_submit(&ring);
    6b5f:	48 89 df             	mov    %rbx,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    6b62:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    6b65:	89 94 24 c4 00 00 00 	mov    %edx,0xc4(%rsp)
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6b6c:	41 8b 57 68          	mov    0x68(%r15),%edx
	sqe->addr3 = 0;
    6b70:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6b74:	d3 e0                	shl    %cl,%eax
    6b76:	48 c1 e0 06          	shl    $0x6,%rax
    6b7a:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
	sqe->opcode = (__u8) op;
    6b82:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    6b88:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    6b8b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    6b93:	4c 89 60 10          	mov    %r12,0x10(%rax)
	sqe->len = len;
    6b97:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    6b9f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    6ba7:	4c 89 70 20          	mov    %r14,0x20(%rax)
	sqe->addr3 = 0;
    6bab:	0f 11 40 30          	movups %xmm0,0x30(%rax)
        io_uring_submit(&ring);
    6baf:	e8 dc b7 ff ff       	call   2390 <io_uring_submit@plt>
    while (data->running == 1) {
    6bb4:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    6bb9:	0f 84 31 fe ff ff    	je     69f0 <io_thread+0xae0>
  if (data->io_mode == IO_MODE_SEND) {
    6bbf:	41 8b 87 04 01 00 00 	mov    0x104(%r15),%eax
    6bc6:	e9 6a f4 ff ff       	jmp    6035 <io_thread+0x125>
    6bcb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    6bd0:	e9 79 fd ff ff       	jmp    694e <io_thread+0xa3e>
    6bd5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    6bd8:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    6bdd:	48 85 c0             	test   %rax,%rax
    6be0:	0f 84 8a fe ff ff    	je     6a70 <io_thread+0xb60>
        if (cqe->user_data == 1) {
    6be6:	48 83 38 01          	cmpq   $0x1,(%rax)
    6bea:	0f 84 82 01 00 00    	je     6d72 <io_thread+0xe62>
    6bf0:	48 8d 3d ef 25 00 00 	lea    0x25ef(%rip),%rdi        # 91e6 <_IO_stdin_used+0x1e6>
    6bf7:	e8 34 b7 ff ff       	call   2330 <puts@plt>
        struct Request *req = (struct Request *) cqe->user_data;
    6bfc:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    6c01:	48 8b 2a             	mov    (%rdx),%rbp
        if (ret < 0)
    6c04:	e9 ac fe ff ff       	jmp    6ab5 <io_thread+0xba5>
    6c09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6c10:	48 8b 94 24 e8 00 00 00 	mov    0xe8(%rsp),%rdx
    6c18:	8b 02                	mov    (%rdx),%eax
    6c1a:	83 c0 01             	add    $0x1,%eax
    6c1d:	89 02                	mov    %eax,(%rdx)
}
    6c1f:	e9 f9 fe ff ff       	jmp    6b1d <io_thread+0xc0d>
    6c24:	0f 1f 40 00          	nopl   0x0(%rax)
                for (int i = 0; i < req->iovec_count; i++) {
    6c28:	8b 75 04             	mov    0x4(%rbp),%esi
    6c2b:	45 31 ed             	xor    %r13d,%r13d
    6c2e:	85 f6                	test   %esi,%esi
    6c30:	7e 21                	jle    6c53 <io_thread+0xd43>
    6c32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
                    free(req->iov[i].iov_base);
    6c38:	4c 89 e8             	mov    %r13,%rax
                for (int i = 0; i < req->iovec_count; i++) {
    6c3b:	49 83 c5 01          	add    $0x1,%r13
                    free(req->iov[i].iov_base);
    6c3f:	48 c1 e0 04          	shl    $0x4,%rax
    6c43:	48 8b 7c 05 10       	mov    0x10(%rbp,%rax,1),%rdi
    6c48:	e8 b3 b6 ff ff       	call   2300 <free@plt>
                for (int i = 0; i < req->iovec_count; i++) {
    6c4d:	44 39 6d 04          	cmp    %r13d,0x4(%rbp)
    6c51:	7f e5                	jg     6c38 <io_thread+0xd28>
                close(req->client_socket);
    6c53:	8b 7d 08             	mov    0x8(%rbp),%edi
    6c56:	e8 75 b7 ff ff       	call   23d0 <close@plt>
                free(req);
    6c5b:	48 89 ef             	mov    %rbp,%rdi
    6c5e:	e8 9d b6 ff ff       	call   2300 <free@plt>
        io_uring_cqe_seen(&ring, cqe);
    6c63:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
                break;
    6c68:	e9 a7 fe ff ff       	jmp    6b14 <io_thread+0xc04>
    6c6d:	0f 1f 00             	nopl   (%rax)
                if (!cqe->res) {
    6c70:	85 c0                	test   %eax,%eax
    6c72:	75 2c                	jne    6ca0 <io_thread+0xd90>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6c74:	48 8b 0d a5 53 00 00 	mov    0x53a5(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6c7b:	ba 0f 00 00 00       	mov    $0xf,%edx
    6c80:	be 01 00 00 00       	mov    $0x1,%esi
    6c85:	48 8d 3d 83 25 00 00 	lea    0x2583(%rip),%rdi        # 920f <_IO_stdin_used+0x20f>
    6c8c:	e8 9f b8 ff ff       	call   2530 <fwrite@plt>
        io_uring_cqe_seen(&ring, cqe);
    6c91:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6c96:	e9 79 fe ff ff       	jmp    6b14 <io_thread+0xc04>
    6c9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int i = 0; i < dest_sz; i++) {
    6ca0:	48 8b 55 10          	mov    0x10(%rbp),%rdx
    6ca4:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    6ca9:	48 8d b4 24 60 05 00 00 	lea    0x560(%rsp),%rsi
    6cb1:	eb 12                	jmp    6cc5 <io_thread+0xdb5>
    6cb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6cb8:	48 83 c0 01          	add    $0x1,%rax
    6cbc:	48 83 c2 01          	add    $0x1,%rdx
    6cc0:	48 39 c6             	cmp    %rax,%rsi
    6cc3:	74 43                	je     6d08 <io_thread+0xdf8>
        dest[i] = src[i];
    6cc5:	0f b6 0a             	movzbl (%rdx),%ecx
    6cc8:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    6cca:	80 f9 0d             	cmp    $0xd,%cl
    6ccd:	75 e9                	jne    6cb8 <io_thread+0xda8>
    6ccf:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    6cd3:	75 e3                	jne    6cb8 <io_thread+0xda8>
            dest[i] = '\0';
    6cd5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    6cd8:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    6cdd:	48 89 da             	mov    %rbx,%rdx
    6ce0:	8b 75 08             	mov    0x8(%rbp),%esi
    6ce3:	e8 a8 ef ff ff       	call   5c90 <handle_http_method>
                free(req->iov[0].iov_base);
    6ce8:	48 8b 7d 10          	mov    0x10(%rbp),%rdi
    6cec:	e8 0f b6 ff ff       	call   2300 <free@plt>
                free(req);
    6cf1:	48 89 ef             	mov    %rbp,%rdi
    6cf4:	e8 07 b6 ff ff       	call   2300 <free@plt>
        io_uring_cqe_seen(&ring, cqe);
    6cf9:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
                break;
    6cfe:	e9 11 fe ff ff       	jmp    6b14 <io_thread+0xc04>
    6d03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6d08:	48 8b 0d 11 53 00 00 	mov    0x5311(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6d0f:	ba 12 00 00 00       	mov    $0x12,%edx
    6d14:	be 01 00 00 00       	mov    $0x1,%esi
    6d19:	48 8d 3d 3e 24 00 00 	lea    0x243e(%rip),%rdi        # 915e <_IO_stdin_used+0x15e>
    6d20:	e8 0b b8 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    6d25:	bf 01 00 00 00       	mov    $0x1,%edi
    6d2a:	e8 e1 b7 ff ff       	call   2510 <exit@plt>
    6d2f:	90                   	nop
	*cqe_ptr = cqe;
    6d30:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
	return err;
    6d35:	e9 04 f8 ff ff       	jmp    653e <io_thread+0x62e>
    6d3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6d40:	48 8b 94 24 e8 00 00 00 	mov    0xe8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6d48:	48 8d 3d 83 24 00 00 	lea    0x2483(%rip),%rdi        # 91d2 <_IO_stdin_used+0x1d2>
    6d4f:	8b 02                	mov    (%rdx),%eax
    6d51:	83 c0 01             	add    $0x1,%eax
    6d54:	89 02                	mov    %eax,(%rdx)
    6d56:	e8 d5 b5 ff ff       	call   2330 <puts@plt>
    6d5b:	e9 90 f7 ff ff       	jmp    64f0 <io_thread+0x5e0>
      for (int x = 0 ; x < buffers->count ; x++) {
    6d60:	eb fe                	jmp    6d60 <io_thread+0xe50>
    6d62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    6d68:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
	return err;
    6d6d:	e9 74 fe ff ff       	jmp    6be6 <io_thread+0xcd6>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6d72:	48 8b 94 24 e8 00 00 00 	mov    0xe8(%rsp),%rdx
    6d7a:	48 8d 3d 51 24 00 00 	lea    0x2451(%rip),%rdi        # 91d2 <_IO_stdin_used+0x1d2>
    6d81:	8b 02                	mov    (%rdx),%eax
    6d83:	83 c0 01             	add    $0x1,%eax
    6d86:	89 02                	mov    %eax,(%rdx)
    6d88:	e8 a3 b5 ff ff       	call   2330 <puts@plt>
    6d8d:	e9 2d fe ff ff       	jmp    6bbf <io_thread+0xcaf>
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    6d92:	f7 d8                	neg    %eax
    6d94:	44 89 04 24          	mov    %r8d,(%rsp)
    6d98:	89 c7                	mov    %eax,%edi
    6d9a:	e8 d1 b7 ff ff       	call   2570 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6d9f:	48 8b 3d 7a 52 00 00 	mov    0x527a(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    6da6:	44 8b 04 24          	mov    (%rsp),%r8d
    6daa:	48 8d 15 17 29 00 00 	lea    0x2917(%rip),%rdx        # 96c8 <_IO_stdin_used+0x6c8>
    6db1:	48 89 c1             	mov    %rax,%rcx
    6db4:	be 01 00 00 00       	mov    $0x1,%esi
    6db9:	31 c0                	xor    %eax,%eax
    6dbb:	e8 80 b7 ff ff       	call   2540 <__fprintf_chk@plt>
            exit(1);
    6dc0:	bf 01 00 00 00       	mov    $0x1,%edi
    6dc5:	e8 46 b7 ff ff       	call   2510 <exit@plt>
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    6dca:	f7 d8                	neg    %eax
    6dcc:	89 14 24             	mov    %edx,(%rsp)
    6dcf:	89 c7                	mov    %eax,%edi
    6dd1:	e8 9a b7 ff ff       	call   2570 <strerror@plt>
    6dd6:	48 8b 3d 43 52 00 00 	mov    0x5243(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    6ddd:	44 8b 04 24          	mov    (%rsp),%r8d
    6de1:	48 8d 15 e0 28 00 00 	lea    0x28e0(%rip),%rdx        # 96c8 <_IO_stdin_used+0x6c8>
    6de8:	48 89 c1             	mov    %rax,%rcx
    6deb:	be 01 00 00 00       	mov    $0x1,%esi
    6df0:	31 c0                	xor    %eax,%eax
    6df2:	e8 49 b7 ff ff       	call   2540 <__fprintf_chk@plt>
            exit(1);
    6df7:	bf 01 00 00 00       	mov    $0x1,%edi
    6dfc:	e8 0f b7 ff ff       	call   2510 <exit@plt>
}
    6e01:	e8 7a b5 ff ff       	call   2380 <__stack_chk_fail@plt>
    6e06:	48 8b 0d 13 52 00 00 	mov    0x5213(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6e0d:	ba 28 00 00 00       	mov    $0x28,%edx
    6e12:	be 01 00 00 00       	mov    $0x1,%esi
    6e17:	48 8d 3d 0a 28 00 00 	lea    0x280a(%rip),%rdi        # 9628 <_IO_stdin_used+0x628>
    6e1e:	e8 0d b7 ff ff       	call   2530 <fwrite@plt>
        exit(1);
    6e23:	bf 01 00 00 00       	mov    $0x1,%edi
    6e28:	e8 e3 b6 ff ff       	call   2510 <exit@plt>
    6e2d:	48 8b 0d ec 51 00 00 	mov    0x51ec(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6e34:	ba 28 00 00 00       	mov    $0x28,%edx
    6e39:	be 01 00 00 00       	mov    $0x1,%esi
    6e3e:	48 8d 3d e3 27 00 00 	lea    0x27e3(%rip),%rdi        # 9628 <_IO_stdin_used+0x628>
    6e45:	e8 e6 b6 ff ff       	call   2530 <fwrite@plt>
    6e4a:	bf 01 00 00 00       	mov    $0x1,%edi
    6e4f:	e8 bc b6 ff ff       	call   2510 <exit@plt>
    6e54:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6e5f:	90                   	nop

0000000000006e60 <buffersend>:
int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send) {
    6e60:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    6e64:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    6e68:	0f 85 96 00 00 00    	jne    6f04 <buffersend+0xa4>
int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send) {
    6e6e:	41 55                	push   %r13
    6e70:	49 89 cd             	mov    %rcx,%r13
    6e73:	41 54                	push   %r12
    6e75:	41 89 d4             	mov    %edx,%r12d
    6e78:	55                   	push   %rbp
    6e79:	48 89 f5             	mov    %rsi,%rbp
    6e7c:	53                   	push   %rbx
    6e7d:	48 83 ec 08          	sub    $0x8,%rsp
      for (int x = 0 ; x < buffers->count ; x++) {
    6e81:	48 63 45 00          	movslq 0x0(%rbp),%rax
    6e85:	85 c0                	test   %eax,%eax
    6e87:	7e 6f                	jle    6ef8 <buffersend+0x98>
        if (buffers->buffer[x].available == 0) {
    6e89:	48 8b 55 08          	mov    0x8(%rbp),%rdx
    6e8d:	48 c1 e0 08          	shl    $0x8,%rax
    6e91:	31 db                	xor    %ebx,%ebx
    6e93:	eb 0f                	jmp    6ea4 <buffersend+0x44>
    6e95:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    6e98:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    6e9f:	48 39 c3             	cmp    %rax,%rbx
    6ea2:	74 54                	je     6ef8 <buffersend+0x98>
        if (buffers->buffer[x].available == 0) {
    6ea4:	8b 8c 1a 80 00 00 00 	mov    0x80(%rdx,%rbx,1),%ecx
    6eab:	85 c9                	test   %ecx,%ecx
    6ead:	75 e9                	jne    6e98 <buffersend+0x38>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6eaf:	8b 8c 1a 98 00 00 00 	mov    0x98(%rdx,%rbx,1),%ecx
    6eb6:	48 8b 97 18 01 00 00 	mov    0x118(%rdi),%rdx
    6ebd:	31 c0                	xor    %eax,%eax
    6ebf:	bf 01 00 00 00       	mov    $0x1,%edi
    6ec4:	48 8d 35 d8 22 00 00 	lea    0x22d8(%rip),%rsi        # 91a3 <_IO_stdin_used+0x1a3>
    6ecb:	e8 e0 b5 ff ff       	call   24b0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    6ed0:	48 03 5d 08          	add    0x8(%rbp),%rbx
    6ed4:	4c 89 2b             	mov    %r13,(%rbx)
          buffers->buffer[x].kind = kind;
    6ed7:	44 89 a3 98 00 00 00 	mov    %r12d,0x98(%rbx)
          buffers->buffer[x].available = 1;
    6ede:	c7 83 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbx)
}
    6ee8:	48 83 c4 08          	add    $0x8,%rsp
    6eec:	31 c0                	xor    %eax,%eax
    6eee:	5b                   	pop    %rbx
    6eef:	5d                   	pop    %rbp
    6ef0:	41 5c                	pop    %r12
    6ef2:	41 5d                	pop    %r13
    6ef4:	c3                   	ret
    6ef5:	0f 1f 00             	nopl   (%rax)
  while (data->running == 1) {
    6ef8:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    6efc:	0f 84 7f ff ff ff    	je     6e81 <buffersend+0x21>
    6f02:	eb e4                	jmp    6ee8 <buffersend+0x88>
}
    6f04:	31 c0                	xor    %eax,%eax
    6f06:	c3                   	ret
    6f07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006f10 <bufferrecv>:
void * bufferrecv(struct KernelThread *data, struct Buffers *buffers, int kind, void ** send) {
    6f10:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    6f14:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    6f18:	0f 85 8f 00 00 00    	jne    6fad <bufferrecv+0x9d>
void * bufferrecv(struct KernelThread *data, struct Buffers *buffers, int kind, void ** send) {
    6f1e:	55                   	push   %rbp
    6f1f:	48 89 f5             	mov    %rsi,%rbp
    6f22:	53                   	push   %rbx
    6f23:	48 83 ec 08          	sub    $0x8,%rsp
      for (int x = 0 ; x < buffers->count ; x++) {
    6f27:	48 63 06             	movslq (%rsi),%rax
    6f2a:	85 c0                	test   %eax,%eax
    6f2c:	7f 02                	jg     6f30 <bufferrecv+0x20>
    6f2e:	eb fe                	jmp    6f2e <bufferrecv+0x1e>
    6f30:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    6f34:	48 c1 e0 08          	shl    $0x8,%rax
        if (buffers->buffer[x].available == 1) {
    6f38:	31 db                	xor    %ebx,%ebx
    6f3a:	eb 10                	jmp    6f4c <bufferrecv+0x3c>
    6f3c:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    6f40:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    6f47:	48 39 c3             	cmp    %rax,%rbx
    6f4a:	74 ec                	je     6f38 <bufferrecv+0x28>
        if (buffers->buffer[x].available == 1) {
    6f4c:	83 bc 1a 80 00 00 00 01 	cmpl   $0x1,0x80(%rdx,%rbx,1)
    6f54:	75 ea                	jne    6f40 <bufferrecv+0x30>
    6f56:	8b 8c 1a 98 00 00 00 	mov    0x98(%rdx,%rbx,1),%ecx
    6f5d:	48 8b 97 18 01 00 00 	mov    0x118(%rdi),%rdx
    6f64:	31 c0                	xor    %eax,%eax
    6f66:	bf 01 00 00 00       	mov    $0x1,%edi
    6f6b:	48 8d 35 3d 22 00 00 	lea    0x223d(%rip),%rsi        # 91af <_IO_stdin_used+0x1af>
    6f72:	e8 39 b5 ff ff       	call   24b0 <__printf_chk@plt>
          struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6f77:	be 00 01 00 00       	mov    $0x100,%esi
    6f7c:	bf 01 00 00 00       	mov    $0x1,%edi
    6f81:	e8 7a b4 ff ff       	call   2400 <calloc@plt>
          reply->data = buffers->buffer[x].data;
    6f86:	48 03 5d 08          	add    0x8(%rbp),%rbx
    6f8a:	48 8b 13             	mov    (%rbx),%rdx
    6f8d:	48 89 10             	mov    %rdx,(%rax)
          reply->kind = buffers->buffer[x].kind;
    6f90:	8b 93 98 00 00 00    	mov    0x98(%rbx),%edx
    6f96:	89 90 98 00 00 00    	mov    %edx,0x98(%rax)
          buffers->buffer[x].available = 0;
    6f9c:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
}
    6fa6:	48 83 c4 08          	add    $0x8,%rsp
    6faa:	5b                   	pop    %rbx
    6fab:	5d                   	pop    %rbp
    6fac:	c3                   	ret
  return 0;
    6fad:	31 c0                	xor    %eax,%eax
}
    6faf:	c3                   	ret

0000000000006fb0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    6fb0:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6fb4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    6fbb:	8b 8e c4 00 00 00    	mov    0xc4(%rsi),%ecx
    6fc1:	85 c9                	test   %ecx,%ecx
    6fc3:	0f 8e e7 00 00 00    	jle    70b0 <barriered_work_ingest+0x100>
int barriered_work_ingest(struct BarrierTask *data) {
    6fc9:	41 56                	push   %r14
    6fcb:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6fcd:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    6fd0:	41 54                	push   %r12
    6fd2:	49 89 fc             	mov    %rdi,%r12
    6fd5:	55                   	push   %rbp
    6fd6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6fd7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6fdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6fe0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    6fe4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    6fec:	31 db                	xor    %ebx,%ebx
    6fee:	8b 10                	mov    (%rax),%edx
    6ff0:	85 d2                	test   %edx,%edx
    6ff2:	7e 26                	jle    701a <barriered_work_ingest+0x6a>
    6ff4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    6ff8:	48 89 dd             	mov    %rbx,%rbp
    6ffb:	48 c1 e5 08          	shl    $0x8,%rbp
    6fff:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    7003:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    700a:	74 24                	je     7030 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    700c:	48 83 c3 01          	add    $0x1,%rbx
    7010:	39 da                	cmp    %ebx,%edx
    7012:	7f e4                	jg     6ff8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    7014:	8b 8e c4 00 00 00    	mov    0xc4(%rsi),%ecx
    701a:	49 83 c5 01          	add    $0x1,%r13
    701e:	44 39 e9             	cmp    %r13d,%ecx
    7021:	7f bd                	jg     6fe0 <barriered_work_ingest+0x30>
}
    7023:	5b                   	pop    %rbx
    7024:	31 c0                	xor    %eax,%eax
    7026:	5d                   	pop    %rbp
    7027:	41 5c                	pop    %r12
    7029:	41 5d                	pop    %r13
    702b:	41 5e                	pop    %r14
    702d:	c3                   	ret
    702e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    7030:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    7039:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    7040:	bf 04 00 00 00       	mov    $0x4,%edi
    7045:	48 c1 e6 05          	shl    $0x5,%rsi
    7049:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    7050:	48 83 c6 10          	add    $0x10,%rsi
    7054:	e8 f7 b2 ff ff       	call   2350 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    7059:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    7061:	48 8b 40 50          	mov    0x50(%rax),%rax
    7065:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    7069:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    706d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    7077:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    707d:	83 c0 01             	add    $0x1,%eax
    7080:	99                   	cltd
    7081:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    7087:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    708d:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    7095:	48 83 c3 01          	add    $0x1,%rbx
    7099:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    709d:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    70a1:	8b 10                	mov    (%rax),%edx
    70a3:	39 da                	cmp    %ebx,%edx
    70a5:	0f 8f 49 ff ff ff    	jg     6ff4 <barriered_work_ingest+0x44>
    70ab:	e9 64 ff ff ff       	jmp    7014 <barriered_work_ingest+0x64>
}
    70b0:	31 c0                	xor    %eax,%eax
    70b2:	c3                   	ret
    70b3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    70be:	66 90                	xchg   %ax,%ax

00000000000070c0 <barriered_thread>:
void* barriered_thread(void *arg) {
    70c0:	f3 0f 1e fa          	endbr64
    70c4:	41 56                	push   %r14
    70c6:	41 55                	push   %r13
    70c8:	41 54                	push   %r12
  int t = 0;
    70ca:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    70cd:	55                   	push   %rbp
  int waiting = 0;
    70ce:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    70d0:	53                   	push   %rbx
    70d1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    70d4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    70d8:	0f 85 7c 02 00 00    	jne    735a <barriered_thread+0x29a>
    if (t >= data->task_count) {
    70de:	8b 43 40             	mov    0x40(%rbx),%eax
    70e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    70e8:	41 39 c4             	cmp    %eax,%r12d
    70eb:	0f 8d 6f 01 00 00    	jge    7260 <barriered_thread+0x1a0>
    70f1:	49 63 fc             	movslq %r12d,%rdi
    70f4:	48 c1 e7 09          	shl    $0x9,%rdi
    70f8:	49 89 fd             	mov    %rdi,%r13
    70fb:	eb 32                	jmp    712f <barriered_thread+0x6f>
    70fd:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    7100:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    7104:	48 8b 43 18          	mov    0x18(%rbx),%rax
    7108:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    710c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7110:	4c 01 ef             	add    %r13,%rdi
    7113:	e8 98 fe ff ff       	call   6fb0 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    7118:	8b 43 40             	mov    0x40(%rbx),%eax
    711b:	41 83 c4 01          	add    $0x1,%r12d
    711f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    7126:	44 39 e0             	cmp    %r12d,%eax
    7129:	0f 8e 21 02 00 00    	jle    7350 <barriered_thread+0x290>
      if (data->tasks[t].available == 1) {
    712f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    7133:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    7137:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    713e:	75 c0                	jne    7100 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    7140:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    7144:	83 e8 01             	sub    $0x1,%eax
    7147:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    714c:	45 85 e4             	test   %r12d,%r12d
    714f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    7152:	45 85 c0             	test   %r8d,%r8d
    7155:	0f 8e 2d 01 00 00    	jle    7288 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    715b:	48 63 c8             	movslq %eax,%rcx
    715e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    7162:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    7165:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    716b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    7172:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    7176:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    7179:	45 31 f6             	xor    %r14d,%r14d
    717c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    7180:	48 8b 10             	mov    (%rax),%rdx
    7183:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    7187:	49 01 cb             	add    %rcx,%r11
    718a:	4c 89 da             	mov    %r11,%rdx
    718d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    7194:	75 04                	jne    719a <barriered_thread+0xda>
            arrived++;
    7196:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    719a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    71a0:	75 04                	jne    71a6 <barriered_thread+0xe6>
            prearrive++;
    71a2:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    71a6:	48 83 c0 08          	add    $0x8,%rax
    71aa:	48 39 c6             	cmp    %rax,%rsi
    71ad:	75 d1                	jne    7180 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    71af:	45 85 d2             	test   %r10d,%r10d
    71b2:	0f 84 c0 00 00 00    	je     7278 <barriered_thread+0x1b8>
    71b8:	45 39 d0             	cmp    %r10d,%r8d
    71bb:	0f 84 b7 00 00 00    	je     7278 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    71c1:	45 85 f6             	test   %r14d,%r14d
    71c4:	74 0a                	je     71d0 <barriered_thread+0x110>
    71c6:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    71ca:	0f 85 b6 01 00 00    	jne    7386 <barriered_thread+0x2c6>
    71d0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    71d4:	4c 01 ea             	add    %r13,%rdx
    71d7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    71de:	45 85 e4             	test   %r12d,%r12d
    71e1:	75 14                	jne    71f7 <barriered_thread+0x137>
    71e3:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    71ea:	48 3b b3 90 00 00 00 	cmp    0x90(%rbx),%rsi
    71f1:	0f 8c 71 01 00 00    	jl     7368 <barriered_thread+0x2a8>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    71f7:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    71fb:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    71ff:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    7209:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    720d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7211:	4c 01 ef             	add    %r13,%rdi
    7214:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    721a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    721e:	4c 01 e8             	add    %r13,%rax
    7221:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7228:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    722b:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7233:	83 e8 01             	sub    $0x1,%eax
    7236:	44 39 e0             	cmp    %r12d,%eax
    7239:	0f 84 a1 00 00 00    	je     72e0 <barriered_thread+0x220>
          if (waiting == 0) {
    723f:	85 ed                	test   %ebp,%ebp
    7241:	0f 84 d9 00 00 00    	je     7320 <barriered_thread+0x260>
        int arrived = 0; 
    7247:	bd 01 00 00 00       	mov    $0x1,%ebp
    724c:	e9 c7 fe ff ff       	jmp    7118 <barriered_thread+0x58>
  while (data->running == 1) {
    7251:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7255:	0f 85 ff 00 00 00    	jne    735a <barriered_thread+0x29a>
    725b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    7260:	48 83 83 b0 00 00 00 01 	addq   $0x1,0xb0(%rbx)
    for (; t < data->task_count; t++) {
    7268:	85 c0                	test   %eax,%eax
    726a:	7e e5                	jle    7251 <barriered_thread+0x191>
    726c:	45 31 e4             	xor    %r12d,%r12d
    726f:	e9 7d fe ff ff       	jmp    70f1 <barriered_thread+0x31>
    7274:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    7278:	83 fd 01             	cmp    $0x1,%ebp
    727b:	74 1b                	je     7298 <barriered_thread+0x1d8>
        int arrived = 0; 
    727d:	31 ed                	xor    %ebp,%ebp
    727f:	e9 3d ff ff ff       	jmp    71c1 <barriered_thread+0x101>
    7284:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    7288:	83 fd 01             	cmp    $0x1,%ebp
    728b:	0f 85 43 ff ff ff    	jne    71d4 <barriered_thread+0x114>
        int arrived = 0; 
    7291:	45 31 f6             	xor    %r14d,%r14d
    7294:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    7298:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    729f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    72a4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    72a6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    72aa:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    72b1:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    72b6:	e8 95 b0 ff ff       	call   2350 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    72bb:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    72c2:	48 83 c0 01          	add    $0x1,%rax
    72c6:	48 99                	cqto
    72c8:	48 f7 bb a8 00 00 00 	idivq  0xa8(%rbx)
    72cf:	48 89 93 a0 00 00 00 	mov    %rdx,0xa0(%rbx)
            waiting = 0; 
    72d6:	e9 e6 fe ff ff       	jmp    71c1 <barriered_thread+0x101>
    72db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    72e0:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    72e7:	48 3b b3 90 00 00 00 	cmp    0x90(%rbx),%rsi
    72ee:	0f 8d 4b ff ff ff    	jge    723f <barriered_thread+0x17f>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    72f4:	48 c1 e6 04          	shl    $0x4,%rsi
    72f8:	bf 04 00 00 00       	mov    $0x4,%edi
    72fd:	48 03 73 78          	add    0x78(%rbx),%rsi
    7301:	e8 4a b0 ff ff       	call   2350 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    7306:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
          if (waiting == 0) {
    730e:	85 ed                	test   %ebp,%ebp
    7310:	0f 85 31 ff ff ff    	jne    7247 <barriered_thread+0x187>
    7316:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    7320:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    7327:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    732c:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    7330:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    7337:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    733b:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    733f:	e8 0c b0 ff ff       	call   2350 <clock_gettime@plt>
            waiting = 1;
    7344:	e9 fe fe ff ff       	jmp    7247 <barriered_thread+0x187>
    7349:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    7350:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7354:	0f 84 8e fd ff ff    	je     70e8 <barriered_thread+0x28>
}
    735a:	5b                   	pop    %rbx
    735b:	31 c0                	xor    %eax,%eax
    735d:	5d                   	pop    %rbp
    735e:	41 5c                	pop    %r12
    7360:	41 5d                	pop    %r13
    7362:	41 5e                	pop    %r14
    7364:	c3                   	ret
    7365:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    7368:	48 c1 e6 04          	shl    $0x4,%rsi
    736c:	bf 04 00 00 00       	mov    $0x4,%edi
    7371:	48 03 73 70          	add    0x70(%rbx),%rsi
    7375:	e8 d6 af ff ff       	call   2350 <clock_gettime@plt>
          data->tasks[t].available = 0;
    737a:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    737e:	4c 01 ea             	add    %r13,%rdx
    7381:	e9 71 fe ff ff       	jmp    71f7 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    7386:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    738a:	48 8b 43 18          	mov    0x18(%rbx),%rax
    738e:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7392:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7396:	4c 01 ef             	add    %r13,%rdi
    7399:	e8 12 fc ff ff       	call   6fb0 <barriered_work_ingest>
          break;
    739e:	e9 31 fd ff ff       	jmp    70d4 <barriered_thread+0x14>
    73a3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    73ae:	66 90                	xchg   %ax,%ax

00000000000073b0 <receive>:
int receive(struct BarrierTask *data) {
    73b0:	f3 0f 1e fa          	endbr64
    73b4:	41 56                	push   %r14
    73b6:	41 55                	push   %r13
    73b8:	41 54                	push   %r12
    73ba:	55                   	push   %rbp
    73bb:	53                   	push   %rbx
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    73bc:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    73c3:	45 85 e4             	test   %r12d,%r12d
    73c6:	0f 8e 27 01 00 00    	jle    74f3 <receive+0x143>
    if (n == data->thread->real_thread_index) { continue; }
    73cc:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    73d3:	48 89 fe             	mov    %rdi,%rsi
    73d6:	31 db                	xor    %ebx,%ebx
    73d8:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    73dc:	49 89 ed             	mov    %rbp,%r13
    73df:	90                   	nop
    73e0:	41 39 dd             	cmp    %ebx,%r13d
    73e3:	0f 84 fd 00 00 00    	je     74e6 <receive+0x136>
    struct Data *me = data->mailboxes[n].lower;
    73e9:	48 89 d8             	mov    %rbx,%rax
    73ec:	48 c1 e0 08          	shl    $0x8,%rax
    73f0:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    73f7:	48 8b 10             	mov    (%rax),%rdx
    if (me->available_reading == 1) {
    73fa:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    7400:	83 f8 01             	cmp    $0x1,%eax
    7403:	74 11                	je     7416 <receive+0x66>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    7405:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    740c:	75 08                	jne    7416 <receive+0x66>
    740e:	85 c0                	test   %eax,%eax
    7410:	0f 84 d0 00 00 00    	je     74e6 <receive+0x136>
    for (; me->messages_count > 0 ; ) {
    7416:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    741d:	48 85 ff             	test   %rdi,%rdi
    7420:	0f 8e a2 00 00 00    	jle    74c8 <receive+0x118>
    7426:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    742d:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    7434:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
    7438:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    743b:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    743f:	49 01 f9             	add    %rdi,%r9
    7442:	49 01 f8             	add    %rdi,%r8
    7445:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    744c:	eb 08                	jmp    7456 <receive+0xa6>
    744e:	66 90                	xchg   %ax,%ax
    for (; me->messages_count > 0 ; ) {
    7450:	48 83 e8 01          	sub    $0x1,%rax
    7454:	72 72                	jb     74c8 <receive+0x118>
      data->sends++;
    7456:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
    7459:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
    7460:	48 29 c1             	sub    %rax,%rcx
    7463:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      data->n++;
    746a:	4c 89 c1             	mov    %r8,%rcx
    746d:	48 29 c1             	sub    %rax,%rcx
    7470:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
    7477:	48 89 f9             	mov    %rdi,%rcx
    747a:	48 29 c1             	sub    %rax,%rcx
    747d:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
      if (me->messages[x]->group == data->group) {
    7484:	48 63 c8             	movslq %eax,%rcx
    7487:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    748b:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    748f:	75 bf                	jne    7450 <receive+0xa0>
    7491:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    7495:	75 b9                	jne    7450 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    7497:	49 63 46 04          	movslq 0x4(%r14),%rax
    749b:	31 c9                	xor    %ecx,%ecx
    749d:	bf 01 00 00 00       	mov    $0x1,%edi
    74a2:	ba 01 00 00 00       	mov    $0x1,%edx
    74a7:	48 8d 35 2a 23 00 00 	lea    0x232a(%rip),%rsi        # 97d8 <_IO_stdin_used+0x7d8>
    74ae:	48 39 e8             	cmp    %rbp,%rax
    74b1:	0f 94 c1             	sete   %cl
    74b4:	31 c0                	xor    %eax,%eax
    74b6:	e8 f5 af ff ff       	call   24b0 <__printf_chk@plt>
        exit(1);
    74bb:	bf 01 00 00 00       	mov    $0x1,%edi
    74c0:	e8 4b b0 ff ff       	call   2510 <exit@plt>
    74c5:	0f 1f 00             	nopl   (%rax)
      me->available_reading = 0;
    74c8:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    74d2:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
    74dc:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    74e6:	48 83 c3 01          	add    $0x1,%rbx
    74ea:	49 39 dc             	cmp    %rbx,%r12
    74ed:	0f 85 ed fe ff ff    	jne    73e0 <receive+0x30>
}
    74f3:	31 c0                	xor    %eax,%eax
    74f5:	5b                   	pop    %rbx
    74f6:	5d                   	pop    %rbp
    74f7:	41 5c                	pop    %r12
    74f9:	41 5d                	pop    %r13
    74fb:	41 5e                	pop    %r14
    74fd:	c3                   	ret
    74fe:	66 90                	xchg   %ax,%ax

0000000000007500 <sendm>:
int sendm(struct BarrierTask *data) {
    7500:	f3 0f 1e fa          	endbr64
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7504:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    750a:	85 c0                	test   %eax,%eax
    750c:	0f 8e 96 02 00 00    	jle    77a8 <sendm+0x2a8>
int sendm(struct BarrierTask *data) {
    7512:	41 57                	push   %r15
    7514:	41 56                	push   %r14
    7516:	41 55                	push   %r13
        if (n == data->thread->real_thread_index) { continue; }
    7518:	45 31 ed             	xor    %r13d,%r13d
int sendm(struct BarrierTask *data) {
    751b:	41 54                	push   %r12
    751d:	4c 63 e0             	movslq %eax,%r12
    7520:	55                   	push   %rbp
    7521:	48 89 fd             	mov    %rdi,%rbp
    7524:	53                   	push   %rbx
        if (n == data->thread->real_thread_index) { continue; }
    7525:	48 8b 9f 28 01 00 00 	mov    0x128(%rdi),%rbx
    752c:	44 8b 7b 08          	mov    0x8(%rbx),%r15d
    7530:	48 89 5c 24 c8       	mov    %rbx,-0x38(%rsp)
    7535:	0f 1f 00             	nopl   (%rax)
    7538:	45 39 ef             	cmp    %r13d,%r15d
    753b:	0f 84 97 00 00 00    	je     75d8 <sendm+0xd8>
        struct Data *them = data->mailboxes[n].higher;
    7541:	4c 89 e8             	mov    %r13,%rax
    7544:	48 c1 e0 08          	shl    $0x8,%rax
    7548:	48 03 85 70 01 00 00 	add    0x170(%rbp),%rax
        data->mailboxes[n].counter++;
    754f:	48 8b 98 b8 00 00 00 	mov    0xb8(%rax),%rbx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7556:	83 b8 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax)
        struct Data *them = data->mailboxes[n].higher;
    755d:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7564:	40 0f 94 c7          	sete   %dil
        data->mailboxes[n].counter++;
    7568:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    756c:	48 89 90 b8 00 00 00 	mov    %rdx,0xb8(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7573:	48 85 d2             	test   %rdx,%rdx
    7576:	7f 05                	jg     757d <sendm+0x7d>
    7578:	40 84 ff             	test   %dil,%dil
    757b:	75 5b                	jne    75d8 <sendm+0xd8>
        if (them->messages_count > 0) {
    757d:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    7584:	48 85 f6             	test   %rsi,%rsi
    7587:	7f 4f                	jg     75d8 <sendm+0xd8>
        if (them->available_sending == 1) {
    7589:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    7590:	41 83 f8 01          	cmp    $0x1,%r8d
    7594:	74 0e                	je     75a4 <sendm+0xa4>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    7596:	83 b9 08 04 00 00 02 	cmpl   $0x2,0x408(%rcx)
    759d:	75 05                	jne    75a4 <sendm+0xa4>
    759f:	45 85 c0             	test   %r8d,%r8d
    75a2:	74 34                	je     75d8 <sendm+0xd8>
        if (data->sending == 1) {
    75a4:	83 bd 88 01 00 00 01 	cmpl   $0x1,0x188(%rbp)
    75ab:	74 4b                	je     75f8 <sendm+0xf8>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter >= limit) {
    75ad:	48 85 d2             	test   %rdx,%rdx
    75b0:	7e 26                	jle    75d8 <sendm+0xd8>
    75b2:	40 84 ff             	test   %dil,%dil
    75b5:	74 21                	je     75d8 <sendm+0xd8>
          data->mailboxes[n].counter = 0;
    75b7:	48 c7 80 b8 00 00 00 00 00 00 00 	movq   $0x0,0xb8(%rax)
          data->thread->have_foreign = 1;
    75c2:	48 8b 44 24 c8       	mov    -0x38(%rsp),%rax
    75c7:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    75d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    75d8:	49 83 c5 01          	add    $0x1,%r13
    75dc:	4d 39 ec             	cmp    %r13,%r12
    75df:	0f 85 53 ff ff ff    	jne    7538 <sendm+0x38>
}
    75e5:	31 c0                	xor    %eax,%eax
    75e7:	5b                   	pop    %rbx
    75e8:	5d                   	pop    %rbp
    75e9:	41 5c                	pop    %r12
    75eb:	41 5d                	pop    %r13
    75ed:	41 5e                	pop    %r14
    75ef:	41 5f                	pop    %r15
    75f1:	c3                   	ret
    75f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (; them->messages_count < min;) {
    75f8:	4c 63 99 88 00 00 00 	movslq 0x88(%rcx),%r11
    75ff:	4c 39 de             	cmp    %r11,%rsi
    7602:	0f 8d c2 00 00 00    	jge    76ca <sendm+0x1ca>
    7608:	48 8b 9d 08 01 00 00 	mov    0x108(%rbp),%rbx
    760f:	4d 89 de             	mov    %r11,%r14
            them->messages[them->messages_count++] = data->message; 
    7612:	4c 8b 11             	mov    (%rcx),%r10
    7615:	49 29 f6             	sub    %rsi,%r14
    7618:	48 89 5c 24 d8       	mov    %rbx,-0x28(%rsp)
    761d:	48 8b 99 80 03 00 00 	mov    0x380(%rcx),%rbx
    7624:	4d 8d 46 ff          	lea    -0x1(%r14),%r8
    7628:	48 89 5c 24 e0       	mov    %rbx,-0x20(%rsp)
    762d:	49 83 f8 02          	cmp    $0x2,%r8
    7631:	0f 86 51 01 00 00    	jbe    7788 <sendm+0x288>
    7637:	48 8d 1c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rbx
    763f:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    7647:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    764c:	4c 01 d3             	add    %r10,%rbx
    764f:	4c 8d 85 90 01 00 00 	lea    0x190(%rbp),%r8
    7656:	48 89 5c 24 d0       	mov    %rbx,-0x30(%rsp)
    765b:	4b 8d 1c 0a          	lea    (%r10,%r9,1),%rbx
    765f:	49 39 d8             	cmp    %rbx,%r8
    7662:	0f 83 88 00 00 00    	jae    76f0 <sendm+0x1f0>
    7668:	48 8d 9d 98 01 00 00 	lea    0x198(%rbp),%rbx
    766f:	48 39 5c 24 d0       	cmp    %rbx,-0x30(%rsp)
    7674:	73 7a                	jae    76f0 <sendm+0x1f0>
    7676:	4c 8b 44 24 e8       	mov    -0x18(%rsp),%r8
    767b:	4b 8d 34 0a          	lea    (%r10,%r9,1),%rsi
    767f:	4d 01 d0             	add    %r10,%r8
    7682:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    7688:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
          for (; them->messages_count < min;) {
    768f:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    7693:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    7697:	4c 39 c6             	cmp    %r8,%rsi
    769a:	75 ec                	jne    7688 <sendm+0x188>
    769c:	0f 1f 40 00          	nopl   0x0(%rax)
    76a0:	48 8b 74 24 d8       	mov    -0x28(%rsp),%rsi
    76a5:	4c 01 f6             	add    %r14,%rsi
    76a8:	48 89 b5 08 01 00 00 	mov    %rsi,0x108(%rbp)
    76af:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    76b4:	4c 89 99 80 00 00 00 	mov    %r11,0x80(%rcx)
    76bb:	4c 01 f6             	add    %r14,%rsi
    76be:	48 89 b1 80 03 00 00 	mov    %rsi,0x380(%rcx)
    76c5:	4f 89 4c da f8       	mov    %r9,-0x8(%r10,%r11,8)
          them->available_sending = 0;
    76ca:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_reading = 1;
    76d4:	c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rcx)
          them->available_receiving = 1;
    76de:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    76e8:	e9 c0 fe ff ff       	jmp    75ad <sendm+0xad>
    76ed:	0f 1f 00             	nopl   (%rax)
    76f0:	4c 89 f3             	mov    %r14,%rbx
    76f3:	4c 8b 44 24 d0       	mov    -0x30(%rsp),%r8
    76f8:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    76ff:	48 d1 eb             	shr    %rbx
    7702:	48 c1 e3 04          	shl    $0x4,%rbx
    7706:	66 49 0f 6e c1       	movq   %r9,%xmm0
    770b:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    7710:	4c 01 c3             	add    %r8,%rbx
    7713:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    7717:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    771c:	48 8b 5c 24 e8       	mov    -0x18(%rsp),%rbx
    7721:	83 e3 10             	and    $0x10,%ebx
    7724:	75 4a                	jne    7770 <sendm+0x270>
    7726:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    772b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    7730:	41 0f 11 00          	movups %xmm0,(%r8)
    7734:	49 83 c0 20          	add    $0x20,%r8
    7738:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    773d:	49 39 d8             	cmp    %rbx,%r8
    7740:	75 ee                	jne    7730 <sendm+0x230>
    7742:	4d 89 f0             	mov    %r14,%r8
    7745:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    7749:	49 01 f0             	add    %rsi,%r8
    774c:	41 f6 c6 01          	test   $0x1,%r14b
    7750:	0f 84 4a ff ff ff    	je     76a0 <sendm+0x1a0>
            them->messages[them->messages_count++] = data->message; 
    7756:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    775d:	4f 89 0c c2          	mov    %r9,(%r10,%r8,8)
          for (; them->messages_count < min;) {
    7761:	e9 3a ff ff ff       	jmp    76a0 <sendm+0x1a0>
    7766:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    7770:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    7775:	41 0f 11 00          	movups %xmm0,(%r8)
          for (; them->messages_count < min;) {
    7779:	49 83 c0 10          	add    $0x10,%r8
    777d:	49 39 d8             	cmp    %rbx,%r8
    7780:	75 ae                	jne    7730 <sendm+0x230>
    7782:	eb be                	jmp    7742 <sendm+0x242>
    7784:	0f 1f 40 00          	nopl   0x0(%rax)
    7788:	48 8d 34 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rsi
    7790:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    7798:	48 89 74 24 e8       	mov    %rsi,-0x18(%rsp)
    779d:	e9 d4 fe ff ff       	jmp    7676 <sendm+0x176>
    77a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
}
    77a8:	31 c0                	xor    %eax,%eax
    77aa:	c3                   	ret
    77ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000077b0 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    77b0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    77b4:	85 f6                	test   %esi,%esi
    77b6:	74 18                	je     77d0 <mailboxkind+0x20>
  return NULL;
    77b8:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    77ba:	83 fe 01             	cmp    $0x1,%esi
    77bd:	74 01                	je     77c0 <mailboxkind+0x10>
}
    77bf:	c3                   	ret
    return mailbox->higher;
    77c0:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
}
    77c7:	c3                   	ret
    77c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    return mailbox->lower;
    77d0:	48 8b 07             	mov    (%rdi),%rax
    77d3:	c3                   	ret
    77d4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    77df:	90                   	nop

00000000000077e0 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    77e0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    77e4:	85 d2                	test   %edx,%edx
    77e6:	75 08                	jne    77f0 <setmailboxkind+0x10>
    mailbox->lower = data;
    77e8:	48 89 37             	mov    %rsi,(%rdi)
}
    77eb:	31 c0                	xor    %eax,%eax
    77ed:	c3                   	ret
    77ee:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    77f0:	83 fa 01             	cmp    $0x1,%edx
    77f3:	74 13                	je     7808 <setmailboxkind+0x28>
  if (kind == 2) {
    77f5:	83 fa 02             	cmp    $0x2,%edx
    77f8:	75 1e                	jne    7818 <setmailboxkind+0x38>
    mailbox->pending_lower = data;
    77fa:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
}
    7801:	31 c0                	xor    %eax,%eax
    7803:	c3                   	ret
    7804:	0f 1f 40 00          	nopl   0x0(%rax)
    mailbox->higher = data;
    7808:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
}
    780f:	31 c0                	xor    %eax,%eax
    7811:	c3                   	ret
    7812:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (kind == 3) {
    7818:	83 fa 03             	cmp    $0x3,%edx
    781b:	75 ce                	jne    77eb <setmailboxkind+0xb>
    mailbox->pending_higher = data;
    781d:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
}
    7824:	31 c0                	xor    %eax,%eax
    7826:	c3                   	ret
    7827:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007830 <fswap>:
int fswap(struct BarrierTask *data) {
    7830:	f3 0f 1e fa          	endbr64
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    7834:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    783b:	8b 97 9c 01 00 00    	mov    0x19c(%rdi),%edx
    7841:	44 8b 97 30 01 00 00 	mov    0x130(%rdi),%r10d
  int t = data->task_index;
    7848:	48 63 4f 04          	movslq 0x4(%rdi),%rcx
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    784c:	8b 86 cc 00 00 00    	mov    0xcc(%rsi),%eax
    7852:	0f af d0             	imul   %eax,%edx
    7855:	41 01 d2             	add    %edx,%r10d
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    7858:	85 c0                	test   %eax,%eax
    785a:	0f 8e 1b 01 00 00    	jle    797b <fswap+0x14b>
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7860:	4d 63 d2             	movslq %r10d,%r10
int fswap(struct BarrierTask *data) {
    7863:	41 56                	push   %r14
    7865:	48 63 d2             	movslq %edx,%rdx
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7868:	48 c1 e1 09          	shl    $0x9,%rcx
int fswap(struct BarrierTask *data) {
    786c:	41 55                	push   %r13
    786e:	4c 63 d8             	movslq %eax,%r11
    7871:	41 54                	push   %r12
    7873:	49 01 d3             	add    %rdx,%r11
    7876:	55                   	push   %rbp
    7877:	49 c1 e3 08          	shl    $0x8,%r11
    787b:	53                   	push   %rbx
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    787c:	48 8b 76 20          	mov    0x20(%rsi),%rsi
        int next_task = abs((t + 1) % (data->thread_count));
    7880:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7887:	4b 8d 3c d2          	lea    (%r10,%r10,8),%rdi
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    788b:	49 c1 e2 08          	shl    $0x8,%r10
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    788f:	48 c1 e7 05          	shl    $0x5,%rdi
    7893:	48 8b 5c 3e 38       	mov    0x38(%rsi,%rdi,1),%rbx
    7898:	48 8b ac 0b 70 01 00 00 	mov    0x170(%rbx,%rcx,1),%rbp
    78a0:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    78a4:	48 c1 e1 05          	shl    $0x5,%rcx
    78a8:	4c 8d 4c 0e 38       	lea    0x38(%rsi,%rcx,1),%r9
    78ad:	48 89 d6             	mov    %rdx,%rsi
    78b0:	48 c1 e6 08          	shl    $0x8,%rsi
    78b4:	eb 21                	jmp    78d7 <fswap+0xa7>
    78b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    78c0:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    78c7:	49 81 c1 20 01 00 00 	add    $0x120,%r9
    78ce:	49 39 f3             	cmp    %rsi,%r11
    78d1:	0f 84 99 00 00 00    	je     7970 <fswap+0x140>
        if (kind == MAILBOX_FRIEND) {
    78d7:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    78df:	75 df                	jne    78c0 <fswap+0x90>
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    78e1:	49 8b 39             	mov    (%r9),%rdi
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    78e4:	45 85 c0             	test   %r8d,%r8d
    78e7:	7e d7                	jle    78c0 <fswap+0x90>
    78e9:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    78f0:	31 c9                	xor    %ecx,%ecx
    78f2:	eb 59                	jmp    794d <fswap+0x11d>
    78f4:	0f 1f 40 00          	nopl   0x0(%rax)
              struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    78f8:	48 63 d2             	movslq %edx,%rdx
    78fb:	48 c1 e2 09          	shl    $0x9,%rdx
    78ff:	4c 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%r13
    7907:	49 01 f5             	add    %rsi,%r13
    790a:	4c 89 ea             	mov    %r13,%rdx
    return mailbox->lower;
    790d:	4d 8b 6d 00          	mov    0x0(%r13),%r13
                if (dest->messages_count != 0) { 
    7911:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    7919:	75 22                	jne    793d <fswap+0x10d>
    mailbox->lower = data;
    791b:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    7922:	4c 89 32             	mov    %r14,(%rdx)
    7925:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    mailbox->higher = data;
    792c:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    mailbox->lower = data;
    7933:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    7936:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    793d:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    7944:	41 39 c8             	cmp    %ecx,%r8d
    7947:	0f 84 73 ff ff ff    	je     78c0 <fswap+0x90>
              int next_task = abs((nn + 1) % (data->thread_count));
    794d:	83 c1 01             	add    $0x1,%ecx
    7950:	89 c8                	mov    %ecx,%eax
    7952:	99                   	cltd
    7953:	41 f7 f8             	idiv   %r8d
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7956:	48 8b 07             	mov    (%rdi),%rax
    7959:	4c 01 d0             	add    %r10,%rax
    return mailbox->lower;
    795c:	4c 8b 20             	mov    (%rax),%r12
                if (source2->messages_count != 0) { 
    795f:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    7968:	74 8e                	je     78f8 <fswap+0xc8>
    796a:	e9 51 ff ff ff       	jmp    78c0 <fswap+0x90>
    796f:	90                   	nop
}
    7970:	5b                   	pop    %rbx
    7971:	31 c0                	xor    %eax,%eax
    7973:	5d                   	pop    %rbp
    7974:	41 5c                	pop    %r12
    7976:	41 5d                	pop    %r13
    7978:	41 5e                	pop    %r14
    797a:	c3                   	ret
    797b:	31 c0                	xor    %eax,%eax
    797d:	c3                   	ret
    797e:	66 90                	xchg   %ax,%ax

0000000000007980 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    7980:	f3 0f 1e fa          	endbr64
    7984:	41 57                	push   %r15
    7986:	41 56                	push   %r14
    7988:	41 55                	push   %r13
    798a:	41 54                	push   %r12
    798c:	55                   	push   %rbp
    798d:	53                   	push   %rbx
    798e:	48 89 fb             	mov    %rdi,%rbx
    7991:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
  struct timespec preempt = {
    7998:	66 0f 6f 05 00 24 00 00 	movdqa 0x2400(%rip),%xmm0        # 9da0 <_IO_stdin_used+0xda0>
int barriered_work(struct BarrierTask *data) {
    79a0:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    79a9:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    79ae:	31 c0                	xor    %eax,%eax
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    79b0:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  struct timespec preempt = {
    79b7:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    79bc:	48 8b 88 f8 00 00 00 	mov    0xf8(%rax),%rcx
  struct timespec rem = {
    79c3:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    79c8:	8b 11                	mov    (%rcx),%edx
    79ca:	83 fa ff             	cmp    $0xffffffff,%edx
    79cd:	0f 84 cd 02 00 00    	je     7ca0 <barriered_work+0x320>
    79d3:	3b 90 f0 00 00 00    	cmp    0xf0(%rax),%edx
    79d9:	74 2d                	je     7a08 <barriered_work+0x88>
}
    79db:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    79e0:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    79e9:	0f 85 20 05 00 00    	jne    7f0f <barriered_work+0x58f>
    79ef:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    79f6:	31 c0                	xor    %eax,%eax
    79f8:	5b                   	pop    %rbx
    79f9:	5d                   	pop    %rbp
    79fa:	41 5c                	pop    %r12
    79fc:	41 5d                	pop    %r13
    79fe:	41 5e                	pop    %r14
    7a00:	41 5f                	pop    %r15
    7a02:	c3                   	ret
    7a03:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    7a08:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    7a0f:	8b 41 04             	mov    0x4(%rcx),%eax
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    7a12:	85 ed                	test   %ebp,%ebp
    7a14:	0f 85 76 04 00 00    	jne    7e90 <barriered_work+0x510>
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    7a1a:	85 c0                	test   %eax,%eax
    7a1c:	0f 84 76 04 00 00    	je     7e98 <barriered_work+0x518>
    7a22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          int t = data->task_index;
    7a28:	44 8b 63 04          	mov    0x4(%rbx),%r12d
      receive(data);
    7a2c:	48 89 df             	mov    %rbx,%rdi
    if (data->thread_index == data->task_index) {
    7a2f:	41 39 ec             	cmp    %ebp,%r12d
    7a32:	0f 85 b0 03 00 00    	jne    7de8 <barriered_work+0x468>
      receive(data);
    7a38:	e8 73 f9 ff ff       	call   73b0 <receive>
        if (data->thread->have_foreign == 1) {
    7a3d:	4c 8b b3 28 01 00 00 	mov    0x128(%rbx),%r14
    7a44:	41 83 be 00 01 00 00 01 	cmpl   $0x1,0x100(%r14)
    7a4c:	0f 85 a1 02 00 00    	jne    7cf3 <barriered_work+0x373>
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7a52:	48 63 93 40 01 00 00 	movslq 0x140(%rbx),%rdx
    7a59:	85 d2                	test   %edx,%edx
    7a5b:	0f 8e 92 02 00 00    	jle    7cf3 <barriered_work+0x373>
                int next_task = abs((t + 1) % (data->thread_count));
    7a61:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7a67:	48 c1 e5 09          	shl    $0x9,%rbp
    7a6b:	31 f6                	xor    %esi,%esi
    7a6d:	49 89 d2             	mov    %rdx,%r10
    7a70:	49 89 ed             	mov    %rbp,%r13
    7a73:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
                int next_task = abs((t + 1) % (data->thread_count));
    7a7b:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
          int b = data->thread->real_thread_index;
    7a7f:	49 63 46 08          	movslq 0x8(%r14),%rax
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7a83:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
          int b = data->thread->real_thread_index;
    7a87:	49 89 c7             	mov    %rax,%r15
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7a8a:	48 c1 e0 08          	shl    $0x8,%rax
    7a8e:	48 c1 e1 05          	shl    $0x5,%rcx
    7a92:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    7a97:	48 89 cd             	mov    %rcx,%rbp
    7a9a:	44 89 e1             	mov    %r12d,%ecx
    7a9d:	eb 1a                	jmp    7ab9 <barriered_work+0x139>
    7a9f:	90                   	nop
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7aa0:	48 83 04 24 01       	addq   $0x1,(%rsp)
    7aa5:	48 8b 04 24          	mov    (%rsp),%rax
    7aa9:	48 81 c6 20 01 00 00 	add    $0x120,%rsi
    7ab0:	49 39 c2             	cmp    %rax,%r10
    7ab3:	0f 84 37 02 00 00    	je     7cf0 <barriered_work+0x370>
                if (y == b) { continue; }
    7ab9:	8b 04 24             	mov    (%rsp),%eax
    7abc:	41 39 c7             	cmp    %eax,%r15d
    7abf:	74 df                	je     7aa0 <barriered_work+0x120>
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7ac1:	49 8b 56 20          	mov    0x20(%r14),%rdx
    7ac5:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    7aca:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    7ace:	44 8b 80 a0 01 00 00 	mov    0x1a0(%rax),%r8d
    7ad5:	45 85 c0             	test   %r8d,%r8d
    7ad8:	75 c6                	jne    7aa0 <barriered_work+0x120>
    7ada:	4c 8b 44 2a 38       	mov    0x38(%rdx,%rbp,1),%r8
    7adf:	4b 8d 14 28          	lea    (%r8,%r13,1),%rdx
    7ae3:	44 8b 8a a0 01 00 00 	mov    0x1a0(%rdx),%r9d
    7aea:	45 85 c9             	test   %r9d,%r9d
    7aed:	75 b1                	jne    7aa0 <barriered_work+0x120>
    7aef:	4c 8b 24 24          	mov    (%rsp),%r12
    7af3:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    7afa:	49 c1 e4 08          	shl    $0x8,%r12
    7afe:	42 83 bc 22 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r12,1)
    7b07:	75 97                	jne    7aa0 <barriered_work+0x120>
    7b09:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    7b10:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    7b15:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    7b1d:	75 81                	jne    7aa0 <barriered_work+0x120>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    7b1f:	48 63 44 24 1c       	movslq 0x1c(%rsp),%rax
    7b24:	85 c0                	test   %eax,%eax
    7b26:	0f 8e 74 ff ff ff    	jle    7aa0 <barriered_work+0x120>
    7b2c:	48 89 c2             	mov    %rax,%rdx
    7b2f:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    7b34:	b8 70 01 00 00       	mov    $0x170,%eax
    7b39:	48 c1 e2 09          	shl    $0x9,%rdx
    7b3d:	89 4c 24 30          	mov    %ecx,0x30(%rsp)
    7b41:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    7b46:	4c 8d 9a a0 01 00 00 	lea    0x1a0(%rdx),%r11
    7b4d:	48 89 54 24 38       	mov    %rdx,0x38(%rsp)
    7b52:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    7b57:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    7b5c:	4c 89 54 24 40       	mov    %r10,0x40(%rsp)
    7b61:	44 8b 54 24 1c       	mov    0x1c(%rsp),%r10d
    7b66:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    7b6b:	48 89 c6             	mov    %rax,%rsi
    7b6e:	66 90                	xchg   %ax,%ax
                        int next_task = abs((nn + 1) % data->thread_count);
    7b70:	41 83 c1 01          	add    $0x1,%r9d
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7b74:	49 8b 0c 30          	mov    (%r8,%rsi,1),%rcx
                        int next_task = abs((nn + 1) % data->thread_count);
    7b78:	44 89 c8             	mov    %r9d,%eax
    7b7b:	99                   	cltd
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7b7c:	4c 01 e1             	add    %r12,%rcx
                        int next_task = abs((nn + 1) % data->thread_count);
    7b7f:	41 f7 fa             	idiv   %r10d
    return mailbox->lower;
    7b82:	4c 8b 31             	mov    (%rcx),%r14
    7b85:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    mailbox->lower = data;
    7b8a:	4c 8b b1 80 00 00 00 	mov    0x80(%rcx),%r14
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    7b91:	48 63 d2             	movslq %edx,%rdx
    7b94:	48 c1 e2 09          	shl    $0x9,%rdx
    7b98:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    7ba0:	4c 01 e8             	add    %r13,%rax
    return mailbox->lower;
    7ba3:	4c 8b 38             	mov    (%rax),%r15
    return mailbox->higher;
    7ba6:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    mailbox->lower = data;
    7bad:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    7bb0:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    7bb5:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    mailbox->lower = data;
    7bbc:	48 89 11             	mov    %rdx,(%rcx)
    mailbox->higher = data;
    7bbf:	4c 89 b9 80 00 00 00 	mov    %r15,0x80(%rcx)
    7bc6:	b9 a0 01 00 00       	mov    $0x1a0,%ecx
    7bcb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
    7bd0:	41 c7 04 08 01 00 00 00 	movl   $0x1,(%r8,%rcx,1)
                          data->thread->all_threads[t2].tasks[jj].swap = 1;
    7bd8:	c7 04 0f 01 00 00 00 	movl   $0x1,(%rdi,%rcx,1)
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
    7bdf:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    7be6:	4c 39 d9             	cmp    %r11,%rcx
    7be9:	75 e5                	jne    7bd0 <barriered_work+0x250>
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    7beb:	48 8b 0c 37          	mov    (%rdi,%rsi,1),%rcx
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    7bef:	48 8b 00             	mov    (%rax),%rax
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    7bf2:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    7bfd:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    7c04:	4a 8b 8c 29 80 00 00 00 	mov    0x80(%rcx,%r13,1),%rcx
    7c0c:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
                            ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    7c16:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    7c20:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    7c2a:	45 39 ca             	cmp    %r9d,%r10d
    7c2d:	0f 85 3d ff ff ff    	jne    7b70 <barriered_work+0x1f0>
    7c33:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
    7c38:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    7c3d:	b8 70 01 00 00       	mov    $0x170,%eax
    7c42:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    7c47:	8b 4c 24 30          	mov    0x30(%rsp),%ecx
    7c4b:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    7c50:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    7c55:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    7c5a:	4c 8d 9a 70 01 00 00 	lea    0x170(%rdx),%r11
    7c61:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    7c66:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    7c6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                          if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    7c70:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    7c74:	4d 8b 0c 00          	mov    (%r8,%rax,1),%r9
    7c78:	4a 8b 14 32          	mov    (%rdx,%r14,1),%rdx
    7c7c:	4b 39 14 21          	cmp    %rdx,(%r9,%r12,1)
    7c80:	0f 84 8e 02 00 00    	je     7f14 <barriered_work+0x594>
                        for (int nn = 0; nn < data->thread_count; nn++) {
    7c86:	48 05 00 02 00 00    	add    $0x200,%rax
    7c8c:	4c 39 d8             	cmp    %r11,%rax
    7c8f:	75 df                	jne    7c70 <barriered_work+0x2f0>
    7c91:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    7c96:	e9 05 fe ff ff       	jmp    7aa0 <barriered_work+0x120>
    7c9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    7ca0:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    7ca7:	85 ed                	test   %ebp,%ebp
    7ca9:	0f 85 79 fd ff ff    	jne    7a28 <barriered_work+0xa8>
    7caf:	44 8b 88 f0 00 00 00 	mov    0xf0(%rax),%r9d
    7cb6:	45 85 c9             	test   %r9d,%r9d
    7cb9:	0f 85 69 fd ff ff    	jne    7a28 <barriered_work+0xa8>
    7cbf:	69 87 80 00 00 00 1d e6 cb 0b 	imul   $0xbcbe61d,0x80(%rdi),%eax
    7cc9:	05 40 7c 0a 00       	add    $0xa7c40,%eax
    7cce:	c1 c8 05             	ror    $0x5,%eax
    7cd1:	3d c4 a7 00 00       	cmp    $0xa7c4,%eax
    7cd6:	0f 87 4c fd ff ff    	ja     7a28 <barriered_work+0xa8>
      data->thread->global->request_group_sync = 0;
    7cdc:	48 c7 01 00 00 00 00 	movq   $0x0,(%rcx)
    7ce3:	e9 40 fd ff ff       	jmp    7a28 <barriered_work+0xa8>
    7ce8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    7cf0:	41 89 cc             	mov    %ecx,%r12d
        fswap(data); 
    7cf3:	48 89 df             	mov    %rbx,%rdi
    7cf6:	e8 35 fb ff ff       	call   7830 <fswap>
        receive(data);
    7cfb:	48 89 df             	mov    %rbx,%rdi
    7cfe:	e8 ad f6 ff ff       	call   73b0 <receive>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    7d03:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    7d0a:	31 ff                	xor    %edi,%edi
    7d0c:	48 c1 e6 05          	shl    $0x5,%rsi
    7d10:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    7d17:	e8 34 a6 ff ff       	call   2350 <clock_gettime@plt>
      int modcount = ++data->thread->protected_state->modcount;
    7d1c:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    7d23:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      int modcount = ++data->thread->protected_state->modcount;
    7d2a:	48 8b 50 48          	mov    0x48(%rax),%rdx
    7d2e:	8b 72 10             	mov    0x10(%rdx),%esi
    7d31:	8d 6e 01             	lea    0x1(%rsi),%ebp
    7d34:	89 6a 10             	mov    %ebp,0x10(%rdx)
      while (data->scheduled == 1) {
    7d37:	75 55                	jne    7d8e <barriered_work+0x40e>
    7d39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    7d40:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    7d47:	48 8b 40 18          	mov    0x18(%rax),%rax
    7d4b:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
        data->n++;
    7d4f:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    7d57:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7d5b:	48 c1 e7 09          	shl    $0x9,%rdi
    7d5f:	48 03 78 38          	add    0x38(%rax),%rdi
    7d63:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      while (data->scheduled == 1) {
    7d69:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      if (modcount != data->thread->protected_state->modcount) {
    7d70:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    7d77:	74 c7                	je     7d40 <barriered_work+0x3c0>
      if (modcount != data->thread->protected_state->modcount) {
    7d79:	48 8b 40 48          	mov    0x48(%rax),%rax
    7d7d:	3b 68 10             	cmp    0x10(%rax),%ebp
    7d80:	74 0c                	je     7d8e <barriered_work+0x40e>
    7d82:	48 8d 3d f8 14 00 00 	lea    0x14f8(%rip),%rdi        # 9281 <_IO_stdin_used+0x281>
    7d89:	e8 a2 a5 ff ff       	call   2330 <puts@plt>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    7d8e:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    7d95:	31 ff                	xor    %edi,%edi
    7d97:	48 c1 e6 05          	shl    $0x5,%rsi
    7d9b:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    7da2:	48 83 c6 10          	add    $0x10,%rsi
    7da6:	e8 a5 a5 ff ff       	call   2350 <clock_gettime@plt>
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    7dab:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    7db2:	48 83 c0 01          	add    $0x1,%rax
    7db6:	48 99                	cqto
    7db8:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    if (t == data->thread_count - 1) {
    7dbf:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    7dc5:	83 e8 01             	sub    $0x1,%eax
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    7dc8:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    if (t == data->thread_count - 1) {
    7dcf:	44 39 e0             	cmp    %r12d,%eax
    7dd2:	74 53                	je     7e27 <barriered_work+0x4a7>
    data->swap = 0;
    7dd4:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    return 0;
    7dde:	e9 f8 fb ff ff       	jmp    79db <barriered_work+0x5b>
    7de3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      receive(data);
    7de8:	e8 c3 f5 ff ff       	call   73b0 <receive>
      while (data->scheduled == 1) {
    7ded:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    7df4:	75 1b                	jne    7e11 <barriered_work+0x491>
    7df6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        data->n++;
    7e00:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      while (data->scheduled == 1) {
    7e08:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    7e0f:	74 ef                	je     7e00 <barriered_work+0x480>
      sendm(data);
    7e11:	48 89 df             	mov    %rbx,%rdi
    7e14:	e8 e7 f6 ff ff       	call   7500 <sendm>
    if (t == data->thread_count - 1) {
    7e19:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    7e1f:	83 e8 01             	sub    $0x1,%eax
    7e22:	44 39 e0             	cmp    %r12d,%eax
    7e25:	75 ad                	jne    7dd4 <barriered_work+0x454>
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    7e27:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    7e2e:	85 d2                	test   %edx,%edx
    7e30:	7e a2                	jle    7dd4 <barriered_work+0x454>
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    7e32:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    7e39:	48 c1 e2 09          	shl    $0x9,%rdx
    7e3d:	48 63 41 08          	movslq 0x8(%rcx),%rax
    7e41:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    7e45:	48 c1 e0 05          	shl    $0x5,%rax
    7e49:	48 03 41 20          	add    0x20(%rcx),%rax
    7e4d:	48 8b 40 38          	mov    0x38(%rax),%rax
    7e51:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    7e55:	80 e6 02             	and    $0x2,%dh
    7e58:	74 16                	je     7e70 <barriered_work+0x4f0>
    7e5a:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    7e61:	48 05 00 02 00 00    	add    $0x200,%rax
    7e67:	48 39 c8             	cmp    %rcx,%rax
    7e6a:	0f 84 64 ff ff ff    	je     7dd4 <barriered_work+0x454>
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    7e70:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    7e77:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    7e7e:	48 05 00 04 00 00    	add    $0x400,%rax
    7e84:	48 39 c8             	cmp    %rcx,%rax
    7e87:	75 e7                	jne    7e70 <barriered_work+0x4f0>
    7e89:	e9 46 ff ff ff       	jmp    7dd4 <barriered_work+0x454>
    7e8e:	66 90                	xchg   %ax,%ax
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    7e90:	39 c5                	cmp    %eax,%ebp
    7e92:	0f 85 90 fb ff ff    	jne    7a28 <barriered_work+0xa8>
      struct ProtectedState *protected = data->thread->global->protected_state;
    7e98:	48 8b 69 08          	mov    0x8(%rcx),%rbp
      nanosleep(&preempt , &rem);
    7e9c:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
    7ea1:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
      int modcount = ++protected->modcount;
    7ea6:	8b 45 10             	mov    0x10(%rbp),%eax
      protected->protected++;
    7ea9:	48 83 45 00 01       	addq   $0x1,0x0(%rbp)
      int modcount = ++protected->modcount;
    7eae:	44 8d 60 01          	lea    0x1(%rax),%r12d
    7eb2:	44 89 65 10          	mov    %r12d,0x10(%rbp)
      nanosleep(&preempt , &rem);
    7eb6:	e8 e5 a4 ff ff       	call   23a0 <nanosleep@plt>
      if (protected->modcount != modcount) {
    7ebb:	44 3b 65 10          	cmp    0x10(%rbp),%r12d
    7ebf:	74 0c                	je     7ecd <barriered_work+0x54d>
    7ec1:	48 8d 3d 81 13 00 00 	lea    0x1381(%rip),%rdi        # 9249 <_IO_stdin_used+0x249>
    7ec8:	e8 63 a4 ff ff       	call   2330 <puts@plt>
      data->thread->global->request_thread_sync = (data->thread_index + 1) % data->thread_count;
    7ecd:	48 63 ab 30 01 00 00 	movslq 0x130(%rbx),%rbp
    7ed4:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    7edb:	8d 45 01             	lea    0x1(%rbp),%eax
    7ede:	48 8b b1 f8 00 00 00 	mov    0xf8(%rcx),%rsi
    7ee5:	99                   	cltd
    7ee6:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    7eec:	89 56 04             	mov    %edx,0x4(%rsi)
      if (data->thread_index == 1) {
    7eef:	83 fd 01             	cmp    $0x1,%ebp
    7ef2:	0f 85 30 fb ff ff    	jne    7a28 <barriered_work+0xa8>
        data->thread->global->request_group_sync = (data->thread->group + 1) % data->thread->group_count;
    7ef8:	8b 81 f0 00 00 00    	mov    0xf0(%rcx),%eax
    7efe:	83 c0 01             	add    $0x1,%eax
    7f01:	99                   	cltd
    7f02:	f7 b9 c8 00 00 00    	idivl  0xc8(%rcx)
    7f08:	89 16                	mov    %edx,(%rsi)
    7f0a:	e9 19 fb ff ff       	jmp    7a28 <barriered_work+0xa8>
}
    7f0f:	e8 6c a4 ff ff       	call   2380 <__stack_chk_fail@plt>
    7f14:	bf 01 00 00 00       	mov    $0x1,%edi
    7f19:	48 8d 35 46 13 00 00 	lea    0x1346(%rip),%rsi        # 9266 <_IO_stdin_used+0x266>
    7f20:	31 c0                	xor    %eax,%eax
    7f22:	e8 89 a5 ff ff       	call   24b0 <__printf_chk@plt>
                            exit(1);
    7f27:	bf 01 00 00 00       	mov    $0x1,%edi
    7f2c:	e8 df a5 ff ff       	call   2510 <exit@plt>
    7f31:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    7f3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000007f40 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    7f40:	f3 0f 1e fa          	endbr64
    7f44:	53                   	push   %rbx
    7f45:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    7f48:	e8 63 f0 ff ff       	call   6fb0 <barriered_work_ingest>
  barriered_work(data);
    7f4d:	48 89 df             	mov    %rbx,%rdi
}
    7f50:	5b                   	pop    %rbx
  barriered_work(data);
    7f51:	e9 2a fa ff ff       	jmp    7980 <barriered_work>
    7f56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000007f60 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    7f60:	f3 0f 1e fa          	endbr64
}
    7f64:	31 c0                	xor    %eax,%eax
    7f66:	c3                   	ret
    7f67:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007f70 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    7f70:	f3 0f 1e fa          	endbr64
    7f74:	31 c0                	xor    %eax,%eax
    7f76:	c3                   	ret
    7f77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007f80 <after>:
int after(struct timespec left, struct timespec right) {
    7f80:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    7f84:	31 c0                	xor    %eax,%eax
    7f86:	48 39 d7             	cmp    %rdx,%rdi
    7f89:	7e 08                	jle    7f93 <after+0x13>
    7f8b:	31 c0                	xor    %eax,%eax
    7f8d:	48 39 ce             	cmp    %rcx,%rsi
    7f90:	0f 9f c0             	setg   %al
}
    7f93:	c3                   	ret
    7f94:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    7f9f:	90                   	nop

0000000000007fa0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    7fa0:	f3 0f 1e fa          	endbr64
    7fa4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    7fa9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    7fae:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7fb0:	48 39 d7             	cmp    %rdx,%rdi
    7fb3:	7f 18                	jg     7fcd <within+0x2d>
    7fb5:	4d 39 d8             	cmp    %r11,%r8
    7fb8:	0f 9e c2             	setle  %dl
    7fbb:	48 39 ce             	cmp    %rcx,%rsi
    7fbe:	0f 9e c0             	setle  %al
    7fc1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7fc3:	31 c0                	xor    %eax,%eax
    7fc5:	4d 39 d1             	cmp    %r10,%r9
    7fc8:	0f 9e c0             	setle  %al
    7fcb:	21 d0                	and    %edx,%eax
}
    7fcd:	c3                   	ret
    7fce:	66 90                	xchg   %ax,%ax

0000000000007fd0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    7fd0:	f3 0f 1e fa          	endbr64
    7fd4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    7fd9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    7fde:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    7fe3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    7fe8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    7fed:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    7ff2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    7ff7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    7ffc:	48 39 fe             	cmp    %rdi,%rsi
    7fff:	7d 2f                	jge    8030 <overlap+0x60>
    8001:	48 39 ca             	cmp    %rcx,%rdx
    8004:	7d 62                	jge    8068 <overlap+0x98>
    8006:	4d 39 da             	cmp    %r11,%r10
    8009:	7d 0e                	jge    8019 <overlap+0x49>
    return 1;
    800b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    8010:	4d 39 c1             	cmp    %r8,%r9
    8013:	0f 8c 7f 00 00 00    	jl     8098 <overlap+0xc8>
  return 0;
    8019:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    801b:	4d 39 c1             	cmp    %r8,%r9
    801e:	7f 4c                	jg     806c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8020:	31 c0                	xor    %eax,%eax
    8022:	4d 39 da             	cmp    %r11,%r10
    8025:	0f 9e c0             	setle  %al
    8028:	c3                   	ret
    8029:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    8030:	7e 4e                	jle    8080 <overlap+0xb0>
    8032:	48 39 ca             	cmp    %rcx,%rdx
    8035:	7f 39                	jg     8070 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8037:	75 31                	jne    806a <overlap+0x9a>
    8039:	4d 39 c1             	cmp    %r8,%r9
    803c:	7c 2c                	jl     806a <overlap+0x9a>
    return 1;
    803e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8043:	4d 39 da             	cmp    %r11,%r10
    8046:	7d 24                	jge    806c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8048:	48 39 ca             	cmp    %rcx,%rdx
    804b:	0f 94 c2             	sete   %dl
    804e:	48 39 fe             	cmp    %rdi,%rsi
    8051:	0f 94 c0             	sete   %al
    8054:	21 c2                	and    %eax,%edx
    8056:	31 c0                	xor    %eax,%eax
    8058:	4d 39 c1             	cmp    %r8,%r9
    805b:	0f 94 c0             	sete   %al
    805e:	21 d0                	and    %edx,%eax
    8060:	c3                   	ret
    8061:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    8068:	74 af                	je     8019 <overlap+0x49>
  return 0;
    806a:	31 c0                	xor    %eax,%eax
}
    806c:	c3                   	ret
    806d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    8070:	4d 39 da             	cmp    %r11,%r10
    8073:	7e c4                	jle    8039 <overlap+0x69>
    return 1;
    8075:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    807a:	4d 39 c1             	cmp    %r8,%r9
    807d:	7e ba                	jle    8039 <overlap+0x69>
    807f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8080:	48 39 ca             	cmp    %rcx,%rdx
    8083:	7c 94                	jl     8019 <overlap+0x49>
    8085:	4d 39 c1             	cmp    %r8,%r9
    8088:	7d b4                	jge    803e <overlap+0x6e>
    808a:	48 39 ca             	cmp    %rcx,%rdx
    808d:	74 91                	je     8020 <overlap+0x50>
    808f:	eb d9                	jmp    806a <overlap+0x9a>
    8091:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    8098:	c3                   	ret
    8099:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000080a0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    80a0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    80a4:	85 f6                	test   %esi,%esi
    80a6:	0f 8e 44 03 00 00    	jle    83f0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    80ac:	41 57                	push   %r15
    80ae:	41 89 f7             	mov    %esi,%r15d
    80b1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    80b3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    80b6:	41 55                	push   %r13
    80b8:	41 54                	push   %r12
    80ba:	55                   	push   %rbp
    80bb:	53                   	push   %rbx
    80bc:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    80c0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    80c4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    80c9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    80ce:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    80d1:	45 39 e6             	cmp    %r12d,%r14d
    80d4:	0f 84 4e 02 00 00    	je     8328 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    80da:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    80df:	8b 50 08             	mov    0x8(%rax),%edx
    80e2:	85 d2                	test   %edx,%edx
    80e4:	0f 8e 3e 02 00 00    	jle    8328 <verify+0x288>
    80ea:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    80ef:	31 c9                	xor    %ecx,%ecx
    80f1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    80f6:	31 c0                	xor    %eax,%eax
    80f8:	44 89 f2             	mov    %r14d,%edx
    80fb:	bf 01 00 00 00       	mov    $0x1,%edi
    8100:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    8105:	48 8d 35 85 11 00 00 	lea    0x1185(%rip),%rsi        # 9291 <_IO_stdin_used+0x291>
    810c:	e8 9f a3 ff ff       	call   24b0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    8111:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    8116:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    811b:	8b 40 08             	mov    0x8(%rax),%eax
    811e:	85 c0                	test   %eax,%eax
    8120:	0f 8e e6 01 00 00    	jle    830c <verify+0x26c>
    8126:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    8129:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    812e:	31 db                	xor    %ebx,%ebx
    8130:	48 c1 e0 09          	shl    $0x9,%rax
    8134:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    8139:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    813e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8143:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    8148:	4c 8b 20             	mov    (%rax),%r12
    814b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    8150:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    8155:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    815a:	49 89 de             	mov    %rbx,%r14
    815d:	48 8d 35 42 11 00 00 	lea    0x1142(%rip),%rsi        # 92a6 <_IO_stdin_used+0x2a6>
    8164:	49 c1 e6 09          	shl    $0x9,%r14
    8168:	bf 01 00 00 00       	mov    $0x1,%edi
    816d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    8171:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    8179:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    817e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    8186:	31 c0                	xor    %eax,%eax
    8188:	e8 23 a3 ff ff       	call   24b0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    818d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8192:	4c 8b 20             	mov    (%rax),%r12
    8195:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    819e:	0f 8e 47 01 00 00    	jle    82eb <verify+0x24b>
    81a4:	4c 03 75 00          	add    0x0(%rbp),%r14
    81a8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    81ad:	ba 01 00 00 00       	mov    $0x1,%edx
    81b2:	4d 89 f5             	mov    %r14,%r13
    81b5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    81bc:	4d 85 f6             	test   %r14,%r14
    81bf:	0f 8e 21 01 00 00    	jle    82e6 <verify+0x246>
    81c5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    81c8:	48 89 d5             	mov    %rdx,%rbp
    81cb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    81d0:	31 db                	xor    %ebx,%ebx
    81d2:	4d 89 f2             	mov    %r14,%r10
    81d5:	48 c1 e5 05          	shl    $0x5,%rbp
    81d9:	48 83 ed 20          	sub    $0x20,%rbp
    81dd:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    81e1:	49 89 ee             	mov    %rbp,%r14
    81e4:	48 89 dd             	mov    %rbx,%rbp
    81e7:	48 89 d3             	mov    %rdx,%rbx
    81ea:	eb 31                	jmp    821d <verify+0x17d>
    81ec:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    81f0:	4c 39 c2             	cmp    %r8,%rdx
    81f3:	0f 8d 57 01 00 00    	jge    8350 <verify+0x2b0>
    81f9:	4c 39 df             	cmp    %r11,%rdi
    81fc:	7e 05                	jle    8203 <verify+0x163>
    81fe:	49 39 c1             	cmp    %rax,%r9
    8201:	7c 75                	jl     8278 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8203:	4c 39 df             	cmp    %r11,%rdi
    8206:	0f 8d ab 01 00 00    	jge    83b7 <verify+0x317>
    820c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8210:	48 83 c5 01          	add    $0x1,%rbp
    8214:	49 39 ea             	cmp    %rbp,%r10
    8217:	0f 8e a9 00 00 00    	jle    82c6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    821d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    8224:	48 89 e8             	mov    %rbp,%rax
    8227:	48 c1 e0 05          	shl    $0x5,%rax
    822b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    8232:	4c 01 f2             	add    %r14,%rdx
    8235:	48 8b 08             	mov    (%rax),%rcx
    8238:	48 8b 78 10          	mov    0x10(%rax),%rdi
    823c:	48 8b 32             	mov    (%rdx),%rsi
    823f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    8243:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    8247:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    824b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    824f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    8253:	48 39 f1             	cmp    %rsi,%rcx
    8256:	7c 98                	jl     81f0 <verify+0x150>
    8258:	0f 8e 42 01 00 00    	jle    83a0 <verify+0x300>
    825e:	4c 39 c2             	cmp    %r8,%rdx
    8261:	0f 8f f9 00 00 00    	jg     8360 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8267:	75 a7                	jne    8210 <verify+0x170>
    8269:	4c 39 df             	cmp    %r11,%rdi
    826c:	7f a2                	jg     8210 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    826e:	49 39 c1             	cmp    %rax,%r9
    8271:	7c 9d                	jl     8210 <verify+0x170>
    8273:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    8278:	49 89 c1             	mov    %rax,%r9
    827b:	48 89 f9             	mov    %rdi,%rcx
    827e:	48 89 f2             	mov    %rsi,%rdx
    8281:	bf 01 00 00 00       	mov    $0x1,%edi
    8286:	48 8d 35 73 15 00 00 	lea    0x1573(%rip),%rsi        # 9800 <_IO_stdin_used+0x800>
    828d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    828f:	48 83 c5 01          	add    $0x1,%rbp
    8293:	e8 18 a2 ff ff       	call   24b0 <__printf_chk@plt>
    8298:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    829d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    82a2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    82a5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    82aa:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    82b1:	4c 8b 20             	mov    (%rax),%r12
    82b4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    82b9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    82bd:	49 39 ea             	cmp    %rbp,%r10
    82c0:	0f 8f 57 ff ff ff    	jg     821d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    82c6:	48 89 da             	mov    %rbx,%rdx
    82c9:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    82d0:	7d 14                	jge    82e6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    82d2:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    82d9:	48 83 c2 01          	add    $0x1,%rdx
    82dd:	4d 85 f6             	test   %r14,%r14
    82e0:	0f 8f e2 fe ff ff    	jg     81c8 <verify+0x128>
    82e6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    82eb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    82f0:	48 83 c3 01          	add    $0x1,%rbx
    82f4:	39 58 08             	cmp    %ebx,0x8(%rax)
    82f7:	0f 8f 53 fe ff ff    	jg     8150 <verify+0xb0>
    82fd:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    8302:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    8307:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    830c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8311:	48 83 c1 01          	add    $0x1,%rcx
    8315:	39 48 08             	cmp    %ecx,0x8(%rax)
    8318:	0f 8f d8 fd ff ff    	jg     80f6 <verify+0x56>
    831e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    8323:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    8328:	48 81 44 24 10 20 01 00 00 	addq   $0x120,0x10(%rsp)
    8331:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    8336:	41 39 c7             	cmp    %eax,%r15d
    8339:	0f 84 86 00 00 00    	je     83c5 <verify+0x325>
    833f:	41 89 c4             	mov    %eax,%r12d
    8342:	e9 8a fd ff ff       	jmp    80d1 <verify+0x31>
    8347:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8350:	0f 85 ba fe ff ff    	jne    8210 <verify+0x170>
    8356:	e9 a8 fe ff ff       	jmp    8203 <verify+0x163>
    835b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    8360:	49 39 c1             	cmp    %rax,%r9
    8363:	7e 09                	jle    836e <verify+0x2ce>
    8365:	4c 39 df             	cmp    %r11,%rdi
    8368:	0f 8c 0a ff ff ff    	jl     8278 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    836e:	4c 39 df             	cmp    %r11,%rdi
    8371:	0f 8f 99 fe ff ff    	jg     8210 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8377:	49 39 c1             	cmp    %rax,%r9
    837a:	0f 8d f8 fe ff ff    	jge    8278 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8380:	48 39 f1             	cmp    %rsi,%rcx
    8383:	0f 85 87 fe ff ff    	jne    8210 <verify+0x170>
    8389:	4c 39 c2             	cmp    %r8,%rdx
    838c:	0f 85 7e fe ff ff    	jne    8210 <verify+0x170>
    8392:	4c 39 df             	cmp    %r11,%rdi
    8395:	0f 84 dd fe ff ff    	je     8278 <verify+0x1d8>
    839b:	e9 70 fe ff ff       	jmp    8210 <verify+0x170>
    83a0:	4c 39 c2             	cmp    %r8,%rdx
    83a3:	0f 8c 5a fe ff ff    	jl     8203 <verify+0x163>
    83a9:	4c 39 df             	cmp    %r11,%rdi
    83ac:	7e c9                	jle    8377 <verify+0x2d7>
    83ae:	4c 39 c2             	cmp    %r8,%rdx
    83b1:	0f 85 59 fe ff ff    	jne    8210 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    83b7:	49 39 c1             	cmp    %rax,%r9
    83ba:	0f 8f 50 fe ff ff    	jg     8210 <verify+0x170>
    83c0:	e9 b3 fe ff ff       	jmp    8278 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    83c5:	48 81 44 24 18 20 01 00 00 	addq   $0x120,0x18(%rsp)
    83ce:	41 8d 46 01          	lea    0x1(%r14),%eax
    83d2:	45 39 e6             	cmp    %r12d,%r14d
    83d5:	74 08                	je     83df <verify+0x33f>
    83d7:	41 89 c6             	mov    %eax,%r14d
    83da:	e9 ea fc ff ff       	jmp    80c9 <verify+0x29>
}
    83df:	48 83 c4 58          	add    $0x58,%rsp
    83e3:	31 c0                	xor    %eax,%eax
    83e5:	5b                   	pop    %rbx
    83e6:	5d                   	pop    %rbp
    83e7:	41 5c                	pop    %r12
    83e9:	41 5d                	pop    %r13
    83eb:	41 5e                	pop    %r14
    83ed:	41 5f                	pop    %r15
    83ef:	c3                   	ret
    83f0:	31 c0                	xor    %eax,%eax
    83f2:	c3                   	ret

Disassembly of section .fini:

00000000000083f4 <_fini>:
    83f4:	f3 0f 1e fa          	endbr64
    83f8:	48 83 ec 08          	sub    $0x8,%rsp
    83fc:	48 83 c4 08          	add    $0x8,%rsp
    8400:	c3                   	ret
