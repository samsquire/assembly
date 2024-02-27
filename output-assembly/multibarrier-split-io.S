
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

0000000000002300 <putchar@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 6e 9b 00 00    	jmp    *0x9b6e(%rip)        # be78 <putchar@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002310 <puts@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 66 9b 00 00    	jmp    *0x9b66(%rip)        # be80 <puts@GLIBC_2.2.5>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <setsockopt@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 5e 9b 00 00    	jmp    *0x9b5e(%rip)        # be88 <setsockopt@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <clock_gettime@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 56 9b 00 00    	jmp    *0x9b56(%rip)        # be90 <clock_gettime@GLIBC_2.17>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <fclose@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 4e 9b 00 00    	jmp    *0x9b4e(%rip)        # be98 <fclose@GLIBC_2.2.5>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <strlen@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 46 9b 00 00    	jmp    *0x9b46(%rip)        # bea0 <strlen@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <__stack_chk_fail@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 3e 9b 00 00    	jmp    *0x9b3e(%rip)        # bea8 <__stack_chk_fail@GLIBC_2.4>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <io_uring_submit@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 36 9b 00 00    	jmp    *0x9b36(%rip)        # beb0 <io_uring_submit@LIBURING_2.0>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <nanosleep@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 2e 9b 00 00    	jmp    *0x9b2e(%rip)        # beb8 <nanosleep@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <strrchr@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 26 9b 00 00    	jmp    *0x9b26(%rip)        # bec0 <strrchr@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <fputs@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 1e 9b 00 00    	jmp    *0x9b1e(%rip)        # bec8 <fputs@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <close@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 16 9b 00 00    	jmp    *0x9b16(%rip)        # bed0 <close@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <strtok_r@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 0e 9b 00 00    	jmp    *0x9b0e(%rip)        # bed8 <strtok_r@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <read@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 06 9b 00 00    	jmp    *0x9b06(%rip)        # bee0 <read@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <calloc@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 fe 9a 00 00    	jmp    *0x9afe(%rip)        # bee8 <calloc@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <strcmp@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 f6 9a 00 00    	jmp    *0x9af6(%rip)        # bef0 <strcmp@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <__memcpy_chk@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 ee 9a 00 00    	jmp    *0x9aee(%rip)        # bef8 <__memcpy_chk@GLIBC_2.3.4>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <stat@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 e6 9a 00 00    	jmp    *0x9ae6(%rip)        # bf00 <stat@GLIBC_2.33>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <memcpy@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 de 9a 00 00    	jmp    *0x9ade(%rip)        # bf08 <memcpy@GLIBC_2.14>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <io_uring_queue_init@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 d6 9a 00 00    	jmp    *0x9ad6(%rip)        # bf10 <io_uring_queue_init@LIBURING_2.0>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <eventfd_write@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 ce 9a 00 00    	jmp    *0x9ace(%rip)        # bf18 <eventfd_write@GLIBC_2.7>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <malloc@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 c6 9a 00 00    	jmp    *0x9ac6(%rip)        # bf20 <malloc@GLIBC_2.2.5>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <listen@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 be 9a 00 00    	jmp    *0x9abe(%rip)        # bf28 <listen@GLIBC_2.2.5>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <__strcpy_chk@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 b6 9a 00 00    	jmp    *0x9ab6(%rip)        # bf30 <__strcpy_chk@GLIBC_2.3.4>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <__io_uring_get_cqe@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 ae 9a 00 00    	jmp    *0x9aae(%rip)        # bf38 <__io_uring_get_cqe@LIBURING_2.0>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <__printf_chk@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 a6 9a 00 00    	jmp    *0x9aa6(%rip)        # bf40 <__printf_chk@GLIBC_2.3.4>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <bind@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 9e 9a 00 00    	jmp    *0x9a9e(%rip)        # bf48 <bind@GLIBC_2.2.5>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <pthread_create@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 96 9a 00 00    	jmp    *0x9a96(%rip)        # bf50 <pthread_create@GLIBC_2.34>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <io_uring_wait_cqe_timeout@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 8e 9a 00 00    	jmp    *0x9a8e(%rip)        # bf58 <io_uring_wait_cqe_timeout@LIBURING_2.0>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <open@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 86 9a 00 00    	jmp    *0x9a86(%rip)        # bf60 <open@GLIBC_2.2.5>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <fopen@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 7e 9a 00 00    	jmp    *0x9a7e(%rip)        # bf68 <fopen@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <perror@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 76 9a 00 00    	jmp    *0x9a76(%rip)        # bf70 <perror@GLIBC_2.2.5>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <exit@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 6e 9a 00 00    	jmp    *0x9a6e(%rip)        # bf78 <exit@GLIBC_2.2.5>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <eventfd@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 66 9a 00 00    	jmp    *0x9a66(%rip)        # bf80 <eventfd@GLIBC_2.7>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <fwrite@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 5e 9a 00 00    	jmp    *0x9a5e(%rip)        # bf88 <fwrite@GLIBC_2.2.5>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <__fprintf_chk@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 56 9a 00 00    	jmp    *0x9a56(%rip)        # bf90 <__fprintf_chk@GLIBC_2.3.4>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <io_uring_register_eventfd@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 4e 9a 00 00    	jmp    *0x9a4e(%rip)        # bf98 <io_uring_register_eventfd@LIBURING_2.0>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <pthread_join@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 46 9a 00 00    	jmp    *0x9a46(%rip)        # bfa0 <pthread_join@GLIBC_2.34>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <strerror@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 3e 9a 00 00    	jmp    *0x9a3e(%rip)        # bfa8 <strerror@GLIBC_2.2.5>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <pthread_mutex_init@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 36 9a 00 00    	jmp    *0x9a36(%rip)        # bfb0 <pthread_mutex_init@GLIBC_2.2.5>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <epoll_create1@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 2e 9a 00 00    	jmp    *0x9a2e(%rip)        # bfb8 <epoll_create1@GLIBC_2.9>
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
  return a;
}

int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send);
int buffersend_filter(struct KernelThread *data, struct Buffers *buffers, int kind, void * send, int filter);
void fatal_error(const char *syscall) {
    25c0:	f3 0f 1e fa          	endbr64
    25c4:	50                   	push   %rax
    25c5:	58                   	pop    %rax
    25c6:	50                   	push   %rax
    perror(syscall);
    25c7:	e8 24 ff ff ff       	call   24f0 <perror@plt>
    exit(1);
    25cc:	bf 01 00 00 00       	mov    $0x1,%edi
    25d1:	e8 2a ff ff ff       	call   2500 <exit@plt>

00000000000025d6 <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    25d6:	48 8d 3d 4f 6c 00 00 	lea    0x6c4f(%rip),%rdi        # 922c <_IO_stdin_used+0x22c>
    25dd:	e8 de ff ff ff       	call   25c0 <fatal_error>

00000000000025e2 <add_read_request.cold>:

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    25e2:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25ea:	0f 0b                	ud2

00000000000025ec <add_accept_request.cold>:
    25ec:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    25f4:	0f 0b                	ud2

00000000000025f6 <io_thread.cold>:
          printf("Received stop event\n");
          break;
        }
        struct Request *req = (struct Request *) cqe->user_data;
        if (ret < 0)
            fatal_error("io_uring_wait_cqe");
    25f6:	48 8d 3d 9a 6b 00 00 	lea    0x6b9a(%rip),%rdi        # 9197 <_IO_stdin_used+0x197>
    25fd:	e8 be ff ff ff       	call   25c0 <fatal_error>
    2602:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    260a:	0f 0b                	ud2
        fatal_error("setsockopt(SO_REUSEADDR)");
    260c:	48 8d 3d 47 6b 00 00 	lea    0x6b47(%rip),%rdi        # 915a <_IO_stdin_used+0x15a>
    2613:	e8 a8 ff ff ff       	call   25c0 <fatal_error>
    2618:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2620:	0f 0b                	ud2
            int client_socket = write->client_socket; 
            // printf("%p write\n", write);
            struct io_uring_sqe *sqe = io_uring_get_sqe(&ring);
            struct Request *req = write->request;
            // printf("req %p\n", req);
            req->event_type = EVENT_TYPE_WRITE;
    2622:	41 c7 06 02 00 00 00 	movl   $0x2,(%r14)
    2629:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2631:	0f 0b                	ud2
        fatal_error("bind()");
    2633:	48 8d 3d 39 6b 00 00 	lea    0x6b39(%rip),%rdi        # 9173 <_IO_stdin_used+0x173>
    263a:	e8 81 ff ff ff       	call   25c0 <fatal_error>
    263f:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2647:	0f 0b                	ud2
    2649:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2651:	0f 0b                	ud2
      fatal_error("listen()");
    2653:	48 8d 3d 20 6b 00 00 	lea    0x6b20(%rip),%rdi        # 917a <_IO_stdin_used+0x17a>
    265a:	e8 61 ff ff ff       	call   25c0 <fatal_error>
    265f:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2667:	0f 0b                	ud2
    2669:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2671:	0f 0b                	ud2
				   perror("new client epoll_create1");
    2673:	48 8d 3d 3f 6b 00 00 	lea    0x6b3f(%rip),%rdi        # 91b9 <_IO_stdin_used+0x1b9>
    267a:	e8 71 fe ff ff       	call   24f0 <perror@plt>
				   exit(EXIT_FAILURE);
    267f:	bf 01 00 00 00       	mov    $0x1,%edi
    2684:	e8 77 fe ff ff       	call   2500 <exit@plt>
    struct NewSocketMessage *msg = bufferreply->data;
    2689:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    2691:	0f 0b                	ud2
        fatal_error("socket()");
    2693:	48 8d 3d b7 6a 00 00 	lea    0x6ab7(%rip),%rdi        # 9151 <_IO_stdin_used+0x151>
    269a:	e8 21 ff ff ff       	call   25c0 <fatal_error>
    int new_client_socket = newclient_message->socket;
    269f:	8b 04 25 00 00 00 00 	mov    0x0,%eax
    26a6:	0f 0b                	ud2
    26a8:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26b0:	0f 0b                	ud2
    26b2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    26bc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000026c0 <main>:
    }


  return 0;
}
int main() {
    26c0:	f3 0f 1e fa          	endbr64
    26c4:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    26c6:	48 8d 3d 93 71 00 00 	lea    0x7193(%rip),%rdi        # 9860 <_IO_stdin_used+0x860>
    26cd:	41 56                	push   %r14
    26cf:	41 55                	push   %r13
    26d1:	4c 8d 2d c7 6c 00 00 	lea    0x6cc7(%rip),%r13        # 939f <_IO_stdin_used+0x39f>
    26d8:	41 54                	push   %r12
    26da:	55                   	push   %rbp
    26db:	53                   	push   %rbx
    26dc:	48 81 ec c8 00 00 00 	sub    $0xc8,%rsp
    26e3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    26ec:	48 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%rsp)
    26f4:	48 8d 05 65 1b 00 00 	lea    0x1b65(%rip),%rax        # 4260 <barriered_reset>
    26fb:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2700:	0f 16 2d 51 95 00 00 	movhps 0x9551(%rip),%xmm5        # bc58 <__do_global_dtors_aux_fini_array_entry+0x8>
    2707:	0f 29 6c 24 70       	movaps %xmm5,0x70(%rsp)
    270c:	e8 ff fb ff ff       	call   2310 <puts@plt>
    2711:	bf 0a 00 00 00       	mov    $0xa,%edi
    2716:	e8 e5 fb ff ff       	call   2300 <putchar@plt>
    271b:	ba 01 00 00 00       	mov    $0x1,%edx
    2720:	48 8d 35 70 6b 00 00 	lea    0x6b70(%rip),%rsi        # 9297 <_IO_stdin_used+0x297>
    2727:	31 c0                	xor    %eax,%eax
    2729:	bf 01 00 00 00       	mov    $0x1,%edi
    272e:	e8 5d fd ff ff       	call   2490 <__printf_chk@plt>
    2733:	ba 02 00 00 00       	mov    $0x2,%edx
    2738:	48 8d 35 68 6b 00 00 	lea    0x6b68(%rip),%rsi        # 92a7 <_IO_stdin_used+0x2a7>
    273f:	31 c0                	xor    %eax,%eax
    2741:	bf 01 00 00 00       	mov    $0x1,%edi
    2746:	e8 45 fd ff ff       	call   2490 <__printf_chk@plt>
    274b:	ba 01 00 00 00       	mov    $0x1,%edx
    2750:	48 8d 35 65 6b 00 00 	lea    0x6b65(%rip),%rsi        # 92bc <_IO_stdin_used+0x2bc>
    2757:	31 c0                	xor    %eax,%eax
    2759:	bf 01 00 00 00       	mov    $0x1,%edi
    275e:	e8 2d fd ff ff       	call   2490 <__printf_chk@plt>
    2763:	ba 02 00 00 00       	mov    $0x2,%edx
    2768:	48 8d 35 5d 6b 00 00 	lea    0x6b5d(%rip),%rsi        # 92cc <_IO_stdin_used+0x2cc>
    276f:	31 c0                	xor    %eax,%eax
    2771:	bf 01 00 00 00       	mov    $0x1,%edi
    2776:	e8 15 fd ff ff       	call   2490 <__printf_chk@plt>
    277b:	48 8d 3d 60 6b 00 00 	lea    0x6b60(%rip),%rdi        # 92e2 <_IO_stdin_used+0x2e2>
    2782:	e8 89 fb ff ff       	call   2310 <puts@plt>
    2787:	ba 02 00 00 00       	mov    $0x2,%edx
    278c:	48 8d 35 6b 6b 00 00 	lea    0x6b6b(%rip),%rsi        # 92fe <_IO_stdin_used+0x2fe>
    2793:	31 c0                	xor    %eax,%eax
    2795:	bf 01 00 00 00       	mov    $0x1,%edi
    279a:	e8 f1 fc ff ff       	call   2490 <__printf_chk@plt>
    279f:	ba 07 00 00 00       	mov    $0x7,%edx
    27a4:	48 8d 35 6d 6b 00 00 	lea    0x6b6d(%rip),%rsi        # 9318 <_IO_stdin_used+0x318>
    27ab:	31 c0                	xor    %eax,%eax
    27ad:	bf 01 00 00 00       	mov    $0x1,%edi
    27b2:	e8 d9 fc ff ff       	call   2490 <__printf_chk@plt>
    27b7:	ba 02 00 00 00       	mov    $0x2,%edx
    27bc:	48 8d 35 69 6b 00 00 	lea    0x6b69(%rip),%rsi        # 932c <_IO_stdin_used+0x32c>
    27c3:	31 c0                	xor    %eax,%eax
    27c5:	bf 01 00 00 00       	mov    $0x1,%edi
    27ca:	e8 c1 fc ff ff       	call   2490 <__printf_chk@plt>
    27cf:	ba 01 00 00 00       	mov    $0x1,%edx
    27d4:	48 8d 35 62 6b 00 00 	lea    0x6b62(%rip),%rsi        # 933d <_IO_stdin_used+0x33d>
    27db:	31 c0                	xor    %eax,%eax
    27dd:	bf 01 00 00 00       	mov    $0x1,%edi
    27e2:	e8 a9 fc ff ff       	call   2490 <__printf_chk@plt>
    27e7:	ba 02 00 00 00       	mov    $0x2,%edx
    27ec:	48 8d 35 62 6b 00 00 	lea    0x6b62(%rip),%rsi        # 9355 <_IO_stdin_used+0x355>
    27f3:	31 c0                	xor    %eax,%eax
    27f5:	bf 01 00 00 00       	mov    $0x1,%edi
    27fa:	e8 91 fc ff ff       	call   2490 <__printf_chk@plt>
    27ff:	ba 01 00 00 00       	mov    $0x1,%edx
    2804:	48 8d 35 bd 70 00 00 	lea    0x70bd(%rip),%rsi        # 98c8 <_IO_stdin_used+0x8c8>
    280b:	31 c0                	xor    %eax,%eax
    280d:	bf 01 00 00 00       	mov    $0x1,%edi
    2812:	e8 79 fc ff ff       	call   2490 <__printf_chk@plt>
    2817:	ba 01 00 00 00       	mov    $0x1,%edx
    281c:	48 8d 35 d5 70 00 00 	lea    0x70d5(%rip),%rsi        # 98f8 <_IO_stdin_used+0x8f8>
    2823:	31 c0                	xor    %eax,%eax
    2825:	bf 01 00 00 00       	mov    $0x1,%edi
    282a:	e8 61 fc ff ff       	call   2490 <__printf_chk@plt>
    282f:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2834:	48 8d 35 36 6b 00 00 	lea    0x6b36(%rip),%rsi        # 9371 <_IO_stdin_used+0x371>
    283b:	31 c0                	xor    %eax,%eax
    283d:	bf 01 00 00 00       	mov    $0x1,%edi
    2842:	e8 49 fc ff ff       	call   2490 <__printf_chk@plt>
    2847:	ba 10 27 00 00       	mov    $0x2710,%edx
    284c:	48 8d 35 38 6b 00 00 	lea    0x6b38(%rip),%rsi        # 938b <_IO_stdin_used+0x38b>
    2853:	31 c0                	xor    %eax,%eax
    2855:	bf 01 00 00 00       	mov    $0x1,%edi
    285a:	e8 31 fc ff ff       	call   2490 <__printf_chk@plt>
    285f:	48 8d 3d 8f 68 00 00 	lea    0x688f(%rip),%rdi        # 90f5 <_IO_stdin_used+0xf5>
    2866:	e8 a5 fa ff ff       	call   2310 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
    286b:	be 18 00 00 00       	mov    $0x18,%esi
    2870:	bf 01 00 00 00       	mov    $0x1,%edi
    2875:	e8 66 fb ff ff       	call   23e0 <calloc@plt>
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    287a:	be 18 00 00 00       	mov    $0x18,%esi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
    287f:	45 31 e4             	xor    %r12d,%r12d
  int cc = 0; 
    2882:	45 31 ff             	xor    %r15d,%r15d
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2885:	bf 01 00 00 00       	mov    $0x1,%edi
  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
    288a:	49 89 c6             	mov    %rax,%r14
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    288d:	e8 4e fb ff ff       	call   23e0 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2892:	be 30 01 00 00       	mov    $0x130,%esi
    2897:	bf 07 00 00 00       	mov    $0x7,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    289c:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28a1:	e8 3a fb ff ff       	call   23e0 <calloc@plt>
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28a6:	be 28 00 00 00       	mov    $0x28,%esi
    28ab:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28b0:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28b5:	e8 26 fb ff ff       	call   23e0 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28ba:	be 28 00 00 00       	mov    $0x28,%esi
    28bf:	bf 31 00 00 00       	mov    $0x31,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28c4:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28cc:	e8 0f fb ff ff       	call   23e0 <calloc@plt>
    28d1:	4c 89 34 24          	mov    %r14,(%rsp)
    28d5:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  for (int x = 0 ; x < total_threads; x++) {
    28dd:	49 89 c6             	mov    %rax,%r14
int main() {
    28e0:	4c 89 f5             	mov    %r14,%rbp
    for (int y = 0 ; y < total_threads; y++) {
    28e3:	31 db                	xor    %ebx,%ebx
    28e5:	0f 1f 00             	nopl   (%rax)
    28e8:	42 8d 14 3b          	lea    (%rbx,%r15,1),%edx
    28ec:	41 89 d8             	mov    %ebx,%r8d
    28ef:	44 89 e1             	mov    %r12d,%ecx
    28f2:	4c 89 ee             	mov    %r13,%rsi
    28f5:	bf 01 00 00 00       	mov    $0x1,%edi
    28fa:	31 c0                	xor    %eax,%eax
    28fc:	83 c3 01             	add    $0x1,%ebx
    28ff:	e8 8c fb ff ff       	call   2490 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    2904:	48 89 ef             	mov    %rbp,%rdi
    2907:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    2909:	48 83 c5 28          	add    $0x28,%rbp
      pthread_mutex_init(&swapmutex[cc++], NULL);
    290d:	e8 5e fc ff ff       	call   2570 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    2912:	83 fb 07             	cmp    $0x7,%ebx
    2915:	75 d1                	jne    28e8 <main+0x228>
    2917:	41 83 c7 07          	add    $0x7,%r15d
  for (int x = 0 ; x < total_threads; x++) {
    291b:	41 83 c4 01          	add    $0x1,%r12d
    291f:	49 81 c6 18 01 00 00 	add    $0x118,%r14
    2926:	41 83 ff 31          	cmp    $0x31,%r15d
    292a:	75 b4                	jne    28e0 <main+0x220>
    292c:	ba 02 00 00 00       	mov    $0x2,%edx
    2931:	bf 01 00 00 00       	mov    $0x1,%edi
    2936:	31 c0                	xor    %eax,%eax
    2938:	4c 8b 34 24          	mov    (%rsp),%r14
    293c:	48 8d 35 6c 6a 00 00 	lea    0x6a6c(%rip),%rsi        # 93af <_IO_stdin_used+0x3af>
    2943:	e8 48 fb ff ff       	call   2490 <__printf_chk@plt>
    2948:	ba 04 00 00 00       	mov    $0x4,%edx
    294d:	48 8d 35 71 6a 00 00 	lea    0x6a71(%rip),%rsi        # 93c5 <_IO_stdin_used+0x3c5>
    2954:	31 c0                	xor    %eax,%eax
    2956:	bf 01 00 00 00       	mov    $0x1,%edi
    295b:	e8 30 fb ff ff       	call   2490 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2960:	be 10 00 00 00       	mov    $0x10,%esi
    2965:	bf 04 00 00 00       	mov    $0x4,%edi
    296a:	e8 71 fa ff ff       	call   23e0 <calloc@plt>
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    296f:	be 10 00 00 00       	mov    $0x10,%esi
    2974:	bf 02 00 00 00       	mov    $0x2,%edi
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2979:	49 89 c7             	mov    %rax,%r15
    297c:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2981:	e8 5a fa ff ff       	call   23e0 <calloc@plt>


  int snapshot_limit = 100;
  for (int x = 0 ; x < io_threads; x++) {
    iobuffers[x].count = buffer_size;
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2986:	be 28 00 00 00       	mov    $0x28,%esi
    298b:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int y = 0 ; y < buffer_size; y++) {
      iobuffers[x].buffer[y].available = 0;
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2990:	4d 89 fd             	mov    %r15,%r13
    iobuffers[x].count = buffer_size;
    2993:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2999:	48 89 c3             	mov    %rax,%rbx
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    299c:	e8 3f fa ff ff       	call   23e0 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29a1:	be 20 00 00 00       	mov    $0x20,%esi
    29a6:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29ab:	48 89 43 08          	mov    %rax,0x8(%rbx)
    29af:	49 89 c4             	mov    %rax,%r12
      iobuffers[x].buffer[y].available = 0;
    29b2:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    29b9:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29c0:	e8 1b fa ff ff       	call   23e0 <calloc@plt>
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29c5:	be 28 00 00 00       	mov    $0x28,%esi
    29ca:	bf 01 00 00 00       	mov    $0x1,%edi
    iobuffers[x].count = buffer_size;
    29cf:	c7 43 10 01 00 00 00 	movl   $0x1,0x10(%rbx)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29d6:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29db:	e8 00 fa ff ff       	call   23e0 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29e0:	be 20 00 00 00       	mov    $0x20,%esi
    29e5:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29ea:	48 89 43 18          	mov    %rax,0x18(%rbx)
    29ee:	49 89 c4             	mov    %rax,%r12
    29f1:	49 8d 5f 40          	lea    0x40(%r15),%rbx
      iobuffers[x].buffer[y].available = 0;
    29f5:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    29fc:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a03:	e8 d8 f9 ff ff       	call   23e0 <calloc@plt>
    2a08:	4c 89 bc 24 80 00 00 00 	mov    %r15,0x80(%rsp)
    2a10:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    }
  }
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a15:	be 28 00 00 00       	mov    $0x28,%esi
    buffers[x].count = buffer_size;
    2a1a:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a22:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2a27:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a2b:	e8 b0 f9 ff ff       	call   23e0 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a30:	be 20 00 00 00       	mov    $0x20,%esi
    2a35:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a3a:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    2a3e:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    2a41:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2a48:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a4f:	e8 8c f9 ff ff       	call   23e0 <calloc@plt>
    2a54:	48 89 45 10          	mov    %rax,0x10(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    2a58:	49 39 dd             	cmp    %rbx,%r13
    2a5b:	75 b8                	jne    2a15 <main+0x355>
  int iocur_buffer = 0;
  int swap = 0;
  int groupcount = 0;
  int seq = 0;
  int seqs[] = {1, 3, 6};
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a5d:	be 08 00 00 00       	mov    $0x8,%esi
    2a62:	bf 64 00 00 00       	mov    $0x64,%edi
    2a67:	e8 74 f9 ff ff       	call   23e0 <calloc@plt>
  struct Global *global = calloc(1, sizeof(struct Global));
    2a6c:	be 10 00 00 00       	mov    $0x10,%esi
    2a71:	bf 01 00 00 00       	mov    $0x1,%edi
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a76:	48 89 c3             	mov    %rax,%rbx
    2a79:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  struct Global *global = calloc(1, sizeof(struct Global));
    2a81:	e8 5a f9 ff ff       	call   23e0 <calloc@plt>
  global->request_group_sync = -1;
  global->protected_state = global_protected_state;
  for (int k = 0 ; k < group_count ; k++) {
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2a86:	be 00 01 00 00       	mov    $0x100,%esi
    2a8b:	bf 01 00 00 00       	mov    $0x1,%edi
  global->request_group_sync = -1;
    2a90:	c7 00 ff ff ff ff    	movl   $0xffffffff,(%rax)
  global->protected_state = global_protected_state;
    2a96:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2a9a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2a9f:	e8 3c f9 ff ff       	call   23e0 <calloc@plt>
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2aa4:	be 08 00 00 00       	mov    $0x8,%esi
    2aa9:	bf 64 00 00 00       	mov    $0x64,%edi
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2aae:	48 89 04 24          	mov    %rax,(%rsp)
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2ab2:	e8 29 f9 ff ff       	call   23e0 <calloc@plt>
    all_groups[groupcount++] = group_data;
    2ab7:	48 8b 14 24          	mov    (%rsp),%rdx
    group_data->thread_count = threads_per_group * group_count;
    group_data->threads = group_threads;
    group_data->global = global;
    2abb:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    group_data->seq = seqs[seq++ % 3];
    2ac0:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
    2ac9:	48 8b 6c 24 68       	mov    0x68(%rsp),%rbp
    2ace:	4c 8b 54 24 38       	mov    0x38(%rsp),%r10
    2ad3:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
    group_data->thread_count = threads_per_group * group_count;
    2adb:	c7 82 90 00 00 00 02 00 00 00 	movl   $0x2,0x90(%rdx)
    group_data->threads = group_threads;
    2ae5:	48 89 82 88 00 00 00 	mov    %rax,0x88(%rdx)
    group_data->global = global;
    2aec:	4c 89 8a 98 00 00 00 	mov    %r9,0x98(%rdx)
    group_data->seq = seqs[seq++ % 3];
    2af3:	c7 82 a0 00 00 00 01 00 00 00 	movl   $0x1,0xa0(%rdx)
    2afd:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    2b05:	48 89 6c 24 58       	mov    %rbp,0x58(%rsp)
    2b0a:	4c 89 8c 24 a0 00 00 00 	mov    %r9,0xa0(%rsp)
    2b12:	48 89 94 24 a8 00 00 00 	mov    %rdx,0xa8(%rsp)
    all_groups[groupcount++] = group_data;
    2b1a:	48 89 13             	mov    %rdx,(%rbx)
    int group_thread_count = 0;
    for (int d = 0 ; d < threads_per_group ; d++) {
    2b1d:	4c 89 d3             	mov    %r10,%rbx
      int x = (k * threads_per_group) + d;
      thread_data[x].group_data = group_data;
      thread_data[x].all_groups = all_groups;
    2b20:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    2b28:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
      thread_data[x].group = k;
    2b2d:	c7 83 f8 00 00 00 00 00 00 00 	movl   $0x0,0xf8(%rbx)
    2b37:	31 d2                	xor    %edx,%edx
      thread_data[x].group_data = group_data;
    2b39:	48 8b ac 24 a8 00 00 00 	mov    0xa8(%rsp),%rbp
    2b41:	48 8d 35 d8 6d 00 00 	lea    0x6dd8(%rip),%rsi        # 9920 <_IO_stdin_used+0x920>
    2b48:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].all_groups = all_groups;
    2b4d:	48 89 83 f0 00 00 00 	mov    %rax,0xf0(%rbx)
    2b54:	44 89 f1             	mov    %r14d,%ecx
    2b57:	47 8d 24 36          	lea    (%r14,%r14,1),%r12d
    2b5b:	45 89 f7             	mov    %r14d,%r15d
      thread_data[x].global = global;
    2b5e:	48 8b 84 24 a0 00 00 00 	mov    0xa0(%rsp),%rax
      thread_data[x].group_data = group_data;
    2b66:	48 89 ab e8 00 00 00 	mov    %rbp,0xe8(%rbx)
      thread_data[x].global = global;
    2b6d:	48 89 83 00 01 00 00 	mov    %rax,0x100(%rbx)
    2b74:	31 c0                	xor    %eax,%eax
    2b76:	e8 15 f9 ff ff       	call   2490 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2b7b:	be 08 00 00 00       	mov    $0x8,%esi
    2b80:	bf 02 00 00 00       	mov    $0x2,%edi
    2b85:	e8 56 f8 ff ff       	call   23e0 <calloc@plt>
      
      group_data->threads[group_thread_count++] = &thread_data[x];  

      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2b8a:	be 80 00 00 00       	mov    $0x80,%esi
    2b8f:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2b94:	49 89 c5             	mov    %rax,%r13
      group_data->threads[group_thread_count++] = &thread_data[x];  
    2b97:	48 8b 85 88 00 00 00 	mov    0x88(%rbp),%rax
    2b9e:	4c 89 f5             	mov    %r14,%rbp
    2ba1:	4a 89 1c f0          	mov    %rbx,(%rax,%r14,8)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2ba5:	e8 36 f8 ff ff       	call   23e0 <calloc@plt>
    2baa:	49 89 c6             	mov    %rax,%r14
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2bad:	48 85 ed             	test   %rbp,%rbp
    2bb0:	0f 84 24 0e 00 00    	je     39da <main+0x131a>
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2bb6:	49 8d 45 08          	lea    0x8(%r13),%rax
    2bba:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    2bbf:	41 b8 01 00 00 00    	mov    $0x1,%r8d
        other = abs(x - 1) % total_threads;
    2bc5:	31 ed                	xor    %ebp,%ebp
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2bc7:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
    2bcc:	48 89 d8             	mov    %rbx,%rax
        my_thread_data[1] = &thread_data[x]; 
    2bcf:	49 89 45 08          	mov    %rax,0x8(%r13)
        thread_data[x].protected_state = &protected_state[k];
    2bd3:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    2bd8:	89 e9                	mov    %ebp,%ecx
    2bda:	48 8d 35 6f 6d 00 00 	lea    0x6d6f(%rip),%rsi        # 9950 <_IO_stdin_used+0x950>
        thread_data[x].thread_index = 1;
    2be1:	44 89 43 04          	mov    %r8d,0x4(%rbx)
    2be5:	bf 01 00 00 00       	mov    $0x1,%edi
        my_thread_data[0] = &thread_data[other]; 
    2bea:	49 89 55 00          	mov    %rdx,0x0(%r13)
    2bee:	44 89 fa             	mov    %r15d,%edx
        thread_data[x].protected_state = &protected_state[k];
    2bf1:	48 89 43 48          	mov    %rax,0x48(%rbx)
    2bf5:	31 c0                	xor    %eax,%eax
    2bf7:	e8 94 f8 ff ff       	call   2490 <__printf_chk@plt>
      thread_data[x].other = other;
    2bfc:	89 ab c8 00 00 00    	mov    %ebp,0xc8(%rbx)
    2c02:	44 89 fa             	mov    %r15d,%edx
    2c05:	31 c0                	xor    %eax,%eax
    2c07:	44 89 e1             	mov    %r12d,%ecx
    2c0a:	48 8d 35 6f 6d 00 00 	lea    0x6d6f(%rip),%rsi        # 9980 <_IO_stdin_used+0x980>
    2c11:	bf 01 00 00 00       	mov    $0x1,%edi
    2c16:	e8 75 f8 ff ff       	call   2490 <__printf_chk@plt>
          CPU_SET(curcpu, sendercpu);
    2c1b:	44 89 e1             	mov    %r12d,%ecx
    2c1e:	b8 01 00 00 00       	mov    $0x1,%eax
      thread_data[x].cpu_set = sendercpu;
    2c23:	4c 89 b3 c0 00 00 00 	mov    %r14,0xc0(%rbx)
          CPU_SET(curcpu, sendercpu);
    2c2a:	48 d3 e0             	shl    %cl,%rax
    2c2d:	49 09 06             	or     %rax,(%r14)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2c30:	be 10 00 00 00       	mov    $0x10,%esi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2c35:	49 89 de             	mov    %rbx,%r14
      thread_data[x].swapmutex = swapmutex;
    2c38:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2c40:	4c 89 6b 18          	mov    %r13,0x18(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2c44:	bf 64 00 00 00       	mov    $0x64,%edi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2c49:	45 31 ed             	xor    %r13d,%r13d
      thread_data[x].kind = KERNEL_THREAD;
    2c4c:	c7 03 5f 00 00 00    	movl   $0x5f,(%rbx)
      thread_data[x].swapmutex = swapmutex;
    2c52:	48 89 83 d8 00 00 00 	mov    %rax,0xd8(%rbx)
      thread_data[x].mswapmutex = mswapmutex;
    2c59:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
      thread_data[x].real_thread_index = x;
    2c61:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
      thread_data[x].mswapmutex = mswapmutex;
    2c65:	48 89 83 e0 00 00 00 	mov    %rax,0xe0(%rbx)
      thread_data[x].all_threads = thread_data;
    2c6c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].task_count = total_barrier_count;
    2c71:	c7 43 40 03 00 00 00 	movl   $0x3,0x40(%rbx)
      thread_data[x].all_threads = thread_data;
    2c78:	48 89 43 20          	mov    %rax,0x20(%rbx)
      thread_data[x].group_count = group_count;
    2c7c:	48 8b 05 8d 72 00 00 	mov    0x728d(%rip),%rax        # 9f10 <_IO_stdin_used+0xf10>
    2c83:	48 89 83 d0 00 00 00 	mov    %rax,0xd0(%rbx)
      thread_data[x].thread_count = 2;
    2c8a:	48 8b 05 87 72 00 00 	mov    0x7287(%rip),%rax        # 9f18 <_IO_stdin_used+0xf18>
    2c91:	48 89 43 28          	mov    %rax,0x28(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2c95:	e8 46 f7 ff ff       	call   23e0 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2c9a:	be 10 00 00 00       	mov    $0x10,%esi
    2c9f:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2ca4:	48 89 43 78          	mov    %rax,0x78(%rbx)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2ca8:	e8 33 f7 ff ff       	call   23e0 <calloc@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2cad:	be 28 00 00 00       	mov    $0x28,%esi
    2cb2:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
    2cb7:	66 0f 6f 3d 21 72 00 00 	movdqa 0x7221(%rip),%xmm7        # 9ee0 <_IO_stdin_used+0xee0>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2cbf:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
      thread_data[x].timestamp_count = 0;
    2cc6:	0f 11 bb 90 00 00 00 	movups %xmm7,0x90(%rbx)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2ccd:	e8 0e f7 ff ff       	call   23e0 <calloc@plt>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2cd2:	be 00 02 00 00       	mov    $0x200,%esi
    2cd7:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2cdc:	66 0f 6f 3d fc 71 00 00 	movdqa 0x71fc(%rip),%xmm7        # 9ee0 <_IO_stdin_used+0xee0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2ce4:	48 89 83 a0 00 00 00 	mov    %rax,0xa0(%rbx)
      thread_data[x].task_timestamp_count = 0;
    2ceb:	0f 11 bb a8 00 00 00 	movups %xmm7,0xa8(%rbx)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2cf2:	e8 e9 f6 ff ff       	call   23e0 <calloc@plt>
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2cf7:	44 89 7c 24 08       	mov    %r15d,0x8(%rsp)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2cfc:	48 89 c5             	mov    %rax,%rbp
        thread_data[x].tasks = barriers;
    2cff:	48 89 43 38          	mov    %rax,0x38(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2d03:	44 89 f8             	mov    %r15d,%eax
    2d06:	83 f0 01             	xor    $0x1,%eax
    2d09:	48 89 ea             	mov    %rbp,%rdx
    2d0c:	89 44 24 20          	mov    %eax,0x20(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2d10:	49 63 c5             	movslq %r13d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2d13:	be 00 01 00 00       	mov    $0x100,%esi
    2d18:	bf 02 00 00 00       	mov    $0x2,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d1d:	31 db                	xor    %ebx,%ebx
          thread_data[x].tasks[y].protected = do_protected_write; 
    2d1f:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2d24:	48 c1 e0 09          	shl    $0x9,%rax
    2d28:	48 8d 2c 02          	lea    (%rdx,%rax,1),%rbp
    2d2c:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2d31:	48 8d 05 e8 14 00 00 	lea    0x14e8(%rip),%rax        # 4220 <do_protected_write>
    2d38:	48 89 85 20 01 00 00 	mov    %rax,0x120(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2d3f:	e8 9c f6 ff ff       	call   23e0 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2d44:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    2d49:	4c 89 74 24 48       	mov    %r14,0x48(%rsp)
    2d4e:	48 89 85 70 01 00 00 	mov    %rax,0x170(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2d55:	49 89 c4             	mov    %rax,%r12
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d58:	45 89 fe             	mov    %r15d,%r14d
    2d5b:	31 c9                	xor    %ecx,%ecx
    2d5d:	89 da                	mov    %ebx,%edx
    2d5f:	48 8d 35 79 66 00 00 	lea    0x6679(%rip),%rsi        # 93df <_IO_stdin_used+0x3df>
    2d66:	bf 01 00 00 00       	mov    $0x1,%edi
    2d6b:	31 c0                	xor    %eax,%eax
    2d6d:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    2d74:	e8 17 f7 ff ff       	call   2490 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d79:	be 08 00 00 00       	mov    $0x8,%esi
    2d7e:	bf 01 00 00 00       	mov    $0x1,%edi
    2d83:	e8 58 f6 ff ff       	call   23e0 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d88:	be 08 00 00 00       	mov    $0x8,%esi
    2d8d:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d92:	48 89 04 24          	mov    %rax,(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d96:	e8 45 f6 ff ff       	call   23e0 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2d9b:	be 80 04 00 00       	mov    $0x480,%esi
    2da0:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2da5:	49 89 c7             	mov    %rax,%r15
              struct Data *data = calloc(3, sizeof(struct Data));
    2da8:	e8 33 f6 ff ff       	call   23e0 <calloc@plt>
              data[0].a = x;
    2dad:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    2db1:	89 da                	mov    %ebx,%edx
              mailboxes[b].pending_lower = NULL;
    2db3:	49 c7 44 24 88 00 00 00 00 	movq   $0x0,-0x78(%r12)
              struct Data *data = calloc(3, sizeof(struct Data));
    2dbc:	48 89 c5             	mov    %rax,%rbp
              data[0].b = y;
    2dbf:	44 89 a8 10 04 00 00 	mov    %r13d,0x410(%rax)
    2dc6:	48 8d 35 d3 6b 00 00 	lea    0x6bd3(%rip),%rsi        # 99a0 <_IO_stdin_used+0x9a0>
              data[0].a = x;
    2dcd:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
              data[0].kind = MAILBOX_LOWER;
    2dd3:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
              data[0].c = b;
    2ddd:	89 98 14 04 00 00    	mov    %ebx,0x414(%rax)
              data[0].id = dataid++;
    2de3:	41 8d 46 01          	lea    0x1(%r14),%eax
              data[1].id = dataid++;
    2de7:	89 85 98 08 00 00    	mov    %eax,0x898(%rbp)
              mailboxes[b].higher = &data[1];
    2ded:	48 8d 85 80 04 00 00 	lea    0x480(%rbp),%rax
    2df4:	49 89 44 24 80       	mov    %rax,-0x80(%r12)
    2df9:	8b 44 24 20          	mov    0x20(%rsp),%eax
              data[0].id = dataid++;
    2dfd:	44 89 b5 18 04 00 00 	mov    %r14d,0x418(%rbp)
              data[1].id = dataid++;
    2e04:	41 83 c6 02          	add    $0x2,%r14d
    2e08:	41 89 44 24 b4       	mov    %eax,-0x4c(%r12)
    2e0d:	89 c1                	mov    %eax,%ecx
    2e0f:	31 c0                	xor    %eax,%eax
              data[1].a = x;
    2e11:	89 bd 8c 08 00 00    	mov    %edi,0x88c(%rbp)
    2e17:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].lower = &data[0];
    2e1c:	49 89 ac 24 00 ff ff ff 	mov    %rbp,-0x100(%r12)
              mailboxes[b].pending_higher = NULL;
    2e24:	49 c7 44 24 90 00 00 00 00 	movq   $0x0,-0x70(%r12)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2e2d:	41 c7 44 24 b0 01 00 00 00 	movl   $0x1,-0x50(%r12)
              data[1].kind = MAILBOX_HIGHER;
    2e36:	c7 85 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%rbp)
              data[1].b = y;
    2e40:	44 89 ad 90 08 00 00 	mov    %r13d,0x890(%rbp)
              data[1].c = b;
    2e47:	89 9d 94 08 00 00    	mov    %ebx,0x894(%rbp)
              data[0].finished_reading = 1;
    2e4d:	c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rbp)
              data[1].finished_reading = 1;
    2e57:	c7 85 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%rbp)
    2e61:	e8 2a f6 ff ff       	call   2490 <__printf_chk@plt>
              data[0].messages = messages;
    2e66:	4c 8b 14 24          	mov    (%rsp),%r10
              data[0].messages_count = 0;
    2e6a:	66 0f 6f 15 7e 70 00 00 	movdqa 0x707e(%rip),%xmm2        # 9ef0 <_IO_stdin_used+0xef0>
              data[1].messages = messages2;
    2e72:	4c 89 bd 80 04 00 00 	mov    %r15,0x480(%rbp)
              data[0].messages = messages;
    2e79:	4c 89 55 00          	mov    %r10,0x0(%rbp)
              data[0].messages_count = 0;
    2e7d:	0f 29 95 80 00 00 00 	movaps %xmm2,0x80(%rbp)
              data[1].messages_count = 0;
    2e84:	0f 29 95 00 05 00 00 	movaps %xmm2,0x500(%rbp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e8b:	85 db                	test   %ebx,%ebx
    2e8d:	75 0a                	jne    2e99 <main+0x7d9>
    2e8f:	bb 01 00 00 00       	mov    $0x1,%ebx
    2e94:	e9 c2 fe ff ff       	jmp    2d5b <main+0x69b>
          char *message = malloc(sizeof(char) * 256);
    2e99:	be 01 00 00 00       	mov    $0x1,%esi
    2e9e:	bf 00 01 00 00       	mov    $0x100,%edi
    2ea3:	4c 8b 74 24 48       	mov    0x48(%rsp),%r14
    2ea8:	83 44 24 28 04       	addl   $0x4,0x28(%rsp)
    2ead:	e8 2e f5 ff ff       	call   23e0 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2eb2:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2eb7:	48 89 c5             	mov    %rax,%rbp
          struct Message *messaged = malloc(sizeof(struct Message));
    2eba:	e8 91 f5 ff ff       	call   2450 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2ebf:	48 83 ec 08          	sub    $0x8,%rsp
    2ec3:	48 89 ef             	mov    %rbp,%rdi
    2ec6:	45 89 e9             	mov    %r13d,%r9d
    2ec9:	6a 00                	push   $0x0
    2ecb:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
    2ed0:	49 89 c4             	mov    %rax,%r12
    2ed3:	ba 00 01 00 00       	mov    $0x100,%edx
    2ed8:	48 8d 0d e9 6a 00 00 	lea    0x6ae9(%rip),%rcx        # 99c8 <_IO_stdin_used+0x9c8>
    2edf:	be 01 00 00 00       	mov    $0x1,%esi
    2ee4:	31 c0                	xor    %eax,%eax
    2ee6:	e8 b5 f6 ff ff       	call   25a0 <__sprintf_chk@plt>
          messaged->task_index = y;
    2eeb:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
          thread_data[x].tasks[y].swap = swap;
    2ef0:	49 8b 56 38          	mov    0x38(%r14),%rdx
          messaged->message = message;
    2ef4:	49 89 2c 24          	mov    %rbp,(%r12)
          thread_data[x].tasks[y].swap = swap;
    2ef8:	48 8b 6c 24 40       	mov    0x40(%rsp),%rbp
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2efd:	be 20 00 00 00       	mov    $0x20,%esi
    2f02:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->group = k;
    2f07:	41 c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%r12)
          messaged->task_index = y;
    2f10:	49 89 44 24 10       	mov    %rax,0x10(%r12)
          messaged->thread_index = thread_data[x].real_thread_index;
    2f15:	49 63 46 08          	movslq 0x8(%r14),%rax
          thread_data[x].tasks[y].swap = swap;
    2f19:	48 01 d5             	add    %rdx,%rbp
    2f1c:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
          messaged->thread_index = thread_data[x].real_thread_index;
    2f21:	49 89 44 24 08       	mov    %rax,0x8(%r12)
          thread_data[x].tasks[y].swap = swap;
    2f26:	8b 44 24 28          	mov    0x28(%rsp),%eax
          thread_data[x].tasks[y].group = k;
    2f2a:	c7 85 9c 01 00 00 00 00 00 00 	movl   $0x0,0x19c(%rbp)
          thread_data[x].tasks[y].swap = swap;
    2f34:	89 85 a0 01 00 00    	mov    %eax,0x1a0(%rbp)
          swap += 1;
    2f3a:	83 c0 01             	add    $0x1,%eax
    2f3d:	89 44 24 28          	mov    %eax,0x28(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2f41:	41 8d 45 01          	lea    0x1(%r13),%eax
    2f45:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2f48:	c7 45 00 41 00 00 00 	movl   $0x41,0x0(%rbp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2f4f:	89 85 98 01 00 00    	mov    %eax,0x198(%rbp)
          thread_data[x].tasks[y].message = messaged;
    2f55:	4c 89 a5 90 01 00 00 	mov    %r12,0x190(%rbp)
          thread_data[x].tasks[y].sending = 1;
    2f5c:	c7 85 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbp)
          thread_data[x].tasks[y].snapshot_count = 99;
    2f66:	48 c7 85 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f71:	e8 6a f4 ff ff       	call   23e0 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2f76:	48 c7 85 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f81:	48 89 85 50 01 00 00 	mov    %rax,0x150(%rbp)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2f88:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    2f8d:	48 8b 00             	mov    (%rax),%rax
    2f90:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2f93:	49 39 c6             	cmp    %rax,%r14
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2f96:	48 89 85 28 01 00 00 	mov    %rax,0x128(%rbp)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2f9d:	89 8d 30 01 00 00    	mov    %ecx,0x130(%rbp)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2fa3:	5a                   	pop    %rdx
    2fa4:	59                   	pop    %rcx
    2fa5:	48 8b 14 24          	mov    (%rsp),%rdx
    2fa9:	0f 85 71 11 00 00    	jne    4120 <main+0x1a60>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2faf:	66 0f 6f 25 49 6f 00 00 	movdqa 0x6f49(%rip),%xmm4        # 9f00 <_IO_stdin_used+0xf00>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2fb7:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
          thread_data[x].tasks[y].available = 1;
    2fbb:	48 8b 05 5e 6f 00 00 	mov    0x6f5e(%rip),%rax        # 9f20 <_IO_stdin_used+0xf20>
          thread_data[x].tasks[y].arrived = 0;
    2fc2:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
          thread_data[x].tasks[y].worker_count = thread_count;
    2fcc:	c7 85 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rbp)
          thread_data[x].tasks[y].available = 1;
    2fd6:	48 89 85 44 01 00 00 	mov    %rax,0x144(%rbp)
          thread_data[x].tasks[y].thread_count = 2;
    2fdd:	0f 11 a5 34 01 00 00 	movups %xmm4,0x134(%rbp)
          if (y == barrier_count - 1) {
    2fe4:	41 83 fd 01          	cmp    $0x1,%r13d
    2fe8:	0f 84 17 01 00 00    	je     3105 <main+0xa45>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    2fee:	45 85 ed             	test   %r13d,%r13d
    2ff1:	0f 84 f8 00 00 00    	je     30ef <main+0xa2f>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    2ff7:	89 d8                	mov    %ebx,%eax
    2ff9:	49 89 ec             	mov    %rbp,%r12
    2ffc:	4c 89 f3             	mov    %r14,%rbx
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    2fff:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    3004:	41 89 c6             	mov    %eax,%r14d
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3007:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    300c:	48 8d 05 1d 47 00 00 	lea    0x471d(%rip),%rax        # 7730 <barriered_work>
    3013:	48 89 d5             	mov    %rdx,%rbp
    3016:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
    for (int d = 0 ; d < threads_per_group ; d++) {
    301e:	48 81 c3 30 01 00 00 	add    $0x130,%rbx
        thread_data[x].buffers_count = buffers_per_thread;
    3025:	c7 43 9c 01 00 00 00 	movl   $0x1,-0x64(%rbx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    302c:	e8 af f3 ff ff       	call   23e0 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3031:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    3036:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
        }
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    303b:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3040:	48 89 83 20 ff ff ff 	mov    %rax,-0xe0(%rbx)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3047:	4c 89 f9             	mov    %r15,%rcx
    304a:	48 c1 e1 04          	shl    $0x4,%rcx
    304e:	48 01 f9             	add    %rdi,%rcx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3051:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3056:	48 89 08             	mov    %rcx,(%rax)
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3059:	e8 82 f3 ff ff       	call   23e0 <calloc@plt>
        for (int b = 0 ; b < io_threads; b++) {	
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    305e:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3063:	66 0f 6f 74 24 70    	movdqa 0x70(%rsp),%xmm6
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3069:	48 89 83 28 ff ff ff 	mov    %rax,-0xd8(%rbx)
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    3070:	48 8d 4f 10          	lea    0x10(%rdi),%rcx
    3074:	48 89 38             	mov    %rdi,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3077:	48 83 c7 20          	add    $0x20,%rdi
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    307b:	48 89 48 08          	mov    %rcx,0x8(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    307f:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    3084:	48 89 7c 24 58       	mov    %rdi,0x58(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3089:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    308c:	0f 11 b5 18 05 00 00 	movups %xmm6,0x518(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    3093:	c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    309d:	48 89 85 28 05 00 00 	mov    %rax,0x528(%rbp)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    30a4:	c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbp)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    30ae:	c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    30b8:	8b 83 d4 fe ff ff    	mov    -0x12c(%rbx),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    30be:	c7 85 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    30c8:	89 85 30 05 00 00    	mov    %eax,0x530(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
    30ce:	48 8b 05 4b 6e 00 00 	mov    0x6e4b(%rip),%rax        # 9f20 <_IO_stdin_used+0xf20>
    30d5:	48 89 85 44 05 00 00 	mov    %rax,0x544(%rbp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    30dc:	4d 85 ff             	test   %r15,%r15
    30df:	75 32                	jne    3113 <main+0xa53>
    30e1:	48 c7 44 24 10 01 00 00 00 	movq   $0x1,0x10(%rsp)
    30ea:	e9 31 fa ff ff       	jmp    2b20 <main+0x460>
    30ef:	48 8d 05 0a 4c 00 00 	lea    0x4c0a(%rip),%rax        # 7d00 <barriered_work_ingest_andwork>
            thread_data[x].tasks[y].run = barriered_work; 
    30f6:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    30fd:	41 89 dd             	mov    %ebx,%r13d
    3100:	e9 0b fc ff ff       	jmp    2d10 <main+0x650>
    3105:	48 8d 05 24 46 00 00 	lea    0x4624(%rip),%rax        # 7730 <barriered_work>
    310c:	bb 02 00 00 00       	mov    $0x2,%ebx
    3111:	eb e3                	jmp    30f6 <main+0xa36>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3113:	bf 00 04 00 00       	mov    $0x400,%edi
    3118:	be 08 00 00 00       	mov    $0x8,%esi
    311d:	31 ed                	xor    %ebp,%ebp
    311f:	e8 bc f2 ff ff       	call   23e0 <calloc@plt>
    3124:	49 89 c4             	mov    %rax,%r12
  int datas_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3127:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    312c:	48 8d 58 38          	lea    0x38(%rax),%rbx
    3130:	48 05 98 02 00 00    	add    $0x298,%rax
    3136:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    313b:	48 89 df             	mov    %rbx,%rdi
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    313e:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    3142:	45 85 c0             	test   %r8d,%r8d
    3145:	7e 57                	jle    319e <main+0xade>
    3147:	48 8b 17             	mov    (%rdi),%rdx
    314a:	49 63 f0             	movslq %r8d,%rsi
    314d:	48 63 c5             	movslq %ebp,%rax
    3150:	48 c1 e6 09          	shl    $0x9,%rsi
    3154:	49 8d 0c c4          	lea    (%r12,%rax,8),%rcx
    3158:	48 01 d6             	add    %rdx,%rsi
    315b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3160:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3167:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    316e:	48 83 c1 20          	add    $0x20,%rcx
    3172:	f3 0f 7e 80 00 01 00 00 	movq   0x100(%rax),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    317a:	f3 0f 7e 08          	movq   (%rax),%xmm1
    317e:	0f 16 80 80 01 00 00 	movhps 0x180(%rax),%xmm0
    3185:	0f 16 88 80 00 00 00 	movhps 0x80(%rax),%xmm1
    318c:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    3190:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3194:	48 39 d6             	cmp    %rdx,%rsi
    3197:	75 c7                	jne    3160 <main+0xaa0>
    3199:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    319e:	48 81 c7 30 01 00 00 	add    $0x130,%rdi
    31a5:	48 39 7c 24 08       	cmp    %rdi,0x8(%rsp)
    31aa:	75 92                	jne    313e <main+0xa7e>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    31ac:	48 8d 3d 3c 62 00 00 	lea    0x623c(%rip),%rdi        # 93ef <_IO_stdin_used+0x3ef>
    31b3:	e8 58 f1 ff ff       	call   2310 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    31b8:	48 8d 3d 47 62 00 00 	lea    0x6247(%rip),%rdi        # 9406 <_IO_stdin_used+0x406>
    31bf:	48 8d 35 3e 62 00 00 	lea    0x623e(%rip),%rsi        # 9404 <_IO_stdin_used+0x404>
    31c6:	e8 15 f3 ff ff       	call   24e0 <fopen@plt>
    31cb:	48 89 c7             	mov    %rax,%rdi
  for (int x = 0 ; x < datas_size; x++) {
    31ce:	85 ed                	test   %ebp,%ebp
    31d0:	0f 8e 85 00 00 00    	jle    325b <main+0xb9b>
    31d6:	48 8d 05 60 62 00 00 	lea    0x6260(%rip),%rax        # 943d <_IO_stdin_used+0x43d>
    31dd:	48 63 ed             	movslq %ebp,%rbp
    31e0:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    31e5:	4c 8d 2d 45 62 00 00 	lea    0x6245(%rip),%r13        # 9431 <_IO_stdin_used+0x431>
    31ec:	48 89 04 24          	mov    %rax,(%rsp)
    31f0:	4d 8d 3c ec          	lea    (%r12,%rbp,8),%r15
    31f4:	48 89 fb             	mov    %rdi,%rbx
    char * c = calloc(250, sizeof(char));
    31f7:	be 01 00 00 00       	mov    $0x1,%esi
    31fc:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    3201:	49 83 c4 08          	add    $0x8,%r12
    char * c = calloc(250, sizeof(char));
    3205:	e8 d6 f1 ff ff       	call   23e0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    320a:	4c 89 e9             	mov    %r13,%rcx
    320d:	ba fa 00 00 00       	mov    $0xfa,%edx
    3212:	be 01 00 00 00       	mov    $0x1,%esi
    3217:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    321a:	49 8b 44 24 f8       	mov    -0x8(%r12),%rax
    321f:	48 89 ef             	mov    %rbp,%rdi
    3222:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3229:	31 c0                	xor    %eax,%eax
    322b:	e8 70 f3 ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3230:	48 8b 34 24          	mov    (%rsp),%rsi
    3234:	48 89 ea             	mov    %rbp,%rdx
    3237:	31 c0                	xor    %eax,%eax
    3239:	bf 01 00 00 00       	mov    $0x1,%edi
    323e:	e8 4d f2 ff ff       	call   2490 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3243:	48 89 de             	mov    %rbx,%rsi
    3246:	48 89 ef             	mov    %rbp,%rdi
    3249:	e8 52 f1 ff ff       	call   23a0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    324e:	4d 39 e7             	cmp    %r12,%r15
    3251:	75 a4                	jne    31f7 <main+0xb37>
    3253:	48 89 df             	mov    %rbx,%rdi
    3256:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    325b:	e8 e0 f0 ff ff       	call   2340 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3260:	48 8d 3d a8 61 00 00 	lea    0x61a8(%rip),%rdi        # 940f <_IO_stdin_used+0x40f>
    3267:	49 89 dc             	mov    %rbx,%r12
    326a:	4c 8d 3d e1 61 00 00 	lea    0x61e1(%rip),%r15        # 9452 <_IO_stdin_used+0x452>
    3271:	e8 9a f0 ff ff       	call   2310 <puts@plt>
    3276:	31 d2                	xor    %edx,%edx
    3278:	48 8d 35 a8 61 00 00 	lea    0x61a8(%rip),%rsi        # 9427 <_IO_stdin_used+0x427>
    327f:	31 c0                	xor    %eax,%eax
    3281:	bf 01 00 00 00       	mov    $0x1,%edi
    3286:	4c 8d 2d d0 61 00 00 	lea    0x61d0(%rip),%r13        # 945d <_IO_stdin_used+0x45d>
    328d:	e8 fe f1 ff ff       	call   2490 <__printf_chk@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    3292:	c7 44 24 40 00 00 00 00 	movl   $0x0,0x40(%rsp)
    329a:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    329f:	8b 54 24 40          	mov    0x40(%rsp),%edx
    32a3:	48 8d 35 96 61 00 00 	lea    0x6196(%rip),%rsi        # 9440 <_IO_stdin_used+0x440>
    32aa:	bf 01 00 00 00       	mov    $0x1,%edi
    32af:	31 c0                	xor    %eax,%eax
    32b1:	89 d1                	mov    %edx,%ecx
    32b3:	e8 d8 f1 ff ff       	call   2490 <__printf_chk@plt>
    32b8:	44 89 74 24 20       	mov    %r14d,0x20(%rsp)
    32bd:	45 31 c0             	xor    %r8d,%r8d
    32c0:	44 89 c2             	mov    %r8d,%edx
    32c3:	4c 89 fe             	mov    %r15,%rsi
    32c6:	bf 01 00 00 00       	mov    $0x1,%edi
    32cb:	31 c0                	xor    %eax,%eax
    32cd:	4c 89 04 24          	mov    %r8,(%rsp)
    32d1:	31 ed                	xor    %ebp,%ebp
    32d3:	e8 b8 f1 ff ff       	call   2490 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    32d8:	48 8b 1c 24          	mov    (%rsp),%rbx
    32dc:	48 c1 e3 09          	shl    $0x9,%rbx
          char * mailbox_kind = calloc(100, sizeof(char));
    32e0:	be 01 00 00 00       	mov    $0x1,%esi
    32e5:	bf 64 00 00 00       	mov    $0x64,%edi
    32ea:	41 89 ee             	mov    %ebp,%r14d
    32ed:	e8 ee f0 ff ff       	call   23e0 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    32f2:	4d 8b 04 24          	mov    (%r12),%r8
    32f6:	48 89 ef             	mov    %rbp,%rdi
          char * mailbox_kind = calloc(100, sizeof(char));
    32f9:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    32fc:	48 c1 e7 08          	shl    $0x8,%rdi
    3300:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3308:	48 01 f8             	add    %rdi,%rax
    330b:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    3311:	83 fe 02             	cmp    $0x2,%esi
    3314:	74 5f                	je     3375 <main+0xcb5>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    3316:	83 fe 01             	cmp    $0x1,%esi
    3319:	74 74                	je     338f <main+0xccf>
    331b:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    3322:	44 89 f2             	mov    %r14d,%edx
    3325:	31 c0                	xor    %eax,%eax
    3327:	4c 89 ee             	mov    %r13,%rsi
    332a:	bf 01 00 00 00       	mov    $0x1,%edi
    332f:	e8 5c f1 ff ff       	call   2490 <__printf_chk@plt>
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3334:	48 85 ed             	test   %rbp,%rbp
    3337:	75 07                	jne    3340 <main+0xc80>
    3339:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    333e:	eb a0                	jmp    32e0 <main+0xc20>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3340:	4c 8b 04 24          	mov    (%rsp),%r8
    3344:	49 83 c0 01          	add    $0x1,%r8
    3348:	49 83 f8 03          	cmp    $0x3,%r8
    334c:	0f 85 6e ff ff ff    	jne    32c0 <main+0xc00>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3352:	8b 44 24 40          	mov    0x40(%rsp),%eax
    3356:	48 89 6c 24 30       	mov    %rbp,0x30(%rsp)
    335b:	49 81 c4 30 01 00 00 	add    $0x130,%r12
    3362:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
    3367:	85 c0                	test   %eax,%eax
    3369:	75 41                	jne    33ac <main+0xcec>
    336b:	44 89 74 24 40       	mov    %r14d,0x40(%rsp)
    3370:	e9 2a ff ff ff       	jmp    329f <main+0xbdf>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3375:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    337f:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3382:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    338a:	48 01 f8             	add    %rdi,%rax
    338d:	eb 8c                	jmp    331b <main+0xc5b>
    338f:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3395:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    339c:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    33a4:	48 01 f8             	add    %rdi,%rax
    33a7:	e9 6f ff ff ff       	jmp    331b <main+0xc5b>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    33ac:	ba 03 00 00 00       	mov    $0x3,%edx
    33b1:	48 8d 35 c0 60 00 00 	lea    0x60c0(%rip),%rsi        # 9478 <_IO_stdin_used+0x478>
    33b8:	bf 01 00 00 00       	mov    $0x1,%edi
    33bd:	31 c0                	xor    %eax,%eax
    33bf:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    33c4:	e8 c7 f0 ff ff       	call   2490 <__printf_chk@plt>
  

  printf("io index = %d\n", io_index);
  int io_mode = 0;
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    33c9:	be 08 00 00 00       	mov    $0x8,%esi
    33ce:	bf 02 00 00 00       	mov    $0x2,%edi
    33d3:	e8 08 f0 ff ff       	call   23e0 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    33d8:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    33dd:	be 08 00 00 00       	mov    $0x8,%esi
    33e2:	bf 02 00 00 00       	mov    $0x2,%edi
    my_thread_data[0] = &thread_data[x]; 
    33e7:	4d 8d a7 90 03 00 00 	lea    0x390(%r15),%r12
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    33ee:	4c 89 78 08          	mov    %r15,0x8(%rax)
    33f2:	4d 8d af 30 01 00 00 	lea    0x130(%r15),%r13

    io_mode = (io_mode + 1) % 2;
    thread_data[x].threads = my_thread_data;
    33f9:	49 89 87 a8 03 00 00 	mov    %rax,0x3a8(%r15)
    my_thread_data[0] = &thread_data[x]; 
    3400:	4d 8d b7 c0 04 00 00 	lea    0x4c0(%r15),%r14
    thread_data[x].thread_count = 2;
    3407:	41 c7 87 b8 03 00 00 02 00 00 00 	movl   $0x2,0x3b8(%r15)
    thread_data[x].thread_index = 0;
    3412:	41 c7 87 94 03 00 00 00 00 00 00 	movl   $0x0,0x394(%r15)
    thread_data[x].task_count = total_barrier_count;
    341d:	41 c7 87 d0 03 00 00 03 00 00 00 	movl   $0x3,0x3d0(%r15)
    my_thread_data[0] = &thread_data[x]; 
    3428:	4c 89 20             	mov    %r12,(%rax)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    342b:	e8 b0 ef ff ff       	call   23e0 <calloc@plt>
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3430:	be 38 00 00 00       	mov    $0x38,%esi
    3435:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[x].thread_count = 2;
    343a:	41 c7 87 e8 04 00 00 02 00 00 00 	movl   $0x2,0x4e8(%r15)
    thread_data[x].threads = my_thread_data;
    3445:	49 89 87 d8 04 00 00 	mov    %rax,0x4d8(%r15)
    my_thread_data[0] = &thread_data[x]; 
    344c:	4c 89 30             	mov    %r14,(%rax)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    344f:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3453:	49 8b 47 38          	mov    0x38(%r15),%rax
    thread_data[x].thread_index = 0;
    3457:	41 c7 87 c4 04 00 00 00 00 00 00 	movl   $0x0,0x4c4(%r15)
    thread_data[x].task_count = total_barrier_count;
    3462:	41 c7 87 00 05 00 00 03 00 00 00 	movl   $0x3,0x500(%r15)
    thread_data[n].tasks[0].scheduled = 1;
    346d:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3477:	49 8b 87 68 01 00 00 	mov    0x168(%r15),%rax
    347e:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3488:	e8 53 ef ff ff       	call   23e0 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    348d:	be 38 00 00 00       	mov    $0x38,%esi
    3492:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3497:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    349b:	e8 40 ef ff ff       	call   23e0 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34a0:	be 38 00 00 00       	mov    $0x38,%esi
    34a5:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34aa:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34af:	e8 2c ef ff ff       	call   23e0 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    34b4:	be 08 00 00 00       	mov    $0x8,%esi
    34b9:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34be:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    34c3:	e8 18 ef ff ff       	call   23e0 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    34c8:	be 08 00 00 00       	mov    $0x8,%esi
    34cd:	bf 07 00 00 00       	mov    $0x7,%edi
  thread_data[timer_threadi].type = TIMER;
    34d2:	41 c7 87 6c 02 00 00 00 00 00 00 	movl   $0x0,0x26c(%r15)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    34dd:	48 89 c5             	mov    %rax,%rbp
  thread_data[timer_threadi].task_count = total_barrier_count;
    34e0:	48 8b 05 41 6a 00 00 	mov    0x6a41(%rip),%rax        # 9f28 <_IO_stdin_used+0xf28>
    34e7:	49 89 87 a0 02 00 00 	mov    %rax,0x2a0(%r15)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    34ee:	e8 ed ee ff ff       	call   23e0 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    34f3:	4c 89 ff             	mov    %r15,%rdi
    34f6:	48 8d 35 8a 5f 00 00 	lea    0x5f8a(%rip),%rsi        # 9487 <_IO_stdin_used+0x487>
    34fd:	4c 89 70 20          	mov    %r14,0x20(%rax)
    3501:	49 89 fe             	mov    %rdi,%r14
    3504:	48 8d bf f0 05 00 00 	lea    0x5f0(%rdi),%rdi
    350b:	48 89 78 28          	mov    %rdi,0x28(%rax)
    350f:	49 8d 96 20 07 00 00 	lea    0x720(%r14),%rdx
    3516:	48 89 7c 24 50       	mov    %rdi,0x50(%rsp)
  }
  thread_data[timer_threadi].threads = my_thread_data;
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    351b:	48 8b 3d f6 69 00 00 	mov    0x69f6(%rip),%rdi        # 9f18 <_IO_stdin_used+0xf18>
    my_thread_data[n] = &thread_data[n]; 
    3522:	4c 89 38             	mov    %r15,(%rax)
    3525:	49 81 c7 60 02 00 00 	add    $0x260,%r15
    352c:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3530:	4c 89 78 10          	mov    %r15,0x10(%rax)
    3534:	48 89 50 30          	mov    %rdx,0x30(%rax)
    3538:	ba 02 00 00 00       	mov    $0x2,%edx
  thread_data[timer_threadi].threads = my_thread_data;
    353d:	49 89 86 78 02 00 00 	mov    %rax,0x278(%r14)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3544:	49 89 be 88 02 00 00 	mov    %rdi,0x288(%r14)
    354b:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    3550:	4c 89 60 18          	mov    %r12,0x18(%rax)
    3554:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3556:	41 c7 86 90 02 00 00 02 00 00 00 	movl   $0x2,0x290(%r14)
  thread_data[timer_threadi].thread_index = 0;
    3561:	41 c7 86 64 02 00 00 00 00 00 00 	movl   $0x0,0x264(%r14)
    356c:	e8 1f ef ff ff       	call   2490 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3571:	48 8b 34 24          	mov    (%rsp),%rsi
    3575:	48 8d 7d 10          	lea    0x10(%rbp),%rdi
    3579:	4c 89 f9             	mov    %r15,%rcx
    357c:	48 8d 15 7d 0e 00 00 	lea    0xe7d(%rip),%rdx        # 4400 <timer_thread>
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
      thread_data[x].running = 1;
    3583:	4d 89 f7             	mov    %r14,%r15
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3586:	48 83 c6 70          	add    $0x70,%rsi
    358a:	e8 21 ef ff ff       	call   24b0 <pthread_create@plt>
    358f:	31 c9                	xor    %ecx,%ecx
    3591:	31 d2                	xor    %edx,%edx
    3593:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].type = WORKER;
    3598:	41 c7 46 0c 01 00 00 00 	movl   $0x1,0xc(%r14)
    35a0:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    35a2:	41 c7 46 44 01 00 00 00 	movl   $0x1,0x44(%r14)
    35aa:	4c 8d 35 47 64 00 00 	lea    0x6447(%rip),%r14        # 99f8 <_IO_stdin_used+0x9f8>
    35b1:	4c 89 f6             	mov    %r14,%rsi
    35b4:	e8 d7 ee ff ff       	call   2490 <__printf_chk@plt>
    35b9:	31 c9                	xor    %ecx,%ecx
    35bb:	ba 01 00 00 00       	mov    $0x1,%edx
    35c0:	4c 89 f6             	mov    %r14,%rsi
      thread_data[x].type = WORKER;
    35c3:	41 c7 87 3c 01 00 00 01 00 00 00 	movl   $0x1,0x13c(%r15)
    35ce:	bf 01 00 00 00       	mov    $0x1,%edi
    35d3:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    35d5:	41 c7 87 74 01 00 00 01 00 00 00 	movl   $0x1,0x174(%r15)
    35e0:	4d 89 ef             	mov    %r13,%r15
    35e3:	4d 89 e5             	mov    %r12,%r13
    35e6:	e8 a5 ee ff ff       	call   2490 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      // pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
      // pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    }
  }
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    35eb:	be 08 00 00 00       	mov    $0x8,%esi
    35f0:	bf 02 00 00 00       	mov    $0x2,%edi
    35f5:	e8 e6 ed ff ff       	call   23e0 <calloc@plt>

  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    35fa:	be d8 00 00 00       	mov    $0xd8,%esi
    35ff:	bf 01 00 00 00       	mov    $0x1,%edi
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    3604:	49 89 c6             	mov    %rax,%r14
    3607:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    360c:	e8 cf ed ff ff       	call   23e0 <calloc@plt>
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3611:	be d8 00 00 00       	mov    $0xd8,%esi
    3616:	bf 01 00 00 00       	mov    $0x1,%edi
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    361b:	49 89 06             	mov    %rax,(%r14)
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    361e:	e8 bd ed ff ff       	call   23e0 <calloc@plt>

  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    3623:	be 10 00 00 00       	mov    $0x10,%esi
    3628:	bf 02 00 00 00       	mov    $0x2,%edi
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    362d:	49 89 46 08          	mov    %rax,0x8(%r14)
  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    3631:	e8 aa ed ff ff       	call   23e0 <calloc@plt>
    3636:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    363b:	49 89 c6             	mov    %rax,%r14
  long iomailboxes_size = 10000;
  for (int x = 0 ; x < io_threads; x++) {
    363e:	48 8d 40 20          	lea    0x20(%rax),%rax
    3642:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    3647:	48 89 04 24          	mov    %rax,(%rsp)
    364b:	4c 89 f5             	mov    %r14,%rbp
    iomailboxes[x].count = iomailboxes_size;
    364e:	c7 45 00 10 27 00 00 	movl   $0x2710,0x0(%rbp)
    iomailboxes[x].buffer = calloc(iomailboxes_size, sizeof(struct Buffer));
    3655:	be 28 00 00 00       	mov    $0x28,%esi
    365a:	bf 10 27 00 00       	mov    $0x2710,%edi
    365f:	e8 7c ed ff ff       	call   23e0 <calloc@plt>
    3664:	48 89 45 08          	mov    %rax,0x8(%rbp)
    3668:	48 89 c3             	mov    %rax,%rbx
    for (int y = 0 ; y < iomailboxes_size; y++) {
    366b:	4c 8d 60 08          	lea    0x8(%rax),%r12
    366f:	48 81 c3 88 1a 06 00 	add    $0x61a88,%rbx
    3676:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      iomailboxes[x].buffer[y].available = 0;
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3680:	be 20 00 00 00       	mov    $0x20,%esi
    3685:	bf 64 00 00 00       	mov    $0x64,%edi
    for (int y = 0 ; y < iomailboxes_size; y++) {
    368a:	49 83 c4 28          	add    $0x28,%r12
      iomailboxes[x].buffer[y].available = 0;
    368e:	41 c7 44 24 d8 00 00 00 00 	movl   $0x0,-0x28(%r12)
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
    3697:	41 c7 44 24 e8 64 00 00 00 	movl   $0x64,-0x18(%r12)
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    36a0:	e8 3b ed ff ff       	call   23e0 <calloc@plt>
    36a5:	49 89 44 24 e0       	mov    %rax,-0x20(%r12)
    for (int y = 0 ; y < iomailboxes_size; y++) {
    36aa:	4c 39 e3             	cmp    %r12,%rbx
    36ad:	75 d1                	jne    3680 <main+0xfc0>
  for (int x = 0 ; x < io_threads; x++) {
    36af:	48 83 c5 10          	add    $0x10,%rbp
    36b3:	48 39 2c 24          	cmp    %rbp,(%rsp)
    36b7:	75 95                	jne    364e <main+0xf8e>
  char * recv_identity = "recv-thread";
  char * unknown_identity = "unknown-thread";
  int counter = 0;

  int dataeventfds[2];
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
    36b9:	be 00 08 00 00       	mov    $0x800,%esi
    36be:	31 ff                	xor    %edi,%edi
    36c0:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    36c5:	4d 89 ec             	mov    %r13,%r12
    36c8:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    36cd:	4d 89 fd             	mov    %r15,%r13
    36d0:	4d 89 e7             	mov    %r12,%r15
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);

  for (int x = io_index ; x < io_index + io_threads ; x++) {
    36d3:	41 bc 03 00 00 00    	mov    $0x3,%r12d
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
    36d9:	e8 32 ee ff ff       	call   2510 <eventfd@plt>
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);
    36de:	be 00 08 00 00       	mov    $0x800,%esi
    36e3:	31 ff                	xor    %edi,%edi
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
    36e5:	89 04 24             	mov    %eax,(%rsp)
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);
    36e8:	e8 23 ee ff ff       	call   2510 <eventfd@plt>
    36ed:	48 89 5c 24 58       	mov    %rbx,0x58(%rsp)
    36f2:	89 44 24 10          	mov    %eax,0x10(%rsp)
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    36f6:	48 8d 45 18          	lea    0x18(%rbp),%rax
    36fa:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    36ff:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3704:	48 05 a8 00 00 00    	add    $0xa8,%rax
    370a:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    370f:	48 8b 05 1a 68 00 00 	mov    0x681a(%rip),%rax        # 9f30 <_IO_stdin_used+0xf30>
    thread_data[x].io_mode = myring;
    thread_data[x].my_io = myring;
    thread_data[x].other_io = otherring;
    thread_data[x].iomailboxes = iomailboxes; 
    printf("%d myring %d other is %d\n", x, myring, otherring);
    thread_data[x].ring = rings[myring]; 
    3716:	48 8b 5c 24 48       	mov    0x48(%rsp),%rbx
    thread_data[x].type = IO;
    371b:	41 c7 47 0c 02 00 00 00 	movl   $0x2,0xc(%r15)
    thread_data[x].task_count = 0;
    3723:	49 89 47 40          	mov    %rax,0x40(%r15)
    thread_data[x].ring = rings[myring]; 
    3727:	44 89 e0             	mov    %r12d,%eax
    372a:	83 e0 01             	and    $0x1,%eax
    372d:	48 8d 1c c3          	lea    (%rbx,%rax,8),%rbx
    if (myring == IO_MODE_SEND) {
    3731:	41 f6 c4 01          	test   $0x1,%r12b
    3735:	0f 84 22 01 00 00    	je     385d <main+0x119d>
      thread_data[x].identity = recv_identity;
    373b:	48 8d 05 85 5e 00 00 	lea    0x5e85(%rip),%rax        # 95c7 <_IO_stdin_used+0x5c7>
    3742:	b9 01 00 00 00       	mov    $0x1,%ecx
    3747:	44 89 e2             	mov    %r12d,%edx
    374a:	45 31 c0             	xor    %r8d,%r8d
    374d:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
    thread_data[x].other_io = otherring;
    3754:	31 c0                	xor    %eax,%eax
    3756:	48 8d 35 76 5e 00 00 	lea    0x5e76(%rip),%rsi        # 95d3 <_IO_stdin_used+0x5d3>
    375d:	bf 01 00 00 00       	mov    $0x1,%edi
    3762:	41 89 87 18 01 00 00 	mov    %eax,0x118(%r15)
    3769:	31 c0                	xor    %eax,%eax
    thread_data[x].io_mode = myring;
    376b:	41 c7 87 0c 01 00 00 01 00 00 00 	movl   $0x1,0x10c(%r15)
    thread_data[x].my_io = myring;
    3776:	41 c7 87 1c 01 00 00 01 00 00 00 	movl   $0x1,0x11c(%r15)
    thread_data[x].iomailboxes = iomailboxes; 
    3781:	4d 89 b7 10 01 00 00 	mov    %r14,0x110(%r15)
    3788:	e8 03 ed ff ff       	call   2490 <__printf_chk@plt>
    thread_data[x].ring = rings[myring]; 
    378d:	48 8b 03             	mov    (%rbx),%rax
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3790:	be 00 08 00 00       	mov    $0x800,%esi
    3795:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = rings[myring]; 
    3797:	49 89 47 60          	mov    %rax,0x60(%r15)
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    379b:	e8 70 ed ff ff       	call   2510 <eventfd@plt>
    if (x % 2 == 0) {
      otherdataeventfd = dataeventfds[0];
      datafd = dataeventfds[1];
    } else {
      otherdataeventfd = dataeventfds[1];
      datafd = dataeventfds[0];
    37a0:	8b 14 24             	mov    (%rsp),%edx
      otherdataeventfd = dataeventfds[1];
    37a3:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
    thread_data[x]._eventfd = myeventfd; 
    37a7:	41 89 47 68          	mov    %eax,0x68(%r15)
    37ab:	48 8d 35 76 62 00 00 	lea    0x6276(%rip),%rsi        # 9a28 <_IO_stdin_used+0xa28>
    37b2:	bf 01 00 00 00       	mov    $0x1,%edi
    37b7:	31 c0                	xor    %eax,%eax
    37b9:	89 4c 24 70          	mov    %ecx,0x70(%rsp)
    37bd:	89 54 24 68          	mov    %edx,0x68(%rsp)
    37c1:	e8 ca ec ff ff       	call   2490 <__printf_chk@plt>
    }
    printf("my data event fd is %d other is %d\n", datafd, otherdataeventfd);
    thread_data[x].dataeventfd = datafd; 
    thread_data[x].otherdataeventfd = otherdataeventfd; 
    37c6:	8b 4c 24 70          	mov    0x70(%rsp),%ecx
    thread_data[x].dataeventfd = datafd; 
    37ca:	8b 54 24 68          	mov    0x68(%rsp),%edx
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    37ce:	be 08 00 00 00       	mov    $0x8,%esi
    37d3:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x].otherdataeventfd = otherdataeventfd; 
    37d8:	41 89 4f 70          	mov    %ecx,0x70(%r15)
    thread_data[x].dataeventfd = datafd; 
    37dc:	41 89 57 6c          	mov    %edx,0x6c(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    37e0:	e8 fb eb ff ff       	call   23e0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    37e5:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].thread_index = x;
    37ea:	45 89 67 04          	mov    %r12d,0x4(%r15)
    37ee:	44 89 e2             	mov    %r12d,%edx
    thread_data[x].threads = my_thread_data;
    37f1:	49 89 47 18          	mov    %rax,0x18(%r15)
    37f5:	48 8d 35 a9 5c 00 00 	lea    0x5ca9(%rip),%rsi        # 94a5 <_IO_stdin_used+0x4a5>
    37fc:	bf 01 00 00 00       	mov    $0x1,%edi
      my_thread_data[n] = &thread_data[n]; 
    3801:	48 89 18             	mov    %rbx,(%rax)
    3804:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3808:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_count = thread_count;
    380a:	41 c7 47 28 02 00 00 00 	movl   $0x2,0x28(%r15)
    3812:	e8 79 ec ff ff       	call   2490 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3817:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    381c:	4c 89 f9             	mov    %r15,%rcx
    381f:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3824:	48 8d 15 05 21 00 00 	lea    0x2105(%rip),%rdx        # 5930 <io_thread>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    382b:	49 81 c7 30 01 00 00 	add    $0x130,%r15
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3832:	48 89 df             	mov    %rbx,%rdi
    3835:	e8 76 ec ff ff       	call   24b0 <pthread_create@plt>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    383a:	48 89 d8             	mov    %rbx,%rax
    383d:	48 83 44 24 18 38    	addq   $0x38,0x18(%rsp)
    3843:	48 83 c0 08          	add    $0x8,%rax
    3847:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    384c:	41 83 fc 03          	cmp    $0x3,%r12d
    3850:	75 7e                	jne    38d0 <main+0x1210>
    3852:	41 bc 04 00 00 00    	mov    $0x4,%r12d
    3858:	e9 b2 fe ff ff       	jmp    370f <main+0x104f>
    385d:	48 8d 05 89 5d 00 00 	lea    0x5d89(%rip),%rax        # 95ed <_IO_stdin_used+0x5ed>
    3864:	31 c9                	xor    %ecx,%ecx
    thread_data[x].io_mode = myring;
    3866:	41 c7 87 0c 01 00 00 00 00 00 00 	movl   $0x0,0x10c(%r15)
    3871:	44 89 e2             	mov    %r12d,%edx
    3874:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
    387b:	41 b8 01 00 00 00    	mov    $0x1,%r8d
    3881:	bf 01 00 00 00       	mov    $0x1,%edi
    3886:	31 c0                	xor    %eax,%eax
    thread_data[x].iomailboxes = iomailboxes; 
    3888:	4d 89 b7 10 01 00 00 	mov    %r14,0x110(%r15)
    388f:	48 8d 35 3d 5d 00 00 	lea    0x5d3d(%rip),%rsi        # 95d3 <_IO_stdin_used+0x5d3>
    thread_data[x].my_io = myring;
    3896:	41 c7 87 1c 01 00 00 00 00 00 00 	movl   $0x0,0x11c(%r15)
    thread_data[x].other_io = otherring;
    38a1:	41 c7 87 18 01 00 00 01 00 00 00 	movl   $0x1,0x118(%r15)
    38ac:	e8 df eb ff ff       	call   2490 <__printf_chk@plt>
    thread_data[x].ring = rings[myring]; 
    38b1:	48 8b 03             	mov    (%rbx),%rax
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    38b4:	be 00 08 00 00       	mov    $0x800,%esi
    38b9:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = rings[myring]; 
    38bb:	49 89 47 60          	mov    %rax,0x60(%r15)
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    38bf:	e8 4c ec ff ff       	call   2510 <eventfd@plt>
      datafd = dataeventfds[1];
    38c4:	8b 54 24 10          	mov    0x10(%rsp),%edx
      otherdataeventfd = dataeventfds[0];
    38c8:	8b 0c 24             	mov    (%rsp),%ecx
    38cb:	e9 d7 fe ff ff       	jmp    37a7 <main+0x10e7>
    38d0:	ba 05 00 00 00       	mov    $0x5,%edx
    38d5:	bf 01 00 00 00       	mov    $0x1,%edi
    38da:	4c 8d 65 28          	lea    0x28(%rbp),%r12
    38de:	31 c0                	xor    %eax,%eax
    38e0:	48 8d 35 d5 5b 00 00 	lea    0x5bd5(%rip),%rsi        # 94bc <_IO_stdin_used+0x4bc>
    38e7:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    38ec:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    38f2:	e8 99 eb ff ff       	call   2490 <__printf_chk@plt>
    38f7:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    38fc:	4c 8b 74 24 50       	mov    0x50(%rsp),%r14
    3901:	48 05 18 01 00 00    	add    $0x118,%rax
    3907:	48 89 04 24          	mov    %rax,(%rsp)
    390b:	48 89 e8             	mov    %rbp,%rax
    390e:	48 89 dd             	mov    %rbx,%rbp
    3911:	48 89 c3             	mov    %rax,%rbx
    3914:	44 89 fa             	mov    %r15d,%edx
    3917:	48 8d 35 b4 5b 00 00 	lea    0x5bb4(%rip),%rsi        # 94d2 <_IO_stdin_used+0x4d2>
    391e:	bf 01 00 00 00       	mov    $0x1,%edi
    3923:	31 c0                	xor    %eax,%eax
    3925:	e8 66 eb ff ff       	call   2490 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    392a:	be 08 00 00 00       	mov    $0x8,%esi
    392f:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3934:	48 8b 05 f5 65 00 00 	mov    0x65f5(%rip),%rax        # 9f30 <_IO_stdin_used+0xf30>
    thread_data[x].type = EXTERNAL;
    393b:	41 c7 46 0c 03 00 00 00 	movl   $0x3,0xc(%r14)
    thread_data[x].task_count = 0;
    3943:	49 89 46 40          	mov    %rax,0x40(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3947:	e8 94 ea ff ff       	call   23e0 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    394c:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3954:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3959:	41 c7 86 cc 00 00 00 01 00 00 00 	movl   $0x1,0xcc(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3964:	49 89 46 50          	mov    %rax,0x50(%r14)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3968:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    396b:	bf 02 00 00 00       	mov    $0x2,%edi
    3970:	e8 6b ea ff ff       	call   23e0 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3975:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    397a:	4c 89 f1             	mov    %r14,%rcx
    397d:	4c 89 e7             	mov    %r12,%rdi
    thread_data[x].threads = my_thread_data;
    3980:	49 89 46 18          	mov    %rax,0x18(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3984:	48 8d 15 75 09 00 00 	lea    0x975(%rip),%rdx        # 4300 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    398b:	49 83 c4 08          	add    $0x8,%r12
    398f:	49 81 c6 30 01 00 00 	add    $0x130,%r14
      my_thread_data[n] = &thread_data[n]; 
    3996:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3999:	48 8b 34 24          	mov    (%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    399d:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    39a1:	48 8b 05 70 65 00 00 	mov    0x6570(%rip),%rax        # 9f18 <_IO_stdin_used+0xf18>
    thread_data[x].thread_index = x;
    39a8:	45 89 be d4 fe ff ff 	mov    %r15d,-0x12c(%r14)
    thread_data[x].thread_count = thread_count;
    39af:	49 89 86 f8 fe ff ff 	mov    %rax,-0x108(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    39b6:	e8 f5 ea ff ff       	call   24b0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    39bb:	48 83 04 24 38       	addq   $0x38,(%rsp)
    39c0:	48 83 84 24 80 00 00 00 10 	addq   $0x10,0x80(%rsp)
    39c9:	41 83 ff 05          	cmp    $0x5,%r15d
    39cd:	75 2b                	jne    39fa <main+0x133a>
    39cf:	41 bf 06 00 00 00    	mov    $0x6,%r15d
    39d5:	e9 3a ff ff ff       	jmp    3914 <main+0x1254>
        my_thread_data[1] = &thread_data[other]; 
    39da:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    39df:	4c 89 6c 24 50       	mov    %r13,0x50(%rsp)
    39e4:	48 89 da             	mov    %rbx,%rdx
    39e7:	45 31 c0             	xor    %r8d,%r8d
        other = (x + 1) % total_threads;
    39ea:	bd 01 00 00 00       	mov    $0x1,%ebp
        my_thread_data[1] = &thread_data[other]; 
    39ef:	48 05 30 01 00 00    	add    $0x130,%rax
        thread_data[x].protected_state = &protected_state[k];
    39f5:	e9 d5 f1 ff ff       	jmp    2bcf <main+0x50f>
    39fa:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    39ff:	48 87 eb             	xchg   %rbp,%rbx
    3a02:	4c 8d 25 e6 5a 00 00 	lea    0x5ae6(%rip),%r12        # 94ef <_IO_stdin_used+0x4ef>
    3a09:	4c 8d 70 04          	lea    0x4(%rax),%r14
    3a0d:	4c 8d a8 54 08 00 00 	lea    0x854(%rax),%r13
    3a14:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3a18:	41 8b 16             	mov    (%r14),%edx
    3a1b:	4c 89 e6             	mov    %r12,%rsi
    3a1e:	bf 01 00 00 00       	mov    $0x1,%edi
    3a23:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3a25:	49 81 c6 30 01 00 00 	add    $0x130,%r14
    3a2c:	e8 5f ea ff ff       	call   2490 <__printf_chk@plt>
    3a31:	4d 39 ee             	cmp    %r13,%r14
    3a34:	75 de                	jne    3a14 <main+0x1354>
    3a36:	48 8d 3d c5 5a 00 00 	lea    0x5ac5(%rip),%rdi        # 9502 <_IO_stdin_used+0x502>
    3a3d:	45 31 f6             	xor    %r14d,%r14d
    3a40:	4c 8d ac 24 b0 00 00 00 	lea    0xb0(%rsp),%r13
    3a48:	e8 c3 e8 ff ff       	call   2310 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3a4d:	4c 8d 25 cc 5a 00 00 	lea    0x5acc(%rip),%r12        # 9520 <_IO_stdin_used+0x520>
    void * result; 
    pthread_join(thread[x], &result);
    3a54:	4a 8b 7c f5 00       	mov    0x0(%rbp,%r14,8),%rdi
    3a59:	4c 89 ee             	mov    %r13,%rsi
    3a5c:	e8 ef ea ff ff       	call   2550 <pthread_join@plt>
    3a61:	44 89 f2             	mov    %r14d,%edx
    3a64:	4c 89 e6             	mov    %r12,%rsi
    3a67:	bf 01 00 00 00       	mov    $0x1,%edi
    3a6c:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3a6e:	49 83 c6 01          	add    $0x1,%r14
    3a72:	e8 19 ea ff ff       	call   2490 <__printf_chk@plt>
    3a77:	49 83 fe 07          	cmp    $0x7,%r14
    3a7b:	75 d7                	jne    3a54 <main+0x1394>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3a7d:	bf 00 04 00 00       	mov    $0x400,%edi
    3a82:	be 08 00 00 00       	mov    $0x8,%esi
    3a87:	31 ed                	xor    %ebp,%ebp
    3a89:	e8 52 e9 ff ff       	call   23e0 <calloc@plt>
    3a8e:	48 89 df             	mov    %rbx,%rdi
    3a91:	49 89 c6             	mov    %rax,%r14
  int datas2_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3a94:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    3a98:	45 85 c0             	test   %r8d,%r8d
    3a9b:	7e 59                	jle    3af6 <main+0x1436>
    3a9d:	48 8b 17             	mov    (%rdi),%rdx
    3aa0:	49 63 f0             	movslq %r8d,%rsi
    3aa3:	48 63 c5             	movslq %ebp,%rax
    3aa6:	48 c1 e6 09          	shl    $0x9,%rsi
    3aaa:	49 8d 0c c6          	lea    (%r14,%rax,8),%rcx
    3aae:	48 01 d6             	add    %rdx,%rsi
    3ab1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3ab8:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3abf:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    3ac6:	48 83 c1 20          	add    $0x20,%rcx
    3aca:	f3 0f 7e 80 00 01 00 00 	movq   0x100(%rax),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3ad2:	f3 0f 7e 08          	movq   (%rax),%xmm1
    3ad6:	0f 16 80 80 01 00 00 	movhps 0x180(%rax),%xmm0
    3add:	0f 16 88 80 00 00 00 	movhps 0x80(%rax),%xmm1
    3ae4:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    3ae8:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3aec:	48 39 f2             	cmp    %rsi,%rdx
    3aef:	75 c7                	jne    3ab8 <main+0x13f8>
    3af1:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3af6:	48 81 c7 30 01 00 00 	add    $0x130,%rdi
    3afd:	48 39 7c 24 08       	cmp    %rdi,0x8(%rsp)
    3b02:	75 90                	jne    3a94 <main+0x13d4>
    3b04:	48 8d 3d 29 5a 00 00 	lea    0x5a29(%rip),%rdi        # 9534 <_IO_stdin_used+0x534>
    3b0b:	e8 00 e8 ff ff       	call   2310 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3b10:	48 8d 35 ed 58 00 00 	lea    0x58ed(%rip),%rsi        # 9404 <_IO_stdin_used+0x404>
    3b17:	48 8d 3d 2e 5a 00 00 	lea    0x5a2e(%rip),%rdi        # 954c <_IO_stdin_used+0x54c>
    3b1e:	e8 bd e9 ff ff       	call   24e0 <fopen@plt>
    3b23:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas2_size; x++) {
    3b26:	85 ed                	test   %ebp,%ebp
    3b28:	0f 8e 80 00 00 00    	jle    3bae <main+0x14ee>
    3b2e:	48 8d 05 08 59 00 00 	lea    0x5908(%rip),%rax        # 943d <_IO_stdin_used+0x43d>
    3b35:	48 63 ed             	movslq %ebp,%rbp
    3b38:	4c 8d 2d f2 58 00 00 	lea    0x58f2(%rip),%r13        # 9431 <_IO_stdin_used+0x431>
    3b3f:	48 89 04 24          	mov    %rax,(%rsp)
    3b43:	4c 89 f0             	mov    %r14,%rax
    3b46:	4d 8d 24 ee          	lea    (%r14,%rbp,8),%r12
    3b4a:	49 89 de             	mov    %rbx,%r14
    3b4d:	48 89 c3             	mov    %rax,%rbx
    char * c = calloc(250, sizeof(char));
    3b50:	be 01 00 00 00       	mov    $0x1,%esi
    3b55:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3b5a:	48 83 c3 08          	add    $0x8,%rbx
    char * c = calloc(250, sizeof(char));
    3b5e:	e8 7d e8 ff ff       	call   23e0 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3b63:	4c 89 e9             	mov    %r13,%rcx
    3b66:	ba fa 00 00 00       	mov    $0xfa,%edx
    3b6b:	be 01 00 00 00       	mov    $0x1,%esi
    3b70:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3b73:	48 8b 43 f8          	mov    -0x8(%rbx),%rax
    3b77:	48 89 ef             	mov    %rbp,%rdi
    3b7a:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3b81:	31 c0                	xor    %eax,%eax
    3b83:	e8 18 ea ff ff       	call   25a0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3b88:	48 8b 34 24          	mov    (%rsp),%rsi
    3b8c:	48 89 ea             	mov    %rbp,%rdx
    3b8f:	31 c0                	xor    %eax,%eax
    3b91:	bf 01 00 00 00       	mov    $0x1,%edi
    3b96:	e8 f5 e8 ff ff       	call   2490 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3b9b:	4c 89 fe             	mov    %r15,%rsi
    3b9e:	48 89 ef             	mov    %rbp,%rdi
    3ba1:	e8 fa e7 ff ff       	call   23a0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3ba6:	4c 39 e3             	cmp    %r12,%rbx
    3ba9:	75 a5                	jne    3b50 <main+0x1490>
    3bab:	4c 89 f3             	mov    %r14,%rbx
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    3bae:	4c 89 ff             	mov    %r15,%rdi
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3bb1:	45 31 ed             	xor    %r13d,%r13d
  fclose(m2);
    3bb4:	45 31 e4             	xor    %r12d,%r12d
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3bb7:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    3bc1:	e8 7a e7 ff ff       	call   2340 <fclose@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3bc6:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  fclose(m2);
    3bcb:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    3bd4:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
    3bdd:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3be2:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3beb:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3bf4:	bf 0a 00 00 00       	mov    $0xa,%edi
    3bf9:	45 89 ee             	mov    %r13d,%r14d
    3bfc:	e8 ff e6 ff ff       	call   2300 <putchar@plt>
    3c01:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3c06:	48 8d 35 48 59 00 00 	lea    0x5948(%rip),%rsi        # 9555 <_IO_stdin_used+0x555>
    3c0d:	bf 01 00 00 00       	mov    $0x1,%edi
    3c12:	41 83 f6 01          	xor    $0x1,%r14d
    3c16:	48 8b 10             	mov    (%rax),%rdx
    3c19:	31 c0                	xor    %eax,%eax
    3c1b:	e8 70 e8 ff ff       	call   2490 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3c20:	8b 53 08             	mov    0x8(%rbx),%edx
    3c23:	85 d2                	test   %edx,%edx
    3c25:	0f 8e ee 04 00 00    	jle    4119 <main+0x1a59>
    3c2b:	48 63 ca             	movslq %edx,%rcx
    3c2e:	48 8b 03             	mov    (%rbx),%rax
      long v = 0;
    3c31:	31 d2                	xor    %edx,%edx
    3c33:	48 c1 e1 09          	shl    $0x9,%rcx
    3c37:	48 01 c1             	add    %rax,%rcx
    3c3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3c40:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3c47:	48 05 00 02 00 00    	add    $0x200,%rax
    3c4d:	48 39 c1             	cmp    %rax,%rcx
    3c50:	75 ee                	jne    3c40 <main+0x1580>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3c52:	4c 89 f0             	mov    %r14,%rax
    3c55:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3c5a:	48 f7 d8             	neg    %rax
    3c5d:	25 30 01 00 00       	and    $0x130,%eax
    3c62:	48 01 f8             	add    %rdi,%rax
    3c65:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3c69:	85 c9                	test   %ecx,%ecx
    3c6b:	7e 25                	jle    3c92 <main+0x15d2>
    3c6d:	48 8b 40 38          	mov    0x38(%rax),%rax
    3c71:	48 c1 e1 09          	shl    $0x9,%rcx
    3c75:	48 01 c1             	add    %rax,%rcx
    3c78:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3c80:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3c87:	48 05 00 02 00 00    	add    $0x200,%rax
    3c8d:	48 39 c8             	cmp    %rcx,%rax
    3c90:	75 ee                	jne    3c80 <main+0x15c0>
    3c92:	48 8d 35 d1 58 00 00 	lea    0x58d1(%rip),%rsi        # 956a <_IO_stdin_used+0x56a>
    3c99:	bf 01 00 00 00       	mov    $0x1,%edi
    3c9e:	31 c0                	xor    %eax,%eax
    3ca0:	e8 eb e7 ff ff       	call   2490 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3ca5:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3caa:	bf 01 00 00 00       	mov    $0x1,%edi
    3caf:	48 8d 35 9a 5d 00 00 	lea    0x5d9a(%rip),%rsi        # 9a50 <_IO_stdin_used+0xa50>
    3cb6:	48 8b 08             	mov    (%rax),%rcx
    3cb9:	48 b8 4b 59 86 38 d6 c5 6d 34 	movabs $0x346dc5d63886594b,%rax
    3cc3:	48 f7 e9             	imul   %rcx
    3cc6:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3cca:	31 c0                	xor    %eax,%eax
    3ccc:	48 c1 fa 0b          	sar    $0xb,%rdx
    3cd0:	48 29 ca             	sub    %rcx,%rdx
    3cd3:	e8 b8 e7 ff ff       	call   2490 <__printf_chk@plt>
    3cd8:	bf 0a 00 00 00       	mov    $0xa,%edi
    3cdd:	e8 1e e6 ff ff       	call   2300 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3ce2:	44 8b 73 08          	mov    0x8(%rbx),%r14d
    3ce6:	45 85 f6             	test   %r14d,%r14d
    3ce9:	0f 8e 30 01 00 00    	jle    3e1f <main+0x175f>
    3cef:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3cf4:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3cf9:	44 89 2c 24          	mov    %r13d,(%rsp)
    3cfd:	31 d2                	xor    %edx,%edx
    3cff:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3d04:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    3d09:	49 89 dd             	mov    %rbx,%r13
    3d0c:	0f 1f 40 00          	nopl   0x0(%rax)
        total += thread_data[x].tasks[n].n;
    3d10:	49 8b 45 00          	mov    0x0(%r13),%rax
    3d14:	49 89 d1             	mov    %rdx,%r9
    3d17:	48 89 54 24 20       	mov    %rdx,0x20(%rsp)
    3d1c:	89 d3                	mov    %edx,%ebx
    3d1e:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    3d22:	45 31 f6             	xor    %r14d,%r14d
        total += thread_data[x].tasks[n].n;
    3d25:	4c 01 c8             	add    %r9,%rax
    3d28:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    3d2d:	48 03 b8 08 01 00 00 	add    0x108(%rax),%rdi
        ingests += thread_data[x].tasks[n].ingest_count;
    3d34:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
        sends += thread_data[x].tasks[n].sends;
    3d3b:	4c 03 90 80 01 00 00 	add    0x180(%rax),%r10
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3d42:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    3d47:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    3d4c:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3d51:	8b 14 24             	mov    (%rsp),%edx
    3d54:	45 89 f0             	mov    %r14d,%r8d
    3d57:	89 d9                	mov    %ebx,%ecx
    3d59:	48 8d 35 17 58 00 00 	lea    0x5817(%rip),%rsi        # 9577 <_IO_stdin_used+0x577>
    3d60:	bf 01 00 00 00       	mov    $0x1,%edi
    3d65:	31 c0                	xor    %eax,%eax
    3d67:	e8 24 e7 ff ff       	call   2490 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3d6c:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3d71:	4c 89 f0             	mov    %r14,%rax
    3d74:	45 89 f0             	mov    %r14d,%r8d
    3d77:	49 8b 55 00          	mov    0x0(%r13),%rdx
    3d7b:	48 c1 e0 08          	shl    $0x8,%rax
    3d7f:	48 83 ec 08          	sub    $0x8,%rsp
    3d83:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    3d8b:	48 8b 38             	mov    (%rax),%rdi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3d8e:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3d95:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3d9c:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3da3:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3daa:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    3db1:	bf 01 00 00 00       	mov    $0x1,%edi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3db6:	49 01 c4             	add    %rax,%r12
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3db9:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3dbc:	49 01 cf             	add    %rcx,%r15
    3dbf:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3dc3:	49 01 f4             	add    %rsi,%r12
    3dc6:	50                   	push   %rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3dc7:	49 01 d7             	add    %rdx,%r15
    3dca:	8b 54 24 10          	mov    0x10(%rsp),%edx
    3dce:	89 d9                	mov    %ebx,%ecx
    3dd0:	48 8d 35 99 5c 00 00 	lea    0x5c99(%rip),%rsi        # 9a70 <_IO_stdin_used+0xa70>
    3dd7:	31 c0                	xor    %eax,%eax
    3dd9:	e8 b2 e6 ff ff       	call   2490 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3dde:	41 5a                	pop    %r10
    3de0:	41 5b                	pop    %r11
    3de2:	4d 85 f6             	test   %r14,%r14
    3de5:	75 0a                	jne    3df1 <main+0x1731>
    3de7:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    3dec:	e9 60 ff ff ff       	jmp    3d51 <main+0x1691>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3df1:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
    3df6:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3dfb:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3e00:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3e05:	48 83 c2 01          	add    $0x1,%rdx
    3e09:	41 39 55 08          	cmp    %edx,0x8(%r13)
    3e0d:	0f 8f fd fe ff ff    	jg     3d10 <main+0x1650>
    3e13:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
    3e18:	4c 89 eb             	mov    %r13,%rbx
    3e1b:	44 8b 2c 24          	mov    (%rsp),%r13d
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3e1f:	45 31 ff             	xor    %r15d,%r15d
    3e22:	48 83 7b 78 00       	cmpq   $0x0,0x78(%rbx)
    3e27:	4c 8d 35 62 5c 00 00 	lea    0x5c62(%rip),%r14        # 9a90 <_IO_stdin_used+0xa90>
    3e2e:	7e 52                	jle    3e82 <main+0x17c2>
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3e30:	48 8b 43 68          	mov    0x68(%rbx),%rax
    3e34:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    3e38:	48 83 ec 08          	sub    $0x8,%rsp
    3e3c:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3e41:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3e45:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3e49:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3e4d:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3e51:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3e54:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3e58:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3e5b:	48 f7 e5             	mul    %rbp
    3e5e:	8b 49 20             	mov    0x20(%rcx),%ecx
    3e61:	56                   	push   %rsi
    3e62:	31 c0                	xor    %eax,%eax
    3e64:	4c 89 f6             	mov    %r14,%rsi
    3e67:	48 c1 ea 12          	shr    $0x12,%rdx
    3e6b:	49 89 d1             	mov    %rdx,%r9
    3e6e:	ba 02 00 00 00       	mov    $0x2,%edx
    3e73:	e8 18 e6 ff ff       	call   2490 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3e78:	41 58                	pop    %r8
    3e7a:	41 59                	pop    %r9
    3e7c:	4c 39 7b 78          	cmp    %r15,0x78(%rbx)
    3e80:	7f ae                	jg     3e30 <main+0x1770>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3e82:	8b 93 94 00 00 00    	mov    0x94(%rbx),%edx
    3e88:	85 d2                	test   %edx,%edx
    3e8a:	0f 8e 0a 01 00 00    	jle    3f9a <main+0x18da>
    3e90:	4c 89 64 24 50       	mov    %r12,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3e95:	48 8b 7b 18          	mov    0x18(%rbx),%rdi
    3e99:	45 31 ff             	xor    %r15d,%r15d
    3e9c:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    3ea1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3ea8:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    3eac:	45 89 fc             	mov    %r15d,%r12d
    3eaf:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    3eb7:	8b 30                	mov    (%rax),%esi
    3eb9:	85 f6                	test   %esi,%esi
    3ebb:	0f 8e c2 00 00 00    	jle    3f83 <main+0x18c3>
    3ec1:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3ec6:	31 d2                	xor    %edx,%edx
    3ec8:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3ecc:	49 89 f8             	mov    %rdi,%r8
    3ecf:	48 89 d7             	mov    %rdx,%rdi
    3ed2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3ed8:	4c 8d 1c bf          	lea    (%rdi,%rdi,4),%r11
    3edc:	45 31 ff             	xor    %r15d,%r15d
    3edf:	4e 8d 34 dd 00 00 00 00 	lea    0x0(,%r11,8),%r14
    3ee7:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    3eeb:	8b 50 1c             	mov    0x1c(%rax),%edx
    3eee:	85 d2                	test   %edx,%edx
    3ef0:	7e 77                	jle    3f69 <main+0x18a9>
    3ef2:	48 89 3c 24          	mov    %rdi,(%rsp)
    3ef6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3f00:	4c 89 f9             	mov    %r15,%rcx
    3f03:	48 83 ec 08          	sub    $0x8,%rsp
    3f07:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3f0c:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3f10:	48 c1 e1 05          	shl    $0x5,%rcx
    3f14:	48 03 48 10          	add    0x10(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3f18:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3f1c:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3f20:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3f23:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3f27:	4c 2b 01             	sub    (%rcx),%r8
    3f2a:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3f2b:	48 f7 e5             	mul    %rbp
    3f2e:	44 89 e1             	mov    %r12d,%ecx
    3f31:	48 8d 35 a8 5b 00 00 	lea    0x5ba8(%rip),%rsi        # 9ae0 <_IO_stdin_used+0xae0>
    3f38:	31 c0                	xor    %eax,%eax
    3f3a:	48 c1 ea 12          	shr    $0x12,%rdx
    3f3e:	49 89 d1             	mov    %rdx,%r9
    3f41:	ba 02 00 00 00       	mov    $0x2,%edx
    3f46:	e8 45 e5 ff ff       	call   2490 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3f4b:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    3f4f:	5e                   	pop    %rsi
    3f50:	5f                   	pop    %rdi
    3f51:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    3f55:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    3f59:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    3f5d:	44 39 78 1c          	cmp    %r15d,0x1c(%rax)
    3f61:	7f 9d                	jg     3f00 <main+0x1840>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3f63:	48 8b 3c 24          	mov    (%rsp),%rdi
    3f67:	8b 32                	mov    (%rdx),%esi
    3f69:	48 83 c7 01          	add    $0x1,%rdi
    3f6d:	39 fe                	cmp    %edi,%esi
    3f6f:	0f 8f 63 ff ff ff    	jg     3ed8 <main+0x1818>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3f75:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    3f7a:	8b 93 94 00 00 00    	mov    0x94(%rbx),%edx
    3f80:	4c 89 c7             	mov    %r8,%rdi
    3f83:	49 83 c7 01          	add    $0x1,%r15
    3f87:	44 39 fa             	cmp    %r15d,%edx
    3f8a:	0f 8f 18 ff ff ff    	jg     3ea8 <main+0x17e8>
    3f90:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    3f95:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    3f9a:	48 83 44 24 48 18    	addq   $0x18,0x48(%rsp)
    3fa0:	48 81 c3 30 01 00 00 	add    $0x130,%rbx
    3fa7:	45 85 ed             	test   %r13d,%r13d
    3faa:	75 0a                	jne    3fb6 <main+0x18f6>
    3fac:	44 8b 6c 24 40       	mov    0x40(%rsp),%r13d
    3fb1:	e9 3e fc ff ff       	jmp    3bf4 <main+0x1534>
    3fb6:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    3fbb:	48 8d 35 c5 55 00 00 	lea    0x55c5(%rip),%rsi        # 9587 <_IO_stdin_used+0x587>
    3fc2:	bf 01 00 00 00       	mov    $0x1,%edi
    3fc7:	31 c0                	xor    %eax,%eax
    3fc9:	4c 89 f2             	mov    %r14,%rdx
    3fcc:	e8 bf e4 ff ff       	call   2490 <__printf_chk@plt>
    3fd1:	bf 0a 00 00 00       	mov    $0xa,%edi
    3fd6:	e8 25 e3 ff ff       	call   2300 <putchar@plt>
    3fdb:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
    3fe0:	48 8d 35 51 5b 00 00 	lea    0x5b51(%rip),%rsi        # 9b38 <_IO_stdin_used+0xb38>
    3fe7:	31 c0                	xor    %eax,%eax
    3fe9:	bf 01 00 00 00       	mov    $0x1,%edi
    3fee:	48 8b 53 08          	mov    0x8(%rbx),%rdx
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    3ff2:	48 bb 4b 59 86 38 d6 c5 6d 34 	movabs $0x346dc5d63886594b,%rbx
    3ffc:	e8 8f e4 ff ff       	call   2490 <__printf_chk@plt>
    4001:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    4006:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    400b:	48 8d 35 4e 5b 00 00 	lea    0x5b4e(%rip),%rsi        # 9b60 <_IO_stdin_used+0xb60>
    4012:	48 f7 eb             	imul   %rbx
    4015:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4019:	31 c0                	xor    %eax,%eax
    401b:	48 c1 fa 0b          	sar    $0xb,%rdx
    401f:	48 29 fa             	sub    %rdi,%rdx
    4022:	bf 01 00 00 00       	mov    $0x1,%edi
    4027:	e8 64 e4 ff ff       	call   2490 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    402c:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    4031:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    4036:	48 8d 35 53 5b 00 00 	lea    0x5b53(%rip),%rsi        # 9b90 <_IO_stdin_used+0xb90>
    403d:	48 f7 eb             	imul   %rbx
    4040:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4044:	31 c0                	xor    %eax,%eax
    4046:	48 c1 fa 0b          	sar    $0xb,%rdx
    404a:	48 29 fa             	sub    %rdi,%rdx
    404d:	bf 01 00 00 00       	mov    $0x1,%edi
    4052:	e8 39 e4 ff ff       	call   2490 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    4057:	4c 89 f0             	mov    %r14,%rax
    405a:	bf 01 00 00 00       	mov    $0x1,%edi
    405f:	48 8d 35 5a 5b 00 00 	lea    0x5b5a(%rip),%rsi        # 9bc0 <_IO_stdin_used+0xbc0>
    4066:	48 f7 eb             	imul   %rbx
    4069:	4c 89 f0             	mov    %r14,%rax
    406c:	48 c1 f8 3f          	sar    $0x3f,%rax
    4070:	48 c1 fa 0b          	sar    $0xb,%rdx
    4074:	48 29 c2             	sub    %rax,%rdx
    4077:	31 c0                	xor    %eax,%eax
    4079:	e8 12 e4 ff ff       	call   2490 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    407e:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4083:	bf 01 00 00 00       	mov    $0x1,%edi
    4088:	48 8d 35 0c 55 00 00 	lea    0x550c(%rip),%rsi        # 959b <_IO_stdin_used+0x59b>
    408f:	48 f7 eb             	imul   %rbx
    4092:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4097:	48 c1 f8 3f          	sar    $0x3f,%rax
    409b:	48 c1 fa 0b          	sar    $0xb,%rdx
    409f:	48 29 c2             	sub    %rax,%rdx
    40a2:	31 c0                	xor    %eax,%eax
    40a4:	48 89 d5             	mov    %rdx,%rbp
    40a7:	e8 e4 e3 ff ff       	call   2490 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
    40ac:	4c 89 e0             	mov    %r12,%rax
    40af:	bf 01 00 00 00       	mov    $0x1,%edi
    40b4:	48 8d 35 25 5b 00 00 	lea    0x5b25(%rip),%rsi        # 9be0 <_IO_stdin_used+0xbe0>
    40bb:	48 f7 eb             	imul   %rbx
    40be:	4c 89 e0             	mov    %r12,%rax
    40c1:	48 c1 f8 3f          	sar    $0x3f,%rax
    40c5:	48 89 d3             	mov    %rdx,%rbx
    40c8:	48 c1 fb 0b          	sar    $0xb,%rbx
    40cc:	48 29 c3             	sub    %rax,%rbx
    40cf:	31 c0                	xor    %eax,%eax
    40d1:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    40d4:	48 29 eb             	sub    %rbp,%rbx
    40d7:	e8 b4 e3 ff ff       	call   2490 <__printf_chk@plt>
    40dc:	31 c0                	xor    %eax,%eax
    40de:	48 89 da             	mov    %rbx,%rdx
    40e1:	bf 01 00 00 00       	mov    $0x1,%edi
    40e6:	48 8d 35 ca 54 00 00 	lea    0x54ca(%rip),%rsi        # 95b7 <_IO_stdin_used+0x5b7>
    40ed:	e8 9e e3 ff ff       	call   2490 <__printf_chk@plt>
  return 0;

}
    40f2:	48 8b 84 24 b8 00 00 00 	mov    0xb8(%rsp),%rax
    40fa:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4103:	75 25                	jne    412a <main+0x1a6a>
    4105:	48 81 c4 c8 00 00 00 	add    $0xc8,%rsp
    410c:	31 c0                	xor    %eax,%eax
    410e:	5b                   	pop    %rbx
    410f:	5d                   	pop    %rbp
    4110:	41 5c                	pop    %r12
    4112:	41 5d                	pop    %r13
    4114:	41 5e                	pop    %r14
    4116:	41 5f                	pop    %r15
    4118:	c3                   	ret
      long v = 0;
    4119:	31 d2                	xor    %edx,%edx
    411b:	e9 32 fb ff ff       	jmp    3c52 <main+0x1592>
            exit(1);
    4120:	bf 01 00 00 00       	mov    $0x1,%edi
    4125:	e8 d6 e3 ff ff       	call   2500 <exit@plt>
}
    412a:	e8 31 e2 ff ff       	call   2360 <__stack_chk_fail@plt>
    412f:	90                   	nop

0000000000004130 <_start>:
    4130:	f3 0f 1e fa          	endbr64
    4134:	31 ed                	xor    %ebp,%ebp
    4136:	49 89 d1             	mov    %rdx,%r9
    4139:	5e                   	pop    %rsi
    413a:	48 89 e2             	mov    %rsp,%rdx
    413d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4141:	50                   	push   %rax
    4142:	54                   	push   %rsp
    4143:	45 31 c0             	xor    %r8d,%r8d
    4146:	31 c9                	xor    %ecx,%ecx
    4148:	48 8d 3d 71 e5 ff ff 	lea    -0x1a8f(%rip),%rdi        # 26c0 <main>
    414f:	ff 15 83 7e 00 00    	call   *0x7e83(%rip)        # bfd8 <__libc_start_main@GLIBC_2.34>
    4155:	f4                   	hlt
    4156:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004160 <deregister_tm_clones>:
    4160:	48 8d 3d b9 7e 00 00 	lea    0x7eb9(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4167:	48 8d 05 b2 7e 00 00 	lea    0x7eb2(%rip),%rax        # c020 <stderr@GLIBC_2.2.5>
    416e:	48 39 f8             	cmp    %rdi,%rax
    4171:	74 15                	je     4188 <deregister_tm_clones+0x28>
    4173:	48 8b 05 66 7e 00 00 	mov    0x7e66(%rip),%rax        # bfe0 <_ITM_deregisterTMCloneTable@Base>
    417a:	48 85 c0             	test   %rax,%rax
    417d:	74 09                	je     4188 <deregister_tm_clones+0x28>
    417f:	ff e0                	jmp    *%rax
    4181:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4188:	c3                   	ret
    4189:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004190 <register_tm_clones>:
    4190:	48 8d 3d 89 7e 00 00 	lea    0x7e89(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4197:	48 8d 35 82 7e 00 00 	lea    0x7e82(%rip),%rsi        # c020 <stderr@GLIBC_2.2.5>
    419e:	48 29 fe             	sub    %rdi,%rsi
    41a1:	48 89 f0             	mov    %rsi,%rax
    41a4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    41a8:	48 c1 f8 03          	sar    $0x3,%rax
    41ac:	48 01 c6             	add    %rax,%rsi
    41af:	48 d1 fe             	sar    %rsi
    41b2:	74 14                	je     41c8 <register_tm_clones+0x38>
    41b4:	48 8b 05 35 7e 00 00 	mov    0x7e35(%rip),%rax        # bff0 <_ITM_registerTMCloneTable@Base>
    41bb:	48 85 c0             	test   %rax,%rax
    41be:	74 08                	je     41c8 <register_tm_clones+0x38>
    41c0:	ff e0                	jmp    *%rax
    41c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    41c8:	c3                   	ret
    41c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000041d0 <__do_global_dtors_aux>:
    41d0:	f3 0f 1e fa          	endbr64
    41d4:	80 3d 4d 7e 00 00 00 	cmpb   $0x0,0x7e4d(%rip)        # c028 <completed.0>
    41db:	75 2b                	jne    4208 <__do_global_dtors_aux+0x38>
    41dd:	55                   	push   %rbp
    41de:	48 83 3d 12 7e 00 00 00 	cmpq   $0x0,0x7e12(%rip)        # bff8 <__cxa_finalize@GLIBC_2.2.5>
    41e6:	48 89 e5             	mov    %rsp,%rbp
    41e9:	74 0c                	je     41f7 <__do_global_dtors_aux+0x27>
    41eb:	48 8b 3d 16 7e 00 00 	mov    0x7e16(%rip),%rdi        # c008 <__dso_handle>
    41f2:	e8 f9 e0 ff ff       	call   22f0 <__cxa_finalize@plt>
    41f7:	e8 64 ff ff ff       	call   4160 <deregister_tm_clones>
    41fc:	c6 05 25 7e 00 00 01 	movb   $0x1,0x7e25(%rip)        # c028 <completed.0>
    4203:	5d                   	pop    %rbp
    4204:	c3                   	ret
    4205:	0f 1f 00             	nopl   (%rax)
    4208:	c3                   	ret
    4209:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004210 <frame_dummy>:
    4210:	f3 0f 1e fa          	endbr64
    4214:	e9 77 ff ff ff       	jmp    4190 <register_tm_clones>
    4219:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004220 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4220:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    4224:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    422b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    422f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4237:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    423b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    423f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4246:	48 85 c9             	test   %rcx,%rcx
    4249:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4250:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4254:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4258:	31 c0                	xor    %eax,%eax
    425a:	c3                   	ret
    425b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004260 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4260:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4264:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    426b:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    for (int x = 0 ; x < data->task_count ; x++) {
    4272:	85 c9                	test   %ecx,%ecx
    4274:	7e 48                	jle    42be <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4276:	48 63 97 30 01 00 00 	movslq 0x130(%rdi),%rdx
    427d:	49 8b 40 18          	mov    0x18(%r8),%rax
    4281:	48 c1 e1 09          	shl    $0x9,%rcx
      data->thread->tasks[x].available = 1; 
    4285:	49 8b 70 38          	mov    0x38(%r8),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4289:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    428d:	48 8b 50 38          	mov    0x38(%rax),%rdx
      data->thread->tasks[x].available = 1; 
    4291:	31 c0                	xor    %eax,%eax
    4293:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4298:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    42a0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    42a8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    42b3:	48 05 00 02 00 00    	add    $0x200,%rax
    42b9:	48 39 c1             	cmp    %rax,%rcx
    42bc:	75 da                	jne    4298 <barriered_reset+0x38>
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    42be:	49 8b 88 00 01 00 00 	mov    0x100(%r8),%rcx
    42c5:	8b 01                	mov    (%rcx),%eax
    42c7:	83 f8 ff             	cmp    $0xffffffff,%eax
    42ca:	74 0e                	je     42da <barriered_reset+0x7a>
    42cc:	41 8b b8 d0 00 00 00 	mov    0xd0(%r8),%edi
    42d3:	8d 57 ff             	lea    -0x1(%rdi),%edx
    42d6:	39 d0                	cmp    %edx,%eax
    42d8:	74 06                	je     42e0 <barriered_reset+0x80>
}
    42da:	31 c0                	xor    %eax,%eax
    42dc:	c3                   	ret
    42dd:	0f 1f 00             	nopl   (%rax)
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    42e0:	41 83 78 04 01       	cmpl   $0x1,0x4(%r8)
    42e5:	75 f3                	jne    42da <barriered_reset+0x7a>
    data->thread->group_data->arrived++;
    42e7:	49 8b 80 e8 00 00 00 	mov    0xe8(%r8),%rax
    42ee:	83 00 01             	addl   $0x1,(%rax)
    data->thread->global->request_group_sync = -1;
    42f1:	c7 01 ff ff ff ff    	movl   $0xffffffff,(%rcx)
    42f7:	eb e1                	jmp    42da <barriered_reset+0x7a>
    42f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004300 <external_thread>:
void * external_thread(void *arg) {
    4300:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    4304:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4308:	0f 85 ec 00 00 00    	jne    43fa <external_thread+0xfa>
void * external_thread(void *arg) {
    430e:	41 57                	push   %r15
    4310:	4c 8d 3d ed 4c 00 00 	lea    0x4ced(%rip),%r15        # 9004 <_IO_stdin_used+0x4>
    4317:	41 56                	push   %r14
    4319:	49 89 fe             	mov    %rdi,%r14
    431c:	41 55                	push   %r13
    431e:	41 54                	push   %r12
    4320:	55                   	push   %rbp
    4321:	53                   	push   %rbx
    4322:	48 83 ec 08          	sub    $0x8,%rsp
    4326:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int b = 0; b < data->buffers_count; b++) {
    4330:	41 8b 8e cc 00 00 00 	mov    0xcc(%r14),%ecx
    4337:	85 c9                	test   %ecx,%ecx
    4339:	7e 55                	jle    4390 <external_thread+0x90>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    433b:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    433f:	45 31 ed             	xor    %r13d,%r13d
    4342:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4348:	4e 8d 24 ed 00 00 00 00 	lea    0x0(,%r13,8),%r12
    4350:	31 db                	xor    %ebx,%ebx
    4352:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    4356:	48 8b 06             	mov    (%rsi),%rax
    4359:	8b 10                	mov    (%rax),%edx
    435b:	85 d2                	test   %edx,%edx
    435d:	7e 28                	jle    4387 <external_thread+0x87>
    435f:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    4363:	48 8d 2c 9b          	lea    (%rbx,%rbx,4),%rbp
    4367:	48 c1 e5 03          	shl    $0x3,%rbp
    436b:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    436f:	44 8b 40 08          	mov    0x8(%rax),%r8d
    4373:	45 85 c0             	test   %r8d,%r8d
    4376:	74 38                	je     43b0 <external_thread+0xb0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4378:	48 83 c3 01          	add    $0x1,%rbx
    437c:	39 da                	cmp    %ebx,%edx
    437e:	7f e3                	jg     4363 <external_thread+0x63>
    for (int b = 0; b < data->buffers_count; b++) {
    4380:	41 8b 8e cc 00 00 00 	mov    0xcc(%r14),%ecx
    4387:	49 83 c5 01          	add    $0x1,%r13
    438b:	44 39 e9             	cmp    %r13d,%ecx
    438e:	7f b8                	jg     4348 <external_thread+0x48>
  while (data->running == 1) {
    4390:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    4395:	74 99                	je     4330 <external_thread+0x30>
}
    4397:	48 83 c4 08          	add    $0x8,%rsp
    439b:	31 c0                	xor    %eax,%eax
    439d:	5b                   	pop    %rbx
    439e:	5d                   	pop    %rbp
    439f:	41 5c                	pop    %r12
    43a1:	41 5d                	pop    %r13
    43a3:	41 5e                	pop    %r14
    43a5:	41 5f                	pop    %r15
    43a7:	c3                   	ret
    43a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    43b0:	4c 89 38             	mov    %r15,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    43b3:	48 8b 06             	mov    (%rsi),%rax
      for (int x = 0; x < data->buffers[b]->count; x++) {
    43b6:	48 83 c3 01          	add    $0x1,%rbx
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    43ba:	48 8b 78 08          	mov    0x8(%rax),%rdi
    43be:	48 01 ef             	add    %rbp,%rdi
    43c1:	48 63 77 1c          	movslq 0x1c(%rdi),%rsi
    43c5:	48 c1 e6 05          	shl    $0x5,%rsi
    43c9:	48 03 77 10          	add    0x10(%rdi),%rsi
    43cd:	bf 04 00 00 00       	mov    $0x4,%edi
    43d2:	e8 59 df ff ff       	call   2330 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    43d7:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    43db:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    43df:	48 8b 06             	mov    (%rsi),%rax
    43e2:	48 8b 50 08          	mov    0x8(%rax),%rdx
    43e6:	c7 44 2a 08 01 00 00 00 	movl   $0x1,0x8(%rdx,%rbp,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
    43ee:	8b 10                	mov    (%rax),%edx
    43f0:	39 da                	cmp    %ebx,%edx
    43f2:	0f 8f 67 ff ff ff    	jg     435f <external_thread+0x5f>
    43f8:	eb 86                	jmp    4380 <external_thread+0x80>
}
    43fa:	31 c0                	xor    %eax,%eax
    43fc:	c3                   	ret
    43fd:	0f 1f 00             	nopl   (%rax)

0000000000004400 <timer_thread>:
void* timer_thread(void *arg) {
    4400:	f3 0f 1e fa          	endbr64
    4404:	41 57                	push   %r15
    4406:	48 8d 35 03 4c 00 00 	lea    0x4c03(%rip),%rsi        # 9010 <_IO_stdin_used+0x10>
    440d:	49 89 ff             	mov    %rdi,%r15
    4410:	41 56                	push   %r14
    4412:	41 55                	push   %r13
    4414:	41 54                	push   %r12
    4416:	55                   	push   %rbp
    4417:	53                   	push   %rbx
    4418:	48 83 ec 58          	sub    $0x58,%rsp
    441c:	8b 57 04             	mov    0x4(%rdi),%edx
    441f:	bf 01 00 00 00       	mov    $0x1,%edi
    4424:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    442d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    4432:	31 c0                	xor    %eax,%eax
    4434:	e8 57 e0 ff ff       	call   2490 <__printf_chk@plt>
  struct timespec preempt = {
    4439:	66 0f 6f 05 bf 59 00 00 	movdqa 0x59bf(%rip),%xmm0        # 9e00 <_IO_stdin_used+0xe00>
    4441:	ba 80 96 98 00       	mov    $0x989680,%edx
    4446:	31 c0                	xor    %eax,%eax
    4448:	48 8d 35 d3 4b 00 00 	lea    0x4bd3(%rip),%rsi        # 9022 <_IO_stdin_used+0x22>
    444f:	bf 01 00 00 00       	mov    $0x1,%edi
    4454:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4459:	e8 32 e0 ff ff       	call   2490 <__printf_chk@plt>
  while (data->running && n < times) {
    445e:	41 8b 47 44          	mov    0x44(%r15),%eax
    4462:	89 c3                	mov    %eax,%ebx
    4464:	85 c0                	test   %eax,%eax
    4466:	0f 84 97 00 00 00    	je     4503 <timer_thread+0x103>
  int n = 0;
    446c:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    446f:	31 db                	xor    %ebx,%ebx
    4471:	49 89 e5             	mov    %rsp,%r13
    y++;
    4474:	31 ed                	xor    %ebp,%ebp
    4476:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    nanosleep(&preempt , &rem2);
    447b:	4c 89 e7             	mov    %r12,%rdi
    447e:	4c 89 ee             	mov    %r13,%rsi
    n++;
    4481:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    4485:	e8 f6 de ff ff       	call   2380 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    448a:	49 63 47 30          	movslq 0x30(%r15),%rax
    y++;
    448e:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4491:	85 c0                	test   %eax,%eax
    4493:	7e 4a                	jle    44df <timer_thread+0xdf>
    4495:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4499:	4c 63 c3             	movslq %ebx,%r8
    449c:	49 c1 e0 09          	shl    $0x9,%r8
    44a0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    44a4:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    44a8:	48 8b 19             	mov    (%rcx),%rbx
    44ab:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    44ad:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    44b1:	99                   	cltd
    44b2:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    44b5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    44b9:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    44bc:	48 63 d2             	movslq %edx,%rdx
    44bf:	48 c1 e2 09          	shl    $0x9,%rdx
    44c3:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    44ce:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    44da:	49 39 c9             	cmp    %rcx,%r9
    44dd:	75 c9                	jne    44a8 <timer_thread+0xa8>
    if (y >= data->threads[0]->task_count) {
    44df:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
    44e3:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    y++;
    44e7:	89 fb                	mov    %edi,%ebx
    if (y >= data->threads[0]->task_count) {
    44e9:	48 8b 00             	mov    (%rax),%rax
    y++;
    44ec:	39 78 40             	cmp    %edi,0x40(%rax)
    44ef:	0f 4e dd             	cmovle %ebp,%ebx
  while (data->running && n < times) {
    44f2:	85 c9                	test   %ecx,%ecx
    44f4:	74 0d                	je     4503 <timer_thread+0x103>
    44f6:	41 81 fe 80 96 98 00 	cmp    $0x989680,%r14d
    44fd:	0f 85 78 ff ff ff    	jne    447b <timer_thread+0x7b>
    4503:	48 8d 3d 2e 4b 00 00 	lea    0x4b2e(%rip),%rdi        # 9038 <_IO_stdin_used+0x38>
    450a:	e8 01 de ff ff       	call   2310 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    450f:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4513:	85 d2                	test   %edx,%edx
    4515:	7e 6e                	jle    4585 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    4517:	49 63 47 40          	movslq 0x40(%r15),%rax
    451b:	85 c0                	test   %eax,%eax
    451d:	7e 66                	jle    4585 <timer_thread+0x185>
    451f:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4523:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4527:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    452f:	31 c9                	xor    %ecx,%ecx
    4531:	48 89 c6             	mov    %rax,%rsi
    4534:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4538:	48 8b 40 38          	mov    0x38(%rax),%rax
    453c:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4540:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4546:	74 18                	je     4560 <timer_thread+0x160>
    4548:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4552:	48 05 00 02 00 00    	add    $0x200,%rax
    4558:	48 39 c2             	cmp    %rax,%rdx
    455b:	74 1f                	je     457c <timer_thread+0x17c>
    455d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->tasks[y].sending = 0;
    4560:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    456a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4570:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4577:	48 39 c2             	cmp    %rax,%rdx
    457a:	75 e4                	jne    4560 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    457c:	48 83 c1 08          	add    $0x8,%rcx
    4580:	48 39 cf             	cmp    %rcx,%rdi
    4583:	75 af                	jne    4534 <timer_thread+0x134>
  struct timespec drain = {
    4585:	66 0f 6f 05 83 58 00 00 	movdqa 0x5883(%rip),%xmm0        # 9e10 <_IO_stdin_used+0xe10>
    458d:	41 89 dc             	mov    %ebx,%r12d
    4590:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4595:	49 63 47 28          	movslq 0x28(%r15),%rax
    y++;
    4599:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    459e:	85 c0                	test   %eax,%eax
    45a0:	7e 49                	jle    45eb <timer_thread+0x1eb>
    45a2:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    45a6:	49 63 ec             	movslq %r12d,%rbp
    45a9:	48 c1 e5 09          	shl    $0x9,%rbp
    45ad:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    45b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    45b8:	48 8b 19             	mov    (%rcx),%rbx
    45bb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    45bd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    45c1:	99                   	cltd
    45c2:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    45c5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    45c9:	48 63 d2             	movslq %edx,%rdx
    45cc:	48 c1 e2 09          	shl    $0x9,%rdx
    45d0:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    45db:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    45e6:	49 39 c8             	cmp    %rcx,%r8
    45e9:	75 cd                	jne    45b8 <timer_thread+0x1b8>
    if (y >= data->threads[0]->task_count) {
    45eb:	49 8b 77 18          	mov    0x18(%r15),%rsi
    y++;
    45ef:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    45f2:	48 8b 06             	mov    (%rsi),%rax
    y++;
    45f5:	39 78 40             	cmp    %edi,0x40(%rax)
    45f8:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    45fc:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4600:	85 ff                	test   %edi,%edi
    4602:	0f 8e ac 01 00 00    	jle    47b4 <timer_thread+0x3b4>
    4608:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    460b:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    4611:	4c 89 f5             	mov    %r14,%rbp
    4614:	0f 1f 40 00          	nopl   0x0(%rax)
    4618:	89 eb                	mov    %ebp,%ebx
      for (int y = 0 ; y < 2 ; y++) {
    461a:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    4622:	45 31 f6             	xor    %r14d,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4625:	85 ff                	test   %edi,%edi
    4627:	7e 7f                	jle    46a8 <timer_thread+0x2a8>
    4629:	4c 89 f6             	mov    %r14,%rsi
    462c:	48 63 cf             	movslq %edi,%rcx
    462f:	45 31 c0             	xor    %r8d,%r8d
    4632:	48 c1 e6 09          	shl    $0x9,%rsi
    4636:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (x == k) { continue; }
    4640:	41 39 e8             	cmp    %ebp,%r8d
    4643:	74 45                	je     468a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4645:	49 8b 47 18          	mov    0x18(%r15),%rax
    4649:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    464d:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4651:	4c 89 c0             	mov    %r8,%rax
    4654:	48 c1 e0 08          	shl    $0x8,%rax
    4658:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4660:	48 8b 10             	mov    (%rax),%rdx
    4663:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    466a:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4671:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4678:	4d 85 c9             	test   %r9,%r9
    467b:	0f 8f 97 00 00 00    	jg     4718 <timer_thread+0x318>
    4681:	4d 85 db             	test   %r11,%r11
    4684:	0f 8f 8e 00 00 00    	jg     4718 <timer_thread+0x318>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    468a:	49 83 c0 01          	add    $0x1,%r8
    468e:	4c 39 c1             	cmp    %r8,%rcx
    4691:	75 ad                	jne    4640 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    4693:	49 83 fe 01          	cmp    $0x1,%r14
    4697:	74 0f                	je     46a8 <timer_thread+0x2a8>
    4699:	41 be 01 00 00 00    	mov    $0x1,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    469f:	85 ff                	test   %edi,%edi
    46a1:	7f 86                	jg     4629 <timer_thread+0x229>
    46a3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46a8:	48 83 c5 01          	add    $0x1,%rbp
    46ac:	39 ef                	cmp    %ebp,%edi
    46ae:	0f 8f 64 ff ff ff    	jg     4618 <timer_thread+0x218>
    46b4:	44 89 d5             	mov    %r10d,%ebp
    for (int k = 0 ; k < data->my_thread_count; k++) {
    46b7:	85 ff                	test   %edi,%edi
    46b9:	7e 3b                	jle    46f6 <timer_thread+0x2f6>
    46bb:	31 db                	xor    %ebx,%ebx
    int all_waited = 1;
    46bd:	bf 01 00 00 00       	mov    $0x1,%edi
    46c2:	49 8b 77 18          	mov    0x18(%r15),%rsi
    46c6:	41 8b 57 40          	mov    0x40(%r15),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    46ca:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    46ce:	48 8b 40 38          	mov    0x38(%rax),%rax
    46d2:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    46d8:	39 d1                	cmp    %edx,%ecx
    46da:	0f 8c a8 00 00 00    	jl     4788 <timer_thread+0x388>
    46e0:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    46e6:	39 d0                	cmp    %edx,%eax
    46e8:	7c 6e                	jl     4758 <timer_thread+0x358>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    46ea:	48 83 c3 01          	add    $0x1,%rbx
    46ee:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    46f2:	7f d6                	jg     46ca <timer_thread+0x2ca>
    46f4:	21 fd                	and    %edi,%ebp
    if (all_empty == 1 && all_waited == 1) {
    46f6:	85 ed                	test   %ebp,%ebp
    46f8:	0f 85 b6 00 00 00    	jne    47b4 <timer_thread+0x3b4>
      nanosleep(&drain , &drainrem);
    46fe:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4703:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4708:	e8 73 dc ff ff       	call   2380 <nanosleep@plt>
    470d:	e9 83 fe ff ff       	jmp    4595 <timer_thread+0x195>
    4712:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4718:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    471e:	48 83 ec 08          	sub    $0x8,%rsp
    4722:	bf 01 00 00 00       	mov    $0x1,%edi
    4727:	44 89 f1             	mov    %r14d,%ecx
    472a:	48 8d 35 2c 49 00 00 	lea    0x492c(%rip),%rsi        # 905d <_IO_stdin_used+0x5d>
    4731:	50                   	push   %rax
    4732:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    4738:	89 da                	mov    %ebx,%edx
    473a:	50                   	push   %rax
    473b:	31 c0                	xor    %eax,%eax
    473d:	41 53                	push   %r11
    473f:	e8 4c dd ff ff       	call   2490 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4744:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4748:	48 83 c4 20          	add    $0x20,%rsp
            all_empty = 0;
    474c:	45 31 d2             	xor    %r10d,%r10d
    474f:	e9 3f ff ff ff       	jmp    4693 <timer_thread+0x293>
    4754:	0f 1f 40 00          	nopl   0x0(%rax)
    4758:	89 c2                	mov    %eax,%edx
    475a:	bf 01 00 00 00       	mov    $0x1,%edi
    475f:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4761:	48 83 c3 01          	add    $0x1,%rbx
    4765:	48 8d 35 bc 4b 00 00 	lea    0x4bbc(%rip),%rsi        # 9328 <_IO_stdin_used+0x328>
    476c:	e8 1f dd ff ff       	call   2490 <__printf_chk@plt>
          all_waited = 0; 
    4771:	31 ff                	xor    %edi,%edi
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4773:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4777:	0f 8f 45 ff ff ff    	jg     46c2 <timer_thread+0x2c2>
    477d:	e9 72 ff ff ff       	jmp    46f4 <timer_thread+0x2f4>
    4782:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4788:	89 ca                	mov    %ecx,%edx
    478a:	48 8d 35 97 4b 00 00 	lea    0x4b97(%rip),%rsi        # 9328 <_IO_stdin_used+0x328>
    4791:	bf 01 00 00 00       	mov    $0x1,%edi
    4796:	31 c0                	xor    %eax,%eax
    4798:	e8 f3 dc ff ff       	call   2490 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    479d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    47a1:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    47a5:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    47a7:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    47ab:	48 8b 40 38          	mov    0x38(%rax),%rax
    47af:	e9 2c ff ff ff       	jmp    46e0 <timer_thread+0x2e0>
    47b4:	48 8d 3d 99 48 00 00 	lea    0x4899(%rip),%rdi        # 9054 <_IO_stdin_used+0x54>
    47bb:	e8 50 db ff ff       	call   2310 <puts@plt>
  while (data->running) {
    47c0:	41 8b 57 44          	mov    0x44(%r15),%edx
    47c4:	85 d2                	test   %edx,%edx
    47c6:	0f 84 e8 00 00 00    	je     48b4 <timer_thread+0x4b4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    47cc:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    47d0:	31 db                	xor    %ebx,%ebx
    47d2:	48 8d 2d a1 48 00 00 	lea    0x48a1(%rip),%rbp        # 907a <_IO_stdin_used+0x7a>
    47d9:	4c 8d 25 b5 48 00 00 	lea    0x48b5(%rip),%r12        # 9095 <_IO_stdin_used+0x95>
    47e0:	85 c0                	test   %eax,%eax
    47e2:	7e 38                	jle    481c <timer_thread+0x41c>
    47e4:	0f 1f 40 00          	nopl   0x0(%rax)
    47e8:	31 c0                	xor    %eax,%eax
    47ea:	89 da                	mov    %ebx,%edx
    47ec:	48 89 ee             	mov    %rbp,%rsi
    47ef:	bf 01 00 00 00       	mov    $0x1,%edi
    47f4:	e8 97 dc ff ff       	call   2490 <__printf_chk@plt>
      data->threads[x]->running = 0;
    47f9:	49 8b 47 18          	mov    0x18(%r15),%rax
    47fd:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4801:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4805:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    480c:	0f 84 cf 00 00 00    	je     48e1 <timer_thread+0x4e1>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4812:	48 83 c3 01          	add    $0x1,%rbx
    4816:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    481a:	7f cc                	jg     47e8 <timer_thread+0x3e8>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    481c:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4820:	85 d2                	test   %edx,%edx
    4822:	7e 7c                	jle    48a0 <timer_thread+0x4a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    4824:	41 8b 47 40          	mov    0x40(%r15),%eax
    4828:	85 c0                	test   %eax,%eax
    482a:	7e 74                	jle    48a0 <timer_thread+0x4a0>
    482c:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    482f:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4833:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    483b:	31 c9                	xor    %ecx,%ecx
    483d:	48 c1 e6 09          	shl    $0x9,%rsi
    4841:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4848:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    484c:	48 8b 40 38          	mov    0x38(%rax),%rax
    4850:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4854:	f7 c6 00 02 00 00    	test   $0x200,%esi
    485a:	74 1c                	je     4878 <timer_thread+0x478>
    485c:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4866:	48 05 00 02 00 00    	add    $0x200,%rax
    486c:	48 39 d0             	cmp    %rdx,%rax
    486f:	74 26                	je     4897 <timer_thread+0x497>
    4871:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4878:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4882:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4888:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4892:	48 39 d0             	cmp    %rdx,%rax
    4895:	75 e1                	jne    4878 <timer_thread+0x478>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4897:	48 83 c1 08          	add    $0x8,%rcx
    489b:	48 39 cf             	cmp    %rcx,%rdi
    489e:	75 a8                	jne    4848 <timer_thread+0x448>
    48a0:	48 8d 3d 00 48 00 00 	lea    0x4800(%rip),%rdi        # 90a7 <_IO_stdin_used+0xa7>
    48a7:	e8 64 da ff ff       	call   2310 <puts@plt>
    data->running = 0;
    48ac:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    48b4:	48 8d 3d f3 47 00 00 	lea    0x47f3(%rip),%rdi        # 90ae <_IO_stdin_used+0xae>
    48bb:	e8 50 da ff ff       	call   2310 <puts@plt>
}
    48c0:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    48c5:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48ce:	75 41                	jne    4911 <timer_thread+0x511>
    48d0:	48 83 c4 58          	add    $0x58,%rsp
    48d4:	31 c0                	xor    %eax,%eax
    48d6:	5b                   	pop    %rbx
    48d7:	5d                   	pop    %rbp
    48d8:	41 5c                	pop    %r12
    48da:	41 5d                	pop    %r13
    48dc:	41 5e                	pop    %r14
    48de:	41 5f                	pop    %r15
    48e0:	c3                   	ret
    48e1:	4c 89 e7             	mov    %r12,%rdi
    48e4:	e8 27 da ff ff       	call   2310 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    48e9:	49 8b 47 18          	mov    0x18(%r15),%rax
    48ed:	be 01 00 00 00       	mov    $0x1,%esi
    48f2:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    48f6:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    48fa:	8b 78 68             	mov    0x68(%rax),%edi
    48fd:	e8 3e db ff ff       	call   2440 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4902:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4906:	0f 8f dc fe ff ff    	jg     47e8 <timer_thread+0x3e8>
    490c:	e9 0b ff ff ff       	jmp    481c <timer_thread+0x41c>
}
    4911:	e8 4a da ff ff       	call   2360 <__stack_chk_fail@plt>
    4916:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004920 <minf>:
int minf(int a, int b) {
    4920:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    4924:	39 f7                	cmp    %esi,%edi
    4926:	89 f0                	mov    %esi,%eax
    4928:	0f 4e c7             	cmovle %edi,%eax
}
    492b:	c3                   	ret
    492c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004930 <maxf>:
int maxf(int a, int b) {
    4930:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    4934:	39 f7                	cmp    %esi,%edi
    4936:	89 f0                	mov    %esi,%eax
    4938:	0f 4d c7             	cmovge %edi,%eax
}
    493b:	c3                   	ret
    493c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004940 <strtolower>:
void strtolower(char *str) {
    4940:	f3 0f 1e fa          	endbr64
    4944:	55                   	push   %rbp
    4945:	53                   	push   %rbx
    4946:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    494a:	48 0f be 1f          	movsbq (%rdi),%rbx
    494e:	84 db                	test   %bl,%bl
    4950:	74 24                	je     4976 <strtolower+0x36>
    4952:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4955:	e8 36 dc ff ff       	call   2590 <__ctype_tolower_loc@plt>
    495a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4960:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4963:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4967:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    496a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    496d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4972:	84 db                	test   %bl,%bl
    4974:	75 ea                	jne    4960 <strtolower+0x20>
}
    4976:	48 83 c4 08          	add    $0x8,%rsp
    497a:	5b                   	pop    %rbx
    497b:	5d                   	pop    %rbp
    497c:	c3                   	ret
    497d:	0f 1f 00             	nopl   (%rax)

0000000000004980 <zh_malloc>:
void *zh_malloc(size_t size) {
    4980:	f3 0f 1e fa          	endbr64
    4984:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4988:	e8 c3 da ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    498d:	48 85 c0             	test   %rax,%rax
    4990:	74 05                	je     4997 <zh_malloc+0x17>
}
    4992:	48 83 c4 08          	add    $0x8,%rsp
    4996:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4997:	48 8b 0d 82 76 00 00 	mov    0x7682(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    499e:	ba 28 00 00 00       	mov    $0x28,%edx
    49a3:	be 01 00 00 00       	mov    $0x1,%esi
    49a8:	48 8d 3d 51 4c 00 00 	lea    0x4c51(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    49af:	e8 6c db ff ff       	call   2520 <fwrite@plt>
        exit(1);
    49b4:	bf 01 00 00 00       	mov    $0x1,%edi
    49b9:	e8 42 db ff ff       	call   2500 <exit@plt>
    49be:	66 90                	xchg   %ax,%ax

00000000000049c0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    49c0:	f3 0f 1e fa          	endbr64
    49c4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    49c5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    49ca:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    49cd:	e8 be d9 ff ff       	call   2390 <strrchr@plt>
    if (!dot || dot == filename)
    49d2:	48 85 c0             	test   %rax,%rax
    49d5:	74 11                	je     49e8 <get_filename_ext+0x28>
    49d7:	48 39 c3             	cmp    %rax,%rbx
    49da:	74 0c                	je     49e8 <get_filename_ext+0x28>
    return dot + 1;
    49dc:	48 83 c0 01          	add    $0x1,%rax
}
    49e0:	5b                   	pop    %rbx
    49e1:	c3                   	ret
    49e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    49e8:	48 8d 05 07 47 00 00 	lea    0x4707(%rip),%rax        # 90f6 <_IO_stdin_used+0xf6>
}
    49ef:	5b                   	pop    %rbx
    49f0:	c3                   	ret
    49f1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    49fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a00 <send_headers>:
void send_headers(struct KernelThread *data, struct Buffers *buffers, const char *path, off_t len, struct iovec *iov) {
    4a00:	f3 0f 1e fa          	endbr64
    4a04:	41 55                	push   %r13
    4a06:	48 89 d6             	mov    %rdx,%rsi
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4a09:	ba 00 04 00 00       	mov    $0x400,%edx
    4a0e:	49 89 cd             	mov    %rcx,%r13
    4a11:	41 54                	push   %r12
    4a13:	55                   	push   %rbp
    4a14:	4c 89 c5             	mov    %r8,%rbp
    4a17:	53                   	push   %rbx
    4a18:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4a1f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4a28:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4a30:	31 c0                	xor    %eax,%eax
    4a32:	49 89 e4             	mov    %rsp,%r12
    4a35:	4c 89 e7             	mov    %r12,%rdi
    4a38:	e8 33 da ff ff       	call   2470 <__strcpy_chk@plt>
    for (; *str; ++str)
    4a3d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4a42:	84 db                	test   %bl,%bl
    4a44:	74 24                	je     4a6a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4a46:	e8 45 db ff ff       	call   2590 <__ctype_tolower_loc@plt>
    4a4b:	48 8b 08             	mov    (%rax),%rcx
    4a4e:	4c 89 e0             	mov    %r12,%rax
    4a51:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4a58:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4a5b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4a5f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4a62:	48 0f be 18          	movsbq (%rax),%rbx
    4a66:	84 db                	test   %bl,%bl
    4a68:	75 ee                	jne    4a58 <send_headers+0x58>
    void *buf = malloc(size);
    4a6a:	bf 11 00 00 00       	mov    $0x11,%edi
    4a6f:	e8 dc d9 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    4a74:	48 85 c0             	test   %rax,%rax
    4a77:	0f 84 7e 04 00 00    	je     4efb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4a7d:	66 0f 6f 05 9b 53 00 00 	movdqa 0x539b(%rip),%xmm0        # 9e20 <_IO_stdin_used+0xe20>
    iov[0].iov_base = zh_malloc(slen);
    4a85:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4a89:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4a8e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4a96:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4a9a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4a9d:	e8 ae d9 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    4aa2:	48 85 c0             	test   %rax,%rax
    4aa5:	0f 84 50 04 00 00    	je     4efb <send_headers+0x4fb>
    4aab:	66 0f 6f 05 7d 53 00 00 	movdqa 0x537d(%rip),%xmm0        # 9e30 <_IO_stdin_used+0xe30>
    iov[1].iov_base = zh_malloc(slen);
    4ab3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4ab7:	4c 89 e7             	mov    %r12,%rdi
    4aba:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4ac4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4acc:	0f 11 00             	movups %xmm0,(%rax)
    4acf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4ad3:	be 2e 00 00 00       	mov    $0x2e,%esi
    4ad8:	e8 b3 d8 ff ff       	call   2390 <strrchr@plt>
    if (!dot || dot == filename)
    4add:	48 85 c0             	test   %rax,%rax
    4ae0:	0f 84 ea 02 00 00    	je     4dd0 <send_headers+0x3d0>
    4ae6:	4c 39 e0             	cmp    %r12,%rax
    4ae9:	0f 84 e1 02 00 00    	je     4dd0 <send_headers+0x3d0>
    return dot + 1;
    4aef:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4af3:	48 8d 3d ca 45 00 00 	lea    0x45ca(%rip),%rdi        # 90c4 <_IO_stdin_used+0xc4>
    4afa:	48 89 de             	mov    %rbx,%rsi
    4afd:	e8 ee d8 ff ff       	call   23f0 <strcmp@plt>
    4b02:	85 c0                	test   %eax,%eax
    4b04:	75 20                	jne    4b26 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b06:	66 0f 6f 05 32 53 00 00 	movdqa 0x5332(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4b0e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b16:	66 0f 6f 05 32 53 00 00 	movdqa 0x5332(%rip),%xmm0        # 9e50 <_IO_stdin_used+0xe50>
    4b1e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4b26:	48 89 de             	mov    %rbx,%rsi
    4b29:	48 8d 3d 98 45 00 00 	lea    0x4598(%rip),%rdi        # 90c8 <_IO_stdin_used+0xc8>
    4b30:	e8 bb d8 ff ff       	call   23f0 <strcmp@plt>
    4b35:	85 c0                	test   %eax,%eax
    4b37:	75 20                	jne    4b59 <send_headers+0x159>
    4b39:	66 0f 6f 05 ff 52 00 00 	movdqa 0x52ff(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4b41:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4b49:	66 0f 6f 05 ff 52 00 00 	movdqa 0x52ff(%rip),%xmm0        # 9e50 <_IO_stdin_used+0xe50>
    4b51:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4b59:	48 89 de             	mov    %rbx,%rsi
    4b5c:	48 8d 3d 6a 45 00 00 	lea    0x456a(%rip),%rdi        # 90cd <_IO_stdin_used+0xcd>
    4b63:	e8 88 d8 ff ff       	call   23f0 <strcmp@plt>
    4b68:	85 c0                	test   %eax,%eax
    4b6a:	0f 84 10 02 00 00    	je     4d80 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4b70:	48 89 de             	mov    %rbx,%rsi
    4b73:	48 8d 3d 57 45 00 00 	lea    0x4557(%rip),%rdi        # 90d1 <_IO_stdin_used+0xd1>
    4b7a:	e8 71 d8 ff ff       	call   23f0 <strcmp@plt>
    4b7f:	85 c0                	test   %eax,%eax
    4b81:	0f 84 a9 02 00 00    	je     4e30 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4b87:	48 89 de             	mov    %rbx,%rsi
    4b8a:	48 8d 3d 44 45 00 00 	lea    0x4544(%rip),%rdi        # 90d5 <_IO_stdin_used+0xd5>
    4b91:	e8 5a d8 ff ff       	call   23f0 <strcmp@plt>
    4b96:	85 c0                	test   %eax,%eax
    4b98:	0f 84 6a 02 00 00    	je     4e08 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4b9e:	48 89 de             	mov    %rbx,%rsi
    4ba1:	48 8d 3d 8d 45 00 00 	lea    0x458d(%rip),%rdi        # 9135 <_IO_stdin_used+0x135>
    4ba8:	e8 43 d8 ff ff       	call   23f0 <strcmp@plt>
    4bad:	85 c0                	test   %eax,%eax
    4baf:	0f 84 2b 02 00 00    	je     4de0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4bb5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4bb8:	0f 84 52 01 00 00    	je     4d10 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4bbe:	48 89 de             	mov    %rbx,%rsi
    4bc1:	48 8d 3d 11 45 00 00 	lea    0x4511(%rip),%rdi        # 90d9 <_IO_stdin_used+0xd9>
    4bc8:	e8 23 d8 ff ff       	call   23f0 <strcmp@plt>
    4bcd:	85 c0                	test   %eax,%eax
    4bcf:	0f 84 ab 02 00 00    	je     4e80 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4bd5:	48 89 de             	mov    %rbx,%rsi
    4bd8:	48 8d 3d fe 44 00 00 	lea    0x44fe(%rip),%rdi        # 90dd <_IO_stdin_used+0xdd>
    4bdf:	e8 0c d8 ff ff       	call   23f0 <strcmp@plt>
    4be4:	85 c0                	test   %eax,%eax
    4be6:	0f 84 6c 02 00 00    	je     4e58 <send_headers+0x458>
    slen = strlen(send_buffer);
    4bec:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4bf4:	4c 89 e7             	mov    %r12,%rdi
    4bf7:	e8 54 d7 ff ff       	call   2350 <strlen@plt>
    void *buf = malloc(size);
    4bfc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4bff:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4c02:	e8 49 d8 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    4c07:	48 85 c0             	test   %rax,%rax
    4c0a:	0f 84 eb 02 00 00    	je     4efb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4c10:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4c14:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4c18:	83 fb 08             	cmp    $0x8,%ebx
    4c1b:	0f 83 3f 01 00 00    	jae    4d60 <send_headers+0x360>
    4c21:	f6 c3 04             	test   $0x4,%bl
    4c24:	0f 85 7b 02 00 00    	jne    4ea5 <send_headers+0x4a5>
    4c2a:	85 db                	test   %ebx,%ebx
    4c2c:	74 13                	je     4c41 <send_headers+0x241>
    4c2e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4c36:	88 10                	mov    %dl,(%rax)
    4c38:	f6 c3 02             	test   $0x2,%bl
    4c3b:	0f 85 96 02 00 00    	jne    4ed7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4c41:	4d 89 e8             	mov    %r13,%r8
    4c44:	48 8d 0d 96 44 00 00 	lea    0x4496(%rip),%rcx        # 90e1 <_IO_stdin_used+0xe1>
    4c4b:	4c 89 e7             	mov    %r12,%rdi
    4c4e:	31 c0                	xor    %eax,%eax
    4c50:	ba 00 04 00 00       	mov    $0x400,%edx
    4c55:	be 01 00 00 00       	mov    $0x1,%esi
    4c5a:	e8 41 d9 ff ff       	call   25a0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4c5f:	4c 89 e7             	mov    %r12,%rdi
    4c62:	e8 e9 d6 ff ff       	call   2350 <strlen@plt>
    void *buf = malloc(size);
    4c67:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4c6a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4c6d:	e8 de d7 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    4c72:	48 85 c0             	test   %rax,%rax
    4c75:	0f 84 80 02 00 00    	je     4efb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4c7b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4c7f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4c83:	83 fb 08             	cmp    $0x8,%ebx
    4c86:	0f 83 1c 01 00 00    	jae    4da8 <send_headers+0x3a8>
    4c8c:	f6 c3 04             	test   $0x4,%bl
    4c8f:	0f 85 29 02 00 00    	jne    4ebe <send_headers+0x4be>
    4c95:	85 db                	test   %ebx,%ebx
    4c97:	74 13                	je     4cac <send_headers+0x2ac>
    4c99:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4ca1:	88 10                	mov    %dl,(%rax)
    4ca3:	f6 c3 02             	test   $0x2,%bl
    4ca6:	0f 85 3d 02 00 00    	jne    4ee9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4cac:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4cb1:	bf 02 00 00 00       	mov    $0x2,%edi
    4cb6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4cbe:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4cc6:	e8 85 d7 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    4ccb:	48 85 c0             	test   %rax,%rax
    4cce:	0f 84 27 02 00 00    	je     4efb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4cd4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4cdc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4ce0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4ce8:	66 89 10             	mov    %dx,(%rax)
}
    4ceb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4cf3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4cfc:	0f 85 20 02 00 00    	jne    4f22 <send_headers+0x522>
    4d02:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4d09:	5b                   	pop    %rbx
    4d0a:	5d                   	pop    %rbp
    4d0b:	41 5c                	pop    %r12
    4d0d:	41 5d                	pop    %r13
    4d0f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4d10:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4d14:	0f 85 a4 fe ff ff    	jne    4bbe <send_headers+0x1be>
    4d1a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4d1e:	0f 85 9a fe ff ff    	jne    4bbe <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d24:	66 0f 6f 05 74 51 00 00 	movdqa 0x5174(%rip),%xmm0        # 9ea0 <_IO_stdin_used+0xea0>
    4d2c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4d36:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d3e:	66 0f 6f 05 6a 51 00 00 	movdqa 0x516a(%rip),%xmm0        # 9eb0 <_IO_stdin_used+0xeb0>
    4d46:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4d4e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4d56:	e9 63 fe ff ff       	jmp    4bbe <send_headers+0x1be>
    4d5b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4d60:	89 da                	mov    %ebx,%edx
    4d62:	48 89 c7             	mov    %rax,%rdi
    4d65:	4c 89 e6             	mov    %r12,%rsi
    4d68:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4d6d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4d72:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4d75:	c1 e9 03             	shr    $0x3,%ecx
    4d78:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4d7b:	e9 c1 fe ff ff       	jmp    4c41 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d80:	66 0f 6f 05 b8 50 00 00 	movdqa 0x50b8(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4d88:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d90:	66 0f 6f 05 c8 50 00 00 	movdqa 0x50c8(%rip),%xmm0        # 9e60 <_IO_stdin_used+0xe60>
    4d98:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4da0:	e9 cb fd ff ff       	jmp    4b70 <send_headers+0x170>
    4da5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4da8:	89 da                	mov    %ebx,%edx
    4daa:	48 89 c7             	mov    %rax,%rdi
    4dad:	4c 89 e6             	mov    %r12,%rsi
    4db0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4db5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4dba:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4dbd:	c1 e9 03             	shr    $0x3,%ecx
    4dc0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4dc3:	e9 e4 fe ff ff       	jmp    4cac <send_headers+0x2ac>
    4dc8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4dd0:	48 8d 1d 1f 43 00 00 	lea    0x431f(%rip),%rbx        # 90f6 <_IO_stdin_used+0xf6>
    4dd7:	e9 94 fd ff ff       	jmp    4b70 <send_headers+0x170>
    4ddc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4de0:	66 0f 6f 05 98 50 00 00 	movdqa 0x5098(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4de8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4df0:	66 0f 6f 05 98 50 00 00 	movdqa 0x5098(%rip),%xmm0        # 9e90 <_IO_stdin_used+0xe90>
    4df8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e00:	e9 b0 fd ff ff       	jmp    4bb5 <send_headers+0x1b5>
    4e05:	0f 1f 00             	nopl   (%rax)
    4e08:	66 0f 6f 05 70 50 00 00 	movdqa 0x5070(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4e10:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e18:	66 0f 6f 05 70 50 00 00 	movdqa 0x5070(%rip),%xmm0        # 9e90 <_IO_stdin_used+0xe90>
    4e20:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e28:	e9 71 fd ff ff       	jmp    4b9e <send_headers+0x19e>
    4e2d:	0f 1f 00             	nopl   (%rax)
    4e30:	66 0f 6f 05 08 50 00 00 	movdqa 0x5008(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4e38:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e40:	66 0f 6f 05 28 50 00 00 	movdqa 0x5028(%rip),%xmm0        # 9e70 <_IO_stdin_used+0xe70>
    4e48:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e50:	e9 32 fd ff ff       	jmp    4b87 <send_headers+0x187>
    4e55:	0f 1f 00             	nopl   (%rax)
    4e58:	66 0f 6f 05 20 50 00 00 	movdqa 0x5020(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4e60:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e68:	66 0f 6f 05 60 50 00 00 	movdqa 0x5060(%rip),%xmm0        # 9ed0 <_IO_stdin_used+0xed0>
    4e70:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4e78:	e9 6f fd ff ff       	jmp    4bec <send_headers+0x1ec>
    4e7d:	0f 1f 00             	nopl   (%rax)
    4e80:	66 0f 6f 05 f8 4f 00 00 	movdqa 0x4ff8(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4e88:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e90:	66 0f 6f 05 28 50 00 00 	movdqa 0x5028(%rip),%xmm0        # 9ec0 <_IO_stdin_used+0xec0>
    4e98:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4ea0:	e9 30 fd ff ff       	jmp    4bd5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ea5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4eac:	89 db                	mov    %ebx,%ebx
    4eae:	89 10                	mov    %edx,(%rax)
    4eb0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4eb5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4eb9:	e9 83 fd ff ff       	jmp    4c41 <send_headers+0x241>
    4ebe:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4ec5:	89 db                	mov    %ebx,%ebx
    4ec7:	89 10                	mov    %edx,(%rax)
    4ec9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4ece:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4ed2:	e9 d5 fd ff ff       	jmp    4cac <send_headers+0x2ac>
    4ed7:	89 db                	mov    %ebx,%ebx
    4ed9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4edf:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4ee4:	e9 58 fd ff ff       	jmp    4c41 <send_headers+0x241>
    4ee9:	89 db                	mov    %ebx,%ebx
    4eeb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4ef1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4ef6:	e9 b1 fd ff ff       	jmp    4cac <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4efb:	48 8b 0d 1e 71 00 00 	mov    0x711e(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    4f02:	ba 28 00 00 00       	mov    $0x28,%edx
    4f07:	be 01 00 00 00       	mov    $0x1,%esi
    4f0c:	48 8d 3d ed 46 00 00 	lea    0x46ed(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    4f13:	e8 08 d6 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4f18:	bf 01 00 00 00       	mov    $0x1,%edi
    4f1d:	e8 de d5 ff ff       	call   2500 <exit@plt>
}
    4f22:	e8 39 d4 ff ff       	call   2360 <__stack_chk_fail@plt>
    4f27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004f30 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4f30:	f3 0f 1e fa          	endbr64
    4f34:	41 55                	push   %r13
    4f36:	49 89 d5             	mov    %rdx,%r13
    4f39:	41 54                	push   %r12
    4f3b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4f3e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4f41:	55                   	push   %rbp
    4f42:	53                   	push   %rbx
    4f43:	48 89 f3             	mov    %rsi,%rbx
    4f46:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4f4a:	e8 01 d5 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    4f4f:	48 85 c0             	test   %rax,%rax
    4f52:	74 6b                	je     4fbf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4f54:	4c 89 e7             	mov    %r12,%rdi
    4f57:	48 89 c5             	mov    %rax,%rbp
    4f5a:	31 f6                	xor    %esi,%esi
    4f5c:	31 c0                	xor    %eax,%eax
    4f5e:	e8 6d d5 ff ff       	call   24d0 <open@plt>
    4f63:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    4f66:	85 c0                	test   %eax,%eax
    4f68:	0f 88 68 d6 ff ff    	js     25d6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    4f6e:	48 89 da             	mov    %rbx,%rdx
    4f71:	48 89 ee             	mov    %rbp,%rsi
    4f74:	89 c7                	mov    %eax,%edi
    4f76:	e8 55 d4 ff ff       	call   23d0 <read@plt>
    if (ret < file_size) {
    4f7b:	48 98                	cltq
    4f7d:	48 39 d8             	cmp    %rbx,%rax
    4f80:	7c 1e                	jl     4fa0 <copy_file_contents+0x70>
    close(fd);
    4f82:	44 89 e7             	mov    %r12d,%edi
    4f85:	e8 26 d4 ff ff       	call   23b0 <close@plt>
    iov->iov_base = buf;
    4f8a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    4f8e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    4f92:	48 83 c4 08          	add    $0x8,%rsp
    4f96:	5b                   	pop    %rbx
    4f97:	5d                   	pop    %rbp
    4f98:	41 5c                	pop    %r12
    4f9a:	41 5d                	pop    %r13
    4f9c:	c3                   	ret
    4f9d:	0f 1f 00             	nopl   (%rax)
    4fa0:	48 8b 0d 79 70 00 00 	mov    0x7079(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    4fa7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    4fac:	be 01 00 00 00       	mov    $0x1,%esi
    4fb1:	48 8d 3d 3f 41 00 00 	lea    0x413f(%rip),%rdi        # 90f7 <_IO_stdin_used+0xf7>
    4fb8:	e8 63 d5 ff ff       	call   2520 <fwrite@plt>
    4fbd:	eb c3                	jmp    4f82 <copy_file_contents+0x52>
    4fbf:	48 8b 0d 5a 70 00 00 	mov    0x705a(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    4fc6:	ba 28 00 00 00       	mov    $0x28,%edx
    4fcb:	be 01 00 00 00       	mov    $0x1,%esi
    4fd0:	48 8d 3d 29 46 00 00 	lea    0x4629(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    4fd7:	e8 44 d5 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    4fdc:	bf 01 00 00 00       	mov    $0x1,%edi
    4fe1:	e8 1a d5 ff ff       	call   2500 <exit@plt>
    4fe6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004ff0 <add_write_request>:
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    4ff0:	f3 0f 1e fa          	endbr64
    4ff4:	55                   	push   %rbp
    struct Write *write = calloc(1, sizeof(struct Write));
    4ff5:	be 10 00 00 00       	mov    $0x10,%esi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    4ffa:	48 89 d5             	mov    %rdx,%rbp
    4ffd:	53                   	push   %rbx
    4ffe:	48 89 fb             	mov    %rdi,%rbx
    struct Write *write = calloc(1, sizeof(struct Write));
    5001:	bf 01 00 00 00       	mov    $0x1,%edi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    5006:	48 83 ec 08          	sub    $0x8,%rsp
    struct Write *write = calloc(1, sizeof(struct Write));
    500a:	e8 d1 d3 ff ff       	call   23e0 <calloc@plt>
    write->client_socket = req->client_socket;
    500f:	f3 0f 7e 45 08       	movq   0x8(%rbp),%xmm0
    req->event_type = EVENT_TYPE_WRITE;
    5014:	c7 45 00 02 00 00 00 	movl   $0x2,0x0(%rbp)
    if (write->client_socket == -1) {
    501b:	66 0f 7e c2          	movd   %xmm0,%edx
    write->client_socket = req->client_socket;
    501f:	66 0f d6 40 08       	movq   %xmm0,0x8(%rax)
    5024:	66 0f 70 c8 e5       	pshufd $0xe5,%xmm0,%xmm1
    if (write->client_socket == -1) {
    5029:	83 fa ff             	cmp    $0xffffffff,%edx
    502c:	74 69                	je     5097 <add_write_request+0xa7>
    buffersend_filter(data, &data->iomailboxes[data->other_io], IO_WRITE, write, write->sockettoken);
    502e:	48 63 b3 18 01 00 00 	movslq 0x118(%rbx),%rsi
    write->request = req;
    5035:	48 89 28             	mov    %rbp,(%rax)
    5038:	66 0f 7e cf          	movd   %xmm1,%edi
    buffersend_filter(data, &data->iomailboxes[data->other_io], IO_WRITE, write, write->sockettoken);
    503c:	48 c1 e6 04          	shl    $0x4,%rsi
    5040:	48 03 b3 10 01 00 00 	add    0x110(%rbx),%rsi
  while (data->running == 1) {
    5047:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    504b:	75 41                	jne    508e <add_write_request+0x9e>
      for (int x = 0 ; x < buffers->count ; x++) {
    504d:	48 63 0e             	movslq (%rsi),%rcx
    5050:	85 c9                	test   %ecx,%ecx
    5052:	7e f3                	jle    5047 <add_write_request+0x57>
    5054:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    5058:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    505c:	48 8d 0c ca          	lea    (%rdx,%rcx,8),%rcx
    5060:	eb 0f                	jmp    5071 <add_write_request+0x81>
    5062:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5068:	48 83 c2 28          	add    $0x28,%rdx
    506c:	48 39 ca             	cmp    %rcx,%rdx
    506f:	74 d6                	je     5047 <add_write_request+0x57>
        if (buffers->buffer[x].available == 0) {
    5071:	44 8b 42 08          	mov    0x8(%rdx),%r8d
    5075:	45 85 c0             	test   %r8d,%r8d
    5078:	75 ee                	jne    5068 <add_write_request+0x78>
          buffers->buffer[x].data = send;
    507a:	48 89 02             	mov    %rax,(%rdx)
          buffers->buffer[x].kind = kind;
    507d:	c7 42 20 03 00 00 00 	movl   $0x3,0x20(%rdx)
          buffers->buffer[x].filter = filter;
    5084:	89 7a 24             	mov    %edi,0x24(%rdx)
          buffers->buffer[x].available = 1;
    5087:	c7 42 08 01 00 00 00 	movl   $0x1,0x8(%rdx)
}
    508e:	48 83 c4 08          	add    $0x8,%rsp
    5092:	31 c0                	xor    %eax,%eax
    5094:	5b                   	pop    %rbx
    5095:	5d                   	pop    %rbp
    5096:	c3                   	ret
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5097:	bf 01 00 00 00       	mov    $0x1,%edi
    509c:	48 8d 35 8d 45 00 00 	lea    0x458d(%rip),%rsi        # 9630 <_IO_stdin_used+0x630>
    50a3:	31 c0                	xor    %eax,%eax
    50a5:	e8 e6 d3 ff ff       	call   2490 <__printf_chk@plt>
      exit(1);
    50aa:	bf 01 00 00 00       	mov    $0x1,%edi
    50af:	e8 4c d4 ff ff       	call   2500 <exit@plt>
    50b4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    50bf:	90                   	nop

00000000000050c0 <add_read_request>:
int add_read_request(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    50c0:	f3 0f 1e fa          	endbr64
    50c4:	41 56                	push   %r14
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    50c6:	41 8b 40 44          	mov    0x44(%r8),%eax
    50ca:	41 89 ce             	mov    %ecx,%r14d
    50cd:	41 55                	push   %r13
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    50cf:	41 8b 88 c0 00 00 00 	mov    0xc0(%r8),%ecx
    50d6:	41 89 d5             	mov    %edx,%r13d
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    50d9:	49 8b 10             	mov    (%r8),%rdx
    50dc:	41 54                	push   %r12
	unsigned int head, next = sq->sqe_tail + 1;
    50de:	83 c0 01             	add    $0x1,%eax
    50e1:	55                   	push   %rbp
    50e2:	53                   	push   %rbx
    50e3:	4c 89 c3             	mov    %r8,%rbx
		head = IO_URING_READ_ONCE(*sq->khead);
    50e6:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    50e8:	f6 c1 02             	test   $0x2,%cl
    50eb:	74 00                	je     50ed <add_read_request+0x2d>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    50ed:	89 c2                	mov    %eax,%edx
    50ef:	29 f2                	sub    %esi,%edx
    50f1:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    50f4:	0f 82 e8 d4 ff ff    	jb     25e2 <add_read_request.cold>
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    50fa:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    50fd:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    5100:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5103:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    5108:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    510b:	23 6b 58             	and    0x58(%rbx),%ebp
    510e:	d3 e5                	shl    %cl,%ebp
    5110:	48 c1 e5 06          	shl    $0x6,%rbp
    5114:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5118:	e8 33 d3 ff ff       	call   2450 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    511d:	be 01 00 00 00       	mov    $0x1,%esi
    5122:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5127:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    512a:	e8 b1 d2 ff ff       	call   23e0 <calloc@plt>
    req->client_socket = client_socket;
    512f:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5134:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5138:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    513b:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    5140:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->sockettoken = sockettoken;
    5145:	45 89 74 24 0c       	mov    %r14d,0xc(%r12)
    req->iov[0].iov_len = READ_SZ;
    514a:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    5153:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    515b:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    515f:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    5163:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    516a:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    5172:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    5176:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    517e:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    5186:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    518a:	e8 e1 d1 ff ff       	call   2370 <io_uring_submit@plt>
}
    518f:	5b                   	pop    %rbx
    5190:	31 c0                	xor    %eax,%eax
    5192:	5d                   	pop    %rbp
    5193:	41 5c                	pop    %r12
    5195:	41 5d                	pop    %r13
    5197:	41 5e                	pop    %r14
    5199:	c3                   	ret
    519a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000051a0 <_send_static_string_content>:
void _send_static_string_content(struct KernelThread *data, struct Buffers *buffers, const char *str, int client_socket, int sockettoken, struct io_uring *ring) {
    51a0:	f3 0f 1e fa          	endbr64
    51a4:	41 57                	push   %r15
    51a6:	4d 89 cf             	mov    %r9,%r15
    51a9:	41 56                	push   %r14
    51ab:	49 89 f6             	mov    %rsi,%r14
    51ae:	41 55                	push   %r13
    51b0:	41 54                	push   %r12
    51b2:	45 89 c4             	mov    %r8d,%r12d
    51b5:	55                   	push   %rbp
    51b6:	48 89 d5             	mov    %rdx,%rbp
    51b9:	53                   	push   %rbx
    51ba:	89 cb                	mov    %ecx,%ebx
    51bc:	48 83 ec 18          	sub    $0x18,%rsp
    51c0:	48 89 3c 24          	mov    %rdi,(%rsp)
    void *buf = malloc(size);
    51c4:	bf 20 00 00 00       	mov    $0x20,%edi
    51c9:	e8 82 d2 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    51ce:	48 85 c0             	test   %rax,%rax
    51d1:	74 6a                	je     523d <_send_static_string_content+0x9d>
    51d3:	49 89 c5             	mov    %rax,%r13
    unsigned long slen = strlen(str);
    51d6:	48 89 ef             	mov    %rbp,%rdi
    51d9:	e8 72 d1 ff ff       	call   2350 <strlen@plt>
    req->iovec_count = 1;
    51de:	41 c7 45 04 01 00 00 00 	movl   $0x1,0x4(%r13)
    req->client_socket = client_socket;
    51e6:	41 89 5d 08          	mov    %ebx,0x8(%r13)
    req->sockettoken = sockettoken;
    51ea:	45 89 65 0c          	mov    %r12d,0xc(%r13)
    if (req->client_socket == -1) {
    51ee:	83 fb ff             	cmp    $0xffffffff,%ebx
    51f1:	74 71                	je     5264 <_send_static_string_content+0xc4>
    void *buf = malloc(size);
    51f3:	48 89 c7             	mov    %rax,%rdi
    51f6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    51fb:	e8 50 d2 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    5200:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    5205:	48 85 c0             	test   %rax,%rax
    void *buf = malloc(size);
    5208:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    520b:	74 30                	je     523d <_send_static_string_content+0x9d>
    req->iov[0].iov_len = slen;
    520d:	49 89 55 18          	mov    %rdx,0x18(%r13)
    5211:	48 89 ee             	mov    %rbp,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    5214:	49 89 45 10          	mov    %rax,0x10(%r13)
    5218:	e8 03 d2 ff ff       	call   2420 <memcpy@plt>
    add_write_request(data, buffers, req, ring);
    521d:	48 8b 3c 24          	mov    (%rsp),%rdi
}
    5221:	48 83 c4 18          	add    $0x18,%rsp
    add_write_request(data, buffers, req, ring);
    5225:	4c 89 f9             	mov    %r15,%rcx
}
    5228:	5b                   	pop    %rbx
    add_write_request(data, buffers, req, ring);
    5229:	4c 89 ea             	mov    %r13,%rdx
}
    522c:	5d                   	pop    %rbp
    add_write_request(data, buffers, req, ring);
    522d:	4c 89 f6             	mov    %r14,%rsi
}
    5230:	41 5c                	pop    %r12
    5232:	41 5d                	pop    %r13
    5234:	41 5e                	pop    %r14
    5236:	41 5f                	pop    %r15
    add_write_request(data, buffers, req, ring);
    5238:	e9 b3 fd ff ff       	jmp    4ff0 <add_write_request>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    523d:	48 8b 0d dc 6d 00 00 	mov    0x6ddc(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5244:	ba 28 00 00 00       	mov    $0x28,%edx
    5249:	be 01 00 00 00       	mov    $0x1,%esi
    524e:	48 8d 3d ab 43 00 00 	lea    0x43ab(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    5255:	e8 c6 d2 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    525a:	bf 01 00 00 00       	mov    $0x1,%edi
    525f:	e8 9c d2 ff ff       	call   2500 <exit@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5264:	48 8d 3d a7 3e 00 00 	lea    0x3ea7(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    526b:	e8 a0 d0 ff ff       	call   2310 <puts@plt>
      exit(1);
    5270:	bf 01 00 00 00       	mov    $0x1,%edi
    5275:	e8 86 d2 ff ff       	call   2500 <exit@plt>
    527a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005280 <handle_unimplemented_method>:
void handle_unimplemented_method(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5280:	f3 0f 1e fa          	endbr64
    5284:	41 57                	push   %r15
    5286:	41 56                	push   %r14
    5288:	4d 89 c6             	mov    %r8,%r14
    528b:	41 55                	push   %r13
    528d:	49 89 f5             	mov    %rsi,%r13
    5290:	41 54                	push   %r12
    5292:	55                   	push   %rbp
    5293:	89 cd                	mov    %ecx,%ebp
    5295:	53                   	push   %rbx
    5296:	89 d3                	mov    %edx,%ebx
    5298:	48 83 ec 18          	sub    $0x18,%rsp
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, sockettoken, ring);
    529c:	4c 8b 3d 75 6d 00 00 	mov    0x6d75(%rip),%r15        # c018 <unimplemented_content>
void handle_unimplemented_method(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    52a3:	48 89 3c 24          	mov    %rdi,(%rsp)
    void *buf = malloc(size);
    52a7:	bf 20 00 00 00       	mov    $0x20,%edi
    52ac:	e8 9f d1 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    52b1:	48 85 c0             	test   %rax,%rax
    52b4:	74 6f                	je     5325 <handle_unimplemented_method+0xa5>
    52b6:	49 89 c4             	mov    %rax,%r12
    unsigned long slen = strlen(str);
    52b9:	4c 89 ff             	mov    %r15,%rdi
    52bc:	e8 8f d0 ff ff       	call   2350 <strlen@plt>
    req->client_socket = client_socket;
    52c1:	41 89 5c 24 08       	mov    %ebx,0x8(%r12)
    req->iovec_count = 1;
    52c6:	41 c7 44 24 04 01 00 00 00 	movl   $0x1,0x4(%r12)
    req->sockettoken = sockettoken;
    52cf:	41 89 6c 24 0c       	mov    %ebp,0xc(%r12)
    if (req->client_socket == -1) {
    52d4:	83 fb ff             	cmp    $0xffffffff,%ebx
    52d7:	74 73                	je     534c <handle_unimplemented_method+0xcc>
    void *buf = malloc(size);
    52d9:	48 89 c7             	mov    %rax,%rdi
    52dc:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    52e1:	e8 6a d1 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    52e6:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    52eb:	48 85 c0             	test   %rax,%rax
    void *buf = malloc(size);
    52ee:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    52f1:	74 32                	je     5325 <handle_unimplemented_method+0xa5>
    req->iov[0].iov_len = slen;
    52f3:	49 89 54 24 18       	mov    %rdx,0x18(%r12)
    52f8:	4c 89 fe             	mov    %r15,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    52fb:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    5300:	e8 1b d1 ff ff       	call   2420 <memcpy@plt>
    add_write_request(data, buffers, req, ring);
    5305:	48 8b 3c 24          	mov    (%rsp),%rdi
}
    5309:	48 83 c4 18          	add    $0x18,%rsp
    add_write_request(data, buffers, req, ring);
    530d:	4c 89 f1             	mov    %r14,%rcx
}
    5310:	5b                   	pop    %rbx
    add_write_request(data, buffers, req, ring);
    5311:	4c 89 e2             	mov    %r12,%rdx
}
    5314:	5d                   	pop    %rbp
    add_write_request(data, buffers, req, ring);
    5315:	4c 89 ee             	mov    %r13,%rsi
}
    5318:	41 5c                	pop    %r12
    531a:	41 5d                	pop    %r13
    531c:	41 5e                	pop    %r14
    531e:	41 5f                	pop    %r15
    add_write_request(data, buffers, req, ring);
    5320:	e9 cb fc ff ff       	jmp    4ff0 <add_write_request>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5325:	48 8b 0d f4 6c 00 00 	mov    0x6cf4(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    532c:	ba 28 00 00 00       	mov    $0x28,%edx
    5331:	be 01 00 00 00       	mov    $0x1,%esi
    5336:	48 8d 3d c3 42 00 00 	lea    0x42c3(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    533d:	e8 de d1 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5342:	bf 01 00 00 00       	mov    $0x1,%edi
    5347:	e8 b4 d1 ff ff       	call   2500 <exit@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    534c:	48 8d 3d bf 3d 00 00 	lea    0x3dbf(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    5353:	e8 b8 cf ff ff       	call   2310 <puts@plt>
      exit(1);
    5358:	bf 01 00 00 00       	mov    $0x1,%edi
    535d:	e8 9e d1 ff ff       	call   2500 <exit@plt>
    5362:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    536d:	0f 1f 00             	nopl   (%rax)

0000000000005370 <handle_http_404>:
void handle_http_404(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5370:	f3 0f 1e fa          	endbr64
    5374:	41 57                	push   %r15
    5376:	41 56                	push   %r14
    5378:	4d 89 c6             	mov    %r8,%r14
    537b:	41 55                	push   %r13
    537d:	49 89 f5             	mov    %rsi,%r13
    5380:	41 54                	push   %r12
    5382:	55                   	push   %rbp
    5383:	89 cd                	mov    %ecx,%ebp
    5385:	53                   	push   %rbx
    5386:	89 d3                	mov    %edx,%ebx
    5388:	48 83 ec 18          	sub    $0x18,%rsp
    _send_static_string_content(data, buffers, http_404_content, client_socket, sockettoken, ring);
    538c:	4c 8b 3d 7d 6c 00 00 	mov    0x6c7d(%rip),%r15        # c010 <http_404_content>
void handle_http_404(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5393:	48 89 3c 24          	mov    %rdi,(%rsp)
    void *buf = malloc(size);
    5397:	bf 20 00 00 00       	mov    $0x20,%edi
    539c:	e8 af d0 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    53a1:	48 85 c0             	test   %rax,%rax
    53a4:	74 6f                	je     5415 <handle_http_404+0xa5>
    53a6:	49 89 c4             	mov    %rax,%r12
    unsigned long slen = strlen(str);
    53a9:	4c 89 ff             	mov    %r15,%rdi
    53ac:	e8 9f cf ff ff       	call   2350 <strlen@plt>
    req->client_socket = client_socket;
    53b1:	41 89 5c 24 08       	mov    %ebx,0x8(%r12)
    req->iovec_count = 1;
    53b6:	41 c7 44 24 04 01 00 00 00 	movl   $0x1,0x4(%r12)
    req->sockettoken = sockettoken;
    53bf:	41 89 6c 24 0c       	mov    %ebp,0xc(%r12)
    if (req->client_socket == -1) {
    53c4:	83 fb ff             	cmp    $0xffffffff,%ebx
    53c7:	74 73                	je     543c <handle_http_404+0xcc>
    void *buf = malloc(size);
    53c9:	48 89 c7             	mov    %rax,%rdi
    53cc:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    53d1:	e8 7a d0 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    53d6:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    53db:	48 85 c0             	test   %rax,%rax
    void *buf = malloc(size);
    53de:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    53e1:	74 32                	je     5415 <handle_http_404+0xa5>
    req->iov[0].iov_len = slen;
    53e3:	49 89 54 24 18       	mov    %rdx,0x18(%r12)
    53e8:	4c 89 fe             	mov    %r15,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    53eb:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    53f0:	e8 2b d0 ff ff       	call   2420 <memcpy@plt>
    add_write_request(data, buffers, req, ring);
    53f5:	48 8b 3c 24          	mov    (%rsp),%rdi
}
    53f9:	48 83 c4 18          	add    $0x18,%rsp
    add_write_request(data, buffers, req, ring);
    53fd:	4c 89 f1             	mov    %r14,%rcx
}
    5400:	5b                   	pop    %rbx
    add_write_request(data, buffers, req, ring);
    5401:	4c 89 e2             	mov    %r12,%rdx
}
    5404:	5d                   	pop    %rbp
    add_write_request(data, buffers, req, ring);
    5405:	4c 89 ee             	mov    %r13,%rsi
}
    5408:	41 5c                	pop    %r12
    540a:	41 5d                	pop    %r13
    540c:	41 5e                	pop    %r14
    540e:	41 5f                	pop    %r15
    add_write_request(data, buffers, req, ring);
    5410:	e9 db fb ff ff       	jmp    4ff0 <add_write_request>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5415:	48 8b 0d 04 6c 00 00 	mov    0x6c04(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    541c:	ba 28 00 00 00       	mov    $0x28,%edx
    5421:	be 01 00 00 00       	mov    $0x1,%esi
    5426:	48 8d 3d d3 41 00 00 	lea    0x41d3(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    542d:	e8 ee d0 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    5432:	bf 01 00 00 00       	mov    $0x1,%edi
    5437:	e8 c4 d0 ff ff       	call   2500 <exit@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    543c:	48 8d 3d cf 3c 00 00 	lea    0x3ccf(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    5443:	e8 c8 ce ff ff       	call   2310 <puts@plt>
      exit(1);
    5448:	bf 01 00 00 00       	mov    $0x1,%edi
    544d:	e8 ae d0 ff ff       	call   2500 <exit@plt>
    5452:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    545d:	0f 1f 00             	nopl   (%rax)

0000000000005460 <handle_get_method>:
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, int sockettoken, struct io_uring *ring) {
    5460:	f3 0f 1e fa          	endbr64
    5464:	41 57                	push   %r15
    5466:	41 56                	push   %r14
    5468:	41 89 ce             	mov    %ecx,%r14d
    546b:	41 55                	push   %r13
    546d:	45 89 c5             	mov    %r8d,%r13d
    5470:	41 54                	push   %r12
    5472:	4d 89 cc             	mov    %r9,%r12
    5475:	55                   	push   %rbp
    5476:	48 89 f5             	mov    %rsi,%rbp
    5479:	53                   	push   %rbx
    547a:	48 89 fb             	mov    %rdi,%rbx
    if (path[strlen(path) - 1] == '/') {
    547d:	48 89 d7             	mov    %rdx,%rdi
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, int sockettoken, struct io_uring *ring) {
    5480:	48 81 ec b8 04 00 00 	sub    $0x4b8,%rsp
    5487:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5490:	48 89 84 24 a8 04 00 00 	mov    %rax,0x4a8(%rsp)
    5498:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    549a:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    549f:	e8 ac ce ff ff       	call   2350 <strlen@plt>
    54a4:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    54a9:	48 89 c2             	mov    %rax,%rdx
    54ac:	80 7c 06 ff 2f       	cmpb   $0x2f,-0x1(%rsi,%rax,1)
    54b1:	0f 84 a9 00 00 00    	je     5560 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    54b7:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    54bc:	48 83 c2 01          	add    $0x1,%rdx
    54c0:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
    54c8:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    54cd:	66 89 84 24 a4 00 00 00 	mov    %ax,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    54d5:	4c 8d bc 24 a0 00 00 00 	lea    0xa0(%rsp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    54dd:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    54e8:	e8 13 cf ff ff       	call   2400 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    54ed:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
    54f2:	4c 89 ff             	mov    %r15,%rdi
    54f5:	e8 16 cf ff ff       	call   2410 <stat@plt>
    54fa:	83 f8 ff             	cmp    $0xffffffff,%eax
    54fd:	74 14                	je     5513 <handle_get_method+0xb3>
        if (S_ISREG(path_stat.st_mode)) {
    54ff:	8b 44 24 28          	mov    0x28(%rsp),%eax
    5503:	25 00 f0 00 00       	and    $0xf000,%eax
    5508:	3d 00 80 00 00       	cmp    $0x8000,%eax
    550d:	0f 84 ad 00 00 00    	je     55c0 <handle_get_method+0x160>
    _send_static_string_content(data, buffers, http_404_content, client_socket, sockettoken, ring);
    5513:	48 8b 15 f6 6a 00 00 	mov    0x6af6(%rip),%rdx        # c010 <http_404_content>
    551a:	4d 89 e1             	mov    %r12,%r9
    551d:	45 89 e8             	mov    %r13d,%r8d
    5520:	44 89 f1             	mov    %r14d,%ecx
    5523:	48 89 ee             	mov    %rbp,%rsi
    5526:	48 89 df             	mov    %rbx,%rdi
    5529:	e8 72 fc ff ff       	call   51a0 <_send_static_string_content>
}
    552e:	48 8b 84 24 a8 04 00 00 	mov    0x4a8(%rsp),%rax
    5536:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    553f:	0f 85 e3 00 00 00    	jne    5628 <handle_get_method+0x1c8>
    5545:	48 81 c4 b8 04 00 00 	add    $0x4b8,%rsp
    554c:	5b                   	pop    %rbx
    554d:	5d                   	pop    %rbp
    554e:	41 5c                	pop    %r12
    5550:	41 5d                	pop    %r13
    5552:	41 5e                	pop    %r14
    5554:	41 5f                	pop    %r15
    5556:	c3                   	ret
    5557:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5560:	b9 69 63 00 00       	mov    $0x6369,%ecx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5565:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    556d:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
    5578:	4c 8d bc 24 a0 00 00 00 	lea    0xa0(%rsp),%r15
    5580:	66 89 8c 24 a4 00 00 00 	mov    %cx,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5588:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    558d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5592:	e8 69 ce ff ff       	call   2400 <__memcpy_chk@plt>
    5597:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    559c:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    55a1:	48 8d 35 87 3b 00 00 	lea    0x3b87(%rip),%rsi        # 912f <_IO_stdin_used+0x12f>
    55a8:	48 29 d1             	sub    %rdx,%rcx
    55ab:	49 8d 7c 17 06       	lea    0x6(%r15,%rdx,1),%rdi
    55b0:	ba 0b 00 00 00       	mov    $0xb,%edx
    55b5:	e8 46 ce ff ff       	call   2400 <__memcpy_chk@plt>
    55ba:	e9 2e ff ff ff       	jmp    54ed <handle_get_method+0x8d>
    55bf:	90                   	nop
    void *buf = malloc(size);
    55c0:	bf 70 00 00 00       	mov    $0x70,%edi
    55c5:	e8 86 ce ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    55ca:	48 85 c0             	test   %rax,%rax
    55cd:	74 5e                	je     562d <handle_get_method+0x1cd>
            req->client_socket = client_socket;
    55cf:	44 89 70 08          	mov    %r14d,0x8(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    55d3:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    55d8:	4c 8d 40 10          	lea    0x10(%rax),%r8
    55dc:	4c 89 fa             	mov    %r15,%rdx
            req->sockettoken = sockettoken;
    55df:	44 89 68 0c          	mov    %r13d,0xc(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    55e3:	48 89 ee             	mov    %rbp,%rsi
    55e6:	48 89 df             	mov    %rbx,%rdi
            req->iovec_count = 6;
    55e9:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    55f0:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    55f5:	e8 06 f4 ff ff       	call   4a00 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    55fa:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    55ff:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    5604:	4c 89 ff             	mov    %r15,%rdi
    5607:	48 8d 50 60          	lea    0x60(%rax),%rdx
    560b:	e8 20 f9 ff ff       	call   4f30 <copy_file_contents>
            add_write_request(data, buffers, req, ring);
    5610:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    5615:	4c 89 e1             	mov    %r12,%rcx
    5618:	48 89 ee             	mov    %rbp,%rsi
    561b:	48 89 df             	mov    %rbx,%rdi
    561e:	e8 cd f9 ff ff       	call   4ff0 <add_write_request>
}
    5623:	e9 06 ff ff ff       	jmp    552e <handle_get_method+0xce>
    5628:	e8 33 cd ff ff       	call   2360 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    562d:	48 8b 0d ec 69 00 00 	mov    0x69ec(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5634:	ba 28 00 00 00       	mov    $0x28,%edx
    5639:	be 01 00 00 00       	mov    $0x1,%esi
    563e:	48 8d 3d bb 3f 00 00 	lea    0x3fbb(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    5645:	e8 d6 ce ff ff       	call   2520 <fwrite@plt>
        exit(1);
    564a:	bf 01 00 00 00       	mov    $0x1,%edi
    564f:	e8 ac ce ff ff       	call   2500 <exit@plt>
    5654:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    565f:	90                   	nop

0000000000005660 <handle_http_method>:
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    5660:	f3 0f 1e fa          	endbr64
    5664:	41 57                	push   %r15
    5666:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5668:	4c 8d 35 3d 3a 00 00 	lea    0x3a3d(%rip),%r14        # 90ac <_IO_stdin_used+0xac>
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    566f:	41 55                	push   %r13
    5671:	4d 89 cd             	mov    %r9,%r13
    5674:	41 54                	push   %r12
    5676:	45 89 c4             	mov    %r8d,%r12d
    5679:	55                   	push   %rbp
    567a:	89 cd                	mov    %ecx,%ebp
    567c:	53                   	push   %rbx
    567d:	48 83 ec 38          	sub    $0x38,%rsp
    5681:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    method = strtok_r(method_buffer, " ", &saveptr);
    5686:	4c 8d 7c 24 20       	lea    0x20(%rsp),%r15
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    568b:	48 89 d7             	mov    %rdx,%rdi
    568e:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    method = strtok_r(method_buffer, " ", &saveptr);
    5693:	4c 89 fa             	mov    %r15,%rdx
    5696:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    5699:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    56a2:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    56a7:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    56a9:	e8 12 cd ff ff       	call   23c0 <strtok_r@plt>
    for (; *str; ++str)
    56ae:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    56b1:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    56b4:	84 d2                	test   %dl,%dl
    56b6:	88 54 24 1f          	mov    %dl,0x1f(%rsp)
    56ba:	74 29                	je     56e5 <handle_http_method+0x85>
        *str = (char)tolower(*str);
    56bc:	e8 cf ce ff ff       	call   2590 <__ctype_tolower_loc@plt>
    56c1:	48 0f be 54 24 1f    	movsbq 0x1f(%rsp),%rdx
    56c7:	48 89 d9             	mov    %rbx,%rcx
    56ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    56d0:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    56d3:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    56d7:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    56da:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    56dd:	48 0f be 11          	movsbq (%rcx),%rdx
    56e1:	84 d2                	test   %dl,%dl
    56e3:	75 eb                	jne    56d0 <handle_http_method+0x70>
    path = strtok_r(NULL, " ", &saveptr);
    56e5:	4c 89 f6             	mov    %r14,%rsi
    56e8:	4c 89 fa             	mov    %r15,%rdx
    56eb:	31 ff                	xor    %edi,%edi
    56ed:	e8 ce cc ff ff       	call   23c0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    56f2:	48 8d 35 41 3a 00 00 	lea    0x3a41(%rip),%rsi        # 913a <_IO_stdin_used+0x13a>
    56f9:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    56fc:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    56ff:	e8 ec cc ff ff       	call   23f0 <strcmp@plt>
        handle_get_method(data, buffers, path, client_socket, sockettoken, ring);
    5704:	4d 89 e9             	mov    %r13,%r9
    5707:	45 89 e0             	mov    %r12d,%r8d
    570a:	89 e9                	mov    %ebp,%ecx
    if (strcmp(method, "get") == 0) {
    570c:	85 c0                	test   %eax,%eax
    570e:	75 38                	jne    5748 <handle_http_method+0xe8>
        handle_get_method(data, buffers, path, client_socket, sockettoken, ring);
    5710:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5715:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    571a:	4c 89 f2             	mov    %r14,%rdx
    571d:	e8 3e fd ff ff       	call   5460 <handle_get_method>
}
    5722:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5727:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5730:	75 2e                	jne    5760 <handle_http_method+0x100>
    5732:	48 83 c4 38          	add    $0x38,%rsp
    5736:	5b                   	pop    %rbx
    5737:	5d                   	pop    %rbp
    5738:	41 5c                	pop    %r12
    573a:	41 5d                	pop    %r13
    573c:	41 5e                	pop    %r14
    573e:	41 5f                	pop    %r15
    5740:	c3                   	ret
    5741:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, sockettoken, ring);
    5748:	48 8b 15 c9 68 00 00 	mov    0x68c9(%rip),%rdx        # c018 <unimplemented_content>
    574f:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5754:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5759:	e8 42 fa ff ff       	call   51a0 <_send_static_string_content>
}
    575e:	eb c2                	jmp    5722 <handle_http_method+0xc2>
    5760:	e8 fb cb ff ff       	call   2360 <__stack_chk_fail@plt>
    5765:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005770 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5770:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5774:	85 d2                	test   %edx,%edx
    5776:	7e 38                	jle    57b0 <get_line+0x40>
    5778:	48 63 d2             	movslq %edx,%rdx
    577b:	48 83 c7 01          	add    $0x1,%rdi
    577f:	48 01 f2             	add    %rsi,%rdx
    5782:	eb 11                	jmp    5795 <get_line+0x25>
    5784:	0f 1f 40 00          	nopl   0x0(%rax)
    5788:	48 83 c6 01          	add    $0x1,%rsi
    578c:	48 83 c7 01          	add    $0x1,%rdi
    5790:	48 39 d6             	cmp    %rdx,%rsi
    5793:	74 1b                	je     57b0 <get_line+0x40>
        dest[i] = src[i];
    5795:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5799:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    579b:	3c 0d                	cmp    $0xd,%al
    579d:	75 e9                	jne    5788 <get_line+0x18>
    579f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    57a2:	75 e4                	jne    5788 <get_line+0x18>
            dest[i] = '\0';
    57a4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    57a7:	31 c0                	xor    %eax,%eax
    57a9:	c3                   	ret
    57aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    57b0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    57b5:	c3                   	ret
    57b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000057c0 <handle_client_request>:
int handle_client_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    57c0:	f3 0f 1e fa          	endbr64
    57c4:	53                   	push   %rbx
    57c5:	49 89 fa             	mov    %rdi,%r10
    57c8:	48 89 f3             	mov    %rsi,%rbx
    57cb:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    57d2:	48 8b 72 10          	mov    0x10(%rdx),%rsi
    57d6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    57df:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    57e7:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    57e9:	49 89 e3             	mov    %rsp,%r11
    57ec:	4c 8d 84 24 00 04 00 00 	lea    0x400(%rsp),%r8
    57f4:	4c 89 d8             	mov    %r11,%rax
    57f7:	eb 14                	jmp    580d <handle_client_request+0x4d>
    57f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5800:	48 83 c0 01          	add    $0x1,%rax
    5804:	48 83 c6 01          	add    $0x1,%rsi
    5808:	4c 39 c0             	cmp    %r8,%rax
    580b:	74 53                	je     5860 <handle_client_request+0xa0>
        dest[i] = src[i];
    580d:	0f b6 3e             	movzbl (%rsi),%edi
    5810:	40 88 38             	mov    %dil,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5813:	40 80 ff 0d          	cmp    $0xd,%dil
    5817:	75 e7                	jne    5800 <handle_client_request+0x40>
    5819:	80 7e 01 0a          	cmpb   $0xa,0x1(%rsi)
    581d:	75 e1                	jne    5800 <handle_client_request+0x40>
            dest[i] = '\0';
    581f:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    5822:	8b 42 08             	mov    0x8(%rdx),%eax
    5825:	49 89 c9             	mov    %rcx,%r9
    5828:	48 89 de             	mov    %rbx,%rsi
    582b:	44 8b 42 0c          	mov    0xc(%rdx),%r8d
    582f:	4c 89 d7             	mov    %r10,%rdi
    5832:	4c 89 da             	mov    %r11,%rdx
    5835:	89 c1                	mov    %eax,%ecx
    5837:	e8 24 fe ff ff       	call   5660 <handle_http_method>
}
    583c:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5844:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    584d:	75 38                	jne    5887 <handle_client_request+0xc7>
    584f:	48 81 c4 10 04 00 00 	add    $0x410,%rsp
    5856:	31 c0                	xor    %eax,%eax
    5858:	5b                   	pop    %rbx
    5859:	c3                   	ret
    585a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5860:	48 8b 0d b9 67 00 00 	mov    0x67b9(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5867:	ba 12 00 00 00       	mov    $0x12,%edx
    586c:	be 01 00 00 00       	mov    $0x1,%esi
    5871:	48 8d 3d c6 38 00 00 	lea    0x38c6(%rip),%rdi        # 913e <_IO_stdin_used+0x13e>
    5878:	e8 a3 cc ff ff       	call   2520 <fwrite@plt>
        exit(1);
    587d:	bf 01 00 00 00       	mov    $0x1,%edi
    5882:	e8 79 cc ff ff       	call   2500 <exit@plt>
}
    5887:	e8 d4 ca ff ff       	call   2360 <__stack_chk_fail@plt>
    588c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005890 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5890:	f3 0f 1e fa          	endbr64
    5894:	55                   	push   %rbp
    5895:	53                   	push   %rbx
    5896:	48 89 cb             	mov    %rcx,%rbx
    5899:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    589d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    58a0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    58a3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    58a9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    58ac:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    58af:	f6 c1 02             	test   $0x2,%cl
    58b2:	74 00                	je     58b4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    58b4:	41 89 c0             	mov    %eax,%r8d
    58b7:	45 29 c8             	sub    %r9d,%r8d
    58ba:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    58be:	0f 82 28 cd ff ff    	jb     25ec <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    58c4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58c7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    58ca:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    58cd:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    58d0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    58d3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58d7:	d3 e5                	shl    %cl,%ebp
    58d9:	48 c1 e5 06          	shl    $0x6,%rbp
    58dd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    58e1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    58e4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    58e9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    58f0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    58f4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    58f8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5900:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5908:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    590c:	e8 3f cb ff ff       	call   2450 <malloc@plt>
  io_uring_submit(ring);
    5911:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5914:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    591a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    591e:	48 83 c4 08          	add    $0x8,%rsp
    5922:	5b                   	pop    %rbx
    5923:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5924:	e9 47 ca ff ff       	jmp    2370 <io_uring_submit@plt>
    5929:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005930 <io_thread>:
void* io_thread(void *arg) {
    5930:	f3 0f 1e fa          	endbr64
    5934:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5936:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5938:	41 56                	push   %r14
    593a:	41 55                	push   %r13
    593c:	41 54                	push   %r12
    593e:	49 89 fc             	mov    %rdi,%r12
    5941:	55                   	push   %rbp
    5942:	53                   	push   %rbx
    5943:	48 81 ec 68 05 00 00 	sub    $0x568,%rsp
  struct io_uring ring = *data->ring;
    594a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5953:	48 89 84 24 58 05 00 00 	mov    %rax,0x558(%rsp)
    595b:	48 8b 47 60          	mov    0x60(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    595f:	4c 8d 6c 24 70       	lea    0x70(%rsp),%r13
    5964:	bf 00 01 00 00       	mov    $0x100,%edi
    5969:	4c 89 ee             	mov    %r13,%rsi
  struct io_uring ring = *data->ring;
    596c:	f3 0f 6f 18          	movdqu (%rax),%xmm3
    5970:	0f 29 5c 24 70       	movaps %xmm3,0x70(%rsp)
    5975:	f3 0f 6f 60 10       	movdqu 0x10(%rax),%xmm4
    597a:	0f 29 a4 24 80 00 00 00 	movaps %xmm4,0x80(%rsp)
    5982:	f3 0f 6f 68 20       	movdqu 0x20(%rax),%xmm5
    5987:	0f 29 ac 24 90 00 00 00 	movaps %xmm5,0x90(%rsp)
    598f:	f3 0f 6f 70 30       	movdqu 0x30(%rax),%xmm6
    5994:	0f 29 b4 24 a0 00 00 00 	movaps %xmm6,0xa0(%rsp)
    599c:	f3 0f 6f 78 40       	movdqu 0x40(%rax),%xmm7
    59a1:	0f 29 bc 24 b0 00 00 00 	movaps %xmm7,0xb0(%rsp)
    59a9:	f3 0f 6f 48 50       	movdqu 0x50(%rax),%xmm1
    59ae:	0f 29 8c 24 c0 00 00 00 	movaps %xmm1,0xc0(%rsp)
    59b6:	f3 0f 6f 58 60       	movdqu 0x60(%rax),%xmm3
    59bb:	0f 29 9c 24 d0 00 00 00 	movaps %xmm3,0xd0(%rsp)
    59c3:	f3 0f 6f 60 70       	movdqu 0x70(%rax),%xmm4
    59c8:	0f 29 a4 24 e0 00 00 00 	movaps %xmm4,0xe0(%rsp)
    59d0:	f3 0f 6f a8 80 00 00 00 	movdqu 0x80(%rax),%xmm5
    59d8:	0f 29 ac 24 f0 00 00 00 	movaps %xmm5,0xf0(%rsp)
    59e0:	f3 0f 6f b0 90 00 00 00 	movdqu 0x90(%rax),%xmm6
    59e8:	0f 29 b4 24 00 01 00 00 	movaps %xmm6,0x100(%rsp)
    59f0:	f3 0f 6f b8 a0 00 00 00 	movdqu 0xa0(%rax),%xmm7
    59f8:	0f 29 bc 24 10 01 00 00 	movaps %xmm7,0x110(%rsp)
    5a00:	f3 0f 6f 88 b0 00 00 00 	movdqu 0xb0(%rax),%xmm1
    5a08:	0f 29 8c 24 20 01 00 00 	movaps %xmm1,0x120(%rsp)
    5a10:	f3 0f 6f 98 c0 00 00 00 	movdqu 0xc0(%rax),%xmm3
    5a18:	0f 29 9c 24 30 01 00 00 	movaps %xmm3,0x130(%rsp)
    5a20:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5a27:	48 89 84 24 40 01 00 00 	mov    %rax,0x140(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a2f:	e8 fc c9 ff ff       	call   2430 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, data->_eventfd);
    5a34:	41 8b 74 24 68       	mov    0x68(%r12),%esi
    5a39:	49 8b 7c 24 60       	mov    0x60(%r12),%rdi
    5a3e:	e8 fd ca ff ff       	call   2540 <io_uring_register_eventfd@plt>
  if (data->io_mode == IO_MODE_RECV) {
    5a43:	41 8b 84 24 0c 01 00 00 	mov    0x10c(%r12),%eax
    5a4b:	83 f8 01             	cmp    $0x1,%eax
    5a4e:	0f 84 98 0b 00 00    	je     65ec <io_thread+0xcbc>
  if (data->io_mode == IO_MODE_SEND) {
    5a54:	85 c0                	test   %eax,%eax
    5a56:	0f 85 9c 06 00 00    	jne    60f8 <io_thread+0x7c8>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5a5c:	48 8d 3d 8d 3c 00 00 	lea    0x3c8d(%rip),%rdi        # 96f0 <_IO_stdin_used+0x6f0>
    5a63:	e8 a8 c8 ff ff       	call   2310 <puts@plt>
    int epollfd = epoll_create1(0);
    5a68:	31 ff                	xor    %edi,%edi
    5a6a:	e8 11 cb ff ff       	call   2580 <epoll_create1@plt>
    5a6f:	89 04 24             	mov    %eax,(%rsp)
				if (epollfd == -1) {
    5a72:	83 f8 ff             	cmp    $0xffffffff,%eax
    5a75:	0f 84 f8 cb ff ff    	je     2673 <io_thread.cold+0x7d>
    5a7b:	89 c2                	mov    %eax,%edx
    5a7d:	48 8d 35 4e 37 00 00 	lea    0x374e(%rip),%rsi        # 91d2 <_IO_stdin_used+0x1d2>
    5a84:	bf 01 00 00 00       	mov    $0x1,%edi
    5a89:	31 c0                	xor    %eax,%eax
    5a8b:	e8 00 ca ff ff       	call   2490 <__printf_chk@plt>
    5a90:	48 8d 3d 91 3c 00 00 	lea    0x3c91(%rip),%rdi        # 9728 <_IO_stdin_used+0x728>
    5a97:	e8 74 c8 ff ff       	call   2310 <puts@plt>
    5a9c:	41 8b 8c 24 1c 01 00 00 	mov    0x11c(%r12),%ecx
    5aa4:	31 c0                	xor    %eax,%eax
    5aa6:	48 8d 35 b3 3c 00 00 	lea    0x3cb3(%rip),%rsi        # 9760 <_IO_stdin_used+0x760>
    5aad:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    5ab5:	45 8b 84 24 18 01 00 00 	mov    0x118(%r12),%r8d
    5abd:	bf 01 00 00 00       	mov    $0x1,%edi
    5ac2:	e8 c9 c9 ff ff       	call   2490 <__printf_chk@plt>
    void * _reply = bufferrecv("waitsocketreply", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET, &reply, 0); 
    5ac7:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    5acf:	48 c1 e0 04          	shl    $0x4,%rax
    5ad3:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
  while (data->running == 1) {
    5adb:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5ae1:	0f 85 a2 cb ff ff    	jne    2689 <io_thread.cold+0x93>
      for (int x = 0 ; x < buffers->count ; x++) {
    5ae7:	8b 08                	mov    (%rax),%ecx
    5ae9:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5aed:	48 63 c1             	movslq %ecx,%rax
    5af0:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    5af4:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    5af8:	85 c9                	test   %ecx,%ecx
    5afa:	0f 8e 55 11 00 00    	jle    6c55 <io_thread+0x1325>
void* io_thread(void *arg) {
    5b00:	48 89 d3             	mov    %rdx,%rbx
    5b03:	eb 0c                	jmp    5b11 <io_thread+0x1e1>
    5b05:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    5b08:	48 83 c3 28          	add    $0x28,%rbx
    5b0c:	48 39 c3             	cmp    %rax,%rbx
    5b0f:	74 ef                	je     5b00 <io_thread+0x1d0>
        if (buffers->buffer[x].available == 1) {
    5b11:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    5b15:	75 f1                	jne    5b08 <io_thread+0x1d8>
          if (buffers->buffer[x].kind == kind) {
    5b17:	44 8b 43 20          	mov    0x20(%rbx),%r8d
    5b1b:	45 85 c0             	test   %r8d,%r8d
    5b1e:	75 e8                	jne    5b08 <io_thread+0x1d8>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    5b20:	be 28 00 00 00       	mov    $0x28,%esi
    5b25:	bf 01 00 00 00       	mov    $0x1,%edi
    5b2a:	e8 b1 c8 ff ff       	call   23e0 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    5b2f:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    5b32:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            reply->kind = buffers->buffer[x].kind;
    5b39:	c7 40 20 00 00 00 00 	movl   $0x0,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    5b40:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    5b43:	0f ae f8             	sfence
    struct NewSocketMessage *msg = bufferreply->data;
    5b46:	48 8b 18             	mov    (%rax),%rbx
    5b49:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    5b51:	48 8d 35 48 3c 00 00 	lea    0x3c48(%rip),%rsi        # 97a0 <_IO_stdin_used+0x7a0>
    5b58:	31 c0                	xor    %eax,%eax
    5b5a:	bf 01 00 00 00       	mov    $0x1,%edi
    5b5f:	8b 0b                	mov    (%rbx),%ecx
    5b61:	e8 2a c9 ff ff       	call   2490 <__printf_chk@plt>
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    5b66:	be 04 00 00 00       	mov    $0x4,%esi
    5b6b:	bf 01 00 00 00       	mov    $0x1,%edi
    5b70:	e8 6b c8 ff ff       	call   23e0 <calloc@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    5b75:	49 63 8c 24 18 01 00 00 	movslq 0x118(%r12),%rcx
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    5b7d:	48 89 c6             	mov    %rax,%rsi
    ourreply->nothing = msg->socket;
    5b80:	8b 03                	mov    (%rbx),%eax
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    5b82:	48 c1 e1 04          	shl    $0x4,%rcx
    5b86:	49 03 8c 24 10 01 00 00 	add    0x110(%r12),%rcx
  while (data->running == 1) {
    5b8e:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    ourreply->nothing = msg->socket;
    5b94:	89 06                	mov    %eax,(%rsi)
  while (data->running == 1) {
    5b96:	75 3e                	jne    5bd6 <io_thread+0x2a6>
      for (int x = 0 ; x < buffers->count ; x++) {
    5b98:	48 63 11             	movslq (%rcx),%rdx
    5b9b:	85 d2                	test   %edx,%edx
    5b9d:	0f 8e 38 0a 00 00    	jle    65db <io_thread+0xcab>
    5ba3:	48 8b 41 08          	mov    0x8(%rcx),%rax
    5ba7:	48 8d 14 92          	lea    (%rdx,%rdx,4),%rdx
    5bab:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    5baf:	eb 0d                	jmp    5bbe <io_thread+0x28e>
    5bb1:	48 83 c0 28          	add    $0x28,%rax
    5bb5:	48 39 d0             	cmp    %rdx,%rax
    5bb8:	0f 84 1d 0a 00 00    	je     65db <io_thread+0xcab>
        if (buffers->buffer[x].available == 0) {
    5bbe:	8b 78 08             	mov    0x8(%rax),%edi
    5bc1:	85 ff                	test   %edi,%edi
    5bc3:	75 ec                	jne    5bb1 <io_thread+0x281>
          buffers->buffer[x].data = send;
    5bc5:	48 89 30             	mov    %rsi,(%rax)
          buffers->buffer[x].kind = kind;
    5bc8:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
          buffers->buffer[x].available = 1;
    5bcf:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    5bd6:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    5bde:	31 c0                	xor    %eax,%eax
    5be0:	bf 01 00 00 00       	mov    $0x1,%edi
    5be5:	48 8d 35 ec 3b 00 00 	lea    0x3bec(%rip),%rsi        # 97d8 <_IO_stdin_used+0x7d8>
    5bec:	e8 9f c8 ff ff       	call   2490 <__printf_chk@plt>
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    5bf1:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    5bf9:	48 c1 e0 04          	shl    $0x4,%rax
    5bfd:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
  while (data->running == 1) {
    5c05:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5c0b:	0f 85 8e ca ff ff    	jne    269f <io_thread.cold+0xa9>
      for (int x = 0 ; x < buffers->count ; x++) {
    5c11:	8b 08                	mov    (%rax),%ecx
    5c13:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5c17:	48 63 c1             	movslq %ecx,%rax
    5c1a:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    5c1e:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    5c22:	85 c9                	test   %ecx,%ecx
    5c24:	0f 8e 29 10 00 00    	jle    6c53 <io_thread+0x1323>
void* io_thread(void *arg) {
    5c2a:	48 89 d3             	mov    %rdx,%rbx
    5c2d:	eb 0a                	jmp    5c39 <io_thread+0x309>
    5c2f:	90                   	nop
      for (int x = 0 ; x < buffers->count ; x++) {
    5c30:	48 83 c3 28          	add    $0x28,%rbx
    5c34:	48 39 c3             	cmp    %rax,%rbx
    5c37:	74 f1                	je     5c2a <io_thread+0x2fa>
        if (buffers->buffer[x].available == 1) {
    5c39:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    5c3d:	75 f1                	jne    5c30 <io_thread+0x300>
          if (buffers->buffer[x].kind == kind) {
    5c3f:	83 7b 20 02          	cmpl   $0x2,0x20(%rbx)
    5c43:	75 eb                	jne    5c30 <io_thread+0x300>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    5c45:	be 28 00 00 00       	mov    $0x28,%esi
    5c4a:	bf 01 00 00 00       	mov    $0x1,%edi
    5c4f:	e8 8c c7 ff ff       	call   23e0 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    5c54:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    5c57:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            reply->kind = buffers->buffer[x].kind;
    5c5e:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    5c65:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    5c68:	0f ae f8             	sfence
  struct NewClientMessage *newclientmsg = newclient->data;
    5c6b:	48 8b 00             	mov    (%rax),%rax
    int new_client_socket = newclient_message->socket;
    5c6e:	44 8b 30             	mov    (%rax),%r14d
  struct NewClientMessage *newclientmsg = newclient->data;
    5c71:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    if (new_client_socket == -1) {
    5c76:	41 83 fe ff          	cmp    $0xffffffff,%r14d
    5c7a:	0f 84 fa 10 00 00    	je     6d7a <io_thread+0x144a>
    5c80:	44 89 f2             	mov    %r14d,%edx
    5c83:	48 8d 35 5d 35 00 00 	lea    0x355d(%rip),%rsi        # 91e7 <_IO_stdin_used+0x1e7>
    5c8a:	bf 01 00 00 00       	mov    $0x1,%edi
    5c8f:	31 c0                	xor    %eax,%eax
    5c91:	e8 fa c7 ff ff       	call   2490 <__printf_chk@plt>
    struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    5c96:	be 0c 00 00 00       	mov    $0xc,%esi
    5c9b:	bf 01 00 00 00       	mov    $0x1,%edi
    5ca0:	e8 3b c7 ff ff       	call   23e0 <calloc@plt>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    5ca5:	bf 01 00 00 00       	mov    $0x1,%edi
    5caa:	be 10 00 00 00       	mov    $0x10,%esi
    ev->events = EPOLLOUT;
    5caf:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
    struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    5cb5:	49 89 c7             	mov    %rax,%r15
    ev->data.fd = new_client_socket;
    5cb8:	44 89 70 04          	mov    %r14d,0x4(%rax)
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    5cbc:	e8 1f c7 ff ff       	call   23e0 <calloc@plt>
    void *buf = malloc(size);
    5cc1:	bf 0a 00 00 00       	mov    $0xa,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    5cc6:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    5cc9:	e8 82 c7 ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    5cce:	48 85 c0             	test   %rax,%rax
    5cd1:	0f 84 7c 10 00 00    	je     6d53 <io_thread+0x1423>
    iov->iov_base = zh_malloc(10);
    5cd7:	48 89 03             	mov    %rax,(%rbx)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    5cda:	be 20 00 00 00       	mov    $0x20,%esi
    5cdf:	bf 01 00 00 00       	mov    $0x1,%edi
    iov->iov_len = 10;
    5ce4:	48 c7 43 08 0a 00 00 00 	movq   $0xa,0x8(%rbx)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    5cec:	e8 ef c6 ff ff       	call   23e0 <calloc@plt>
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    5cf1:	be 20 00 00 00       	mov    $0x20,%esi
    5cf6:	bf 01 00 00 00       	mov    $0x1,%edi
    eventfdstop->kind = 3; 
    5cfb:	c7 00 03 00 00 00    	movl   $0x3,(%rax)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    5d01:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    5d06:	e8 d5 c6 ff ff       	call   23e0 <calloc@plt>
    io_uring_register_eventfd(data->ring, data->dataeventfd);
    5d0b:	41 8b 74 24 6c       	mov    0x6c(%r12),%esi
    5d10:	49 8b 7c 24 60       	mov    0x60(%r12),%rdi
    removed->kind = 7; 
    5d15:	c7 00 07 00 00 00    	movl   $0x7,(%rax)
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    5d1b:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    io_uring_register_eventfd(data->ring, data->dataeventfd);
    5d20:	e8 1b c8 ff ff       	call   2540 <io_uring_register_eventfd@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5d25:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5d2c:	8b 94 24 30 01 00 00 	mov    0x130(%rsp),%edx
	unsigned int head, next = sq->sqe_tail + 1;
    5d33:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    5d36:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    5d3b:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5d3d:	f6 c2 02             	test   $0x2,%dl
    5d40:	74 00                	je     5d42 <io_thread+0x412>
	if (next - head <= sq->ring_entries) {
    5d42:	89 f1                	mov    %esi,%ecx
    5d44:	29 c1                	sub    %eax,%ecx
    5d46:	39 8c 24 cc 00 00 00 	cmp    %ecx,0xcc(%rsp)
    5d4d:	0f 82 55 c9 ff ff    	jb     26a8 <io_thread.cold+0xb2>
	if (ring->flags & IORING_SETUP_SQE128)
    5d53:	c1 ea 0a             	shr    $0xa,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d56:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	sqe->addr3 = 0;
    5d5d:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d61:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5d68:	89 d1                	mov    %edx,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d6a:	41 89 c1             	mov    %eax,%r9d
	sqe->fd = fd;
    5d6d:	8b 04 24             	mov    (%rsp),%eax
		sq->sqe_tail = next;
    5d70:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
    5d77:	83 e1 01             	and    $0x1,%ecx
          struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    5d7a:	be 20 00 00 00       	mov    $0x20,%esi
    5d7f:	bf 01 00 00 00       	mov    $0x1,%edi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d84:	41 d3 e1             	shl    %cl,%r9d
    5d87:	49 c1 e1 06          	shl    $0x6,%r9
    5d8b:	4c 03 8c 24 a8 00 00 00 	add    0xa8(%rsp),%r9
	sqe->fd = fd;
    5d93:	41 89 41 04          	mov    %eax,0x4(%r9)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    5d97:	44 89 f0             	mov    %r14d,%eax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d9a:	4c 89 cd             	mov    %r9,%rbp
	sqe->opcode = (__u8) op;
    5d9d:	41 c7 01 1d 00 00 00 	movl   $0x1d,(%r9)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    5da4:	49 89 41 08          	mov    %rax,0x8(%r9)
	sqe->addr = (unsigned long) addr;
    5da8:	4d 89 79 10          	mov    %r15,0x10(%r9)
	sqe->len = len;
    5dac:	49 c7 41 18 01 00 00 00 	movq   $0x1,0x18(%r9)
	sqe->buf_index = 0;
    5db4:	49 c7 41 28 00 00 00 00 	movq   $0x0,0x28(%r9)
	sqe->addr3 = 0;
    5dbc:	41 0f 11 41 30       	movups %xmm0,0x30(%r9)
    5dc1:	e8 1a c6 ff ff       	call   23e0 <calloc@plt>
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    5dc6:	be 18 00 00 00       	mov    $0x18,%esi
    5dcb:	bf 01 00 00 00       	mov    $0x1,%edi
          readywriting->kind = 4; 
    5dd0:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
    5dd6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    5ddb:	e8 00 c6 ff ff       	call   23e0 <calloc@plt>
          rr->sockettoken = newclient_message->sockettoken; 
    5de0:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
          readywriting->data = rr; 
    5de5:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
          io_uring_submit(&ring);
    5dea:	4c 89 ef             	mov    %r13,%rdi
          rr->client_socket = new_client_socket; 
    5ded:	44 89 30             	mov    %r14d,(%rax)
          rr->sockettoken = newclient_message->sockettoken; 
    5df0:	8b 49 04             	mov    0x4(%rcx),%ecx
          readywriting->data = rr; 
    5df3:	48 89 42 08          	mov    %rax,0x8(%rdx)
          readywriting->event = ev; 
    5df7:	4c 89 7a 10          	mov    %r15,0x10(%rdx)
          rr->sockettoken = newclient_message->sockettoken; 
    5dfb:	89 48 10             	mov    %ecx,0x10(%rax)
	sqe->user_data = (unsigned long) data;
    5dfe:	48 89 55 20          	mov    %rdx,0x20(%rbp)
          io_uring_submit(&ring);
    5e02:	e8 69 c5 ff ff       	call   2370 <io_uring_submit@plt>
    struct SendUserData *dataavailable = calloc(1, sizeof(struct SendUserData));
    5e07:	be 20 00 00 00       	mov    $0x20,%esi
    5e0c:	bf 01 00 00 00       	mov    $0x1,%edi
    5e11:	e8 ca c5 ff ff       	call   23e0 <calloc@plt>
    5e16:	41 8b 54 24 6c       	mov    0x6c(%r12),%edx
    5e1b:	bf 01 00 00 00       	mov    $0x1,%edi
    5e20:	48 8d 35 d3 33 00 00 	lea    0x33d3(%rip),%rsi        # 91fa <_IO_stdin_used+0x1fa>
    dataavailable->kind = 8; 
    5e27:	c7 00 08 00 00 00    	movl   $0x8,(%rax)
    struct SendUserData *dataavailable = calloc(1, sizeof(struct SendUserData));
    5e2d:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5e32:	31 c0                	xor    %eax,%eax
    5e34:	e8 57 c6 ff ff       	call   2490 <__printf_chk@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5e39:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    5e40:	8d 50 01             	lea    0x1(%rax),%edx
	if (ring->flags & IORING_SETUP_SQE128)
    5e43:	8b 84 24 30 01 00 00 	mov    0x130(%rsp),%eax
    5e4a:	89 c1                	mov    %eax,%ecx
    5e4c:	c1 e9 0a             	shr    $0xa,%ecx
    5e4f:	83 e1 01             	and    $0x1,%ecx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5e52:	a8 02                	test   $0x2,%al
		head = IO_URING_READ_ONCE(*sq->khead);
    5e54:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    5e59:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5e5b:	0f 85 ce 02 00 00    	jne    612f <io_thread+0x7ff>
	if (next - head <= sq->ring_entries) {
    5e61:	89 d6                	mov    %edx,%esi
    5e63:	29 c6                	sub    %eax,%esi
    5e65:	39 b4 24 cc 00 00 00 	cmp    %esi,0xcc(%rsp)
    5e6c:	0f 82 90 c7 ff ff    	jb     2602 <io_thread.cold+0xc>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e72:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	sqe->addr3 = 0;
    5e79:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(&ring);
    5e7d:	4c 89 ef             	mov    %r13,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e80:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
		sq->sqe_tail = next;
    5e87:	89 94 24 b4 00 00 00 	mov    %edx,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e8e:	d3 e0                	shl    %cl,%eax
    io_uring_prep_readv(sqe, data->dataeventfd, iov, 1, 0);
    5e90:	41 8b 54 24 6c       	mov    0x6c(%r12),%edx
	sqe->user_data = (unsigned long) data;
    5e95:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e9a:	48 c1 e0 06          	shl    $0x6,%rax
    5e9e:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->opcode = (__u8) op;
    5ea6:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5eac:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5eaf:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5eb7:	48 89 58 10          	mov    %rbx,0x10(%rax)
	sqe->len = len;
    5ebb:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5ec3:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5ecb:	48 89 48 20          	mov    %rcx,0x20(%rax)
	sqe->addr3 = 0;
    5ecf:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(&ring);
    5ed3:	e8 98 c4 ff ff       	call   2370 <io_uring_submit@plt>
    while (data->running == 1) {
    5ed8:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5ede:	0f 85 08 02 00 00    	jne    60ec <io_thread+0x7bc>
void* io_thread(void *arg) {
    5ee4:	b8 01 00 00 00       	mov    $0x1,%eax
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
    5ee9:	83 f8 01             	cmp    $0x1,%eax
    5eec:	0f 85 9e 00 00 00    	jne    5f90 <io_thread+0x660>
    5ef2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    5ef8:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    5f00:	48 c1 e0 04          	shl    $0x4,%rax
    5f04:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
      for (int x = 0 ; x < buffers->count ; x++) {
    5f0c:	48 63 10             	movslq (%rax),%rdx
    5f0f:	85 d2                	test   %edx,%edx
    5f11:	7e 7d                	jle    5f90 <io_thread+0x660>
    5f13:	4c 8b 70 08          	mov    0x8(%rax),%r14
    5f17:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    5f1b:	49 8d 04 c6          	lea    (%r14,%rax,8),%rax
    5f1f:	eb 10                	jmp    5f31 <io_thread+0x601>
    5f21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f28:	49 83 c6 28          	add    $0x28,%r14
    5f2c:	49 39 c6             	cmp    %rax,%r14
    5f2f:	74 5f                	je     5f90 <io_thread+0x660>
        if (buffers->buffer[x].available == 1) {
    5f31:	41 83 7e 08 01       	cmpl   $0x1,0x8(%r14)
    5f36:	75 f0                	jne    5f28 <io_thread+0x5f8>
          if (buffers->buffer[x].kind == kind) {
    5f38:	41 83 7e 20 02       	cmpl   $0x2,0x20(%r14)
    5f3d:	75 e9                	jne    5f28 <io_thread+0x5f8>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    5f3f:	be 28 00 00 00       	mov    $0x28,%esi
    5f44:	bf 01 00 00 00       	mov    $0x1,%edi
    5f49:	e8 92 c4 ff ff       	call   23e0 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    5f4e:	49 8b 16             	mov    (%r14),%rdx
            buffers->buffer[x].available = 0;
    5f51:	41 c7 46 08 00 00 00 00 	movl   $0x0,0x8(%r14)
            reply->kind = buffers->buffer[x].kind;
    5f59:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    5f60:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    5f63:	0f ae f8             	sfence
  struct NewClientMessage *newclientmsg = newclient->data;
    5f66:	4c 8b 38             	mov    (%rax),%r15
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
    5f69:	4d 85 ff             	test   %r15,%r15
    5f6c:	74 22                	je     5f90 <io_thread+0x660>
    5f6e:	45 8b 37             	mov    (%r15),%r14d
    5f71:	45 85 f6             	test   %r14d,%r14d
    5f74:	74 1a                	je     5f90 <io_thread+0x660>
          if (new_client_socket != -1) {
    5f76:	41 83 fe ff          	cmp    $0xffffffff,%r14d
    5f7a:	0f 85 b4 01 00 00    	jne    6134 <io_thread+0x804>
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
    5f80:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    5f85:	83 f8 01             	cmp    $0x1,%eax
    5f88:	0f 84 6a ff ff ff    	je     5ef8 <io_thread+0x5c8>
    5f8e:	66 90                	xchg   %ax,%ax
        struct __kernel_timespec delay = {
    5f90:	66 0f 6f 15 78 3e 00 00 	movdqa 0x3e78(%rip),%xmm2        # 9e10 <_IO_stdin_used+0xe10>
        int ret = io_uring_wait_cqe_timeout(&ring, &cqe, &delay);
    5f98:	48 8d 54 24 40       	lea    0x40(%rsp),%rdx
    5f9d:	48 8d 74 24 38       	lea    0x38(%rsp),%rsi
    5fa2:	4c 89 ef             	mov    %r13,%rdi
        struct __kernel_timespec delay = {
    5fa5:	0f 29 54 24 40       	movaps %xmm2,0x40(%rsp)
        int ret = io_uring_wait_cqe_timeout(&ring, &cqe, &delay);
    5faa:	e8 11 c5 ff ff       	call   24c0 <io_uring_wait_cqe_timeout@plt>
        if (ret < 0) { continue; }
    5faf:	85 c0                	test   %eax,%eax
    5fb1:	0f 88 29 01 00 00    	js     60e0 <io_thread+0x7b0>
        if (((struct SendUserData*) cqe->user_data)->kind == 3) {
    5fb7:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5fbc:	4c 8b 3a             	mov    (%rdx),%r15
    5fbf:	41 8b 07             	mov    (%r15),%eax
    5fc2:	4c 89 f9             	mov    %r15,%rcx
    5fc5:	83 f8 03             	cmp    $0x3,%eax
    5fc8:	0f 84 97 0c 00 00    	je     6c65 <io_thread+0x1335>
        if (((struct SendUserData*) cqe->user_data)->kind == 8) {
    5fce:	83 f8 08             	cmp    $0x8,%eax
    5fd1:	0f 84 31 03 00 00    	je     6308 <io_thread+0x9d8>
        if (((struct SendUserData*) cqe->user_data)->kind == 4) {
    5fd7:	83 f8 04             	cmp    $0x4,%eax
    5fda:	0f 84 4e 03 00 00    	je     632e <io_thread+0x9fe>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
    5fe0:	83 f8 05             	cmp    $0x5,%eax
    5fe3:	0f 84 53 02 00 00    	je     623c <io_thread+0x90c>
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    5fe9:	83 f8 07             	cmp    $0x7,%eax
    5fec:	0f 84 e3 02 00 00    	je     62d5 <io_thread+0x9a5>
	unsigned int head, next = sq->sqe_tail + 1;
    5ff2:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5ff9:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    6000:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    6003:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    6008:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    600a:	f6 c1 02             	test   $0x2,%cl
    600d:	74 00                	je     600f <io_thread+0x6df>
	if (next - head <= sq->ring_entries) {
    600f:	89 d0                	mov    %edx,%eax
    6011:	29 f0                	sub    %esi,%eax
    6013:	39 84 24 cc 00 00 00 	cmp    %eax,0xcc(%rsp)
    601a:	0f 82 49 c6 ff ff    	jb     2669 <io_thread.cold+0x73>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6020:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6027:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    602a:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
          io_uring_submit(&ring);
    6031:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    6034:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6037:	41 89 c7             	mov    %eax,%r15d
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    603a:	41 8b 44 24 68       	mov    0x68(%r12),%eax
	sqe->addr3 = 0;
    603f:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6043:	41 d3 e7             	shl    %cl,%r15d
		sq->sqe_tail = next;
    6046:	89 94 24 b4 00 00 00 	mov    %edx,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    604d:	49 c1 e7 06          	shl    $0x6,%r15
    6051:	4c 03 bc 24 a8 00 00 00 	add    0xa8(%rsp),%r15
	sqe->fd = fd;
    6059:	41 89 47 04          	mov    %eax,0x4(%r15)
	sqe->user_data = (unsigned long) data;
    605d:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
	sqe->opcode = (__u8) op;
    6062:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
	sqe->off = offset;
    6069:	49 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%r15)
	sqe->addr = (unsigned long) addr;
    6071:	49 89 5f 10          	mov    %rbx,0x10(%r15)
	sqe->len = len;
    6075:	49 c7 47 18 01 00 00 00 	movq   $0x1,0x18(%r15)
	sqe->buf_index = 0;
    607d:	49 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%r15)
	sqe->user_data = (unsigned long) data;
    6085:	49 89 47 20          	mov    %rax,0x20(%r15)
	sqe->addr3 = 0;
    6089:	41 0f 11 47 30       	movups %xmm0,0x30(%r15)
          io_uring_submit(&ring);
    608e:	e8 dd c2 ff ff       	call   2370 <io_uring_submit@plt>
          io_uring_prep_readv(sqe, data->dataeventfd, iov, 1, 0);
    6093:	41 8b 44 24 6c       	mov    0x6c(%r12),%eax
	sqe->addr = (unsigned long) addr;
    6098:	49 89 5f 10          	mov    %rbx,0x10(%r15)
	sqe->addr3 = 0;
    609c:	66 0f ef c0          	pxor   %xmm0,%xmm0
	sqe->opcode = (__u8) op;
    60a0:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
          io_uring_submit(&ring);
    60a7:	4c 89 ef             	mov    %r13,%rdi
	sqe->fd = fd;
    60aa:	41 89 47 04          	mov    %eax,0x4(%r15)
	sqe->user_data = (unsigned long) data;
    60ae:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
	sqe->off = offset;
    60b3:	49 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%r15)
	sqe->len = len;
    60bb:	49 c7 47 18 01 00 00 00 	movq   $0x1,0x18(%r15)
	sqe->buf_index = 0;
    60c3:	49 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%r15)
	sqe->user_data = (unsigned long) data;
    60cb:	49 89 47 20          	mov    %rax,0x20(%r15)
	sqe->addr3 = 0;
    60cf:	41 0f 11 47 30       	movups %xmm0,0x30(%r15)
    60d4:	e8 97 c2 ff ff       	call   2370 <io_uring_submit@plt>
    60d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    while (data->running == 1) {
    60e0:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    60e6:	0f 84 f8 fd ff ff    	je     5ee4 <io_thread+0x5b4>
    60ec:	48 8d 3d 1c 31 00 00 	lea    0x311c(%rip),%rdi        # 920f <_IO_stdin_used+0x20f>
    60f3:	e8 18 c2 ff ff       	call   2310 <puts@plt>
    60f8:	48 8d 3d 1f 31 00 00 	lea    0x311f(%rip),%rdi        # 921e <_IO_stdin_used+0x21e>
    60ff:	e8 0c c2 ff ff       	call   2310 <puts@plt>
}
    6104:	48 8b 84 24 58 05 00 00 	mov    0x558(%rsp),%rax
    610c:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    6115:	0f 85 9f 0c 00 00    	jne    6dba <io_thread+0x148a>
    611b:	48 81 c4 68 05 00 00 	add    $0x568,%rsp
    6122:	31 c0                	xor    %eax,%eax
    6124:	5b                   	pop    %rbx
    6125:	5d                   	pop    %rbp
    6126:	41 5c                	pop    %r12
    6128:	41 5d                	pop    %r13
    612a:	41 5e                	pop    %r14
    612c:	41 5f                	pop    %r15
    612e:	c3                   	ret
		head = io_uring_smp_load_acquire(sq->khead);
    612f:	e9 2d fd ff ff       	jmp    5e61 <io_thread+0x531>
            struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    6134:	be 0c 00 00 00       	mov    $0xc,%esi
    6139:	bf 01 00 00 00       	mov    $0x1,%edi
    613e:	e8 9d c2 ff ff       	call   23e0 <calloc@plt>
            struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    6143:	be 20 00 00 00       	mov    $0x20,%esi
    6148:	bf 01 00 00 00       	mov    $0x1,%edi
            ev->events = EPOLLOUT;
    614d:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
            ev->data.fd = new_client_socket;
    6153:	44 89 70 04          	mov    %r14d,0x4(%rax)
    6157:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
            struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    615c:	e8 7f c2 ff ff       	call   23e0 <calloc@plt>
            readywriting->event = ev;
    6161:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
            readywriting->sockettoken = ncm->sockettoken;
    6166:	45 8b 7f 04          	mov    0x4(%r15),%r15d
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    616a:	be 18 00 00 00       	mov    $0x18,%esi
            readywriting->kind = 4; 
    616f:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    6175:	bf 01 00 00 00       	mov    $0x1,%edi
            readywriting->event = ev;
    617a:	4c 89 40 10          	mov    %r8,0x10(%rax)
            readywriting->sockettoken = ncm->sockettoken;
    617e:	44 89 78 18          	mov    %r15d,0x18(%rax)
            readywriting->event = ev;
    6182:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
            readywriting->sockettoken = ncm->sockettoken;
    6187:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    618c:	e8 4f c2 ff ff       	call   23e0 <calloc@plt>
            readywriting->data = rr; 
    6191:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
		head = IO_URING_READ_ONCE(*sq->khead);
    6196:	48 8b 7c 24 70       	mov    0x70(%rsp),%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    619b:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    61a2:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
            rr->client_socket = new_client_socket; 
    61a7:	44 89 30             	mov    %r14d,(%rax)
            rr->sockettoken = ncm->sockettoken; 
    61aa:	44 89 78 10          	mov    %r15d,0x10(%rax)
            readywriting->data = rr; 
    61ae:	48 89 42 08          	mov    %rax,0x8(%rdx)
	unsigned int head, next = sq->sqe_tail + 1;
    61b2:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    61b9:	f6 c1 02             	test   $0x2,%cl
	unsigned int head, next = sq->sqe_tail + 1;
    61bc:	8d 70 01             	lea    0x1(%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    61bf:	0f 85 24 01 00 00    	jne    62e9 <io_thread+0x9b9>
		head = IO_URING_READ_ONCE(*sq->khead);
    61c5:	44 8b 0f             	mov    (%rdi),%r9d
	if (next - head <= sq->ring_entries) {
    61c8:	89 f7                	mov    %esi,%edi
    61ca:	44 29 cf             	sub    %r9d,%edi
    61cd:	39 bc 24 cc 00 00 00 	cmp    %edi,0xcc(%rsp)
    61d4:	0f 82 e5 0b 00 00    	jb     6dbf <io_thread+0x148f>
	if (ring->flags & IORING_SETUP_SQE128)
    61da:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    61dd:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
	sqe->addr3 = 0;
    61e4:	66 0f ef c0          	pxor   %xmm0,%xmm0
            io_uring_submit(&ring);
    61e8:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    61eb:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    61ee:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    61f5:	d3 e0                	shl    %cl,%eax
	sqe->fd = fd;
    61f7:	8b 0c 24             	mov    (%rsp),%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    61fa:	48 c1 e0 06          	shl    $0x6,%rax
    61fe:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->fd = fd;
    6206:	89 48 04             	mov    %ecx,0x4(%rax)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6209:	44 89 f1             	mov    %r14d,%ecx
    620c:	48 89 48 08          	mov    %rcx,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    6210:	4c 89 40 10          	mov    %r8,0x10(%rax)
	sqe->user_data = (unsigned long) data;
    6214:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->opcode = (__u8) op;
    6218:	c7 00 1d 00 00 00    	movl   $0x1d,(%rax)
	sqe->len = len;
    621e:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    6226:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    622e:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    6232:	e8 39 c1 ff ff       	call   2370 <io_uring_submit@plt>
    6237:	e9 44 fd ff ff       	jmp    5f80 <io_thread+0x650>
          struct Request *req = ((struct SendUserData *) cqe->user_data)->data;
    623c:	4c 8b 79 08          	mov    0x8(%rcx),%r15
          if (cqe->res < 0) {
    6240:	8b 42 08             	mov    0x8(%rdx),%eax
              fprintf(stderr, "Async request failed: %s for event: %d\n",
    6243:	45 8b 37             	mov    (%r15),%r14d
          if (cqe->res < 0) {
    6246:	85 c0                	test   %eax,%eax
    6248:	0f 88 93 0a 00 00    	js     6ce1 <io_thread+0x13b1>
          switch (req->event_type) {
    624e:	41 83 fe 01          	cmp    $0x1,%r14d
    6252:	0f 84 5d 03 00 00    	je     65b5 <io_thread+0xc85>
    6258:	41 83 fe 02          	cmp    $0x2,%r14d
    625c:	0f 85 5b 03 00 00    	jne    65bd <io_thread+0xc8d>
	sqe->fd = fd;
    6262:	8b 04 24             	mov    (%rsp),%eax
                  io_uring_prep_epoll_ctl(sqe, epollfd, req->client_socket, EPOLL_CTL_DEL, ((struct SendUserData *) cqe->user_data)->event);
    6265:	f3 0f 7e 49 10       	movq   0x10(%rcx),%xmm1
                  io_uring_submit(&ring);
    626a:	4c 89 ef             	mov    %r13,%rdi
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    626d:	66 41 0f 6e 47 08    	movd   0x8(%r15),%xmm0
	sqe->opcode = (__u8) op;
    6273:	c7 45 00 1d 00 00 00 	movl   $0x1d,0x0(%rbp)
	sqe->fd = fd;
    627a:	89 45 04             	mov    %eax,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    627d:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
	sqe->off = offset;
    6282:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
	sqe->len = len;
    6286:	48 c7 45 18 02 00 00 00 	movq   $0x2,0x18(%rbp)
	sqe->buf_index = 0;
    628e:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->user_data = (unsigned long) data;
    6296:	48 89 45 20          	mov    %rax,0x20(%rbp)
	sqe->off = offset;
    629a:	0f 11 45 08          	movups %xmm0,0x8(%rbp)
	sqe->addr3 = 0;
    629e:	66 0f ef c0          	pxor   %xmm0,%xmm0
    62a2:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    62a6:	e8 c5 c0 ff ff       	call   2370 <io_uring_submit@plt>
                  close(req->client_socket);
    62ab:	41 8b 7f 08          	mov    0x8(%r15),%edi
    62af:	e8 fc c0 ff ff       	call   23b0 <close@plt>
            io_uring_cqe_seen(&ring, cqe);
    62b4:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    62b9:	48 85 c0             	test   %rax,%rax
    62bc:	0f 85 fb 02 00 00    	jne    65bd <io_thread+0xc8d>
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    62c2:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    62ca:	8b 00                	mov    (%rax),%eax
    62cc:	83 f8 07             	cmp    $0x7,%eax
    62cf:	0f 85 1d fd ff ff    	jne    5ff2 <io_thread+0x6c2>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    62d5:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    62dd:	8b 02                	mov    (%rdx),%eax
    62df:	83 c0 01             	add    $0x1,%eax
    62e2:	89 02                	mov    %eax,(%rdx)
}
    62e4:	e9 09 fd ff ff       	jmp    5ff2 <io_thread+0x6c2>
		head = io_uring_smp_load_acquire(sq->khead);
    62e9:	8b 3f                	mov    (%rdi),%edi
	if (next - head <= sq->ring_entries) {
    62eb:	89 f0                	mov    %esi,%eax
    62ed:	29 f8                	sub    %edi,%eax
    62ef:	39 84 24 cc 00 00 00 	cmp    %eax,0xcc(%rsp)
    62f6:	0f 82 63 c3 ff ff    	jb     265f <io_thread.cold+0x69>
    62fc:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    6303:	e9 d2 fe ff ff       	jmp    61da <io_thread+0x8aa>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6308:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6310:	8b 02                	mov    (%rdx),%eax
    6312:	83 c0 01             	add    $0x1,%eax
    6315:	89 02                	mov    %eax,(%rdx)
        if (((struct SendUserData*) cqe->user_data)->kind == 4) {
    6317:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    631c:	4c 8b 3a             	mov    (%rdx),%r15
    631f:	41 8b 07             	mov    (%r15),%eax
    6322:	4c 89 f9             	mov    %r15,%rcx
    6325:	83 f8 04             	cmp    $0x4,%eax
    6328:	0f 85 b2 fc ff ff    	jne    5fe0 <io_thread+0x6b0>
          struct ReadyWriting *rr = readywriting->data; 
    632e:	49 8b 47 08          	mov    0x8(%r15),%rax
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
    6332:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
          struct ReadyWriting *rr = readywriting->data; 
    6338:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
    633d:	0f 85 af fc ff ff    	jne    5ff2 <io_thread+0x6c2>
    6343:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    6348:	48 89 dd             	mov    %rbx,%rbp
    634b:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    6350:	8b 70 10             	mov    0x10(%rax),%esi
    6353:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    635b:	48 c1 e0 04          	shl    $0x4,%rax
    635f:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
      for (int x = 0 ; x < buffers->count ; x++) {
    6367:	8b 08                	mov    (%rax),%ecx
    6369:	85 c9                	test   %ecx,%ecx
    636b:	0f 8e 2d 02 00 00    	jle    659e <io_thread+0xc6e>
    6371:	4c 8b 70 08          	mov    0x8(%rax),%r14
    6375:	48 63 c1             	movslq %ecx,%rax
    6378:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    637c:	49 8d 04 c6          	lea    (%r14,%rax,8),%rax
    6380:	eb 13                	jmp    6395 <io_thread+0xa65>
    6382:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6388:	49 83 c6 28          	add    $0x28,%r14
    638c:	49 39 c6             	cmp    %rax,%r14
    638f:	0f 84 09 02 00 00    	je     659e <io_thread+0xc6e>
        if (buffers->buffer[x].available == 1) {
    6395:	41 83 7e 08 01       	cmpl   $0x1,0x8(%r14)
    639a:	75 ec                	jne    6388 <io_thread+0xa58>
          if (buffers->buffer[x].kind == kind && buffers->buffer[x].filter == filter) {
    639c:	41 83 7e 20 03       	cmpl   $0x3,0x20(%r14)
    63a1:	75 e5                	jne    6388 <io_thread+0xa58>
    63a3:	41 3b 76 24          	cmp    0x24(%r14),%esi
    63a7:	75 df                	jne    6388 <io_thread+0xa58>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    63a9:	be 28 00 00 00       	mov    $0x28,%esi
    63ae:	bf 01 00 00 00       	mov    $0x1,%edi
    63b3:	e8 28 c0 ff ff       	call   23e0 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    63b8:	49 8b 0e             	mov    (%r14),%rcx
            buffers->buffer[x].available = 0;
    63bb:	41 c7 46 08 00 00 00 00 	movl   $0x0,0x8(%r14)
            reply->kind = buffers->buffer[x].kind;
    63c3:	c7 40 20 03 00 00 00 	movl   $0x3,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    63ca:	48 89 08             	mov    %rcx,(%rax)
            asm volatile ("mfence" ::: "memory");
    63cd:	0f ae f0             	mfence
	unsigned int head, next = sq->sqe_tail + 1;
    63d0:	8b 8c 24 b4 00 00 00 	mov    0xb4(%rsp),%ecx
            struct Write *write = send->data;
    63d7:	48 8b 00             	mov    (%rax),%rax
    63da:	8d 71 01             	lea    0x1(%rcx),%esi
	if (ring->flags & IORING_SETUP_SQE128)
    63dd:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
            int client_socket = write->client_socket; 
    63e4:	8b 78 08             	mov    0x8(%rax),%edi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    63e7:	f6 c1 02             	test   $0x2,%cl
    63ea:	0f 84 08 08 00 00    	je     6bf8 <io_thread+0x12c8>
		head = io_uring_smp_load_acquire(sq->khead);
    63f0:	4c 8b 44 24 70       	mov    0x70(%rsp),%r8
    63f5:	45 8b 00             	mov    (%r8),%r8d
            struct Request *req = write->request;
    63f8:	4c 8b 30             	mov    (%rax),%r14
	if (next - head <= sq->ring_entries) {
    63fb:	89 f0                	mov    %esi,%eax
    63fd:	44 29 c0             	sub    %r8d,%eax
    6400:	39 84 24 cc 00 00 00 	cmp    %eax,0xcc(%rsp)
    6407:	0f 82 15 c2 ff ff    	jb     2622 <io_thread.cold+0x2c>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    640d:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6414:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
    6417:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    641b:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6422:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6425:	89 c3                	mov    %eax,%ebx
            io_uring_prep_writev(sqe, client_socket, req->iov, req->iovec_count, 0);
    6427:	41 8b 46 04          	mov    0x4(%r14),%eax
		sq->sqe_tail = next;
    642b:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6432:	d3 e3                	shl    %cl,%ebx
    6434:	49 8d 4e 10          	lea    0x10(%r14),%rcx
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    6438:	be 20 00 00 00       	mov    $0x20,%esi
    643d:	48 c1 e3 06          	shl    $0x6,%rbx
    6441:	48 03 9c 24 a8 00 00 00 	add    0xa8(%rsp),%rbx
            req->event_type = EVENT_TYPE_WRITE;
    6449:	41 c7 06 02 00 00 00 	movl   $0x2,(%r14)
	sqe->fd = fd;
    6450:	89 7b 04             	mov    %edi,0x4(%rbx)
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    6453:	bf 01 00 00 00       	mov    $0x1,%edi
            io_uring_prep_writev(sqe, client_socket, req->iov, req->iovec_count, 0);
    6458:	48 89 4b 10          	mov    %rcx,0x10(%rbx)
	sqe->opcode = (__u8) op;
    645c:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->off = offset;
    6462:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
	sqe->len = len;
    646a:	89 43 18             	mov    %eax,0x18(%rbx)
	sqe->rw_flags = 0;
    646d:	c7 43 1c 00 00 00 00 	movl   $0x0,0x1c(%rbx)
	sqe->buf_index = 0;
    6474:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->addr3 = 0;
    647c:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    6480:	e8 5b bf ff ff       	call   23e0 <calloc@plt>
            finishedwrite->data = req;
    6485:	66 49 0f 6e c6       	movq   %r14,%xmm0
            io_uring_submit(&ring);
    648a:	4c 89 ef             	mov    %r13,%rdi
            finishedwrite->data = req;
    648d:	41 0f 16 47 10       	movhps 0x10(%r15),%xmm0
            finishedwrite->kind = 5; 
    6492:	c7 00 05 00 00 00    	movl   $0x5,(%rax)
            finishedwrite->data = req;
    6498:	0f 11 40 08          	movups %xmm0,0x8(%rax)
	sqe->user_data = (unsigned long) data;
    649c:	48 89 43 20          	mov    %rax,0x20(%rbx)
            io_uring_submit(&ring);
    64a0:	e8 cb be ff ff       	call   2370 <io_uring_submit@plt>
	if (cqe)
    64a5:	48 83 7c 24 38 00    	cmpq   $0x0,0x38(%rsp)
    64ab:	74 0f                	je     64bc <io_thread+0xb8c>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    64ad:	48 8b 8c 24 d8 00 00 00 	mov    0xd8(%rsp),%rcx
    64b5:	8b 01                	mov    (%rcx),%eax
    64b7:	83 c0 01             	add    $0x1,%eax
    64ba:	89 01                	mov    %eax,(%rcx)
	unsigned int head, next = sq->sqe_tail + 1;
    64bc:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    64c3:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    64ca:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    64cd:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    64d2:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    64d4:	f6 c1 02             	test   $0x2,%cl
    64d7:	74 00                	je     64d9 <io_thread+0xba9>
	if (next - head <= sq->ring_entries) {
    64d9:	89 f7                	mov    %esi,%edi
    64db:	29 c7                	sub    %eax,%edi
    64dd:	39 bc 24 cc 00 00 00 	cmp    %edi,0xcc(%rsp)
    64e4:	0f 82 2e c1 ff ff    	jb     2618 <io_thread.cold+0x22>
	if (ring->flags & IORING_SETUP_SQE128)
    64ea:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    64ed:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    64f4:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
              io_uring_submit(&ring);
    64fb:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    64fe:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    6501:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	sqe->addr3 = 0;
    6508:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    650c:	d3 e0                	shl    %cl,%eax
              io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    650e:	41 8b 4c 24 68       	mov    0x68(%r12),%ecx
    6513:	48 c1 e0 06          	shl    $0x6,%rax
    6517:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->fd = fd;
    651f:	89 48 04             	mov    %ecx,0x4(%rax)
	sqe->user_data = (unsigned long) data;
    6522:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
	sqe->opcode = (__u8) op;
    6527:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->user_data = (unsigned long) data;
    652d:	48 89 48 20          	mov    %rcx,0x20(%rax)
	sqe->off = offset;
    6531:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    6539:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->len = len;
    653d:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    6545:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    654d:	0f 11 40 30          	movups %xmm0,0x30(%rax)
              io_uring_submit(&ring);
    6551:	e8 1a be ff ff       	call   2370 <io_uring_submit@plt>
	sqe->fd = fd;
    6556:	8b 04 24             	mov    (%rsp),%eax
	sqe->addr = (unsigned long) addr;
    6559:	48 89 6b 10          	mov    %rbp,0x10(%rbx)
	sqe->addr3 = 0;
    655d:	66 0f ef c0          	pxor   %xmm0,%xmm0
	sqe->opcode = (__u8) op;
    6561:	c7 03 01 00 00 00    	movl   $0x1,(%rbx)
          io_uring_submit(&ring);
    6567:	4c 89 ef             	mov    %r13,%rdi
	sqe->fd = fd;
    656a:	89 43 04             	mov    %eax,0x4(%rbx)
	sqe->off = offset;
    656d:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
	sqe->len = len;
    6575:	48 c7 43 18 01 00 00 00 	movq   $0x1,0x18(%rbx)
	sqe->buf_index = 0;
    657d:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->user_data = (unsigned long) data;
    6585:	4c 89 7b 20          	mov    %r15,0x20(%rbx)
	sqe->addr3 = 0;
    6589:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
    658d:	e8 de bd ff ff       	call   2370 <io_uring_submit@plt>
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
    6592:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6598:	0f 84 ad fd ff ff    	je     634b <io_thread+0xa1b>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
    659e:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    65a3:	48 89 eb             	mov    %rbp,%rbx
    65a6:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    65ab:	48 8b 0a             	mov    (%rdx),%rcx
    65ae:	8b 01                	mov    (%rcx),%eax
    65b0:	e9 2b fa ff ff       	jmp    5fe0 <io_thread+0x6b0>
                  if (!cqe->res) {
    65b5:	85 c0                	test   %eax,%eax
    65b7:	0f 84 6f 06 00 00    	je     6c2c <io_thread+0x12fc>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    65bd:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    65c5:	8b 02                	mov    (%rdx),%eax
    65c7:	83 c0 01             	add    $0x1,%eax
    65ca:	89 02                	mov    %eax,(%rdx)
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    65cc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    65d1:	48 8b 00             	mov    (%rax),%rax
    65d4:	8b 00                	mov    (%rax),%eax
}
    65d6:	e9 0e fa ff ff       	jmp    5fe9 <io_thread+0x6b9>
  while (data->running == 1) {
    65db:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    65e1:	0f 84 b1 f5 ff ff    	je     5b98 <io_thread+0x268>
    65e7:	e9 ea f5 ff ff       	jmp    5bd6 <io_thread+0x2a6>
    sock = socket(PF_INET, SOCK_STREAM, 0);
    65ec:	31 d2                	xor    %edx,%edx
    65ee:	be 01 00 00 00       	mov    $0x1,%esi
    65f3:	bf 02 00 00 00       	mov    $0x2,%edi
    65f8:	e8 b3 bf ff ff       	call   25b0 <socket@plt>
    65fd:	89 c3                	mov    %eax,%ebx
    if (sock == -1)
    65ff:	83 f8 ff             	cmp    $0xffffffff,%eax
    6602:	0f 84 8b c0 ff ff    	je     2693 <io_thread.cold+0x9d>
    if (setsockopt(sock,
    6608:	48 8d 4c 24 34       	lea    0x34(%rsp),%rcx
    660d:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    6613:	ba 02 00 00 00       	mov    $0x2,%edx
    6618:	89 c7                	mov    %eax,%edi
    661a:	be 01 00 00 00       	mov    $0x1,%esi
    int enable = 1;
    661f:	c7 44 24 34 01 00 00 00 	movl   $0x1,0x34(%rsp)
    if (setsockopt(sock,
    6627:	e8 f4 bc ff ff       	call   2320 <setsockopt@plt>
    662c:	85 c0                	test   %eax,%eax
    662e:	0f 88 d8 bf ff ff    	js     260c <io_thread.cold+0x16>
  return __builtin___memset_chk (__dest, __ch, __len,
    6634:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
    if (bind(sock,
    6639:	ba 10 00 00 00       	mov    $0x10,%edx
    663e:	89 df                	mov    %ebx,%edi
    6640:	48 c7 44 24 54 00 00 00 00 	movq   $0x0,0x54(%rsp)
    6649:	c7 44 24 5c 00 00 00 00 	movl   $0x0,0x5c(%rsp)
    srv_addr.sin_family = AF_INET;
    6651:	c7 44 24 50 02 00 18 db 	movl   $0xdb180002,0x50(%rsp)
    if (bind(sock,
    6659:	e8 42 be ff ff       	call   24a0 <bind@plt>
    665e:	85 c0                	test   %eax,%eax
    6660:	0f 88 cd bf ff ff    	js     2633 <io_thread.cold+0x3d>
    if (listen(sock, 10) < 0) {
    6666:	be 0a 00 00 00       	mov    $0xa,%esi
    666b:	89 df                	mov    %ebx,%edi
    666d:	e8 ee bd ff ff       	call   2460 <listen@plt>
    6672:	85 c0                	test   %eax,%eax
    6674:	0f 88 d9 bf ff ff    	js     2653 <io_thread.cold+0x5d>
    667a:	89 d9                	mov    %ebx,%ecx
    667c:	ba db 18 00 00       	mov    $0x18db,%edx
    6681:	48 8d 35 d0 2f 00 00 	lea    0x2fd0(%rip),%rsi        # 9658 <_IO_stdin_used+0x658>
    6688:	31 c0                	xor    %eax,%eax
    668a:	bf 01 00 00 00       	mov    $0x1,%edi
    668f:	e8 fc bd ff ff       	call   2490 <__printf_chk@plt>
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    6694:	be 04 00 00 00       	mov    $0x4,%esi
    6699:	bf 01 00 00 00       	mov    $0x1,%edi
    669e:	e8 3d bd ff ff       	call   23e0 <calloc@plt>
    66a3:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    66ab:	bf 01 00 00 00       	mov    $0x1,%edi
    66b0:	48 8d 35 c1 2f 00 00 	lea    0x2fc1(%rip),%rsi        # 9678 <_IO_stdin_used+0x678>
    msg->socket = sock;
    66b7:	89 18                	mov    %ebx,(%rax)
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    66b9:	48 89 c5             	mov    %rax,%rbp
    66bc:	31 c0                	xor    %eax,%eax
    66be:	e8 cd bd ff ff       	call   2490 <__printf_chk@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET, msg);
    66c3:	49 63 94 24 18 01 00 00 	movslq 0x118(%r12),%rdx
    66cb:	48 c1 e2 04          	shl    $0x4,%rdx
    66cf:	49 03 94 24 10 01 00 00 	add    0x110(%r12),%rdx
  while (data->running == 1) {
    66d7:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    66dd:	0f 85 b1 00 00 00    	jne    6794 <io_thread+0xe64>
      for (int x = 0 ; x < buffers->count ; x++) {
    66e3:	48 63 0a             	movslq (%rdx),%rcx
    66e6:	85 c9                	test   %ecx,%ecx
    66e8:	7e ed                	jle    66d7 <io_thread+0xda7>
    66ea:	48 8b 42 08          	mov    0x8(%rdx),%rax
    66ee:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    66f2:	48 8d 0c c8          	lea    (%rax,%rcx,8),%rcx
    66f6:	eb 09                	jmp    6701 <io_thread+0xdd1>
    66f8:	48 83 c0 28          	add    $0x28,%rax
    66fc:	48 39 c1             	cmp    %rax,%rcx
    66ff:	74 d6                	je     66d7 <io_thread+0xda7>
        if (buffers->buffer[x].available == 0) {
    6701:	44 8b 50 08          	mov    0x8(%rax),%r10d
    6705:	45 85 d2             	test   %r10d,%r10d
    6708:	75 ee                	jne    66f8 <io_thread+0xdc8>
          buffers->buffer[x].data = send;
    670a:	48 89 28             	mov    %rbp,(%rax)
          buffers->buffer[x].kind = kind;
    670d:	c7 40 20 00 00 00 00 	movl   $0x0,0x20(%rax)
          buffers->buffer[x].available = 1;
    6714:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
    671b:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    6723:	48 c1 e0 04          	shl    $0x4,%rax
    6727:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
  while (data->running == 1) {
    672f:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6735:	75 5d                	jne    6794 <io_thread+0xe64>
      for (int x = 0 ; x < buffers->count ; x++) {
    6737:	8b 10                	mov    (%rax),%edx
    6739:	48 8b 48 08          	mov    0x8(%rax),%rcx
    673d:	48 63 c2             	movslq %edx,%rax
    6740:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6744:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    6748:	85 d2                	test   %edx,%edx
    674a:	0f 8e 01 06 00 00    	jle    6d51 <io_thread+0x1421>
void* io_thread(void *arg) {
    6750:	48 89 cd             	mov    %rcx,%rbp
    6753:	eb 0c                	jmp    6761 <io_thread+0xe31>
    6755:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    6758:	48 83 c5 28          	add    $0x28,%rbp
    675c:	48 39 e8             	cmp    %rbp,%rax
    675f:	74 ef                	je     6750 <io_thread+0xe20>
        if (buffers->buffer[x].available == 1) {
    6761:	83 7d 08 01          	cmpl   $0x1,0x8(%rbp)
    6765:	75 f1                	jne    6758 <io_thread+0xe28>
          if (buffers->buffer[x].kind == kind) {
    6767:	83 7d 20 01          	cmpl   $0x1,0x20(%rbp)
    676b:	75 eb                	jne    6758 <io_thread+0xe28>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    676d:	be 28 00 00 00       	mov    $0x28,%esi
    6772:	bf 01 00 00 00       	mov    $0x1,%edi
    6777:	e8 64 bc ff ff       	call   23e0 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    677c:	48 8b 55 00          	mov    0x0(%rbp),%rdx
            buffers->buffer[x].available = 0;
    6780:	c7 45 08 00 00 00 00 	movl   $0x0,0x8(%rbp)
            reply->kind = buffers->buffer[x].kind;
    6787:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    678e:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    6791:	0f ae f8             	sfence
    6794:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    679c:	48 8d 35 fd 2e 00 00 	lea    0x2efd(%rip),%rsi        # 96a0 <_IO_stdin_used+0x6a0>
    67a3:	bf 01 00 00 00       	mov    $0x1,%edi
    67a8:	31 c0                	xor    %eax,%eax
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    67aa:	4c 8d 74 24 38       	lea    0x38(%rsp),%r14
    67af:	e8 dc bc ff ff       	call   2490 <__printf_chk@plt>
    67b4:	48 8d 44 24 60       	lea    0x60(%rsp),%rax
    67b9:	4c 89 e9             	mov    %r13,%rcx
    67bc:	4c 89 f2             	mov    %r14,%rdx
    67bf:	48 89 c6             	mov    %rax,%rsi
    67c2:	89 df                	mov    %ebx,%edi
    socklen_t client_addr_len = sizeof(client_addr);
    67c4:	c7 44 24 38 10 00 00 00 	movl   $0x10,0x38(%rsp)
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    67cc:	48 89 04 24          	mov    %rax,(%rsp)
    67d0:	e8 bb f0 ff ff       	call   5890 <add_accept_request>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    67d5:	bf 01 00 00 00       	mov    $0x1,%edi
    67da:	be 10 00 00 00       	mov    $0x10,%esi
    67df:	e8 fc bb ff ff       	call   23e0 <calloc@plt>
    void *buf = malloc(size);
    67e4:	bf e8 03 00 00       	mov    $0x3e8,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    67e9:	48 89 c5             	mov    %rax,%rbp
    void *buf = malloc(size);
    67ec:	e8 5f bc ff ff       	call   2450 <malloc@plt>
    if (!buf) {
    67f1:	48 85 c0             	test   %rax,%rax
    67f4:	0f 84 8a 05 00 00    	je     6d84 <io_thread+0x1454>
    iov->iov_base = zh_malloc(1000);
    67fa:	48 89 45 00          	mov    %rax,0x0(%rbp)
	unsigned int head, next = sq->sqe_tail + 1;
    67fe:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6805:	8b 94 24 30 01 00 00 	mov    0x130(%rsp),%edx
    iov->iov_len = 1000;
    680c:	48 c7 45 08 e8 03 00 00 	movq   $0x3e8,0x8(%rbp)
	unsigned int head, next = sq->sqe_tail + 1;
    6814:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    6817:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    681c:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    681e:	f6 c2 02             	test   $0x2,%dl
    6821:	0f 85 39 04 00 00    	jne    6c60 <io_thread+0x1330>
	if (next - head <= sq->ring_entries) {
    6827:	89 f1                	mov    %esi,%ecx
    6829:	29 c1                	sub    %eax,%ecx
    682b:	39 8c 24 cc 00 00 00 	cmp    %ecx,0xcc(%rsp)
    6832:	0f 82 07 be ff ff    	jb     263f <io_thread.cold+0x49>
	if (ring->flags & IORING_SETUP_SQE128)
    6838:	c1 ea 0a             	shr    $0xa,%edx
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
    683b:	4d 8d 7c 24 68       	lea    0x68(%r12),%r15
	sqe->addr3 = 0;
    6840:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(&ring);
    6844:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    6847:	89 d1                	mov    %edx,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6849:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    6850:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
		sq->sqe_tail = next;
    6857:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
    685e:	83 e1 01             	and    $0x1,%ecx
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6861:	41 8b 54 24 68       	mov    0x68(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6866:	d3 e0                	shl    %cl,%eax
    6868:	48 c1 e0 06          	shl    $0x6,%rax
    686c:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->opcode = (__u8) op;
    6874:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    687a:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    687d:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    6885:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->len = len;
    6889:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    6891:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    6899:	4c 89 78 20          	mov    %r15,0x20(%rax)
	sqe->addr3 = 0;
    689d:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(&ring);
    68a1:	e8 ca ba ff ff       	call   2370 <io_uring_submit@plt>
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    68a6:	48 8d 44 24 40       	lea    0x40(%rsp),%rax
    68ab:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    while (data->running == 1) {
    68b0:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    68b6:	0f 85 17 03 00 00    	jne    6bd3 <io_thread+0x12a3>
	if (ring->flags & IORING_SETUP_CQE32)
    68bc:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    68c3:	8b 94 24 20 01 00 00 	mov    0x120(%rsp),%edx
	if (ring->flags & IORING_SETUP_CQE32)
    68ca:	c1 e9 0b             	shr    $0xb,%ecx
    68cd:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    68d0:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
    68d8:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    68da:	48 8b bc 24 d8 00 00 00 	mov    0xd8(%rsp),%rdi
    68e2:	8b 37                	mov    (%rdi),%esi
		if (!available)
    68e4:	39 f0                	cmp    %esi,%eax
    68e6:	74 36                	je     691e <io_thread+0xfee>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    68e8:	89 d0                	mov    %edx,%eax
    68ea:	21 f0                	and    %esi,%eax
    68ec:	d3 e0                	shl    %cl,%eax
    68ee:	48 c1 e0 04          	shl    $0x4,%rax
    68f2:	48 03 84 24 08 01 00 00 	add    0x108(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    68fa:	f6 84 24 39 01 00 00 01 	testb  $0x1,0x139(%rsp)
    6902:	0f 85 95 02 00 00    	jne    6b9d <io_thread+0x126d>
    6908:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    690c:	0f 85 9e 04 00 00    	jne    6db0 <io_thread+0x1480>
			if (cqe->res < 0)
    6912:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6915:	83 c6 01             	add    $0x1,%esi
    6918:	89 37                	mov    %esi,(%rdi)
			if (!err)
    691a:	85 c0                	test   %eax,%eax
    691c:	79 b2                	jns    68d0 <io_thread+0xfa0>
	*cqe_ptr = cqe;
    691e:	48 c7 44 24 40 00 00 00 00 	movq   $0x0,0x40(%rsp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    6927:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    692c:	b9 01 00 00 00       	mov    $0x1,%ecx
    6931:	31 d2                	xor    %edx,%edx
    6933:	45 31 c0             	xor    %r8d,%r8d
    6936:	4c 89 ef             	mov    %r13,%rdi
    6939:	e8 42 bb ff ff       	call   2480 <__io_uring_get_cqe@plt>
    693e:	89 c1                	mov    %eax,%ecx
        if (cqe->user_data == 1) {
    6940:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6945:	48 8b 10             	mov    (%rax),%rdx
    6948:	48 83 fa 01          	cmp    $0x1,%rdx
    694c:	0f 84 66 02 00 00    	je     6bb8 <io_thread+0x1288>
        if (ret < 0)
    6952:	85 c9                	test   %ecx,%ecx
    6954:	0f 88 9c bc ff ff    	js     25f6 <io_thread.cold>
        if (cqe->res < 0) {
    695a:	8b 40 08             	mov    0x8(%rax),%eax
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    695d:	44 8b 02             	mov    (%rdx),%r8d
        if (cqe->res < 0) {
    6960:	85 c0                	test   %eax,%eax
    6962:	0f 88 29 03 00 00    	js     6c91 <io_thread+0x1361>
        switch (req->event_type) {
    6968:	45 85 c0             	test   %r8d,%r8d
    696b:	0f 84 9e 00 00 00    	je     6a0f <io_thread+0x10df>
    6971:	41 83 f8 01          	cmp    $0x1,%r8d
    6975:	0f 85 77 01 00 00    	jne    6af2 <io_thread+0x11c2>
                if (!cqe->res) {
    697b:	85 c0                	test   %eax,%eax
    697d:	0f 84 82 02 00 00    	je     6c05 <io_thread+0x12d5>
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    6983:	48 8d b4 24 50 01 00 00 	lea    0x150(%rsp),%rsi
    698b:	4d 8b 8c 24 10 01 00 00 	mov    0x110(%r12),%r9
    6993:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    6997:	4c 8d 94 24 50 05 00 00 	lea    0x550(%rsp),%r10
    699f:	41 8b bc 24 18 01 00 00 	mov    0x118(%r12),%edi
    for (int i = 0; i < dest_sz; i++) {
    69a7:	48 89 f0             	mov    %rsi,%rax
    69aa:	eb 15                	jmp    69c1 <io_thread+0x1091>
    69ac:	0f 1f 40 00          	nopl   0x0(%rax)
    69b0:	48 83 c0 01          	add    $0x1,%rax
    69b4:	48 83 c1 01          	add    $0x1,%rcx
    69b8:	4c 39 d0             	cmp    %r10,%rax
    69bb:	0f 84 69 03 00 00    	je     6d2a <io_thread+0x13fa>
        dest[i] = src[i];
    69c1:	44 0f b6 01          	movzbl (%rcx),%r8d
    69c5:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    69c8:	41 80 f8 0d          	cmp    $0xd,%r8b
    69cc:	75 e2                	jne    69b0 <io_thread+0x1080>
    69ce:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    69d2:	75 dc                	jne    69b0 <io_thread+0x1080>
            dest[i] = '\0';
    69d4:	c6 00 00             	movb   $0x0,(%rax)
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    69d7:	48 63 c7             	movslq %edi,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    69da:	8b 4a 08             	mov    0x8(%rdx),%ecx
    69dd:	4c 89 e7             	mov    %r12,%rdi
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    69e0:	48 c1 e0 04          	shl    $0x4,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    69e4:	44 8b 42 0c          	mov    0xc(%rdx),%r8d
    69e8:	48 89 f2             	mov    %rsi,%rdx
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    69eb:	4c 01 c8             	add    %r9,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    69ee:	4d 89 e9             	mov    %r13,%r9
    69f1:	48 89 c6             	mov    %rax,%rsi
    69f4:	e8 67 ec ff ff       	call   5660 <handle_http_method>
                eventfd_write(data->otherdataeventfd, 0);
    69f9:	41 8b 7c 24 70       	mov    0x70(%r12),%edi
    69fe:	31 f6                	xor    %esi,%esi
    6a00:	e8 3b ba ff ff       	call   2440 <eventfd_write@plt>
          io_uring_cqe_seen(&ring, cqe);
    6a05:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
                break;
    6a0a:	e9 de 00 00 00       	jmp    6aed <io_thread+0x11bd>
                add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6a0f:	48 8b 34 24          	mov    (%rsp),%rsi
    6a13:	4c 89 e9             	mov    %r13,%rcx
    6a16:	4c 89 f2             	mov    %r14,%rdx
    6a19:	89 df                	mov    %ebx,%edi
    6a1b:	e8 70 ee ff ff       	call   5890 <add_accept_request>
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
    6a20:	be 08 00 00 00       	mov    $0x8,%esi
    6a25:	bf 01 00 00 00       	mov    $0x1,%edi
    6a2a:	e8 b1 b9 ff ff       	call   23e0 <calloc@plt>
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
    6a2f:	49 63 b4 24 18 01 00 00 	movslq 0x118(%r12),%rsi
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
    6a37:	48 89 c7             	mov    %rax,%rdi
                newclientmsg->socket = cqe->res;
    6a3a:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
    6a3f:	48 c1 e6 04          	shl    $0x4,%rsi
    6a43:	49 03 b4 24 10 01 00 00 	add    0x110(%r12),%rsi
  while (data->running == 1) {
    6a4b:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
                newclientmsg->socket = cqe->res;
    6a51:	8b 50 08             	mov    0x8(%rax),%edx
                data->sockettoken++;
    6a54:	41 8b 84 24 28 01 00 00 	mov    0x128(%r12),%eax
    6a5c:	8d 48 01             	lea    0x1(%rax),%ecx
                newclientmsg->socket = cqe->res;
    6a5f:	66 0f 6e c2          	movd   %edx,%xmm0
    6a63:	66 0f 6e e1          	movd   %ecx,%xmm4
                data->sockettoken++;
    6a67:	41 89 8c 24 28 01 00 00 	mov    %ecx,0x128(%r12)
                newclientmsg->socket = cqe->res;
    6a6f:	66 0f 62 c4          	punpckldq %xmm4,%xmm0
    6a73:	66 0f d6 07          	movq   %xmm0,(%rdi)
  while (data->running == 1) {
    6a77:	75 64                	jne    6add <io_thread+0x11ad>
      for (int x = 0 ; x < buffers->count ; x++) {
    6a79:	48 63 16             	movslq (%rsi),%rdx
    6a7c:	85 d2                	test   %edx,%edx
    6a7e:	0f 8e 5c 01 00 00    	jle    6be0 <io_thread+0x12b0>
    6a84:	48 8b 46 08          	mov    0x8(%rsi),%rax
    6a88:	48 8d 14 92          	lea    (%rdx,%rdx,4),%rdx
    6a8c:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    6a90:	eb 0d                	jmp    6a9f <io_thread+0x116f>
    6a92:	48 83 c0 28          	add    $0x28,%rax
    6a96:	48 39 d0             	cmp    %rdx,%rax
    6a99:	0f 84 41 01 00 00    	je     6be0 <io_thread+0x12b0>
        if (buffers->buffer[x].available == 0) {
    6a9f:	44 8b 48 08          	mov    0x8(%rax),%r9d
    6aa3:	45 85 c9             	test   %r9d,%r9d
    6aa6:	75 ea                	jne    6a92 <io_thread+0x1162>
          buffers->buffer[x].data = send;
    6aa8:	48 89 38             	mov    %rdi,(%rax)
          buffers->buffer[x].kind = kind;
    6aab:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
          buffers->buffer[x].available = 1;
    6ab2:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
                add_read_request(data, &data->iomailboxes[data->other_io], cqe->res, data->sockettoken, &ring);
    6ab9:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6abe:	49 63 b4 24 18 01 00 00 	movslq 0x118(%r12),%rsi
    6ac6:	41 8b 8c 24 28 01 00 00 	mov    0x128(%r12),%ecx
    6ace:	8b 50 08             	mov    0x8(%rax),%edx
    6ad1:	48 c1 e6 04          	shl    $0x4,%rsi
    6ad5:	49 03 b4 24 10 01 00 00 	add    0x110(%r12),%rsi
    6add:	4d 89 e8             	mov    %r13,%r8
    6ae0:	4c 89 e7             	mov    %r12,%rdi
    6ae3:	e8 d8 e5 ff ff       	call   50c0 <add_read_request>
          io_uring_cqe_seen(&ring, cqe);
    6ae8:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
	if (cqe)
    6aed:	48 85 c0             	test   %rax,%rax
    6af0:	74 0f                	je     6b01 <io_thread+0x11d1>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6af2:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6afa:	8b 02                	mov    (%rdx),%eax
    6afc:	83 c0 01             	add    $0x1,%eax
    6aff:	89 02                	mov    %eax,(%rdx)
	unsigned int head, next = sq->sqe_tail + 1;
    6b01:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6b08:	8b 94 24 30 01 00 00 	mov    0x130(%rsp),%edx
	unsigned int head, next = sq->sqe_tail + 1;
    6b0f:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    6b12:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    6b17:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6b19:	f6 c2 02             	test   $0x2,%dl
    6b1c:	74 00                	je     6b1e <io_thread+0x11ee>
	if (next - head <= sq->ring_entries) {
    6b1e:	89 f1                	mov    %esi,%ecx
    6b20:	29 c1                	sub    %eax,%ecx
    6b22:	39 8c 24 cc 00 00 00 	cmp    %ecx,0xcc(%rsp)
    6b29:	0f 82 1a bb ff ff    	jb     2649 <io_thread.cold+0x53>
	if (ring->flags & IORING_SETUP_SQE128)
    6b2f:	c1 ea 0a             	shr    $0xa,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6b32:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    6b39:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
        io_uring_submit(&ring);
    6b40:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    6b43:	89 d1                	mov    %edx,%ecx
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6b45:	41 8b 54 24 68       	mov    0x68(%r12),%edx
		sq->sqe_tail = next;
    6b4a:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	sqe->addr3 = 0;
    6b51:	66 0f ef ed          	pxor   %xmm5,%xmm5
	if (ring->flags & IORING_SETUP_SQE128)
    6b55:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6b58:	d3 e0                	shl    %cl,%eax
    6b5a:	48 c1 e0 06          	shl    $0x6,%rax
    6b5e:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->fd = fd;
    6b66:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->addr = (unsigned long) addr;
    6b69:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->user_data = (unsigned long) data;
    6b6d:	4c 89 78 20          	mov    %r15,0x20(%rax)
	sqe->opcode = (__u8) op;
    6b71:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->off = offset;
    6b77:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->len = len;
    6b7f:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    6b87:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    6b8f:	0f 11 68 30          	movups %xmm5,0x30(%rax)
        io_uring_submit(&ring);
    6b93:	e8 d8 b7 ff ff       	call   2370 <io_uring_submit@plt>
    while (data->running == 1) {
    6b98:	e9 13 fd ff ff       	jmp    68b0 <io_thread+0xf80>
	*cqe_ptr = cqe;
    6b9d:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    6ba2:	48 85 c0             	test   %rax,%rax
    6ba5:	0f 84 7c fd ff ff    	je     6927 <io_thread+0xff7>
        if (cqe->user_data == 1) {
    6bab:	48 8b 10             	mov    (%rax),%rdx
    6bae:	48 83 fa 01          	cmp    $0x1,%rdx
    6bb2:	0f 85 a2 fd ff ff    	jne    695a <io_thread+0x102a>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6bb8:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6bc0:	48 8d 3d bc 25 00 00 	lea    0x25bc(%rip),%rdi        # 9183 <_IO_stdin_used+0x183>
    6bc7:	8b 02                	mov    (%rdx),%eax
    6bc9:	83 c0 01             	add    $0x1,%eax
    6bcc:	89 02                	mov    %eax,(%rdx)
    6bce:	e8 3d b7 ff ff       	call   2310 <puts@plt>
  if (data->io_mode == IO_MODE_SEND) {
    6bd3:	41 8b 84 24 0c 01 00 00 	mov    0x10c(%r12),%eax
    6bdb:	e9 74 ee ff ff       	jmp    5a54 <io_thread+0x124>
  while (data->running == 1) {
    6be0:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6be6:	0f 84 8d fe ff ff    	je     6a79 <io_thread+0x1149>
    6bec:	e9 c8 fe ff ff       	jmp    6ab9 <io_thread+0x1189>
    6bf1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		head = IO_URING_READ_ONCE(*sq->khead);
    6bf8:	4c 8b 44 24 70       	mov    0x70(%rsp),%r8
    6bfd:	45 8b 00             	mov    (%r8),%r8d
    6c00:	e9 f3 f7 ff ff       	jmp    63f8 <io_thread+0xac8>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6c05:	48 8b 0d 14 54 00 00 	mov    0x5414(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6c0c:	ba 0f 00 00 00       	mov    $0xf,%edx
    6c11:	be 01 00 00 00       	mov    $0x1,%esi
    6c16:	48 8d 3d 8c 25 00 00 	lea    0x258c(%rip),%rdi        # 91a9 <_IO_stdin_used+0x1a9>
    6c1d:	e8 fe b8 ff ff       	call   2520 <fwrite@plt>
          io_uring_cqe_seen(&ring, cqe);
    6c22:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6c27:	e9 c1 fe ff ff       	jmp    6aed <io_thread+0x11bd>
    6c2c:	48 8b 0d ed 53 00 00 	mov    0x53ed(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6c33:	ba 0f 00 00 00       	mov    $0xf,%edx
    6c38:	be 01 00 00 00       	mov    $0x1,%esi
    6c3d:	48 8d 3d 65 25 00 00 	lea    0x2565(%rip),%rdi        # 91a9 <_IO_stdin_used+0x1a9>
    6c44:	e8 d7 b8 ff ff       	call   2520 <fwrite@plt>
            io_uring_cqe_seen(&ring, cqe);
    6c49:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    6c4e:	e9 66 f6 ff ff       	jmp    62b9 <io_thread+0x989>
      for (int x = 0 ; x < buffers->count ; x++) {
    6c53:	eb fe                	jmp    6c53 <io_thread+0x1323>
    6c55:	eb fe                	jmp    6c55 <io_thread+0x1325>
    6c57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    6c60:	e9 c2 fb ff ff       	jmp    6827 <io_thread+0xef7>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6c65:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6c6d:	48 8d 3d 0f 25 00 00 	lea    0x250f(%rip),%rdi        # 9183 <_IO_stdin_used+0x183>
    6c74:	8b 02                	mov    (%rdx),%eax
    6c76:	83 c0 01             	add    $0x1,%eax
    6c79:	89 02                	mov    %eax,(%rdx)
    6c7b:	e8 90 b6 ff ff       	call   2310 <puts@plt>
    6c80:	48 8d 3d 88 25 00 00 	lea    0x2588(%rip),%rdi        # 920f <_IO_stdin_used+0x20f>
    6c87:	e8 84 b6 ff ff       	call   2310 <puts@plt>
    6c8c:	e9 67 f4 ff ff       	jmp    60f8 <io_thread+0x7c8>
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    6c91:	f7 d8                	neg    %eax
    6c93:	44 89 44 24 10       	mov    %r8d,0x10(%rsp)
    6c98:	89 c7                	mov    %eax,%edi
    6c9a:	e8 c1 b8 ff ff       	call   2560 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6c9f:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
    6ca4:	be 01 00 00 00       	mov    $0x1,%esi
    6ca9:	48 8b 3d 70 53 00 00 	mov    0x5370(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    6cb0:	48 89 c1             	mov    %rax,%rcx
    6cb3:	48 8d 15 0e 2a 00 00 	lea    0x2a0e(%rip),%rdx        # 96c8 <_IO_stdin_used+0x6c8>
    6cba:	31 c0                	xor    %eax,%eax
    6cbc:	e8 6f b8 ff ff       	call   2530 <__fprintf_chk@plt>
	if (cqe)
    6cc1:	48 83 7c 24 40 00    	cmpq   $0x0,0x40(%rsp)
    6cc7:	0f 84 e3 fb ff ff    	je     68b0 <io_thread+0xf80>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6ccd:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6cd5:	8b 02                	mov    (%rdx),%eax
    6cd7:	83 c0 01             	add    $0x1,%eax
    6cda:	89 02                	mov    %eax,(%rdx)
}
    6cdc:	e9 cf fb ff ff       	jmp    68b0 <io_thread+0xf80>
              fprintf(stderr, "Async request failed: %s for event: %d\n",
    6ce1:	f7 d8                	neg    %eax
    6ce3:	89 c7                	mov    %eax,%edi
    6ce5:	e8 76 b8 ff ff       	call   2560 <strerror@plt>
    6cea:	48 8b 3d 2f 53 00 00 	mov    0x532f(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    6cf1:	45 89 f0             	mov    %r14d,%r8d
    6cf4:	48 8d 15 cd 29 00 00 	lea    0x29cd(%rip),%rdx        # 96c8 <_IO_stdin_used+0x6c8>
    6cfb:	48 89 c1             	mov    %rax,%rcx
    6cfe:	be 01 00 00 00       	mov    $0x1,%esi
    6d03:	31 c0                	xor    %eax,%eax
    6d05:	e8 26 b8 ff ff       	call   2530 <__fprintf_chk@plt>
	if (cqe)
    6d0a:	48 83 7c 24 38 00    	cmpq   $0x0,0x38(%rsp)
    6d10:	0f 84 ca f3 ff ff    	je     60e0 <io_thread+0x7b0>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6d16:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6d1e:	8b 02                	mov    (%rdx),%eax
    6d20:	83 c0 01             	add    $0x1,%eax
    6d23:	89 02                	mov    %eax,(%rdx)
}
    6d25:	e9 b6 f3 ff ff       	jmp    60e0 <io_thread+0x7b0>
    6d2a:	48 8b 0d ef 52 00 00 	mov    0x52ef(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6d31:	ba 12 00 00 00       	mov    $0x12,%edx
    6d36:	be 01 00 00 00       	mov    $0x1,%esi
    6d3b:	48 8d 3d fc 23 00 00 	lea    0x23fc(%rip),%rdi        # 913e <_IO_stdin_used+0x13e>
    6d42:	e8 d9 b7 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    6d47:	bf 01 00 00 00       	mov    $0x1,%edi
    6d4c:	e8 af b7 ff ff       	call   2500 <exit@plt>
      for (int x = 0 ; x < buffers->count ; x++) {
    6d51:	eb fe                	jmp    6d51 <io_thread+0x1421>
    6d53:	48 8b 0d c6 52 00 00 	mov    0x52c6(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6d5a:	ba 28 00 00 00       	mov    $0x28,%edx
    6d5f:	be 01 00 00 00       	mov    $0x1,%esi
    6d64:	48 8d 3d 95 28 00 00 	lea    0x2895(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    6d6b:	e8 b0 b7 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    6d70:	bf 01 00 00 00       	mov    $0x1,%edi
    6d75:	e8 86 b7 ff ff       	call   2500 <exit@plt>
      exit(1); 
    6d7a:	bf 01 00 00 00       	mov    $0x1,%edi
    6d7f:	e8 7c b7 ff ff       	call   2500 <exit@plt>
    6d84:	48 8b 0d 95 52 00 00 	mov    0x5295(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6d8b:	ba 28 00 00 00       	mov    $0x28,%edx
    6d90:	be 01 00 00 00       	mov    $0x1,%esi
    6d95:	48 8d 3d 64 28 00 00 	lea    0x2864(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    6d9c:	e8 7f b7 ff ff       	call   2520 <fwrite@plt>
        exit(1);
    6da1:	bf 01 00 00 00       	mov    $0x1,%edi
    6da6:	e8 55 b7 ff ff       	call   2500 <exit@plt>
    6dab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    6db0:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
	return err;
    6db5:	e9 f1 fd ff ff       	jmp    6bab <io_thread+0x127b>
}
    6dba:	e8 a1 b5 ff ff       	call   2360 <__stack_chk_fail@plt>
    6dbf:	e9 9b b8 ff ff       	jmp    265f <io_thread.cold+0x69>
    6dc4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6dcf:	90                   	nop

0000000000006dd0 <buffersend>:
int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send) {
    6dd0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    6dd4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    6dd8:	75 35                	jne    6e0f <buffersend+0x3f>
      for (int x = 0 ; x < buffers->count ; x++) {
    6dda:	4c 63 06             	movslq (%rsi),%r8
    6ddd:	45 85 c0             	test   %r8d,%r8d
    6de0:	7e f2                	jle    6dd4 <buffersend+0x4>
    6de2:	48 8b 46 08          	mov    0x8(%rsi),%rax
    6de6:	4f 8d 04 80          	lea    (%r8,%r8,4),%r8
    6dea:	4e 8d 04 c0          	lea    (%rax,%r8,8),%r8
    6dee:	eb 09                	jmp    6df9 <buffersend+0x29>
    6df0:	48 83 c0 28          	add    $0x28,%rax
    6df4:	4c 39 c0             	cmp    %r8,%rax
    6df7:	74 db                	je     6dd4 <buffersend+0x4>
        if (buffers->buffer[x].available == 0) {
    6df9:	44 8b 48 08          	mov    0x8(%rax),%r9d
    6dfd:	45 85 c9             	test   %r9d,%r9d
    6e00:	75 ee                	jne    6df0 <buffersend+0x20>
          buffers->buffer[x].data = send;
    6e02:	48 89 08             	mov    %rcx,(%rax)
          buffers->buffer[x].kind = kind;
    6e05:	89 50 20             	mov    %edx,0x20(%rax)
          buffers->buffer[x].available = 1;
    6e08:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
}
    6e0f:	31 c0                	xor    %eax,%eax
    6e11:	c3                   	ret
    6e12:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6e1d:	0f 1f 00             	nopl   (%rax)

0000000000006e20 <buffersend_filter>:
int buffersend_filter(struct KernelThread *data, struct Buffers *buffers, int kind, void * send, int filter) {
    6e20:	f3 0f 1e fa          	endbr64
    6e24:	49 89 f9             	mov    %rdi,%r9
    6e27:	48 89 f7             	mov    %rsi,%rdi
  while (data->running == 1) {
    6e2a:	41 83 79 44 01       	cmpl   $0x1,0x44(%r9)
    6e2f:	75 42                	jne    6e73 <buffersend_filter+0x53>
      for (int x = 0 ; x < buffers->count ; x++) {
    6e31:	48 63 37             	movslq (%rdi),%rsi
    6e34:	85 f6                	test   %esi,%esi
    6e36:	7e f2                	jle    6e2a <buffersend_filter+0xa>
    6e38:	48 8b 47 08          	mov    0x8(%rdi),%rax
    6e3c:	48 8d 34 b6          	lea    (%rsi,%rsi,4),%rsi
    6e40:	48 8d 34 f0          	lea    (%rax,%rsi,8),%rsi
    6e44:	eb 13                	jmp    6e59 <buffersend_filter+0x39>
    6e46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6e50:	48 83 c0 28          	add    $0x28,%rax
    6e54:	48 39 f0             	cmp    %rsi,%rax
    6e57:	74 d1                	je     6e2a <buffersend_filter+0xa>
        if (buffers->buffer[x].available == 0) {
    6e59:	44 8b 50 08          	mov    0x8(%rax),%r10d
    6e5d:	45 85 d2             	test   %r10d,%r10d
    6e60:	75 ee                	jne    6e50 <buffersend_filter+0x30>
          buffers->buffer[x].data = send;
    6e62:	48 89 08             	mov    %rcx,(%rax)
          buffers->buffer[x].kind = kind;
    6e65:	89 50 20             	mov    %edx,0x20(%rax)
          buffers->buffer[x].filter = filter;
    6e68:	44 89 40 24          	mov    %r8d,0x24(%rax)
          buffers->buffer[x].available = 1;
    6e6c:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
}
    6e73:	31 c0                	xor    %eax,%eax
    6e75:	c3                   	ret
    6e76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006e80 <bufferrecv_filter>:
void * bufferrecv_filter(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking, int filter) {
    6e80:	f3 0f 1e fa          	endbr64
    6e84:	55                   	push   %rbp
    6e85:	48 89 f0             	mov    %rsi,%rax
    6e88:	53                   	push   %rbx
    6e89:	48 83 ec 08          	sub    $0x8,%rsp
  while (data->running == 1) {
    6e8d:	83 78 44 01          	cmpl   $0x1,0x44(%rax)
void * bufferrecv_filter(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking, int filter) {
    6e91:	8b 74 24 20          	mov    0x20(%rsp),%esi
  while (data->running == 1) {
    6e95:	75 75                	jne    6f0c <bufferrecv_filter+0x8c>
    6e97:	89 cd                	mov    %ecx,%ebp
      for (int x = 0 ; x < buffers->count ; x++) {
    6e99:	8b 0a                	mov    (%rdx),%ecx
    6e9b:	85 c9                	test   %ecx,%ecx
    6e9d:	7e 61                	jle    6f00 <bufferrecv_filter+0x80>
    6e9f:	90                   	nop
    6ea0:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    6ea4:	48 63 c1             	movslq %ecx,%rax
    6ea7:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6eab:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    6eaf:	eb 10                	jmp    6ec1 <bufferrecv_filter+0x41>
    6eb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6eb8:	48 83 c3 28          	add    $0x28,%rbx
    6ebc:	48 39 c3             	cmp    %rax,%rbx
    6ebf:	74 3f                	je     6f00 <bufferrecv_filter+0x80>
        if (buffers->buffer[x].available == 1) {
    6ec1:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    6ec5:	75 f1                	jne    6eb8 <bufferrecv_filter+0x38>
          if (buffers->buffer[x].kind == kind && buffers->buffer[x].filter == filter) {
    6ec7:	39 6b 20             	cmp    %ebp,0x20(%rbx)
    6eca:	75 ec                	jne    6eb8 <bufferrecv_filter+0x38>
    6ecc:	39 73 24             	cmp    %esi,0x24(%rbx)
    6ecf:	75 e7                	jne    6eb8 <bufferrecv_filter+0x38>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6ed1:	be 28 00 00 00       	mov    $0x28,%esi
    6ed6:	bf 01 00 00 00       	mov    $0x1,%edi
    6edb:	e8 00 b5 ff ff       	call   23e0 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    6ee0:	48 8b 13             	mov    (%rbx),%rdx
            reply->kind = buffers->buffer[x].kind;
    6ee3:	89 68 20             	mov    %ebp,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    6ee6:	48 89 10             	mov    %rdx,(%rax)
            buffers->buffer[x].available = 0;
    6ee9:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            asm volatile ("mfence" ::: "memory");
    6ef0:	0f ae f0             	mfence
}
    6ef3:	48 83 c4 08          	add    $0x8,%rsp
    6ef7:	5b                   	pop    %rbx
    6ef8:	5d                   	pop    %rbp
    6ef9:	c3                   	ret
    6efa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
     if (nonblocking == 1) { return NULL; }
    6f00:	41 83 f9 01          	cmp    $0x1,%r9d
    6f04:	74 06                	je     6f0c <bufferrecv_filter+0x8c>
      for (int x = 0 ; x < buffers->count ; x++) {
    6f06:	85 c9                	test   %ecx,%ecx
    6f08:	7f 96                	jg     6ea0 <bufferrecv_filter+0x20>
    6f0a:	eb fa                	jmp    6f06 <bufferrecv_filter+0x86>
}
    6f0c:	48 83 c4 08          	add    $0x8,%rsp
     if (nonblocking == 1) { return NULL; }
    6f10:	31 c0                	xor    %eax,%eax
}
    6f12:	5b                   	pop    %rbx
    6f13:	5d                   	pop    %rbp
    6f14:	c3                   	ret
    6f15:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000006f20 <bufferrecv>:
void * bufferrecv(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking) {
    6f20:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    6f24:	83 7e 44 01          	cmpl   $0x1,0x44(%rsi)
    6f28:	75 76                	jne    6fa0 <bufferrecv+0x80>
void * bufferrecv(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking) {
    6f2a:	55                   	push   %rbp
    6f2b:	89 cd                	mov    %ecx,%ebp
    6f2d:	53                   	push   %rbx
    6f2e:	48 83 ec 08          	sub    $0x8,%rsp
      for (int x = 0 ; x < buffers->count ; x++) {
    6f32:	8b 0a                	mov    (%rdx),%ecx
    6f34:	85 c9                	test   %ecx,%ecx
    6f36:	7e 58                	jle    6f90 <bufferrecv+0x70>
    6f38:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    6f3c:	48 63 c1             	movslq %ecx,%rax
    6f3f:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6f43:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    6f47:	eb 10                	jmp    6f59 <bufferrecv+0x39>
    6f49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6f50:	48 83 c3 28          	add    $0x28,%rbx
    6f54:	48 39 c3             	cmp    %rax,%rbx
    6f57:	74 37                	je     6f90 <bufferrecv+0x70>
        if (buffers->buffer[x].available == 1) {
    6f59:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    6f5d:	75 f1                	jne    6f50 <bufferrecv+0x30>
          if (buffers->buffer[x].kind == kind) {
    6f5f:	39 6b 20             	cmp    %ebp,0x20(%rbx)
    6f62:	75 ec                	jne    6f50 <bufferrecv+0x30>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6f64:	be 28 00 00 00       	mov    $0x28,%esi
    6f69:	bf 01 00 00 00       	mov    $0x1,%edi
    6f6e:	e8 6d b4 ff ff       	call   23e0 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    6f73:	48 8b 13             	mov    (%rbx),%rdx
            reply->kind = buffers->buffer[x].kind;
    6f76:	89 68 20             	mov    %ebp,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    6f79:	48 89 10             	mov    %rdx,(%rax)
            buffers->buffer[x].available = 0;
    6f7c:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            asm volatile ("sfence" ::: "memory");
    6f83:	0f ae f8             	sfence
}
    6f86:	48 83 c4 08          	add    $0x8,%rsp
    6f8a:	5b                   	pop    %rbx
    6f8b:	5d                   	pop    %rbp
    6f8c:	c3                   	ret
    6f8d:	0f 1f 00             	nopl   (%rax)
     if (nonblocking == 1) { return NULL; }
    6f90:	41 83 f9 01          	cmp    $0x1,%r9d
    6f94:	74 06                	je     6f9c <bufferrecv+0x7c>
      for (int x = 0 ; x < buffers->count ; x++) {
    6f96:	85 c9                	test   %ecx,%ecx
    6f98:	7f 9e                	jg     6f38 <bufferrecv+0x18>
    6f9a:	eb fa                	jmp    6f96 <bufferrecv+0x76>
     if (nonblocking == 1) { return NULL; }
    6f9c:	31 c0                	xor    %eax,%eax
    6f9e:	eb e6                	jmp    6f86 <bufferrecv+0x66>
    6fa0:	31 c0                	xor    %eax,%eax
}
    6fa2:	c3                   	ret
    6fa3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6fae:	66 90                	xchg   %ax,%ax

0000000000006fb0 <wait_for_new_client>:
struct NewClientMessage * wait_for_new_client(struct KernelThread *data, int nonblocking) {
    6fb0:	f3 0f 1e fa          	endbr64
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    6fb4:	48 63 97 1c 01 00 00 	movslq 0x11c(%rdi),%rdx
    6fbb:	48 c1 e2 04          	shl    $0x4,%rdx
    6fbf:	48 03 97 10 01 00 00 	add    0x110(%rdi),%rdx
  while (data->running == 1) {
    6fc6:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    6fca:	0f 85 84 00 00 00    	jne    7054 <wait_for_new_client+0xa4>
      for (int x = 0 ; x < buffers->count ; x++) {
    6fd0:	8b 0a                	mov    (%rdx),%ecx
    6fd2:	85 c9                	test   %ecx,%ecx
    6fd4:	7e 65                	jle    703b <wait_for_new_client+0x8b>
struct NewClientMessage * wait_for_new_client(struct KernelThread *data, int nonblocking) {
    6fd6:	53                   	push   %rbx
    6fd7:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    6fdb:	48 63 c1             	movslq %ecx,%rax
    6fde:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6fe2:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    6fe6:	eb 11                	jmp    6ff9 <wait_for_new_client+0x49>
    6fe8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    6ff0:	48 83 c3 28          	add    $0x28,%rbx
    6ff4:	48 39 c3             	cmp    %rax,%rbx
    6ff7:	74 37                	je     7030 <wait_for_new_client+0x80>
        if (buffers->buffer[x].available == 1) {
    6ff9:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    6ffd:	75 f1                	jne    6ff0 <wait_for_new_client+0x40>
          if (buffers->buffer[x].kind == kind) {
    6fff:	83 7b 20 02          	cmpl   $0x2,0x20(%rbx)
    7003:	75 eb                	jne    6ff0 <wait_for_new_client+0x40>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    7005:	be 28 00 00 00       	mov    $0x28,%esi
    700a:	bf 01 00 00 00       	mov    $0x1,%edi
    700f:	e8 cc b3 ff ff       	call   23e0 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    7014:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    7017:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            reply->kind = buffers->buffer[x].kind;
    701e:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    7025:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    7028:	0f ae f8             	sfence
  struct NewClientMessage *newclientmsg = newclient->data;
    702b:	48 8b 00             	mov    (%rax),%rax
}
    702e:	5b                   	pop    %rbx
    702f:	c3                   	ret
     if (nonblocking == 1) { return NULL; }
    7030:	83 fe 01             	cmp    $0x1,%esi
    7033:	74 1b                	je     7050 <wait_for_new_client+0xa0>
      for (int x = 0 ; x < buffers->count ; x++) {
    7035:	85 c9                	test   %ecx,%ecx
    7037:	7f 9e                	jg     6fd7 <wait_for_new_client+0x27>
    7039:	eb fa                	jmp    7035 <wait_for_new_client+0x85>
     if (nonblocking == 1) { return NULL; }
    703b:	83 fe 01             	cmp    $0x1,%esi
    703e:	74 14                	je     7054 <wait_for_new_client+0xa4>
      for (int x = 0 ; x < buffers->count ; x++) {
    7040:	85 c9                	test   %ecx,%ecx
    7042:	7f 92                	jg     6fd6 <wait_for_new_client+0x26>
    7044:	eb fa                	jmp    7040 <wait_for_new_client+0x90>
    7046:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    return NULL;
    7050:	31 c0                	xor    %eax,%eax
}
    7052:	5b                   	pop    %rbx
    7053:	c3                   	ret
    return NULL;
    7054:	31 c0                	xor    %eax,%eax
}
    7056:	c3                   	ret
    7057:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007060 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    7060:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    7064:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    706b:	8b 8e cc 00 00 00    	mov    0xcc(%rsi),%ecx
    7071:	85 c9                	test   %ecx,%ecx
    7073:	0f 8e d5 00 00 00    	jle    714e <barriered_work_ingest+0xee>
int barriered_work_ingest(struct BarrierTask *data) {
    7079:	41 56                	push   %r14
    707b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    707d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    7080:	41 54                	push   %r12
    7082:	49 89 fc             	mov    %rdi,%r12
    7085:	55                   	push   %rbp
    7086:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    7087:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    708b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7090:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    7094:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    709c:	31 ed                	xor    %ebp,%ebp
    709e:	8b 10                	mov    (%rax),%edx
    70a0:	85 d2                	test   %edx,%edx
    70a2:	7e 25                	jle    70c9 <barriered_work_ingest+0x69>
    70a4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    70a8:	48 8d 5c ad 00       	lea    0x0(%rbp,%rbp,4),%rbx
    70ad:	48 c1 e3 03          	shl    $0x3,%rbx
    70b1:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    70b5:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    70b9:	74 25                	je     70e0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    70bb:	48 83 c5 01          	add    $0x1,%rbp
    70bf:	39 ea                	cmp    %ebp,%edx
    70c1:	7f e5                	jg     70a8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    70c3:	8b 8e cc 00 00 00    	mov    0xcc(%rsi),%ecx
    70c9:	49 83 c5 01          	add    $0x1,%r13
    70cd:	44 39 e9             	cmp    %r13d,%ecx
    70d0:	7f be                	jg     7090 <barriered_work_ingest+0x30>
}
    70d2:	5b                   	pop    %rbx
    70d3:	31 c0                	xor    %eax,%eax
    70d5:	5d                   	pop    %rbp
    70d6:	41 5c                	pop    %r12
    70d8:	41 5d                	pop    %r13
    70da:	41 5e                	pop    %r14
    70dc:	c3                   	ret
    70dd:	0f 1f 00             	nopl   (%rax)
        data->ingest_count++;
    70e0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    70e9:	48 63 70 1c          	movslq 0x1c(%rax),%rsi
    70ed:	bf 04 00 00 00       	mov    $0x4,%edi
    70f2:	48 c1 e6 05          	shl    $0x5,%rsi
    70f6:	48 03 70 10          	add    0x10(%rax),%rsi
    70fa:	48 83 c6 10          	add    $0x10,%rsi
    70fe:	e8 2d b2 ff ff       	call   2330 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    7103:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    710b:	48 8b 40 50          	mov    0x50(%rax),%rax
    710f:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    7113:	48 03 58 08          	add    0x8(%rax),%rbx
    7117:	8b 43 1c             	mov    0x1c(%rbx),%eax
        data->thread->buffers[b]->buffer[x].available = 0;
    711a:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    7121:	83 c0 01             	add    $0x1,%eax
    7124:	99                   	cltd
    7125:	f7 7b 18             	idivl  0x18(%rbx)
    7128:	89 53 1c             	mov    %edx,0x1c(%rbx)
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    712b:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    7133:	48 83 c5 01          	add    $0x1,%rbp
    7137:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    713b:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    713f:	8b 10                	mov    (%rax),%edx
    7141:	39 ea                	cmp    %ebp,%edx
    7143:	0f 8f 5b ff ff ff    	jg     70a4 <barriered_work_ingest+0x44>
    7149:	e9 75 ff ff ff       	jmp    70c3 <barriered_work_ingest+0x63>
}
    714e:	31 c0                	xor    %eax,%eax
    7150:	c3                   	ret
    7151:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    715c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000007160 <receive>:
int receive(struct BarrierTask *data) {
    7160:	f3 0f 1e fa          	endbr64
    7164:	41 56                	push   %r14
    7166:	41 55                	push   %r13
    7168:	41 54                	push   %r12
    716a:	55                   	push   %rbp
    716b:	53                   	push   %rbx
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    716c:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    7173:	45 85 e4             	test   %r12d,%r12d
    7176:	0f 8e 27 01 00 00    	jle    72a3 <receive+0x143>
    if (n == data->thread->real_thread_index) { continue; }
    717c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    7183:	48 89 fe             	mov    %rdi,%rsi
    7186:	31 db                	xor    %ebx,%ebx
    7188:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    718c:	49 89 ed             	mov    %rbp,%r13
    718f:	90                   	nop
    7190:	41 39 dd             	cmp    %ebx,%r13d
    7193:	0f 84 fd 00 00 00    	je     7296 <receive+0x136>
    struct Data *me = data->mailboxes[n].lower;
    7199:	48 89 d8             	mov    %rbx,%rax
    719c:	48 c1 e0 08          	shl    $0x8,%rax
    71a0:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    71a7:	48 8b 10             	mov    (%rax),%rdx
    if (me->available_reading == 1) {
    71aa:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    71b0:	83 f8 01             	cmp    $0x1,%eax
    71b3:	74 11                	je     71c6 <receive+0x66>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    71b5:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    71bc:	75 08                	jne    71c6 <receive+0x66>
    71be:	85 c0                	test   %eax,%eax
    71c0:	0f 84 d0 00 00 00    	je     7296 <receive+0x136>
    for (; me->messages_count > 0 ; ) {
    71c6:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    71cd:	48 85 ff             	test   %rdi,%rdi
    71d0:	0f 8e a2 00 00 00    	jle    7278 <receive+0x118>
    71d6:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    71dd:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    71e4:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
    71e8:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    71eb:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    71ef:	49 01 f9             	add    %rdi,%r9
    71f2:	49 01 f8             	add    %rdi,%r8
    71f5:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    71fc:	eb 08                	jmp    7206 <receive+0xa6>
    71fe:	66 90                	xchg   %ax,%ax
    for (; me->messages_count > 0 ; ) {
    7200:	48 83 e8 01          	sub    $0x1,%rax
    7204:	72 72                	jb     7278 <receive+0x118>
      data->sends++;
    7206:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
    7209:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
    7210:	48 29 c1             	sub    %rax,%rcx
    7213:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      data->n++;
    721a:	4c 89 c1             	mov    %r8,%rcx
    721d:	48 29 c1             	sub    %rax,%rcx
    7220:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
    7227:	48 89 f9             	mov    %rdi,%rcx
    722a:	48 29 c1             	sub    %rax,%rcx
    722d:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
      if (me->messages[x]->group == data->group) {
    7234:	48 63 c8             	movslq %eax,%rcx
    7237:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    723b:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    723f:	75 bf                	jne    7200 <receive+0xa0>
    7241:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    7245:	75 b9                	jne    7200 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    7247:	49 63 46 04          	movslq 0x4(%r14),%rax
    724b:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    724d:	bf 01 00 00 00       	mov    $0x1,%edi
    7252:	ba 01 00 00 00       	mov    $0x1,%edx
    7257:	48 8d 35 b2 25 00 00 	lea    0x25b2(%rip),%rsi        # 9810 <_IO_stdin_used+0x810>
    725e:	48 39 e8             	cmp    %rbp,%rax
    7261:	0f 94 c1             	sete   %cl
    7264:	31 c0                	xor    %eax,%eax
    7266:	e8 25 b2 ff ff       	call   2490 <__printf_chk@plt>
        exit(1);
    726b:	bf 01 00 00 00       	mov    $0x1,%edi
    7270:	e8 8b b2 ff ff       	call   2500 <exit@plt>
    7275:	0f 1f 00             	nopl   (%rax)
      me->available_reading = 0;
    7278:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    7282:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
    728c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7296:	48 83 c3 01          	add    $0x1,%rbx
    729a:	49 39 dc             	cmp    %rbx,%r12
    729d:	0f 85 ed fe ff ff    	jne    7190 <receive+0x30>
}
    72a3:	31 c0                	xor    %eax,%eax
    72a5:	5b                   	pop    %rbx
    72a6:	5d                   	pop    %rbp
    72a7:	41 5c                	pop    %r12
    72a9:	41 5d                	pop    %r13
    72ab:	41 5e                	pop    %r14
    72ad:	c3                   	ret
    72ae:	66 90                	xchg   %ax,%ax

00000000000072b0 <sendm>:
int sendm(struct BarrierTask *data) {
    72b0:	f3 0f 1e fa          	endbr64
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    72b4:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    72ba:	85 c0                	test   %eax,%eax
    72bc:	0f 8e 96 02 00 00    	jle    7558 <sendm+0x2a8>
int sendm(struct BarrierTask *data) {
    72c2:	41 57                	push   %r15
    72c4:	41 56                	push   %r14
    72c6:	41 55                	push   %r13
        if (n == data->thread->real_thread_index) { continue; }
    72c8:	45 31 ed             	xor    %r13d,%r13d
int sendm(struct BarrierTask *data) {
    72cb:	41 54                	push   %r12
    72cd:	4c 63 e0             	movslq %eax,%r12
    72d0:	55                   	push   %rbp
    72d1:	48 89 fd             	mov    %rdi,%rbp
    72d4:	53                   	push   %rbx
        if (n == data->thread->real_thread_index) { continue; }
    72d5:	48 8b 9f 28 01 00 00 	mov    0x128(%rdi),%rbx
    72dc:	44 8b 7b 08          	mov    0x8(%rbx),%r15d
    72e0:	48 89 5c 24 c8       	mov    %rbx,-0x38(%rsp)
    72e5:	0f 1f 00             	nopl   (%rax)
    72e8:	45 39 ef             	cmp    %r13d,%r15d
    72eb:	0f 84 97 00 00 00    	je     7388 <sendm+0xd8>
        struct Data *them = data->mailboxes[n].higher;
    72f1:	4c 89 e8             	mov    %r13,%rax
    72f4:	48 c1 e0 08          	shl    $0x8,%rax
    72f8:	48 03 85 70 01 00 00 	add    0x170(%rbp),%rax
        data->mailboxes[n].counter++;
    72ff:	48 8b 98 b8 00 00 00 	mov    0xb8(%rax),%rbx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7306:	83 b8 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax)
        struct Data *them = data->mailboxes[n].higher;
    730d:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7314:	40 0f 94 c7          	sete   %dil
        data->mailboxes[n].counter++;
    7318:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    731c:	48 89 90 b8 00 00 00 	mov    %rdx,0xb8(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7323:	48 85 d2             	test   %rdx,%rdx
    7326:	7f 05                	jg     732d <sendm+0x7d>
    7328:	40 84 ff             	test   %dil,%dil
    732b:	75 5b                	jne    7388 <sendm+0xd8>
        if (them->messages_count > 0) {
    732d:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    7334:	48 85 f6             	test   %rsi,%rsi
    7337:	7f 4f                	jg     7388 <sendm+0xd8>
        if (them->available_sending == 1) {
    7339:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    7340:	41 83 f8 01          	cmp    $0x1,%r8d
    7344:	74 0e                	je     7354 <sendm+0xa4>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    7346:	83 b9 08 04 00 00 02 	cmpl   $0x2,0x408(%rcx)
    734d:	75 05                	jne    7354 <sendm+0xa4>
    734f:	45 85 c0             	test   %r8d,%r8d
    7352:	74 34                	je     7388 <sendm+0xd8>
        if (data->sending == 1) {
    7354:	83 bd 88 01 00 00 01 	cmpl   $0x1,0x188(%rbp)
    735b:	74 4b                	je     73a8 <sendm+0xf8>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter >= limit) {
    735d:	48 85 d2             	test   %rdx,%rdx
    7360:	7e 26                	jle    7388 <sendm+0xd8>
    7362:	40 84 ff             	test   %dil,%dil
    7365:	74 21                	je     7388 <sendm+0xd8>
          data->mailboxes[n].counter = 0;
    7367:	48 c7 80 b8 00 00 00 00 00 00 00 	movq   $0x0,0xb8(%rax)
          data->thread->have_foreign = 1;
    7372:	48 8b 44 24 c8       	mov    -0x38(%rsp),%rax
    7377:	c7 80 08 01 00 00 01 00 00 00 	movl   $0x1,0x108(%rax)
    7381:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7388:	49 83 c5 01          	add    $0x1,%r13
    738c:	4d 39 ec             	cmp    %r13,%r12
    738f:	0f 85 53 ff ff ff    	jne    72e8 <sendm+0x38>
}
    7395:	31 c0                	xor    %eax,%eax
    7397:	5b                   	pop    %rbx
    7398:	5d                   	pop    %rbp
    7399:	41 5c                	pop    %r12
    739b:	41 5d                	pop    %r13
    739d:	41 5e                	pop    %r14
    739f:	41 5f                	pop    %r15
    73a1:	c3                   	ret
    73a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (; them->messages_count < min;) {
    73a8:	4c 63 99 88 00 00 00 	movslq 0x88(%rcx),%r11
    73af:	4c 39 de             	cmp    %r11,%rsi
    73b2:	0f 8d c2 00 00 00    	jge    747a <sendm+0x1ca>
    73b8:	48 8b 9d 08 01 00 00 	mov    0x108(%rbp),%rbx
    73bf:	4d 89 de             	mov    %r11,%r14
            them->messages[them->messages_count++] = data->message; 
    73c2:	4c 8b 11             	mov    (%rcx),%r10
    73c5:	49 29 f6             	sub    %rsi,%r14
    73c8:	48 89 5c 24 d8       	mov    %rbx,-0x28(%rsp)
    73cd:	48 8b 99 80 03 00 00 	mov    0x380(%rcx),%rbx
    73d4:	4d 8d 46 ff          	lea    -0x1(%r14),%r8
    73d8:	48 89 5c 24 e0       	mov    %rbx,-0x20(%rsp)
    73dd:	49 83 f8 02          	cmp    $0x2,%r8
    73e1:	0f 86 51 01 00 00    	jbe    7538 <sendm+0x288>
    73e7:	48 8d 1c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rbx
    73ef:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    73f7:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    73fc:	4c 01 d3             	add    %r10,%rbx
    73ff:	4c 8d 85 90 01 00 00 	lea    0x190(%rbp),%r8
    7406:	48 89 5c 24 d0       	mov    %rbx,-0x30(%rsp)
    740b:	4b 8d 1c 0a          	lea    (%r10,%r9,1),%rbx
    740f:	49 39 d8             	cmp    %rbx,%r8
    7412:	0f 83 88 00 00 00    	jae    74a0 <sendm+0x1f0>
    7418:	48 8d 9d 98 01 00 00 	lea    0x198(%rbp),%rbx
    741f:	48 39 5c 24 d0       	cmp    %rbx,-0x30(%rsp)
    7424:	73 7a                	jae    74a0 <sendm+0x1f0>
    7426:	4c 8b 44 24 e8       	mov    -0x18(%rsp),%r8
    742b:	4b 8d 34 0a          	lea    (%r10,%r9,1),%rsi
    742f:	4d 01 d0             	add    %r10,%r8
    7432:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    7438:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
          for (; them->messages_count < min;) {
    743f:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    7443:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    7447:	4c 39 c6             	cmp    %r8,%rsi
    744a:	75 ec                	jne    7438 <sendm+0x188>
    744c:	0f 1f 40 00          	nopl   0x0(%rax)
    7450:	48 8b 74 24 d8       	mov    -0x28(%rsp),%rsi
    7455:	4c 01 f6             	add    %r14,%rsi
    7458:	48 89 b5 08 01 00 00 	mov    %rsi,0x108(%rbp)
    745f:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    7464:	4c 89 99 80 00 00 00 	mov    %r11,0x80(%rcx)
    746b:	4c 01 f6             	add    %r14,%rsi
    746e:	48 89 b1 80 03 00 00 	mov    %rsi,0x380(%rcx)
    7475:	4f 89 4c da f8       	mov    %r9,-0x8(%r10,%r11,8)
          them->available_sending = 0;
    747a:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_reading = 1;
    7484:	c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rcx)
          them->available_receiving = 1;
    748e:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    7498:	e9 c0 fe ff ff       	jmp    735d <sendm+0xad>
    749d:	0f 1f 00             	nopl   (%rax)
    74a0:	4c 89 f3             	mov    %r14,%rbx
    74a3:	4c 8b 44 24 d0       	mov    -0x30(%rsp),%r8
    74a8:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    74af:	48 d1 eb             	shr    %rbx
    74b2:	48 c1 e3 04          	shl    $0x4,%rbx
    74b6:	66 49 0f 6e c1       	movq   %r9,%xmm0
    74bb:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    74c0:	4c 01 c3             	add    %r8,%rbx
    74c3:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    74c7:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    74cc:	48 8b 5c 24 e8       	mov    -0x18(%rsp),%rbx
    74d1:	83 e3 10             	and    $0x10,%ebx
    74d4:	75 4a                	jne    7520 <sendm+0x270>
    74d6:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    74db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    74e0:	41 0f 11 00          	movups %xmm0,(%r8)
    74e4:	49 83 c0 20          	add    $0x20,%r8
    74e8:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    74ed:	49 39 d8             	cmp    %rbx,%r8
    74f0:	75 ee                	jne    74e0 <sendm+0x230>
    74f2:	4d 89 f0             	mov    %r14,%r8
    74f5:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    74f9:	49 01 f0             	add    %rsi,%r8
    74fc:	41 f6 c6 01          	test   $0x1,%r14b
    7500:	0f 84 4a ff ff ff    	je     7450 <sendm+0x1a0>
            them->messages[them->messages_count++] = data->message; 
    7506:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    750d:	4f 89 0c c2          	mov    %r9,(%r10,%r8,8)
          for (; them->messages_count < min;) {
    7511:	e9 3a ff ff ff       	jmp    7450 <sendm+0x1a0>
    7516:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    7520:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    7525:	41 0f 11 00          	movups %xmm0,(%r8)
          for (; them->messages_count < min;) {
    7529:	49 83 c0 10          	add    $0x10,%r8
    752d:	49 39 d8             	cmp    %rbx,%r8
    7530:	75 ae                	jne    74e0 <sendm+0x230>
    7532:	eb be                	jmp    74f2 <sendm+0x242>
    7534:	0f 1f 40 00          	nopl   0x0(%rax)
    7538:	48 8d 34 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rsi
    7540:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    7548:	48 89 74 24 e8       	mov    %rsi,-0x18(%rsp)
    754d:	e9 d4 fe ff ff       	jmp    7426 <sendm+0x176>
    7552:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
}
    7558:	31 c0                	xor    %eax,%eax
    755a:	c3                   	ret
    755b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000007560 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    7560:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    7564:	85 f6                	test   %esi,%esi
    7566:	74 18                	je     7580 <mailboxkind+0x20>
  return NULL;
    7568:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    756a:	83 fe 01             	cmp    $0x1,%esi
    756d:	74 01                	je     7570 <mailboxkind+0x10>
}
    756f:	c3                   	ret
    return mailbox->higher;
    7570:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
}
    7577:	c3                   	ret
    7578:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    return mailbox->lower;
    7580:	48 8b 07             	mov    (%rdi),%rax
    7583:	c3                   	ret
    7584:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    758f:	90                   	nop

0000000000007590 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    7590:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    7594:	85 d2                	test   %edx,%edx
    7596:	75 08                	jne    75a0 <setmailboxkind+0x10>
    mailbox->lower = data;
    7598:	48 89 37             	mov    %rsi,(%rdi)
}
    759b:	31 c0                	xor    %eax,%eax
    759d:	c3                   	ret
    759e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    75a0:	83 fa 01             	cmp    $0x1,%edx
    75a3:	74 13                	je     75b8 <setmailboxkind+0x28>
  if (kind == 2) {
    75a5:	83 fa 02             	cmp    $0x2,%edx
    75a8:	75 1e                	jne    75c8 <setmailboxkind+0x38>
    mailbox->pending_lower = data;
    75aa:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
}
    75b1:	31 c0                	xor    %eax,%eax
    75b3:	c3                   	ret
    75b4:	0f 1f 40 00          	nopl   0x0(%rax)
    mailbox->higher = data;
    75b8:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
}
    75bf:	31 c0                	xor    %eax,%eax
    75c1:	c3                   	ret
    75c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (kind == 3) {
    75c8:	83 fa 03             	cmp    $0x3,%edx
    75cb:	75 ce                	jne    759b <setmailboxkind+0xb>
    mailbox->pending_higher = data;
    75cd:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
}
    75d4:	31 c0                	xor    %eax,%eax
    75d6:	c3                   	ret
    75d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000075e0 <fswap>:
int fswap(struct BarrierTask *data) {
    75e0:	f3 0f 1e fa          	endbr64
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    75e4:	48 8b 8f 28 01 00 00 	mov    0x128(%rdi),%rcx
    75eb:	8b 87 9c 01 00 00    	mov    0x19c(%rdi),%eax
    75f1:	44 8b 97 30 01 00 00 	mov    0x130(%rdi),%r10d
  int t = data->task_index;
    75f8:	48 63 57 04          	movslq 0x4(%rdi),%rdx
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    75fc:	4c 63 99 d4 00 00 00 	movslq 0xd4(%rcx),%r11
    7603:	41 0f af c3          	imul   %r11d,%eax
    7607:	41 01 c2             	add    %eax,%r10d
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    760a:	45 85 db             	test   %r11d,%r11d
    760d:	0f 8e 18 01 00 00    	jle    772b <fswap+0x14b>
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7613:	4d 63 d2             	movslq %r10d,%r10
int fswap(struct BarrierTask *data) {
    7616:	41 56                	push   %r14
    7618:	48 98                	cltq
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    761a:	48 c1 e2 09          	shl    $0x9,%rdx
int fswap(struct BarrierTask *data) {
    761e:	41 55                	push   %r13
    7620:	48 89 c6             	mov    %rax,%rsi
    7623:	49 01 c3             	add    %rax,%r11
    7626:	41 54                	push   %r12
    7628:	48 c1 e6 08          	shl    $0x8,%rsi
    762c:	49 c1 e3 08          	shl    $0x8,%r11
    7630:	55                   	push   %rbp
    7631:	53                   	push   %rbx
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7632:	4c 8b 49 20          	mov    0x20(%rcx),%r9
    7636:	4b 8d 0c d2          	lea    (%r10,%r10,8),%rcx
    763a:	49 8d 0c 4a          	lea    (%r10,%rcx,2),%rcx
        int next_task = abs((t + 1) % (data->thread_count));
    763e:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    7645:	49 c1 e2 08          	shl    $0x8,%r10
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7649:	48 c1 e1 04          	shl    $0x4,%rcx
    764d:	49 8b 5c 09 38       	mov    0x38(%r9,%rcx,1),%rbx
    7652:	48 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%rbp
    765a:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    765e:	48 8d 14 50          	lea    (%rax,%rdx,2),%rdx
    7662:	48 c1 e2 04          	shl    $0x4,%rdx
    7666:	49 01 d1             	add    %rdx,%r9
    7669:	eb 1c                	jmp    7687 <fswap+0xa7>
    766b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    7670:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    7677:	49 81 c1 30 01 00 00 	add    $0x130,%r9
    767e:	49 39 f3             	cmp    %rsi,%r11
    7681:	0f 84 99 00 00 00    	je     7720 <fswap+0x140>
        if (kind == MAILBOX_FRIEND) {
    7687:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    768f:	75 df                	jne    7670 <fswap+0x90>
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    7691:	49 8b 79 38          	mov    0x38(%r9),%rdi
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    7695:	45 85 c0             	test   %r8d,%r8d
    7698:	7e d6                	jle    7670 <fswap+0x90>
    769a:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    76a1:	31 c9                	xor    %ecx,%ecx
    76a3:	eb 58                	jmp    76fd <fswap+0x11d>
    76a5:	0f 1f 00             	nopl   (%rax)
              struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    76a8:	48 63 d2             	movslq %edx,%rdx
    76ab:	48 c1 e2 09          	shl    $0x9,%rdx
    76af:	4c 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%r13
    76b7:	49 01 f5             	add    %rsi,%r13
    76ba:	4c 89 ea             	mov    %r13,%rdx
    return mailbox->lower;
    76bd:	4d 8b 6d 00          	mov    0x0(%r13),%r13
                if (dest->messages_count != 0) { 
    76c1:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    76c9:	75 22                	jne    76ed <fswap+0x10d>
    mailbox->lower = data;
    76cb:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    76d2:	4c 89 32             	mov    %r14,(%rdx)
    76d5:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    mailbox->higher = data;
    76dc:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    mailbox->lower = data;
    76e3:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    76e6:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    76ed:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    76f4:	41 39 c8             	cmp    %ecx,%r8d
    76f7:	0f 84 73 ff ff ff    	je     7670 <fswap+0x90>
              int next_task = abs((nn + 1) % (data->thread_count));
    76fd:	83 c1 01             	add    $0x1,%ecx
    7700:	89 c8                	mov    %ecx,%eax
    7702:	99                   	cltd
    7703:	41 f7 f8             	idiv   %r8d
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7706:	48 8b 07             	mov    (%rdi),%rax
    7709:	4c 01 d0             	add    %r10,%rax
    return mailbox->lower;
    770c:	4c 8b 20             	mov    (%rax),%r12
                if (source2->messages_count != 0) { 
    770f:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    7718:	74 8e                	je     76a8 <fswap+0xc8>
    771a:	e9 51 ff ff ff       	jmp    7670 <fswap+0x90>
    771f:	90                   	nop
}
    7720:	5b                   	pop    %rbx
    7721:	31 c0                	xor    %eax,%eax
    7723:	5d                   	pop    %rbp
    7724:	41 5c                	pop    %r12
    7726:	41 5d                	pop    %r13
    7728:	41 5e                	pop    %r14
    772a:	c3                   	ret
    772b:	31 c0                	xor    %eax,%eax
    772d:	c3                   	ret
    772e:	66 90                	xchg   %ax,%ax

0000000000007730 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    7730:	f3 0f 1e fa          	endbr64
    7734:	41 57                	push   %r15
    7736:	41 56                	push   %r14
    7738:	41 55                	push   %r13
    773a:	41 54                	push   %r12
    773c:	55                   	push   %rbp
    773d:	53                   	push   %rbx
    773e:	48 89 fb             	mov    %rdi,%rbx
    7741:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
  struct timespec preempt = {
    7748:	66 0f 6f 05 b0 26 00 00 	movdqa 0x26b0(%rip),%xmm0        # 9e00 <_IO_stdin_used+0xe00>
int barriered_work(struct BarrierTask *data) {
    7750:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    7759:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    775e:	31 c0                	xor    %eax,%eax
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    7760:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  struct timespec preempt = {
    7767:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    776c:	48 8b 88 00 01 00 00 	mov    0x100(%rax),%rcx
  struct timespec rem = {
    7773:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    7778:	8b 11                	mov    (%rcx),%edx
    777a:	83 fa ff             	cmp    $0xffffffff,%edx
    777d:	0f 84 ed 02 00 00    	je     7a70 <barriered_work+0x340>
    7783:	3b 90 f8 00 00 00    	cmp    0xf8(%rax),%edx
    7789:	74 2d                	je     77b8 <barriered_work+0x88>
}
    778b:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    7790:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    7799:	0f 85 50 05 00 00    	jne    7cef <barriered_work+0x5bf>
    779f:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    77a6:	31 c0                	xor    %eax,%eax
    77a8:	5b                   	pop    %rbx
    77a9:	5d                   	pop    %rbp
    77aa:	41 5c                	pop    %r12
    77ac:	41 5d                	pop    %r13
    77ae:	41 5e                	pop    %r14
    77b0:	41 5f                	pop    %r15
    77b2:	c3                   	ret
    77b3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    77b8:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    77bf:	8b 41 04             	mov    0x4(%rcx),%eax
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    77c2:	85 ed                	test   %ebp,%ebp
    77c4:	0f 85 a6 04 00 00    	jne    7c70 <barriered_work+0x540>
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    77ca:	85 c0                	test   %eax,%eax
    77cc:	0f 84 a6 04 00 00    	je     7c78 <barriered_work+0x548>
    77d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          int t = data->task_index;
    77d8:	44 8b 63 04          	mov    0x4(%rbx),%r12d
      receive(data);
    77dc:	48 89 df             	mov    %rbx,%rdi
    if (data->thread_index == data->task_index) {
    77df:	41 39 ec             	cmp    %ebp,%r12d
    77e2:	0f 85 d0 03 00 00    	jne    7bb8 <barriered_work+0x488>
      receive(data);
    77e8:	e8 73 f9 ff ff       	call   7160 <receive>
        if (data->thread->have_foreign == 1) {
    77ed:	4c 8b bb 28 01 00 00 	mov    0x128(%rbx),%r15
    77f4:	41 83 bf 08 01 00 00 01 	cmpl   $0x1,0x108(%r15)
    77fc:	0f 85 c6 02 00 00    	jne    7ac8 <barriered_work+0x398>
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7802:	44 8b b3 40 01 00 00 	mov    0x140(%rbx),%r14d
    7809:	45 85 f6             	test   %r14d,%r14d
    780c:	0f 8e b6 02 00 00    	jle    7ac8 <barriered_work+0x398>
                int next_task = abs((t + 1) % (data->thread_count));
    7812:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7818:	48 c1 e5 09          	shl    $0x9,%rbp
    781c:	45 31 c0             	xor    %r8d,%r8d
    781f:	31 f6                	xor    %esi,%esi
    7821:	49 89 ed             	mov    %rbp,%r13
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7824:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
                int next_task = abs((t + 1) % (data->thread_count));
    782c:	89 44 24 24          	mov    %eax,0x24(%rsp)
          int b = data->thread->real_thread_index;
    7830:	49 63 47 08          	movslq 0x8(%r15),%rax
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7834:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7839:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
          int b = data->thread->real_thread_index;
    783d:	48 89 c2             	mov    %rax,%rdx
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7840:	48 8d 0c 48          	lea    (%rax,%rcx,2),%rcx
    7844:	48 c1 e0 08          	shl    $0x8,%rax
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7848:	41 89 d3             	mov    %edx,%r11d
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    784b:	48 c1 e1 04          	shl    $0x4,%rcx
    784f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    7854:	48 89 cd             	mov    %rcx,%rbp
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7857:	48 89 d9             	mov    %rbx,%rcx
    785a:	eb 24                	jmp    7880 <barriered_work+0x150>
    785c:	0f 1f 40 00          	nopl   0x0(%rax)
    7860:	83 44 24 0c 01       	addl   $0x1,0xc(%rsp)
    7865:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    7869:	48 81 c6 30 01 00 00 	add    $0x130,%rsi
    7870:	49 81 c0 00 01 00 00 	add    $0x100,%r8
    7877:	44 39 f0             	cmp    %r14d,%eax
    787a:	0f 84 40 02 00 00    	je     7ac0 <barriered_work+0x390>
                if (y == b) { continue; }
    7880:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    7884:	41 39 c3             	cmp    %eax,%r11d
    7887:	74 d7                	je     7860 <barriered_work+0x130>
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7889:	49 8b 57 20          	mov    0x20(%r15),%rdx
    788d:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    7892:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    7896:	44 8b 88 a0 01 00 00 	mov    0x1a0(%rax),%r9d
    789d:	45 85 c9             	test   %r9d,%r9d
    78a0:	75 be                	jne    7860 <barriered_work+0x130>
    78a2:	4c 8b 4c 2a 38       	mov    0x38(%rdx,%rbp,1),%r9
    78a7:	4b 8d 14 29          	lea    (%r9,%r13,1),%rdx
    78ab:	44 8b 92 a0 01 00 00 	mov    0x1a0(%rdx),%r10d
    78b2:	45 85 d2             	test   %r10d,%r10d
    78b5:	75 a9                	jne    7860 <barriered_work+0x130>
    78b7:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    78be:	42 83 bc 02 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r8,1)
    78c7:	75 97                	jne    7860 <barriered_work+0x130>
    78c9:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    78d0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    78d5:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    78dd:	75 81                	jne    7860 <barriered_work+0x130>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    78df:	48 63 44 24 24       	movslq 0x24(%rsp),%rax
    78e4:	85 c0                	test   %eax,%eax
    78e6:	0f 8e 74 ff ff ff    	jle    7860 <barriered_work+0x130>
    78ec:	48 89 c2             	mov    %rax,%rdx
    78ef:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    78f4:	41 bc 70 01 00 00    	mov    $0x170,%r12d
    78fa:	48 c1 e2 09          	shl    $0x9,%rdx
    78fe:	44 89 74 24 3c       	mov    %r14d,0x3c(%rsp)
    7903:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    7908:	48 8d 9a a0 01 00 00 	lea    0x1a0(%rdx),%rbx
    790f:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    7914:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    7919:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    791e:	44 89 5c 24 38       	mov    %r11d,0x38(%rsp)
    7923:	44 8b 5c 24 24       	mov    0x24(%rsp),%r11d
    7928:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                        int next_task = abs((nn + 1) % data->thread_count);
    7930:	41 83 c2 01          	add    $0x1,%r10d
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7934:	4b 8b 34 21          	mov    (%r9,%r12,1),%rsi
                        int next_task = abs((nn + 1) % data->thread_count);
    7938:	44 89 d0             	mov    %r10d,%eax
    793b:	99                   	cltd
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    793c:	4c 01 c6             	add    %r8,%rsi
                        int next_task = abs((nn + 1) % data->thread_count);
    793f:	41 f7 fb             	idiv   %r11d
    return mailbox->lower;
    7942:	4c 8b 36             	mov    (%rsi),%r14
    7945:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    mailbox->lower = data;
    794a:	4c 8b b6 80 00 00 00 	mov    0x80(%rsi),%r14
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    7951:	48 63 d2             	movslq %edx,%rdx
    7954:	48 c1 e2 09          	shl    $0x9,%rdx
    7958:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    7960:	4c 01 e8             	add    %r13,%rax
    return mailbox->lower;
    7963:	4c 8b 38             	mov    (%rax),%r15
    return mailbox->higher;
    7966:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    mailbox->lower = data;
    796d:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    7970:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    7975:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    mailbox->lower = data;
    797c:	48 89 16             	mov    %rdx,(%rsi)
    mailbox->higher = data;
    797f:	4c 89 be 80 00 00 00 	mov    %r15,0x80(%rsi)
    7986:	be a0 01 00 00       	mov    $0x1a0,%esi
    798b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
    7990:	41 c7 04 31 01 00 00 00 	movl   $0x1,(%r9,%rsi,1)
                          data->thread->all_threads[t2].tasks[jj].swap = 1;
    7998:	c7 04 37 01 00 00 00 	movl   $0x1,(%rdi,%rsi,1)
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
    799f:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    79a6:	48 39 de             	cmp    %rbx,%rsi
    79a9:	75 e5                	jne    7990 <barriered_work+0x260>
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    79ab:	4a 8b 34 27          	mov    (%rdi,%r12,1),%rsi
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    79af:	48 8b 00             	mov    (%rax),%rax
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    79b2:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    79bd:	49 81 c4 00 02 00 00 	add    $0x200,%r12
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    79c4:	4a 8b b4 2e 80 00 00 00 	mov    0x80(%rsi,%r13,1),%rsi
    79cc:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
                            ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    79d6:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    79e0:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    79ea:	45 39 d3             	cmp    %r10d,%r11d
    79ed:	0f 85 3d ff ff ff    	jne    7930 <barriered_work+0x200>
    79f3:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    79f8:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    79fd:	b8 70 01 00 00       	mov    $0x170,%eax
    7a02:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    7a07:	44 8b 5c 24 38       	mov    0x38(%rsp),%r11d
    7a0c:	44 8b 74 24 3c       	mov    0x3c(%rsp),%r14d
    7a11:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    7a16:	48 8d 9a 70 01 00 00 	lea    0x170(%rdx),%rbx
    7a1d:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    7a22:	eb 13                	jmp    7a37 <barriered_work+0x307>
    7a24:	0f 1f 40 00          	nopl   0x0(%rax)
                        for (int nn = 0; nn < data->thread_count; nn++) {
    7a28:	48 05 00 02 00 00    	add    $0x200,%rax
    7a2e:	48 39 d8             	cmp    %rbx,%rax
    7a31:	0f 84 29 fe ff ff    	je     7860 <barriered_work+0x130>
                          if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    7a37:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    7a3b:	4d 8b 14 01          	mov    (%r9,%rax,1),%r10
    7a3f:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    7a43:	4b 39 14 02          	cmp    %rdx,(%r10,%r8,1)
    7a47:	75 df                	jne    7a28 <barriered_work+0x2f8>
    7a49:	bf 01 00 00 00       	mov    $0x1,%edi
    7a4e:	48 8d 35 f9 17 00 00 	lea    0x17f9(%rip),%rsi        # 924e <_IO_stdin_used+0x24e>
    7a55:	31 c0                	xor    %eax,%eax
    7a57:	e8 34 aa ff ff       	call   2490 <__printf_chk@plt>
                            exit(1);
    7a5c:	bf 01 00 00 00       	mov    $0x1,%edi
    7a61:	e8 9a aa ff ff       	call   2500 <exit@plt>
    7a66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    7a70:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    7a77:	85 ed                	test   %ebp,%ebp
    7a79:	0f 85 59 fd ff ff    	jne    77d8 <barriered_work+0xa8>
    7a7f:	44 8b 90 f8 00 00 00 	mov    0xf8(%rax),%r10d
    7a86:	45 85 d2             	test   %r10d,%r10d
    7a89:	0f 85 49 fd ff ff    	jne    77d8 <barriered_work+0xa8>
    7a8f:	69 87 80 00 00 00 1d e6 cb 0b 	imul   $0xbcbe61d,0x80(%rdi),%eax
    7a99:	05 40 7c 0a 00       	add    $0xa7c40,%eax
    7a9e:	c1 c8 05             	ror    $0x5,%eax
    7aa1:	3d c4 a7 00 00       	cmp    $0xa7c4,%eax
    7aa6:	0f 87 2c fd ff ff    	ja     77d8 <barriered_work+0xa8>
      data->thread->global->request_group_sync = 0;
    7aac:	48 c7 01 00 00 00 00 	movq   $0x0,(%rcx)
    7ab3:	e9 20 fd ff ff       	jmp    77d8 <barriered_work+0xa8>
    7ab8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    7ac0:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    7ac5:	48 89 cb             	mov    %rcx,%rbx
        fswap(data); 
    7ac8:	48 89 df             	mov    %rbx,%rdi
    7acb:	e8 10 fb ff ff       	call   75e0 <fswap>
        receive(data);
    7ad0:	48 89 df             	mov    %rbx,%rdi
    7ad3:	e8 88 f6 ff ff       	call   7160 <receive>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    7ad8:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    7adf:	31 ff                	xor    %edi,%edi
    7ae1:	48 c1 e6 05          	shl    $0x5,%rsi
    7ae5:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    7aec:	e8 3f a8 ff ff       	call   2330 <clock_gettime@plt>
      int modcount = ++data->thread->protected_state->modcount;
    7af1:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    7af8:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      int modcount = ++data->thread->protected_state->modcount;
    7aff:	48 8b 50 48          	mov    0x48(%rax),%rdx
    7b03:	8b 4a 10             	mov    0x10(%rdx),%ecx
    7b06:	8d 69 01             	lea    0x1(%rcx),%ebp
    7b09:	89 6a 10             	mov    %ebp,0x10(%rdx)
      while (data->scheduled == 1) {
    7b0c:	75 50                	jne    7b5e <barriered_work+0x42e>
    7b0e:	66 90                	xchg   %ax,%ax
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    7b10:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    7b17:	48 8b 40 18          	mov    0x18(%rax),%rax
    7b1b:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
        data->n++;
    7b1f:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    7b27:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7b2b:	48 c1 e7 09          	shl    $0x9,%rdi
    7b2f:	48 03 78 38          	add    0x38(%rax),%rdi
    7b33:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      while (data->scheduled == 1) {
    7b39:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      if (modcount != data->thread->protected_state->modcount) {
    7b40:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    7b47:	74 c7                	je     7b10 <barriered_work+0x3e0>
      if (modcount != data->thread->protected_state->modcount) {
    7b49:	48 8b 40 48          	mov    0x48(%rax),%rax
    7b4d:	3b 68 10             	cmp    0x10(%rax),%ebp
    7b50:	74 0c                	je     7b5e <barriered_work+0x42e>
    7b52:	48 8d 3d 10 17 00 00 	lea    0x1710(%rip),%rdi        # 9269 <_IO_stdin_used+0x269>
    7b59:	e8 b2 a7 ff ff       	call   2310 <puts@plt>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    7b5e:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    7b65:	31 ff                	xor    %edi,%edi
    7b67:	48 c1 e6 05          	shl    $0x5,%rsi
    7b6b:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    7b72:	48 83 c6 10          	add    $0x10,%rsi
    7b76:	e8 b5 a7 ff ff       	call   2330 <clock_gettime@plt>
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    7b7b:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    7b82:	48 83 c0 01          	add    $0x1,%rax
    7b86:	48 99                	cqto
    7b88:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    if (t == data->thread_count - 1) {
    7b8f:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    7b95:	83 e8 01             	sub    $0x1,%eax
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    7b98:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    if (t == data->thread_count - 1) {
    7b9f:	44 39 e0             	cmp    %r12d,%eax
    7ba2:	74 53                	je     7bf7 <barriered_work+0x4c7>
    data->swap = 0;
    7ba4:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    return 0;
    7bae:	e9 d8 fb ff ff       	jmp    778b <barriered_work+0x5b>
    7bb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      receive(data);
    7bb8:	e8 a3 f5 ff ff       	call   7160 <receive>
      while (data->scheduled == 1) {
    7bbd:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    7bc4:	75 1b                	jne    7be1 <barriered_work+0x4b1>
    7bc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        data->n++;
    7bd0:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      while (data->scheduled == 1) {
    7bd8:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    7bdf:	74 ef                	je     7bd0 <barriered_work+0x4a0>
      sendm(data);
    7be1:	48 89 df             	mov    %rbx,%rdi
    7be4:	e8 c7 f6 ff ff       	call   72b0 <sendm>
    if (t == data->thread_count - 1) {
    7be9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    7bef:	83 e8 01             	sub    $0x1,%eax
    7bf2:	44 39 e0             	cmp    %r12d,%eax
    7bf5:	75 ad                	jne    7ba4 <barriered_work+0x474>
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    7bf7:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    7bfe:	85 d2                	test   %edx,%edx
    7c00:	7e a2                	jle    7ba4 <barriered_work+0x474>
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    7c02:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    7c09:	48 c1 e2 09          	shl    $0x9,%rdx
    7c0d:	48 63 41 08          	movslq 0x8(%rcx),%rax
    7c11:	48 8d 34 c0          	lea    (%rax,%rax,8),%rsi
    7c15:	48 8d 04 70          	lea    (%rax,%rsi,2),%rax
    7c19:	48 c1 e0 04          	shl    $0x4,%rax
    7c1d:	48 03 41 20          	add    0x20(%rcx),%rax
    7c21:	48 8b 40 38          	mov    0x38(%rax),%rax
    7c25:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    7c29:	80 e6 02             	and    $0x2,%dh
    7c2c:	74 1a                	je     7c48 <barriered_work+0x518>
    7c2e:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    7c35:	48 05 00 02 00 00    	add    $0x200,%rax
    7c3b:	48 39 c8             	cmp    %rcx,%rax
    7c3e:	0f 84 60 ff ff ff    	je     7ba4 <barriered_work+0x474>
    7c44:	0f 1f 40 00          	nopl   0x0(%rax)
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    7c48:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    7c4f:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    7c56:	48 05 00 04 00 00    	add    $0x400,%rax
    7c5c:	48 39 c8             	cmp    %rcx,%rax
    7c5f:	75 e7                	jne    7c48 <barriered_work+0x518>
    7c61:	e9 3e ff ff ff       	jmp    7ba4 <barriered_work+0x474>
    7c66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    7c70:	39 c5                	cmp    %eax,%ebp
    7c72:	0f 85 60 fb ff ff    	jne    77d8 <barriered_work+0xa8>
      struct ProtectedState *protected = data->thread->global->protected_state;
    7c78:	48 8b 69 08          	mov    0x8(%rcx),%rbp
      nanosleep(&preempt , &rem);
    7c7c:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
    7c81:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
      int modcount = ++protected->modcount;
    7c86:	8b 45 10             	mov    0x10(%rbp),%eax
      protected->protected++;
    7c89:	48 83 45 00 01       	addq   $0x1,0x0(%rbp)
      int modcount = ++protected->modcount;
    7c8e:	44 8d 60 01          	lea    0x1(%rax),%r12d
    7c92:	44 89 65 10          	mov    %r12d,0x10(%rbp)
      nanosleep(&preempt , &rem);
    7c96:	e8 e5 a6 ff ff       	call   2380 <nanosleep@plt>
      if (protected->modcount != modcount) {
    7c9b:	44 3b 65 10          	cmp    0x10(%rbp),%r12d
    7c9f:	74 0c                	je     7cad <barriered_work+0x57d>
    7ca1:	48 8d 3d 89 15 00 00 	lea    0x1589(%rip),%rdi        # 9231 <_IO_stdin_used+0x231>
    7ca8:	e8 63 a6 ff ff       	call   2310 <puts@plt>
      data->thread->global->request_thread_sync = (data->thread_index + 1) % data->thread_count;
    7cad:	48 63 ab 30 01 00 00 	movslq 0x130(%rbx),%rbp
    7cb4:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    7cbb:	8d 45 01             	lea    0x1(%rbp),%eax
    7cbe:	48 8b b1 00 01 00 00 	mov    0x100(%rcx),%rsi
    7cc5:	99                   	cltd
    7cc6:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    7ccc:	89 56 04             	mov    %edx,0x4(%rsi)
      if (data->thread_index == 1) {
    7ccf:	83 fd 01             	cmp    $0x1,%ebp
    7cd2:	0f 85 00 fb ff ff    	jne    77d8 <barriered_work+0xa8>
        data->thread->global->request_group_sync = (data->thread->group + 1) % data->thread->group_count;
    7cd8:	8b 81 f8 00 00 00    	mov    0xf8(%rcx),%eax
    7cde:	83 c0 01             	add    $0x1,%eax
    7ce1:	99                   	cltd
    7ce2:	f7 b9 d0 00 00 00    	idivl  0xd0(%rcx)
    7ce8:	89 16                	mov    %edx,(%rsi)
    7cea:	e9 e9 fa ff ff       	jmp    77d8 <barriered_work+0xa8>
}
    7cef:	e8 6c a6 ff ff       	call   2360 <__stack_chk_fail@plt>
    7cf4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    7cff:	90                   	nop

0000000000007d00 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    7d00:	f3 0f 1e fa          	endbr64
    7d04:	53                   	push   %rbx
    7d05:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    7d08:	e8 53 f3 ff ff       	call   7060 <barriered_work_ingest>
  barriered_work(data);
    7d0d:	48 89 df             	mov    %rbx,%rdi
}
    7d10:	5b                   	pop    %rbx
  barriered_work(data);
    7d11:	e9 1a fa ff ff       	jmp    7730 <barriered_work>
    7d16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000007d20 <barriered_thread>:
void* barriered_thread(void *arg) {
    7d20:	f3 0f 1e fa          	endbr64
    7d24:	41 56                	push   %r14
    7d26:	41 55                	push   %r13
    7d28:	41 54                	push   %r12
  int t = 0;
    7d2a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    7d2d:	55                   	push   %rbp
  int waiting = 0;
    7d2e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    7d30:	53                   	push   %rbx
    7d31:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    7d34:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7d38:	0f 85 7c 02 00 00    	jne    7fba <barriered_thread+0x29a>
    if (t >= data->task_count) {
    7d3e:	8b 43 40             	mov    0x40(%rbx),%eax
    7d41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7d48:	41 39 c4             	cmp    %eax,%r12d
    7d4b:	0f 8d 6f 01 00 00    	jge    7ec0 <barriered_thread+0x1a0>
    7d51:	49 63 fc             	movslq %r12d,%rdi
    7d54:	48 c1 e7 09          	shl    $0x9,%rdi
    7d58:	49 89 fd             	mov    %rdi,%r13
    7d5b:	eb 32                	jmp    7d8f <barriered_thread+0x6f>
    7d5d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    7d60:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    7d64:	48 8b 43 18          	mov    0x18(%rbx),%rax
    7d68:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7d6c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7d70:	4c 01 ef             	add    %r13,%rdi
    7d73:	e8 e8 f2 ff ff       	call   7060 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    7d78:	8b 43 40             	mov    0x40(%rbx),%eax
    7d7b:	41 83 c4 01          	add    $0x1,%r12d
    7d7f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    7d86:	44 39 e0             	cmp    %r12d,%eax
    7d89:	0f 8e 21 02 00 00    	jle    7fb0 <barriered_thread+0x290>
      if (data->tasks[t].available == 1) {
    7d8f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    7d93:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    7d97:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    7d9e:	75 c0                	jne    7d60 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    7da0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    7da4:	83 e8 01             	sub    $0x1,%eax
    7da7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    7dac:	45 85 e4             	test   %r12d,%r12d
    7daf:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    7db2:	45 85 c0             	test   %r8d,%r8d
    7db5:	0f 8e 2d 01 00 00    	jle    7ee8 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    7dbb:	48 63 c8             	movslq %eax,%rcx
    7dbe:	48 8b 43 18          	mov    0x18(%rbx),%rax
    7dc2:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    7dc5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    7dcb:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    7dd2:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    7dd6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    7dd9:	45 31 f6             	xor    %r14d,%r14d
    7ddc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    7de0:	48 8b 10             	mov    (%rax),%rdx
    7de3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    7de7:	49 01 cb             	add    %rcx,%r11
    7dea:	4c 89 da             	mov    %r11,%rdx
    7ded:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    7df4:	75 04                	jne    7dfa <barriered_thread+0xda>
            arrived++;
    7df6:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    7dfa:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    7e00:	75 04                	jne    7e06 <barriered_thread+0xe6>
            prearrive++;
    7e02:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    7e06:	48 83 c0 08          	add    $0x8,%rax
    7e0a:	48 39 c6             	cmp    %rax,%rsi
    7e0d:	75 d1                	jne    7de0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    7e0f:	45 85 d2             	test   %r10d,%r10d
    7e12:	0f 84 c0 00 00 00    	je     7ed8 <barriered_thread+0x1b8>
    7e18:	45 39 d0             	cmp    %r10d,%r8d
    7e1b:	0f 84 b7 00 00 00    	je     7ed8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    7e21:	45 85 f6             	test   %r14d,%r14d
    7e24:	74 0a                	je     7e30 <barriered_thread+0x110>
    7e26:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    7e2a:	0f 85 b6 01 00 00    	jne    7fe6 <barriered_thread+0x2c6>
    7e30:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    7e34:	4c 01 ea             	add    %r13,%rdx
    7e37:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    7e3e:	45 85 e4             	test   %r12d,%r12d
    7e41:	75 14                	jne    7e57 <barriered_thread+0x137>
    7e43:	48 8b b3 90 00 00 00 	mov    0x90(%rbx),%rsi
    7e4a:	48 3b b3 98 00 00 00 	cmp    0x98(%rbx),%rsi
    7e51:	0f 8c 71 01 00 00    	jl     7fc8 <barriered_thread+0x2a8>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    7e57:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    7e5b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    7e5f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    7e69:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    7e6d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7e71:	4c 01 ef             	add    %r13,%rdi
    7e74:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    7e7a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    7e7e:	4c 01 e8             	add    %r13,%rax
    7e81:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7e88:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    7e8b:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7e93:	83 e8 01             	sub    $0x1,%eax
    7e96:	44 39 e0             	cmp    %r12d,%eax
    7e99:	0f 84 a1 00 00 00    	je     7f40 <barriered_thread+0x220>
          if (waiting == 0) {
    7e9f:	85 ed                	test   %ebp,%ebp
    7ea1:	0f 84 d9 00 00 00    	je     7f80 <barriered_thread+0x260>
        int arrived = 0; 
    7ea7:	bd 01 00 00 00       	mov    $0x1,%ebp
    7eac:	e9 c7 fe ff ff       	jmp    7d78 <barriered_thread+0x58>
  while (data->running == 1) {
    7eb1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7eb5:	0f 85 ff 00 00 00    	jne    7fba <barriered_thread+0x29a>
    7ebb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    7ec0:	48 83 83 b8 00 00 00 01 	addq   $0x1,0xb8(%rbx)
    for (; t < data->task_count; t++) {
    7ec8:	85 c0                	test   %eax,%eax
    7eca:	7e e5                	jle    7eb1 <barriered_thread+0x191>
    7ecc:	45 31 e4             	xor    %r12d,%r12d
    7ecf:	e9 7d fe ff ff       	jmp    7d51 <barriered_thread+0x31>
    7ed4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    7ed8:	83 fd 01             	cmp    $0x1,%ebp
    7edb:	74 1b                	je     7ef8 <barriered_thread+0x1d8>
        int arrived = 0; 
    7edd:	31 ed                	xor    %ebp,%ebp
    7edf:	e9 3d ff ff ff       	jmp    7e21 <barriered_thread+0x101>
    7ee4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    7ee8:	83 fd 01             	cmp    $0x1,%ebp
    7eeb:	0f 85 43 ff ff ff    	jne    7e34 <barriered_thread+0x114>
        int arrived = 0; 
    7ef1:	45 31 f6             	xor    %r14d,%r14d
    7ef4:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    7ef8:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    7eff:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    7f04:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    7f06:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    7f0a:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    7f11:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    7f16:	e8 15 a4 ff ff       	call   2330 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    7f1b:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    7f22:	48 83 c0 01          	add    $0x1,%rax
    7f26:	48 99                	cqto
    7f28:	48 f7 bb b0 00 00 00 	idivq  0xb0(%rbx)
    7f2f:	48 89 93 a8 00 00 00 	mov    %rdx,0xa8(%rbx)
            waiting = 0; 
    7f36:	e9 e6 fe ff ff       	jmp    7e21 <barriered_thread+0x101>
    7f3b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7f40:	48 8b b3 90 00 00 00 	mov    0x90(%rbx),%rsi
    7f47:	48 3b b3 98 00 00 00 	cmp    0x98(%rbx),%rsi
    7f4e:	0f 8d 4b ff ff ff    	jge    7e9f <barriered_thread+0x17f>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    7f54:	48 c1 e6 04          	shl    $0x4,%rsi
    7f58:	bf 04 00 00 00       	mov    $0x4,%edi
    7f5d:	48 03 b3 80 00 00 00 	add    0x80(%rbx),%rsi
    7f64:	e8 c7 a3 ff ff       	call   2330 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    7f69:	48 83 83 90 00 00 00 01 	addq   $0x1,0x90(%rbx)
          if (waiting == 0) {
    7f71:	85 ed                	test   %ebp,%ebp
    7f73:	0f 85 2e ff ff ff    	jne    7ea7 <barriered_thread+0x187>
    7f79:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            data->task_snapshot[data->task_timestamp_count].task = t;
    7f80:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    7f87:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    7f8c:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    7f90:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    7f97:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    7f9b:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    7f9f:	e8 8c a3 ff ff       	call   2330 <clock_gettime@plt>
            waiting = 1;
    7fa4:	e9 fe fe ff ff       	jmp    7ea7 <barriered_thread+0x187>
    7fa9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    7fb0:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7fb4:	0f 84 8e fd ff ff    	je     7d48 <barriered_thread+0x28>
}
    7fba:	5b                   	pop    %rbx
    7fbb:	31 c0                	xor    %eax,%eax
    7fbd:	5d                   	pop    %rbp
    7fbe:	41 5c                	pop    %r12
    7fc0:	41 5d                	pop    %r13
    7fc2:	41 5e                	pop    %r14
    7fc4:	c3                   	ret
    7fc5:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    7fc8:	48 c1 e6 04          	shl    $0x4,%rsi
    7fcc:	bf 04 00 00 00       	mov    $0x4,%edi
    7fd1:	48 03 73 78          	add    0x78(%rbx),%rsi
    7fd5:	e8 56 a3 ff ff       	call   2330 <clock_gettime@plt>
          data->tasks[t].available = 0;
    7fda:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    7fde:	4c 01 ea             	add    %r13,%rdx
    7fe1:	e9 71 fe ff ff       	jmp    7e57 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    7fe6:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    7fea:	48 8b 43 18          	mov    0x18(%rbx),%rax
    7fee:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7ff2:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7ff6:	4c 01 ef             	add    %r13,%rdi
    7ff9:	e8 62 f0 ff ff       	call   7060 <barriered_work_ingest>
          break;
    7ffe:	e9 31 fd ff ff       	jmp    7d34 <barriered_thread+0x14>
    8003:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    800e:	66 90                	xchg   %ax,%ax

0000000000008010 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    8010:	f3 0f 1e fa          	endbr64
}
    8014:	31 c0                	xor    %eax,%eax
    8016:	c3                   	ret
    8017:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000008020 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    8020:	f3 0f 1e fa          	endbr64
    8024:	31 c0                	xor    %eax,%eax
    8026:	c3                   	ret
    8027:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000008030 <after>:
int after(struct timespec left, struct timespec right) {
    8030:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    8034:	31 c0                	xor    %eax,%eax
    8036:	48 39 d7             	cmp    %rdx,%rdi
    8039:	7e 08                	jle    8043 <after+0x13>
    803b:	31 c0                	xor    %eax,%eax
    803d:	48 39 ce             	cmp    %rcx,%rsi
    8040:	0f 9f c0             	setg   %al
}
    8043:	c3                   	ret
    8044:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    804f:	90                   	nop

0000000000008050 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    8050:	f3 0f 1e fa          	endbr64
    8054:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    8059:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    805e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8060:	48 39 d7             	cmp    %rdx,%rdi
    8063:	7f 18                	jg     807d <within+0x2d>
    8065:	4d 39 d8             	cmp    %r11,%r8
    8068:	0f 9e c2             	setle  %dl
    806b:	48 39 ce             	cmp    %rcx,%rsi
    806e:	0f 9e c0             	setle  %al
    8071:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8073:	31 c0                	xor    %eax,%eax
    8075:	4d 39 d1             	cmp    %r10,%r9
    8078:	0f 9e c0             	setle  %al
    807b:	21 d0                	and    %edx,%eax
}
    807d:	c3                   	ret
    807e:	66 90                	xchg   %ax,%ax

0000000000008080 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    8080:	f3 0f 1e fa          	endbr64
    8084:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    8089:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    808e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    8093:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    8098:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    809d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    80a2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    80a7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    80ac:	48 39 fe             	cmp    %rdi,%rsi
    80af:	7d 2f                	jge    80e0 <overlap+0x60>
    80b1:	48 39 ca             	cmp    %rcx,%rdx
    80b4:	7d 62                	jge    8118 <overlap+0x98>
    80b6:	4d 39 da             	cmp    %r11,%r10
    80b9:	7d 0e                	jge    80c9 <overlap+0x49>
    return 1;
    80bb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    80c0:	4d 39 c1             	cmp    %r8,%r9
    80c3:	0f 8c 7f 00 00 00    	jl     8148 <overlap+0xc8>
  return 0;
    80c9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    80cb:	4d 39 c1             	cmp    %r8,%r9
    80ce:	7f 4c                	jg     811c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    80d0:	31 c0                	xor    %eax,%eax
    80d2:	4d 39 da             	cmp    %r11,%r10
    80d5:	0f 9e c0             	setle  %al
    80d8:	c3                   	ret
    80d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    80e0:	7e 4e                	jle    8130 <overlap+0xb0>
    80e2:	48 39 ca             	cmp    %rcx,%rdx
    80e5:	7f 39                	jg     8120 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    80e7:	75 31                	jne    811a <overlap+0x9a>
    80e9:	4d 39 c1             	cmp    %r8,%r9
    80ec:	7c 2c                	jl     811a <overlap+0x9a>
    return 1;
    80ee:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    80f3:	4d 39 da             	cmp    %r11,%r10
    80f6:	7d 24                	jge    811c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    80f8:	48 39 ca             	cmp    %rcx,%rdx
    80fb:	0f 94 c2             	sete   %dl
    80fe:	48 39 fe             	cmp    %rdi,%rsi
    8101:	0f 94 c0             	sete   %al
    8104:	21 c2                	and    %eax,%edx
    8106:	31 c0                	xor    %eax,%eax
    8108:	4d 39 c1             	cmp    %r8,%r9
    810b:	0f 94 c0             	sete   %al
    810e:	21 d0                	and    %edx,%eax
    8110:	c3                   	ret
    8111:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    8118:	74 af                	je     80c9 <overlap+0x49>
  return 0;
    811a:	31 c0                	xor    %eax,%eax
}
    811c:	c3                   	ret
    811d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    8120:	4d 39 da             	cmp    %r11,%r10
    8123:	7e c4                	jle    80e9 <overlap+0x69>
    return 1;
    8125:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    812a:	4d 39 c1             	cmp    %r8,%r9
    812d:	7e ba                	jle    80e9 <overlap+0x69>
    812f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8130:	48 39 ca             	cmp    %rcx,%rdx
    8133:	7c 94                	jl     80c9 <overlap+0x49>
    8135:	4d 39 c1             	cmp    %r8,%r9
    8138:	7d b4                	jge    80ee <overlap+0x6e>
    813a:	48 39 ca             	cmp    %rcx,%rdx
    813d:	74 91                	je     80d0 <overlap+0x50>
    813f:	eb d9                	jmp    811a <overlap+0x9a>
    8141:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    8148:	c3                   	ret
    8149:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000008150 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    8150:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    8154:	85 f6                	test   %esi,%esi
    8156:	0f 8e 44 03 00 00    	jle    84a0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    815c:	41 57                	push   %r15
    815e:	41 89 f7             	mov    %esi,%r15d
    8161:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    8163:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    8166:	41 55                	push   %r13
    8168:	41 54                	push   %r12
    816a:	55                   	push   %rbp
    816b:	53                   	push   %rbx
    816c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    8170:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    8174:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    8179:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    817e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    8181:	45 39 e6             	cmp    %r12d,%r14d
    8184:	0f 84 4e 02 00 00    	je     83d8 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    818a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    818f:	8b 50 08             	mov    0x8(%rax),%edx
    8192:	85 d2                	test   %edx,%edx
    8194:	0f 8e 3e 02 00 00    	jle    83d8 <verify+0x288>
    819a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    819f:	31 c9                	xor    %ecx,%ecx
    81a1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    81a6:	31 c0                	xor    %eax,%eax
    81a8:	44 89 f2             	mov    %r14d,%edx
    81ab:	bf 01 00 00 00       	mov    $0x1,%edi
    81b0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    81b5:	48 8d 35 bd 10 00 00 	lea    0x10bd(%rip),%rsi        # 9279 <_IO_stdin_used+0x279>
    81bc:	e8 cf a2 ff ff       	call   2490 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    81c1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    81c6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    81cb:	8b 40 08             	mov    0x8(%rax),%eax
    81ce:	85 c0                	test   %eax,%eax
    81d0:	0f 8e e6 01 00 00    	jle    83bc <verify+0x26c>
    81d6:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    81d9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    81de:	31 db                	xor    %ebx,%ebx
    81e0:	48 c1 e0 09          	shl    $0x9,%rax
    81e4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    81e9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    81ee:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    81f3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    81f8:	4c 8b 20             	mov    (%rax),%r12
    81fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    8200:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    8205:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    820a:	49 89 de             	mov    %rbx,%r14
    820d:	48 8d 35 7a 10 00 00 	lea    0x107a(%rip),%rsi        # 928e <_IO_stdin_used+0x28e>
    8214:	49 c1 e6 09          	shl    $0x9,%r14
    8218:	bf 01 00 00 00       	mov    $0x1,%edi
    821d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    8221:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    8229:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    822e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    8236:	31 c0                	xor    %eax,%eax
    8238:	e8 53 a2 ff ff       	call   2490 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    823d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8242:	4c 8b 20             	mov    (%rax),%r12
    8245:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    824e:	0f 8e 47 01 00 00    	jle    839b <verify+0x24b>
    8254:	4c 03 75 00          	add    0x0(%rbp),%r14
    8258:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    825d:	ba 01 00 00 00       	mov    $0x1,%edx
    8262:	4d 89 f5             	mov    %r14,%r13
    8265:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    826c:	4d 85 f6             	test   %r14,%r14
    826f:	0f 8e 21 01 00 00    	jle    8396 <verify+0x246>
    8275:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    8278:	48 89 d5             	mov    %rdx,%rbp
    827b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8280:	31 db                	xor    %ebx,%ebx
    8282:	4d 89 f2             	mov    %r14,%r10
    8285:	48 c1 e5 05          	shl    $0x5,%rbp
    8289:	48 83 ed 20          	sub    $0x20,%rbp
    828d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    8291:	49 89 ee             	mov    %rbp,%r14
    8294:	48 89 dd             	mov    %rbx,%rbp
    8297:	48 89 d3             	mov    %rdx,%rbx
    829a:	eb 31                	jmp    82cd <verify+0x17d>
    829c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    82a0:	4c 39 c2             	cmp    %r8,%rdx
    82a3:	0f 8d 57 01 00 00    	jge    8400 <verify+0x2b0>
    82a9:	4c 39 df             	cmp    %r11,%rdi
    82ac:	7e 05                	jle    82b3 <verify+0x163>
    82ae:	49 39 c1             	cmp    %rax,%r9
    82b1:	7c 75                	jl     8328 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    82b3:	4c 39 df             	cmp    %r11,%rdi
    82b6:	0f 8d ab 01 00 00    	jge    8467 <verify+0x317>
    82bc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    82c0:	48 83 c5 01          	add    $0x1,%rbp
    82c4:	49 39 ea             	cmp    %rbp,%r10
    82c7:	0f 8e a9 00 00 00    	jle    8376 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    82cd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    82d4:	48 89 e8             	mov    %rbp,%rax
    82d7:	48 c1 e0 05          	shl    $0x5,%rax
    82db:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    82e2:	4c 01 f2             	add    %r14,%rdx
    82e5:	48 8b 08             	mov    (%rax),%rcx
    82e8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    82ec:	48 8b 32             	mov    (%rdx),%rsi
    82ef:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    82f3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    82f7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    82fb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    82ff:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    8303:	48 39 f1             	cmp    %rsi,%rcx
    8306:	7c 98                	jl     82a0 <verify+0x150>
    8308:	0f 8e 42 01 00 00    	jle    8450 <verify+0x300>
    830e:	4c 39 c2             	cmp    %r8,%rdx
    8311:	0f 8f f9 00 00 00    	jg     8410 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8317:	75 a7                	jne    82c0 <verify+0x170>
    8319:	4c 39 df             	cmp    %r11,%rdi
    831c:	7f a2                	jg     82c0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    831e:	49 39 c1             	cmp    %rax,%r9
    8321:	7c 9d                	jl     82c0 <verify+0x170>
    8323:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    8328:	49 89 c1             	mov    %rax,%r9
    832b:	48 89 f9             	mov    %rdi,%rcx
    832e:	48 89 f2             	mov    %rsi,%rdx
    8331:	bf 01 00 00 00       	mov    $0x1,%edi
    8336:	48 8d 35 fb 14 00 00 	lea    0x14fb(%rip),%rsi        # 9838 <_IO_stdin_used+0x838>
    833d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    833f:	48 83 c5 01          	add    $0x1,%rbp
    8343:	e8 48 a1 ff ff       	call   2490 <__printf_chk@plt>
    8348:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    834d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    8352:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8355:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    835a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8361:	4c 8b 20             	mov    (%rax),%r12
    8364:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8369:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    836d:	49 39 ea             	cmp    %rbp,%r10
    8370:	0f 8f 57 ff ff ff    	jg     82cd <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8376:	48 89 da             	mov    %rbx,%rdx
    8379:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    8380:	7d 14                	jge    8396 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8382:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    8389:	48 83 c2 01          	add    $0x1,%rdx
    838d:	4d 85 f6             	test   %r14,%r14
    8390:	0f 8f e2 fe ff ff    	jg     8278 <verify+0x128>
    8396:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    839b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    83a0:	48 83 c3 01          	add    $0x1,%rbx
    83a4:	39 58 08             	cmp    %ebx,0x8(%rax)
    83a7:	0f 8f 53 fe ff ff    	jg     8200 <verify+0xb0>
    83ad:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    83b2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    83b7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    83bc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    83c1:	48 83 c1 01          	add    $0x1,%rcx
    83c5:	39 48 08             	cmp    %ecx,0x8(%rax)
    83c8:	0f 8f d8 fd ff ff    	jg     81a6 <verify+0x56>
    83ce:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    83d3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    83d8:	48 81 44 24 10 30 01 00 00 	addq   $0x130,0x10(%rsp)
    83e1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    83e6:	41 39 c7             	cmp    %eax,%r15d
    83e9:	0f 84 86 00 00 00    	je     8475 <verify+0x325>
    83ef:	41 89 c4             	mov    %eax,%r12d
    83f2:	e9 8a fd ff ff       	jmp    8181 <verify+0x31>
    83f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8400:	0f 85 ba fe ff ff    	jne    82c0 <verify+0x170>
    8406:	e9 a8 fe ff ff       	jmp    82b3 <verify+0x163>
    840b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    8410:	49 39 c1             	cmp    %rax,%r9
    8413:	7e 09                	jle    841e <verify+0x2ce>
    8415:	4c 39 df             	cmp    %r11,%rdi
    8418:	0f 8c 0a ff ff ff    	jl     8328 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    841e:	4c 39 df             	cmp    %r11,%rdi
    8421:	0f 8f 99 fe ff ff    	jg     82c0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8427:	49 39 c1             	cmp    %rax,%r9
    842a:	0f 8d f8 fe ff ff    	jge    8328 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8430:	48 39 f1             	cmp    %rsi,%rcx
    8433:	0f 85 87 fe ff ff    	jne    82c0 <verify+0x170>
    8439:	4c 39 c2             	cmp    %r8,%rdx
    843c:	0f 85 7e fe ff ff    	jne    82c0 <verify+0x170>
    8442:	4c 39 df             	cmp    %r11,%rdi
    8445:	0f 84 dd fe ff ff    	je     8328 <verify+0x1d8>
    844b:	e9 70 fe ff ff       	jmp    82c0 <verify+0x170>
    8450:	4c 39 c2             	cmp    %r8,%rdx
    8453:	0f 8c 5a fe ff ff    	jl     82b3 <verify+0x163>
    8459:	4c 39 df             	cmp    %r11,%rdi
    845c:	7e c9                	jle    8427 <verify+0x2d7>
    845e:	4c 39 c2             	cmp    %r8,%rdx
    8461:	0f 85 59 fe ff ff    	jne    82c0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8467:	49 39 c1             	cmp    %rax,%r9
    846a:	0f 8f 50 fe ff ff    	jg     82c0 <verify+0x170>
    8470:	e9 b3 fe ff ff       	jmp    8328 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    8475:	48 81 44 24 18 30 01 00 00 	addq   $0x130,0x18(%rsp)
    847e:	41 8d 46 01          	lea    0x1(%r14),%eax
    8482:	45 39 e6             	cmp    %r12d,%r14d
    8485:	74 08                	je     848f <verify+0x33f>
    8487:	41 89 c6             	mov    %eax,%r14d
    848a:	e9 ea fc ff ff       	jmp    8179 <verify+0x29>
}
    848f:	48 83 c4 58          	add    $0x58,%rsp
    8493:	31 c0                	xor    %eax,%eax
    8495:	5b                   	pop    %rbx
    8496:	5d                   	pop    %rbp
    8497:	41 5c                	pop    %r12
    8499:	41 5d                	pop    %r13
    849b:	41 5e                	pop    %r14
    849d:	41 5f                	pop    %r15
    849f:	c3                   	ret
    84a0:	31 c0                	xor    %eax,%eax
    84a2:	c3                   	ret

Disassembly of section .fini:

00000000000084a4 <_fini>:
    84a4:	f3 0f 1e fa          	endbr64
    84a8:	48 83 ec 08          	sub    $0x8,%rsp
    84ac:	48 83 c4 08          	add    $0x8,%rsp
    84b0:	c3                   	ret
