
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
    2020:	ff 35 3a 9e 00 00    	push   0x9e3a(%rip)        # be60 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 3c 9e 00 00    	jmp    *0x9e3c(%rip)        # be68 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

0000000000002300 <__cxa_finalize@plt>:
    2300:	f3 0f 1e fa          	endbr64
    2304:	ff 25 ee 9c 00 00    	jmp    *0x9cee(%rip)        # bff8 <__cxa_finalize@GLIBC_2.2.5>
    230a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000002310 <putchar@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 56 9b 00 00    	jmp    *0x9b56(%rip)        # be70 <putchar@GLIBC_2.2.5>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <pthread_setaffinity_np@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 4e 9b 00 00    	jmp    *0x9b4e(%rip)        # be78 <pthread_setaffinity_np@GLIBC_2.34>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <puts@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 46 9b 00 00    	jmp    *0x9b46(%rip)        # be80 <puts@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <setsockopt@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 3e 9b 00 00    	jmp    *0x9b3e(%rip)        # be88 <setsockopt@GLIBC_2.2.5>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <clock_gettime@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 36 9b 00 00    	jmp    *0x9b36(%rip)        # be90 <clock_gettime@GLIBC_2.17>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <fclose@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 2e 9b 00 00    	jmp    *0x9b2e(%rip)        # be98 <fclose@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <strlen@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 26 9b 00 00    	jmp    *0x9b26(%rip)        # bea0 <strlen@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <__stack_chk_fail@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 1e 9b 00 00    	jmp    *0x9b1e(%rip)        # bea8 <__stack_chk_fail@GLIBC_2.4>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <io_uring_submit@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 16 9b 00 00    	jmp    *0x9b16(%rip)        # beb0 <io_uring_submit@LIBURING_2.0>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <nanosleep@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 0e 9b 00 00    	jmp    *0x9b0e(%rip)        # beb8 <nanosleep@GLIBC_2.2.5>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <strrchr@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 06 9b 00 00    	jmp    *0x9b06(%rip)        # bec0 <strrchr@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <fputs@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 fe 9a 00 00    	jmp    *0x9afe(%rip)        # bec8 <fputs@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <close@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 f6 9a 00 00    	jmp    *0x9af6(%rip)        # bed0 <close@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <strtok_r@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 ee 9a 00 00    	jmp    *0x9aee(%rip)        # bed8 <strtok_r@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <read@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 e6 9a 00 00    	jmp    *0x9ae6(%rip)        # bee0 <read@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <calloc@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 de 9a 00 00    	jmp    *0x9ade(%rip)        # bee8 <calloc@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <strcmp@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 d6 9a 00 00    	jmp    *0x9ad6(%rip)        # bef0 <strcmp@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <__memcpy_chk@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 ce 9a 00 00    	jmp    *0x9ace(%rip)        # bef8 <__memcpy_chk@GLIBC_2.3.4>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <stat@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 c6 9a 00 00    	jmp    *0x9ac6(%rip)        # bf00 <stat@GLIBC_2.33>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <memcpy@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 be 9a 00 00    	jmp    *0x9abe(%rip)        # bf08 <memcpy@GLIBC_2.14>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <io_uring_queue_init@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 b6 9a 00 00    	jmp    *0x9ab6(%rip)        # bf10 <io_uring_queue_init@LIBURING_2.0>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <eventfd_write@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 ae 9a 00 00    	jmp    *0x9aae(%rip)        # bf18 <eventfd_write@GLIBC_2.7>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <malloc@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 a6 9a 00 00    	jmp    *0x9aa6(%rip)        # bf20 <malloc@GLIBC_2.2.5>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <listen@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 9e 9a 00 00    	jmp    *0x9a9e(%rip)        # bf28 <listen@GLIBC_2.2.5>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <__strcpy_chk@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 96 9a 00 00    	jmp    *0x9a96(%rip)        # bf30 <__strcpy_chk@GLIBC_2.3.4>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <__io_uring_get_cqe@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 8e 9a 00 00    	jmp    *0x9a8e(%rip)        # bf38 <__io_uring_get_cqe@LIBURING_2.0>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <__printf_chk@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 86 9a 00 00    	jmp    *0x9a86(%rip)        # bf40 <__printf_chk@GLIBC_2.3.4>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <bind@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 7e 9a 00 00    	jmp    *0x9a7e(%rip)        # bf48 <bind@GLIBC_2.2.5>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <pthread_create@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 76 9a 00 00    	jmp    *0x9a76(%rip)        # bf50 <pthread_create@GLIBC_2.34>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <io_uring_wait_cqe_timeout@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 6e 9a 00 00    	jmp    *0x9a6e(%rip)        # bf58 <io_uring_wait_cqe_timeout@LIBURING_2.0>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <open@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 66 9a 00 00    	jmp    *0x9a66(%rip)        # bf60 <open@GLIBC_2.2.5>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <fopen@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 5e 9a 00 00    	jmp    *0x9a5e(%rip)        # bf68 <fopen@GLIBC_2.2.5>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <perror@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 56 9a 00 00    	jmp    *0x9a56(%rip)        # bf70 <perror@GLIBC_2.2.5>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <exit@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 4e 9a 00 00    	jmp    *0x9a4e(%rip)        # bf78 <exit@GLIBC_2.2.5>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <eventfd@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 46 9a 00 00    	jmp    *0x9a46(%rip)        # bf80 <eventfd@GLIBC_2.7>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <fwrite@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 3e 9a 00 00    	jmp    *0x9a3e(%rip)        # bf88 <fwrite@GLIBC_2.2.5>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <__fprintf_chk@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 36 9a 00 00    	jmp    *0x9a36(%rip)        # bf90 <__fprintf_chk@GLIBC_2.3.4>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <io_uring_register_eventfd@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 2e 9a 00 00    	jmp    *0x9a2e(%rip)        # bf98 <io_uring_register_eventfd@LIBURING_2.0>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <pthread_join@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 26 9a 00 00    	jmp    *0x9a26(%rip)        # bfa0 <pthread_join@GLIBC_2.34>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <strerror@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 1e 9a 00 00    	jmp    *0x9a1e(%rip)        # bfa8 <strerror@GLIBC_2.2.5>
    258a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002590 <pthread_mutex_init@plt>:
    2590:	f3 0f 1e fa          	endbr64
    2594:	ff 25 16 9a 00 00    	jmp    *0x9a16(%rip)        # bfb0 <pthread_mutex_init@GLIBC_2.2.5>
    259a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025a0 <epoll_create1@plt>:
    25a0:	f3 0f 1e fa          	endbr64
    25a4:	ff 25 0e 9a 00 00    	jmp    *0x9a0e(%rip)        # bfb8 <epoll_create1@GLIBC_2.9>
    25aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025b0 <__ctype_tolower_loc@plt>:
    25b0:	f3 0f 1e fa          	endbr64
    25b4:	ff 25 06 9a 00 00    	jmp    *0x9a06(%rip)        # bfc0 <__ctype_tolower_loc@GLIBC_2.3>
    25ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025c0 <__sprintf_chk@plt>:
    25c0:	f3 0f 1e fa          	endbr64
    25c4:	ff 25 fe 99 00 00    	jmp    *0x99fe(%rip)        # bfc8 <__sprintf_chk@GLIBC_2.3.4>
    25ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025d0 <socket@plt>:
    25d0:	f3 0f 1e fa          	endbr64
    25d4:	ff 25 f6 99 00 00    	jmp    *0x99f6(%rip)        # bfd0 <socket@GLIBC_2.2.5>
    25da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

00000000000025e0 <fatal_error>:
  return a;
}

int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send);
int buffersend_filter(struct KernelThread *data, struct Buffers *buffers, int kind, void * send, int filter);
void fatal_error(const char *syscall) {
    25e0:	f3 0f 1e fa          	endbr64
    25e4:	50                   	push   %rax
    25e5:	58                   	pop    %rax
    25e6:	50                   	push   %rax
    perror(syscall);
    25e7:	e8 24 ff ff ff       	call   2510 <perror@plt>
    exit(1);
    25ec:	bf 01 00 00 00       	mov    $0x1,%edi
    25f1:	e8 2a ff ff ff       	call   2520 <exit@plt>

00000000000025f6 <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    25f6:	48 8d 3d 2f 6c 00 00 	lea    0x6c2f(%rip),%rdi        # 922c <_IO_stdin_used+0x22c>
    25fd:	e8 de ff ff ff       	call   25e0 <fatal_error>

0000000000002602 <add_read_request.cold>:

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    2602:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    260a:	0f 0b                	ud2

000000000000260c <add_accept_request.cold>:
    260c:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2614:	0f 0b                	ud2

0000000000002616 <io_thread.cold>:
    2616:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    261e:	0f 0b                	ud2
    printf("in send io read my identity %s my ring is %d other io is %d\n", data->identity, data->my_io, data->other_io);
    void * reply;
    
    void * _reply = bufferrecv("waitsocketreply", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET, &reply, 0); 
    struct Buffer *bufferreply = _reply;
    struct NewSocketMessage *msg = bufferreply->data;
    2620:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    2628:	0f 0b                	ud2
    262a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2632:	0f 0b                	ud2
				   perror("new client epoll_create1");
    2634:	48 8d 3d 7e 6b 00 00 	lea    0x6b7e(%rip),%rdi        # 91b9 <_IO_stdin_used+0x1b9>
    263b:	e8 d0 fe ff ff       	call   2510 <perror@plt>
				   exit(EXIT_FAILURE);
    2640:	bf 01 00 00 00       	mov    $0x1,%edi
    2645:	e8 d6 fe ff ff       	call   2520 <exit@plt>
            int client_socket = write->client_socket; 
            // printf("%p write\n", write);
            struct io_uring_sqe *sqe = io_uring_get_sqe(&ring);
            struct Request *req = write->request;
            // printf("req %p\n", req);
            req->event_type = EVENT_TYPE_WRITE;
    264a:	41 c7 06 02 00 00 00 	movl   $0x2,(%r14)
    2651:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2659:	0f 0b                	ud2
    265b:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2663:	0f 0b                	ud2
    2665:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    266d:	0f 0b                	ud2
    266f:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2677:	0f 0b                	ud2
        fatal_error("socket()");
    2679:	48 8d 3d d1 6a 00 00 	lea    0x6ad1(%rip),%rdi        # 9151 <_IO_stdin_used+0x151>
    2680:	e8 5b ff ff ff       	call   25e0 <fatal_error>
        fatal_error("setsockopt(SO_REUSEADDR)");
    2685:	48 8d 3d ce 6a 00 00 	lea    0x6ace(%rip),%rdi        # 915a <_IO_stdin_used+0x15a>
    268c:	e8 4f ff ff ff       	call   25e0 <fatal_error>
        fatal_error("bind()");
    2691:	48 8d 3d db 6a 00 00 	lea    0x6adb(%rip),%rdi        # 9173 <_IO_stdin_used+0x173>
    2698:	e8 43 ff ff ff       	call   25e0 <fatal_error>
      fatal_error("listen()");
    269d:	48 8d 3d d6 6a 00 00 	lea    0x6ad6(%rip),%rdi        # 917a <_IO_stdin_used+0x17a>
    26a4:	e8 37 ff ff ff       	call   25e0 <fatal_error>
    26a9:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26b1:	0f 0b                	ud2
            fatal_error("io_uring_wait_cqe");
    26b3:	48 8d 3d dd 6a 00 00 	lea    0x6add(%rip),%rdi        # 9197 <_IO_stdin_used+0x197>
    26ba:	e8 21 ff ff ff       	call   25e0 <fatal_error>
    26bf:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26c7:	0f 0b                	ud2
    26c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000026d0 <main>:
    }


  return 0;
}
int main() {
    26d0:	f3 0f 1e fa          	endbr64
    26d4:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    26d6:	48 8d 3d 83 71 00 00 	lea    0x7183(%rip),%rdi        # 9860 <_IO_stdin_used+0x860>
    26dd:	41 56                	push   %r14
    26df:	41 55                	push   %r13
    26e1:	4c 8d 2d b7 6c 00 00 	lea    0x6cb7(%rip),%r13        # 939f <_IO_stdin_used+0x39f>
    26e8:	41 54                	push   %r12
    26ea:	55                   	push   %rbp
    26eb:	53                   	push   %rbx
    26ec:	48 81 ec c8 00 00 00 	sub    $0xc8,%rsp
    26f3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    26fc:	48 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%rsp)
    2704:	48 8d 05 f5 1b 00 00 	lea    0x1bf5(%rip),%rax        # 4300 <barriered_reset>
    270b:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2710:	0f 16 2d 39 95 00 00 	movhps 0x9539(%rip),%xmm5        # bc50 <__do_global_dtors_aux_fini_array_entry+0x8>
    2717:	0f 29 6c 24 70       	movaps %xmm5,0x70(%rsp)
    271c:	e8 0f fc ff ff       	call   2330 <puts@plt>
    2721:	bf 0a 00 00 00       	mov    $0xa,%edi
    2726:	e8 e5 fb ff ff       	call   2310 <putchar@plt>
    272b:	ba 01 00 00 00       	mov    $0x1,%edx
    2730:	48 8d 35 60 6b 00 00 	lea    0x6b60(%rip),%rsi        # 9297 <_IO_stdin_used+0x297>
    2737:	31 c0                	xor    %eax,%eax
    2739:	bf 01 00 00 00       	mov    $0x1,%edi
    273e:	e8 6d fd ff ff       	call   24b0 <__printf_chk@plt>
    2743:	ba 02 00 00 00       	mov    $0x2,%edx
    2748:	48 8d 35 58 6b 00 00 	lea    0x6b58(%rip),%rsi        # 92a7 <_IO_stdin_used+0x2a7>
    274f:	31 c0                	xor    %eax,%eax
    2751:	bf 01 00 00 00       	mov    $0x1,%edi
    2756:	e8 55 fd ff ff       	call   24b0 <__printf_chk@plt>
    275b:	ba 01 00 00 00       	mov    $0x1,%edx
    2760:	48 8d 35 55 6b 00 00 	lea    0x6b55(%rip),%rsi        # 92bc <_IO_stdin_used+0x2bc>
    2767:	31 c0                	xor    %eax,%eax
    2769:	bf 01 00 00 00       	mov    $0x1,%edi
    276e:	e8 3d fd ff ff       	call   24b0 <__printf_chk@plt>
    2773:	ba 02 00 00 00       	mov    $0x2,%edx
    2778:	48 8d 35 4d 6b 00 00 	lea    0x6b4d(%rip),%rsi        # 92cc <_IO_stdin_used+0x2cc>
    277f:	31 c0                	xor    %eax,%eax
    2781:	bf 01 00 00 00       	mov    $0x1,%edi
    2786:	e8 25 fd ff ff       	call   24b0 <__printf_chk@plt>
    278b:	48 8d 3d 50 6b 00 00 	lea    0x6b50(%rip),%rdi        # 92e2 <_IO_stdin_used+0x2e2>
    2792:	e8 99 fb ff ff       	call   2330 <puts@plt>
    2797:	ba 02 00 00 00       	mov    $0x2,%edx
    279c:	48 8d 35 5b 6b 00 00 	lea    0x6b5b(%rip),%rsi        # 92fe <_IO_stdin_used+0x2fe>
    27a3:	31 c0                	xor    %eax,%eax
    27a5:	bf 01 00 00 00       	mov    $0x1,%edi
    27aa:	e8 01 fd ff ff       	call   24b0 <__printf_chk@plt>
    27af:	ba 07 00 00 00       	mov    $0x7,%edx
    27b4:	48 8d 35 5d 6b 00 00 	lea    0x6b5d(%rip),%rsi        # 9318 <_IO_stdin_used+0x318>
    27bb:	31 c0                	xor    %eax,%eax
    27bd:	bf 01 00 00 00       	mov    $0x1,%edi
    27c2:	e8 e9 fc ff ff       	call   24b0 <__printf_chk@plt>
    27c7:	ba 02 00 00 00       	mov    $0x2,%edx
    27cc:	48 8d 35 59 6b 00 00 	lea    0x6b59(%rip),%rsi        # 932c <_IO_stdin_used+0x32c>
    27d3:	31 c0                	xor    %eax,%eax
    27d5:	bf 01 00 00 00       	mov    $0x1,%edi
    27da:	e8 d1 fc ff ff       	call   24b0 <__printf_chk@plt>
    27df:	ba 01 00 00 00       	mov    $0x1,%edx
    27e4:	48 8d 35 52 6b 00 00 	lea    0x6b52(%rip),%rsi        # 933d <_IO_stdin_used+0x33d>
    27eb:	31 c0                	xor    %eax,%eax
    27ed:	bf 01 00 00 00       	mov    $0x1,%edi
    27f2:	e8 b9 fc ff ff       	call   24b0 <__printf_chk@plt>
    27f7:	ba 02 00 00 00       	mov    $0x2,%edx
    27fc:	48 8d 35 52 6b 00 00 	lea    0x6b52(%rip),%rsi        # 9355 <_IO_stdin_used+0x355>
    2803:	31 c0                	xor    %eax,%eax
    2805:	bf 01 00 00 00       	mov    $0x1,%edi
    280a:	e8 a1 fc ff ff       	call   24b0 <__printf_chk@plt>
    280f:	ba 01 00 00 00       	mov    $0x1,%edx
    2814:	48 8d 35 ad 70 00 00 	lea    0x70ad(%rip),%rsi        # 98c8 <_IO_stdin_used+0x8c8>
    281b:	31 c0                	xor    %eax,%eax
    281d:	bf 01 00 00 00       	mov    $0x1,%edi
    2822:	e8 89 fc ff ff       	call   24b0 <__printf_chk@plt>
    2827:	ba 01 00 00 00       	mov    $0x1,%edx
    282c:	48 8d 35 c5 70 00 00 	lea    0x70c5(%rip),%rsi        # 98f8 <_IO_stdin_used+0x8f8>
    2833:	31 c0                	xor    %eax,%eax
    2835:	bf 01 00 00 00       	mov    $0x1,%edi
    283a:	e8 71 fc ff ff       	call   24b0 <__printf_chk@plt>
    283f:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2844:	48 8d 35 26 6b 00 00 	lea    0x6b26(%rip),%rsi        # 9371 <_IO_stdin_used+0x371>
    284b:	31 c0                	xor    %eax,%eax
    284d:	bf 01 00 00 00       	mov    $0x1,%edi
    2852:	e8 59 fc ff ff       	call   24b0 <__printf_chk@plt>
    2857:	ba 0a 00 00 00       	mov    $0xa,%edx
    285c:	48 8d 35 28 6b 00 00 	lea    0x6b28(%rip),%rsi        # 938b <_IO_stdin_used+0x38b>
    2863:	31 c0                	xor    %eax,%eax
    2865:	bf 01 00 00 00       	mov    $0x1,%edi
    286a:	e8 41 fc ff ff       	call   24b0 <__printf_chk@plt>
    286f:	48 8d 3d 7f 68 00 00 	lea    0x687f(%rip),%rdi        # 90f5 <_IO_stdin_used+0xf5>
    2876:	e8 b5 fa ff ff       	call   2330 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
    287b:	be 18 00 00 00       	mov    $0x18,%esi
    2880:	bf 01 00 00 00       	mov    $0x1,%edi
    2885:	e8 76 fb ff ff       	call   2400 <calloc@plt>
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    288a:	be 18 00 00 00       	mov    $0x18,%esi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
    288f:	45 31 e4             	xor    %r12d,%r12d
  int cc = 0; 
    2892:	45 31 ff             	xor    %r15d,%r15d
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2895:	bf 01 00 00 00       	mov    $0x1,%edi
  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
    289a:	49 89 c6             	mov    %rax,%r14
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    289d:	e8 5e fb ff ff       	call   2400 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28a2:	be 30 01 00 00       	mov    $0x130,%esi
    28a7:	bf 07 00 00 00       	mov    $0x7,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    28ac:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28b1:	e8 4a fb ff ff       	call   2400 <calloc@plt>
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28b6:	be 28 00 00 00       	mov    $0x28,%esi
    28bb:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28c0:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28c5:	e8 36 fb ff ff       	call   2400 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28ca:	be 28 00 00 00       	mov    $0x28,%esi
    28cf:	bf 31 00 00 00       	mov    $0x31,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28d4:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28dc:	e8 1f fb ff ff       	call   2400 <calloc@plt>
    28e1:	4c 89 34 24          	mov    %r14,(%rsp)
    28e5:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  for (int x = 0 ; x < total_threads; x++) {
    28ed:	49 89 c6             	mov    %rax,%r14
int main() {
    28f0:	4c 89 f5             	mov    %r14,%rbp
    for (int y = 0 ; y < total_threads; y++) {
    28f3:	31 db                	xor    %ebx,%ebx
    28f5:	0f 1f 00             	nopl   (%rax)
    28f8:	42 8d 14 3b          	lea    (%rbx,%r15,1),%edx
    28fc:	41 89 d8             	mov    %ebx,%r8d
    28ff:	44 89 e1             	mov    %r12d,%ecx
    2902:	4c 89 ee             	mov    %r13,%rsi
    2905:	bf 01 00 00 00       	mov    $0x1,%edi
    290a:	31 c0                	xor    %eax,%eax
    290c:	83 c3 01             	add    $0x1,%ebx
    290f:	e8 9c fb ff ff       	call   24b0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    2914:	48 89 ef             	mov    %rbp,%rdi
    2917:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    2919:	48 83 c5 28          	add    $0x28,%rbp
      pthread_mutex_init(&swapmutex[cc++], NULL);
    291d:	e8 6e fc ff ff       	call   2590 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    2922:	83 fb 07             	cmp    $0x7,%ebx
    2925:	75 d1                	jne    28f8 <main+0x228>
    2927:	41 83 c7 07          	add    $0x7,%r15d
  for (int x = 0 ; x < total_threads; x++) {
    292b:	41 83 c4 01          	add    $0x1,%r12d
    292f:	49 81 c6 18 01 00 00 	add    $0x118,%r14
    2936:	41 83 ff 31          	cmp    $0x31,%r15d
    293a:	75 b4                	jne    28f0 <main+0x220>
    293c:	ba 02 00 00 00       	mov    $0x2,%edx
    2941:	bf 01 00 00 00       	mov    $0x1,%edi
    2946:	31 c0                	xor    %eax,%eax
    2948:	4c 8b 34 24          	mov    (%rsp),%r14
    294c:	48 8d 35 5c 6a 00 00 	lea    0x6a5c(%rip),%rsi        # 93af <_IO_stdin_used+0x3af>
    2953:	e8 58 fb ff ff       	call   24b0 <__printf_chk@plt>
    2958:	ba 04 00 00 00       	mov    $0x4,%edx
    295d:	48 8d 35 61 6a 00 00 	lea    0x6a61(%rip),%rsi        # 93c5 <_IO_stdin_used+0x3c5>
    2964:	31 c0                	xor    %eax,%eax
    2966:	bf 01 00 00 00       	mov    $0x1,%edi
    296b:	e8 40 fb ff ff       	call   24b0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2970:	be 10 00 00 00       	mov    $0x10,%esi
    2975:	bf 04 00 00 00       	mov    $0x4,%edi
    297a:	e8 81 fa ff ff       	call   2400 <calloc@plt>
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    297f:	be 10 00 00 00       	mov    $0x10,%esi
    2984:	bf 02 00 00 00       	mov    $0x2,%edi
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2989:	49 89 c7             	mov    %rax,%r15
    298c:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2991:	e8 6a fa ff ff       	call   2400 <calloc@plt>


  int snapshot_limit = 100;
  for (int x = 0 ; x < io_threads; x++) {
    iobuffers[x].count = buffer_size;
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2996:	be 28 00 00 00       	mov    $0x28,%esi
    299b:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int y = 0 ; y < buffer_size; y++) {
      iobuffers[x].buffer[y].available = 0;
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29a0:	4d 89 fd             	mov    %r15,%r13
    iobuffers[x].count = buffer_size;
    29a3:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    29a9:	48 89 c3             	mov    %rax,%rbx
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29ac:	e8 4f fa ff ff       	call   2400 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29b1:	be 20 00 00 00       	mov    $0x20,%esi
    29b6:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29bb:	48 89 43 08          	mov    %rax,0x8(%rbx)
    29bf:	49 89 c4             	mov    %rax,%r12
      iobuffers[x].buffer[y].available = 0;
    29c2:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    29c9:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29d0:	e8 2b fa ff ff       	call   2400 <calloc@plt>
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29d5:	be 28 00 00 00       	mov    $0x28,%esi
    29da:	bf 01 00 00 00       	mov    $0x1,%edi
    iobuffers[x].count = buffer_size;
    29df:	c7 43 10 01 00 00 00 	movl   $0x1,0x10(%rbx)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29e6:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29eb:	e8 10 fa ff ff       	call   2400 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29f0:	be 20 00 00 00       	mov    $0x20,%esi
    29f5:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29fa:	48 89 43 18          	mov    %rax,0x18(%rbx)
    29fe:	49 89 c4             	mov    %rax,%r12
    2a01:	49 8d 5f 40          	lea    0x40(%r15),%rbx
      iobuffers[x].buffer[y].available = 0;
    2a05:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2a0c:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a13:	e8 e8 f9 ff ff       	call   2400 <calloc@plt>
    2a18:	4c 89 bc 24 80 00 00 00 	mov    %r15,0x80(%rsp)
    2a20:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    }
  }
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a25:	be 28 00 00 00       	mov    $0x28,%esi
    buffers[x].count = buffer_size;
    2a2a:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a32:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2a37:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a3b:	e8 c0 f9 ff ff       	call   2400 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a40:	be 20 00 00 00       	mov    $0x20,%esi
    2a45:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a4a:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    2a4e:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    2a51:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2a58:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a5f:	e8 9c f9 ff ff       	call   2400 <calloc@plt>
    2a64:	48 89 45 10          	mov    %rax,0x10(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    2a68:	49 39 dd             	cmp    %rbx,%r13
    2a6b:	75 b8                	jne    2a25 <main+0x355>
  int iocur_buffer = 0;
  int swap = 0;
  int groupcount = 0;
  int seq = 0;
  int seqs[] = {1, 3, 6};
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a6d:	be 08 00 00 00       	mov    $0x8,%esi
    2a72:	bf 64 00 00 00       	mov    $0x64,%edi
    2a77:	e8 84 f9 ff ff       	call   2400 <calloc@plt>
  struct Global *global = calloc(1, sizeof(struct Global));
    2a7c:	be 10 00 00 00       	mov    $0x10,%esi
    2a81:	bf 01 00 00 00       	mov    $0x1,%edi
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a86:	48 89 c3             	mov    %rax,%rbx
    2a89:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  struct Global *global = calloc(1, sizeof(struct Global));
    2a91:	e8 6a f9 ff ff       	call   2400 <calloc@plt>
  global->request_group_sync = -1;
  global->protected_state = global_protected_state;
  for (int k = 0 ; k < group_count ; k++) {
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2a96:	be 00 01 00 00       	mov    $0x100,%esi
    2a9b:	bf 01 00 00 00       	mov    $0x1,%edi
  global->request_group_sync = -1;
    2aa0:	c7 00 ff ff ff ff    	movl   $0xffffffff,(%rax)
  global->protected_state = global_protected_state;
    2aa6:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2aaa:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2aaf:	e8 4c f9 ff ff       	call   2400 <calloc@plt>
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2ab4:	be 08 00 00 00       	mov    $0x8,%esi
    2ab9:	bf 64 00 00 00       	mov    $0x64,%edi
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2abe:	48 89 04 24          	mov    %rax,(%rsp)
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2ac2:	e8 39 f9 ff ff       	call   2400 <calloc@plt>
    all_groups[groupcount++] = group_data;
    2ac7:	48 8b 14 24          	mov    (%rsp),%rdx
    group_data->thread_count = threads_per_group * group_count;
    group_data->threads = group_threads;
    group_data->global = global;
    2acb:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    group_data->seq = seqs[seq++ % 3];
    2ad0:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    2ad9:	48 8b 6c 24 68       	mov    0x68(%rsp),%rbp
    2ade:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    2ae3:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
    group_data->thread_count = threads_per_group * group_count;
    2aeb:	c7 82 90 00 00 00 02 00 00 00 	movl   $0x2,0x90(%rdx)
    group_data->threads = group_threads;
    2af5:	48 89 82 88 00 00 00 	mov    %rax,0x88(%rdx)
    group_data->global = global;
    2afc:	4c 89 8a 98 00 00 00 	mov    %r9,0x98(%rdx)
    group_data->seq = seqs[seq++ % 3];
    2b03:	c7 82 a0 00 00 00 01 00 00 00 	movl   $0x1,0xa0(%rdx)
    2b0d:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    2b15:	48 89 6c 24 58       	mov    %rbp,0x58(%rsp)
    2b1a:	4c 89 8c 24 a0 00 00 00 	mov    %r9,0xa0(%rsp)
    2b22:	48 89 94 24 a8 00 00 00 	mov    %rdx,0xa8(%rsp)
    all_groups[groupcount++] = group_data;
    2b2a:	48 89 13             	mov    %rdx,(%rbx)
    int group_thread_count = 0;
    for (int d = 0 ; d < threads_per_group ; d++) {
    2b2d:	4c 89 d3             	mov    %r10,%rbx
      int x = (k * threads_per_group) + d;
      thread_data[x].group_data = group_data;
      thread_data[x].all_groups = all_groups;
    2b30:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    2b38:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
      thread_data[x].group = k;
    2b3d:	c7 83 f8 00 00 00 00 00 00 00 	movl   $0x0,0xf8(%rbx)
    2b47:	31 d2                	xor    %edx,%edx
      thread_data[x].group_data = group_data;
    2b49:	48 8b ac 24 a8 00 00 00 	mov    0xa8(%rsp),%rbp
    2b51:	48 8d 35 c8 6d 00 00 	lea    0x6dc8(%rip),%rsi        # 9920 <_IO_stdin_used+0x920>
    2b58:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].all_groups = all_groups;
    2b5d:	48 89 83 f0 00 00 00 	mov    %rax,0xf0(%rbx)
    2b64:	44 89 f1             	mov    %r14d,%ecx
    2b67:	47 8d 24 36          	lea    (%r14,%r14,1),%r12d
    2b6b:	45 89 f7             	mov    %r14d,%r15d
      thread_data[x].global = global;
    2b6e:	48 8b 84 24 a0 00 00 00 	mov    0xa0(%rsp),%rax
      thread_data[x].group_data = group_data;
    2b76:	48 89 ab e8 00 00 00 	mov    %rbp,0xe8(%rbx)
      thread_data[x].global = global;
    2b7d:	48 89 83 00 01 00 00 	mov    %rax,0x100(%rbx)
    2b84:	31 c0                	xor    %eax,%eax
    2b86:	e8 25 f9 ff ff       	call   24b0 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2b8b:	be 08 00 00 00       	mov    $0x8,%esi
    2b90:	bf 02 00 00 00       	mov    $0x2,%edi
    2b95:	e8 66 f8 ff ff       	call   2400 <calloc@plt>
      
      group_data->threads[group_thread_count++] = &thread_data[x];  

      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2b9a:	be 80 00 00 00       	mov    $0x80,%esi
    2b9f:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2ba4:	49 89 c5             	mov    %rax,%r13
      group_data->threads[group_thread_count++] = &thread_data[x];  
    2ba7:	48 8b 85 88 00 00 00 	mov    0x88(%rbp),%rax
    2bae:	4c 89 f5             	mov    %r14,%rbp
    2bb1:	4a 89 1c f0          	mov    %rbx,(%rax,%r14,8)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2bb5:	e8 46 f8 ff ff       	call   2400 <calloc@plt>
    2bba:	49 89 c6             	mov    %rax,%r14
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2bbd:	48 85 ed             	test   %rbp,%rbp
    2bc0:	0f 84 ae 0e 00 00    	je     3a74 <main+0x13a4>
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2bc6:	49 8d 45 08          	lea    0x8(%r13),%rax
    2bca:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    2bcf:	41 b8 01 00 00 00    	mov    $0x1,%r8d
        other = abs(x - 1) % total_threads;
    2bd5:	31 ed                	xor    %ebp,%ebp
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2bd7:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
    2bdc:	48 89 d8             	mov    %rbx,%rax
        my_thread_data[1] = &thread_data[x]; 
    2bdf:	49 89 45 08          	mov    %rax,0x8(%r13)
        thread_data[x].protected_state = &protected_state[k];
    2be3:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    2be8:	89 e9                	mov    %ebp,%ecx
    2bea:	48 8d 35 5f 6d 00 00 	lea    0x6d5f(%rip),%rsi        # 9950 <_IO_stdin_used+0x950>
        thread_data[x].thread_index = 1;
    2bf1:	44 89 43 04          	mov    %r8d,0x4(%rbx)
    2bf5:	bf 01 00 00 00       	mov    $0x1,%edi
        my_thread_data[0] = &thread_data[other]; 
    2bfa:	49 89 55 00          	mov    %rdx,0x0(%r13)
    2bfe:	44 89 fa             	mov    %r15d,%edx
        thread_data[x].protected_state = &protected_state[k];
    2c01:	48 89 43 48          	mov    %rax,0x48(%rbx)
    2c05:	31 c0                	xor    %eax,%eax
    2c07:	e8 a4 f8 ff ff       	call   24b0 <__printf_chk@plt>
      thread_data[x].other = other;
    2c0c:	89 ab c8 00 00 00    	mov    %ebp,0xc8(%rbx)
    2c12:	44 89 fa             	mov    %r15d,%edx
    2c15:	31 c0                	xor    %eax,%eax
    2c17:	44 89 e1             	mov    %r12d,%ecx
    2c1a:	48 8d 35 5f 6d 00 00 	lea    0x6d5f(%rip),%rsi        # 9980 <_IO_stdin_used+0x980>
    2c21:	bf 01 00 00 00       	mov    $0x1,%edi
    2c26:	e8 85 f8 ff ff       	call   24b0 <__printf_chk@plt>
          CPU_SET(curcpu, sendercpu);
    2c2b:	44 89 e1             	mov    %r12d,%ecx
    2c2e:	b8 01 00 00 00       	mov    $0x1,%eax
      thread_data[x].cpu_set = sendercpu;
    2c33:	4c 89 b3 c0 00 00 00 	mov    %r14,0xc0(%rbx)
          CPU_SET(curcpu, sendercpu);
    2c3a:	48 d3 e0             	shl    %cl,%rax
    2c3d:	49 09 06             	or     %rax,(%r14)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2c40:	be 10 00 00 00       	mov    $0x10,%esi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2c45:	49 89 de             	mov    %rbx,%r14
      thread_data[x].swapmutex = swapmutex;
    2c48:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2c50:	4c 89 6b 18          	mov    %r13,0x18(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2c54:	bf 64 00 00 00       	mov    $0x64,%edi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2c59:	45 31 ed             	xor    %r13d,%r13d
      thread_data[x].kind = KERNEL_THREAD;
    2c5c:	c7 03 5f 00 00 00    	movl   $0x5f,(%rbx)
      thread_data[x].swapmutex = swapmutex;
    2c62:	48 89 83 d8 00 00 00 	mov    %rax,0xd8(%rbx)
      thread_data[x].mswapmutex = mswapmutex;
    2c69:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
      thread_data[x].real_thread_index = x;
    2c71:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
      thread_data[x].mswapmutex = mswapmutex;
    2c75:	48 89 83 e0 00 00 00 	mov    %rax,0xe0(%rbx)
      thread_data[x].all_threads = thread_data;
    2c7c:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
      thread_data[x].task_count = total_barrier_count;
    2c81:	c7 43 40 03 00 00 00 	movl   $0x3,0x40(%rbx)
      thread_data[x].all_threads = thread_data;
    2c88:	48 89 43 20          	mov    %rax,0x20(%rbx)
      thread_data[x].group_count = group_count;
    2c8c:	48 8b 05 7d 72 00 00 	mov    0x727d(%rip),%rax        # 9f10 <_IO_stdin_used+0xf10>
    2c93:	48 89 83 d0 00 00 00 	mov    %rax,0xd0(%rbx)
      thread_data[x].thread_count = 2;
    2c9a:	48 8b 05 77 72 00 00 	mov    0x7277(%rip),%rax        # 9f18 <_IO_stdin_used+0xf18>
    2ca1:	48 89 43 28          	mov    %rax,0x28(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2ca5:	e8 56 f7 ff ff       	call   2400 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2caa:	be 10 00 00 00       	mov    $0x10,%esi
    2caf:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2cb4:	48 89 43 78          	mov    %rax,0x78(%rbx)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2cb8:	e8 43 f7 ff ff       	call   2400 <calloc@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2cbd:	be 28 00 00 00       	mov    $0x28,%esi
    2cc2:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
    2cc7:	66 0f 6f 3d 11 72 00 00 	movdqa 0x7211(%rip),%xmm7        # 9ee0 <_IO_stdin_used+0xee0>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2ccf:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
      thread_data[x].timestamp_count = 0;
    2cd6:	0f 11 bb 90 00 00 00 	movups %xmm7,0x90(%rbx)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2cdd:	e8 1e f7 ff ff       	call   2400 <calloc@plt>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2ce2:	be 00 02 00 00       	mov    $0x200,%esi
    2ce7:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2cec:	66 0f 6f 3d ec 71 00 00 	movdqa 0x71ec(%rip),%xmm7        # 9ee0 <_IO_stdin_used+0xee0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2cf4:	48 89 83 a0 00 00 00 	mov    %rax,0xa0(%rbx)
      thread_data[x].task_timestamp_count = 0;
    2cfb:	0f 11 bb a8 00 00 00 	movups %xmm7,0xa8(%rbx)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2d02:	e8 f9 f6 ff ff       	call   2400 <calloc@plt>
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2d07:	44 89 7c 24 08       	mov    %r15d,0x8(%rsp)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2d0c:	48 89 c5             	mov    %rax,%rbp
        thread_data[x].tasks = barriers;
    2d0f:	48 89 43 38          	mov    %rax,0x38(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2d13:	44 89 f8             	mov    %r15d,%eax
    2d16:	83 f0 01             	xor    $0x1,%eax
    2d19:	48 89 ea             	mov    %rbp,%rdx
    2d1c:	89 44 24 10          	mov    %eax,0x10(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2d20:	49 63 c5             	movslq %r13d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2d23:	be 00 01 00 00       	mov    $0x100,%esi
    2d28:	bf 02 00 00 00       	mov    $0x2,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d2d:	31 db                	xor    %ebx,%ebx
          thread_data[x].tasks[y].protected = do_protected_write; 
    2d2f:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2d34:	48 c1 e0 09          	shl    $0x9,%rax
    2d38:	48 8d 2c 02          	lea    (%rdx,%rax,1),%rbp
    2d3c:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2d41:	48 8d 05 78 15 00 00 	lea    0x1578(%rip),%rax        # 42c0 <do_protected_write>
    2d48:	48 89 85 20 01 00 00 	mov    %rax,0x120(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2d4f:	e8 ac f6 ff ff       	call   2400 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2d54:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    2d59:	4c 89 74 24 48       	mov    %r14,0x48(%rsp)
    2d5e:	41 89 de             	mov    %ebx,%r14d
    2d61:	48 89 85 70 01 00 00 	mov    %rax,0x170(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2d68:	49 89 c4             	mov    %rax,%r12
    2d6b:	31 c9                	xor    %ecx,%ecx
    2d6d:	44 89 f2             	mov    %r14d,%edx
    2d70:	48 8d 35 68 66 00 00 	lea    0x6668(%rip),%rsi        # 93df <_IO_stdin_used+0x3df>
    2d77:	31 c0                	xor    %eax,%eax
    2d79:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d7e:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    2d85:	e8 26 f7 ff ff       	call   24b0 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d8a:	be 08 00 00 00       	mov    $0x8,%esi
    2d8f:	bf 01 00 00 00       	mov    $0x1,%edi
    2d94:	e8 67 f6 ff ff       	call   2400 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d99:	be 08 00 00 00       	mov    $0x8,%esi
    2d9e:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2da3:	48 89 04 24          	mov    %rax,(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2da7:	e8 54 f6 ff ff       	call   2400 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2dac:	be 80 04 00 00       	mov    $0x480,%esi
    2db1:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2db6:	48 89 c3             	mov    %rax,%rbx
              struct Data *data = calloc(3, sizeof(struct Data));
    2db9:	e8 42 f6 ff ff       	call   2400 <calloc@plt>
              data[0].a = x;
    2dbe:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    2dc2:	44 89 f2             	mov    %r14d,%edx
              mailboxes[b].pending_lower = NULL;
    2dc5:	49 c7 44 24 88 00 00 00 00 	movq   $0x0,-0x78(%r12)
              struct Data *data = calloc(3, sizeof(struct Data));
    2dce:	48 89 c5             	mov    %rax,%rbp
              data[0].b = y;
    2dd1:	44 89 a8 10 04 00 00 	mov    %r13d,0x410(%rax)
    2dd8:	48 8d 35 c1 6b 00 00 	lea    0x6bc1(%rip),%rsi        # 99a0 <_IO_stdin_used+0x9a0>
              data[0].a = x;
    2ddf:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
              data[0].kind = MAILBOX_LOWER;
    2de5:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
              data[0].c = b;
    2def:	44 89 b0 14 04 00 00 	mov    %r14d,0x414(%rax)
              data[0].id = dataid++;
    2df6:	41 8d 47 01          	lea    0x1(%r15),%eax
              data[1].id = dataid++;
    2dfa:	89 85 98 08 00 00    	mov    %eax,0x898(%rbp)
              mailboxes[b].higher = &data[1];
    2e00:	48 8d 85 80 04 00 00 	lea    0x480(%rbp),%rax
    2e07:	49 89 44 24 80       	mov    %rax,-0x80(%r12)
    2e0c:	8b 44 24 10          	mov    0x10(%rsp),%eax
              data[0].id = dataid++;
    2e10:	44 89 bd 18 04 00 00 	mov    %r15d,0x418(%rbp)
              data[1].id = dataid++;
    2e17:	41 83 c7 02          	add    $0x2,%r15d
    2e1b:	41 89 44 24 b4       	mov    %eax,-0x4c(%r12)
    2e20:	89 c1                	mov    %eax,%ecx
    2e22:	31 c0                	xor    %eax,%eax
              data[1].a = x;
    2e24:	89 bd 8c 08 00 00    	mov    %edi,0x88c(%rbp)
    2e2a:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].lower = &data[0];
    2e2f:	49 89 ac 24 00 ff ff ff 	mov    %rbp,-0x100(%r12)
              mailboxes[b].pending_higher = NULL;
    2e37:	49 c7 44 24 90 00 00 00 00 	movq   $0x0,-0x70(%r12)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2e40:	41 c7 44 24 b0 01 00 00 00 	movl   $0x1,-0x50(%r12)
              data[1].kind = MAILBOX_HIGHER;
    2e49:	c7 85 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%rbp)
              data[1].b = y;
    2e53:	44 89 ad 90 08 00 00 	mov    %r13d,0x890(%rbp)
              data[1].c = b;
    2e5a:	44 89 b5 94 08 00 00 	mov    %r14d,0x894(%rbp)
              data[0].finished_reading = 1;
    2e61:	c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rbp)
              data[1].finished_reading = 1;
    2e6b:	c7 85 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%rbp)
    2e75:	e8 36 f6 ff ff       	call   24b0 <__printf_chk@plt>
              data[0].messages = messages;
    2e7a:	4c 8b 14 24          	mov    (%rsp),%r10
              data[0].messages_count = 0;
    2e7e:	66 0f 6f 15 6a 70 00 00 	movdqa 0x706a(%rip),%xmm2        # 9ef0 <_IO_stdin_used+0xef0>
              data[1].messages = messages2;
    2e86:	48 89 9d 80 04 00 00 	mov    %rbx,0x480(%rbp)
              data[0].messages = messages;
    2e8d:	4c 89 55 00          	mov    %r10,0x0(%rbp)
              data[0].messages_count = 0;
    2e91:	0f 29 95 80 00 00 00 	movaps %xmm2,0x80(%rbp)
              data[1].messages_count = 0;
    2e98:	0f 29 95 00 05 00 00 	movaps %xmm2,0x500(%rbp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e9f:	45 85 f6             	test   %r14d,%r14d
    2ea2:	75 0b                	jne    2eaf <main+0x7df>
    2ea4:	41 be 01 00 00 00    	mov    $0x1,%r14d
    2eaa:	e9 bc fe ff ff       	jmp    2d6b <main+0x69b>
          char *message = malloc(sizeof(char) * 256);
    2eaf:	be 01 00 00 00       	mov    $0x1,%esi
    2eb4:	bf 00 01 00 00       	mov    $0x100,%edi
    2eb9:	83 44 24 28 04       	addl   $0x4,0x28(%rsp)
    2ebe:	44 89 f3             	mov    %r14d,%ebx
    2ec1:	4c 8b 74 24 48       	mov    0x48(%rsp),%r14
    2ec6:	e8 35 f5 ff ff       	call   2400 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2ecb:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2ed0:	48 89 c5             	mov    %rax,%rbp
          struct Message *messaged = malloc(sizeof(struct Message));
    2ed3:	e8 98 f5 ff ff       	call   2470 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2ed8:	48 83 ec 08          	sub    $0x8,%rsp
    2edc:	48 89 ef             	mov    %rbp,%rdi
    2edf:	45 89 e9             	mov    %r13d,%r9d
    2ee2:	6a 00                	push   $0x0
    2ee4:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
    2ee9:	49 89 c4             	mov    %rax,%r12
    2eec:	ba 00 01 00 00       	mov    $0x100,%edx
    2ef1:	48 8d 0d d0 6a 00 00 	lea    0x6ad0(%rip),%rcx        # 99c8 <_IO_stdin_used+0x9c8>
    2ef8:	be 01 00 00 00       	mov    $0x1,%esi
    2efd:	31 c0                	xor    %eax,%eax
    2eff:	e8 bc f6 ff ff       	call   25c0 <__sprintf_chk@plt>
          messaged->task_index = y;
    2f04:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
          thread_data[x].tasks[y].swap = swap;
    2f09:	49 8b 56 38          	mov    0x38(%r14),%rdx
          messaged->message = message;
    2f0d:	49 89 2c 24          	mov    %rbp,(%r12)
          thread_data[x].tasks[y].swap = swap;
    2f11:	48 8b 6c 24 48       	mov    0x48(%rsp),%rbp
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f16:	be 20 00 00 00       	mov    $0x20,%esi
    2f1b:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->group = k;
    2f20:	41 c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%r12)
          messaged->task_index = y;
    2f29:	49 89 44 24 10       	mov    %rax,0x10(%r12)
          messaged->thread_index = thread_data[x].real_thread_index;
    2f2e:	49 63 46 08          	movslq 0x8(%r14),%rax
          thread_data[x].tasks[y].swap = swap;
    2f32:	48 01 d5             	add    %rdx,%rbp
    2f35:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
          messaged->thread_index = thread_data[x].real_thread_index;
    2f3a:	49 89 44 24 08       	mov    %rax,0x8(%r12)
          thread_data[x].tasks[y].swap = swap;
    2f3f:	8b 44 24 28          	mov    0x28(%rsp),%eax
          thread_data[x].tasks[y].group = k;
    2f43:	c7 85 9c 01 00 00 00 00 00 00 	movl   $0x0,0x19c(%rbp)
          thread_data[x].tasks[y].swap = swap;
    2f4d:	89 85 a0 01 00 00    	mov    %eax,0x1a0(%rbp)
          swap += 1;
    2f53:	83 c0 01             	add    $0x1,%eax
    2f56:	89 44 24 28          	mov    %eax,0x28(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2f5a:	41 8d 45 01          	lea    0x1(%r13),%eax
    2f5e:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2f61:	c7 45 00 41 00 00 00 	movl   $0x41,0x0(%rbp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2f68:	89 85 98 01 00 00    	mov    %eax,0x198(%rbp)
          thread_data[x].tasks[y].message = messaged;
    2f6e:	4c 89 a5 90 01 00 00 	mov    %r12,0x190(%rbp)
          thread_data[x].tasks[y].sending = 1;
    2f75:	c7 85 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbp)
          thread_data[x].tasks[y].snapshot_count = 99;
    2f7f:	48 c7 85 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f8a:	e8 71 f4 ff ff       	call   2400 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2f8f:	48 c7 85 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f9a:	48 89 85 50 01 00 00 	mov    %rax,0x150(%rbp)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2fa1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    2fa6:	48 8b 00             	mov    (%rax),%rax
    2fa9:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2fac:	49 39 c6             	cmp    %rax,%r14
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2faf:	48 89 85 28 01 00 00 	mov    %rax,0x128(%rbp)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2fb6:	89 8d 30 01 00 00    	mov    %ecx,0x130(%rbp)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2fbc:	5a                   	pop    %rdx
    2fbd:	59                   	pop    %rcx
    2fbe:	48 8b 14 24          	mov    (%rsp),%rdx
    2fc2:	0f 85 f8 11 00 00    	jne    41c0 <main+0x1af0>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2fc8:	66 0f 6f 25 30 6f 00 00 	movdqa 0x6f30(%rip),%xmm4        # 9f00 <_IO_stdin_used+0xf00>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    2fd0:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
          thread_data[x].tasks[y].available = 1;
    2fd4:	48 8b 05 45 6f 00 00 	mov    0x6f45(%rip),%rax        # 9f20 <_IO_stdin_used+0xf20>
          thread_data[x].tasks[y].arrived = 0;
    2fdb:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
          thread_data[x].tasks[y].worker_count = thread_count;
    2fe5:	c7 85 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rbp)
          thread_data[x].tasks[y].available = 1;
    2fef:	48 89 85 44 01 00 00 	mov    %rax,0x144(%rbp)
          thread_data[x].tasks[y].thread_count = 2;
    2ff6:	0f 11 a5 34 01 00 00 	movups %xmm4,0x134(%rbp)
          if (y == barrier_count - 1) {
    2ffd:	41 83 fd 01          	cmp    $0x1,%r13d
    3001:	0f 84 18 01 00 00    	je     311f <main+0xa4f>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    3007:	45 85 ed             	test   %r13d,%r13d
    300a:	0f 84 f9 00 00 00    	je     3109 <main+0xa39>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    3010:	4c 89 f0             	mov    %r14,%rax
    3013:	49 89 ec             	mov    %rbp,%r12
    3016:	41 89 de             	mov    %ebx,%r14d
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3019:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    301e:	48 89 c3             	mov    %rax,%rbx
    3021:	48 8d 05 98 4a 00 00 	lea    0x4a98(%rip),%rax        # 7ac0 <barriered_work>
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3028:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    302d:	48 89 d5             	mov    %rdx,%rbp
    3030:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3038:	48 81 c3 30 01 00 00 	add    $0x130,%rbx
        thread_data[x].buffers_count = buffers_per_thread;
    303f:	c7 43 9c 01 00 00 00 	movl   $0x1,-0x64(%rbx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3046:	e8 b5 f3 ff ff       	call   2400 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    304b:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    3050:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
        }
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3055:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    305a:	48 89 83 20 ff ff ff 	mov    %rax,-0xe0(%rbx)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3061:	4c 89 f9             	mov    %r15,%rcx
    3064:	48 c1 e1 04          	shl    $0x4,%rcx
    3068:	48 01 f9             	add    %rdi,%rcx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    306b:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3070:	48 89 08             	mov    %rcx,(%rax)
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3073:	e8 88 f3 ff ff       	call   2400 <calloc@plt>
        for (int b = 0 ; b < io_threads; b++) {	
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    3078:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    307d:	66 0f 6f 74 24 70    	movdqa 0x70(%rsp),%xmm6
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3083:	48 89 83 28 ff ff ff 	mov    %rax,-0xd8(%rbx)
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    308a:	48 8d 4f 10          	lea    0x10(%rdi),%rcx
    308e:	48 89 38             	mov    %rdi,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3091:	48 83 c7 20          	add    $0x20,%rdi
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    3095:	48 89 48 08          	mov    %rcx,0x8(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3099:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    309e:	48 89 7c 24 58       	mov    %rdi,0x58(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    30a3:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    30a6:	0f 11 b5 18 05 00 00 	movups %xmm6,0x518(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    30ad:	c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    30b7:	48 89 85 28 05 00 00 	mov    %rax,0x528(%rbp)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    30be:	c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbp)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    30c8:	c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    30d2:	8b 83 d4 fe ff ff    	mov    -0x12c(%rbx),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    30d8:	c7 85 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    30e2:	89 85 30 05 00 00    	mov    %eax,0x530(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
    30e8:	48 8b 05 31 6e 00 00 	mov    0x6e31(%rip),%rax        # 9f20 <_IO_stdin_used+0xf20>
    30ef:	48 89 85 44 05 00 00 	mov    %rax,0x544(%rbp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    30f6:	4d 85 ff             	test   %r15,%r15
    30f9:	75 32                	jne    312d <main+0xa5d>
    30fb:	48 c7 44 24 20 01 00 00 00 	movq   $0x1,0x20(%rsp)
    3104:	e9 27 fa ff ff       	jmp    2b30 <main+0x460>
    3109:	48 8d 05 80 4f 00 00 	lea    0x4f80(%rip),%rax        # 8090 <barriered_work_ingest_andwork>
            thread_data[x].tasks[y].run = barriered_work; 
    3110:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    3117:	41 89 dd             	mov    %ebx,%r13d
    311a:	e9 01 fc ff ff       	jmp    2d20 <main+0x650>
    311f:	48 8d 05 9a 49 00 00 	lea    0x499a(%rip),%rax        # 7ac0 <barriered_work>
    3126:	bb 02 00 00 00       	mov    $0x2,%ebx
    312b:	eb e3                	jmp    3110 <main+0xa40>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    312d:	bf 00 04 00 00       	mov    $0x400,%edi
    3132:	be 08 00 00 00       	mov    $0x8,%esi
    3137:	31 ed                	xor    %ebp,%ebp
    3139:	e8 c2 f2 ff ff       	call   2400 <calloc@plt>
    313e:	49 89 c4             	mov    %rax,%r12
  int datas_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3141:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3146:	48 8d 58 38          	lea    0x38(%rax),%rbx
    314a:	48 05 98 02 00 00    	add    $0x298,%rax
    3150:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3155:	48 89 df             	mov    %rbx,%rdi
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3158:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    315c:	45 85 c0             	test   %r8d,%r8d
    315f:	7e 55                	jle    31b6 <main+0xae6>
    3161:	48 8b 17             	mov    (%rdi),%rdx
    3164:	49 63 f0             	movslq %r8d,%rsi
    3167:	48 63 c5             	movslq %ebp,%rax
    316a:	48 c1 e6 09          	shl    $0x9,%rsi
    316e:	49 8d 0c c4          	lea    (%r12,%rax,8),%rcx
    3172:	48 01 d6             	add    %rdx,%rsi
    3175:	0f 1f 00             	nopl   (%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3178:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    317f:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    3186:	48 83 c1 20          	add    $0x20,%rcx
    318a:	f3 0f 7e 80 00 01 00 00 	movq   0x100(%rax),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3192:	f3 0f 7e 08          	movq   (%rax),%xmm1
    3196:	0f 16 80 80 01 00 00 	movhps 0x180(%rax),%xmm0
    319d:	0f 16 88 80 00 00 00 	movhps 0x80(%rax),%xmm1
    31a4:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    31a8:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31ac:	48 39 d6             	cmp    %rdx,%rsi
    31af:	75 c7                	jne    3178 <main+0xaa8>
    31b1:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    31b6:	48 81 c7 30 01 00 00 	add    $0x130,%rdi
    31bd:	48 39 7c 24 10       	cmp    %rdi,0x10(%rsp)
    31c2:	75 94                	jne    3158 <main+0xa88>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    31c4:	48 8d 3d 24 62 00 00 	lea    0x6224(%rip),%rdi        # 93ef <_IO_stdin_used+0x3ef>
    31cb:	e8 60 f1 ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    31d0:	48 8d 3d 2f 62 00 00 	lea    0x622f(%rip),%rdi        # 9406 <_IO_stdin_used+0x406>
    31d7:	48 8d 35 26 62 00 00 	lea    0x6226(%rip),%rsi        # 9404 <_IO_stdin_used+0x404>
    31de:	e8 1d f3 ff ff       	call   2500 <fopen@plt>
    31e3:	48 89 c7             	mov    %rax,%rdi
  for (int x = 0 ; x < datas_size; x++) {
    31e6:	85 ed                	test   %ebp,%ebp
    31e8:	0f 8e 85 00 00 00    	jle    3273 <main+0xba3>
    31ee:	48 8d 05 48 62 00 00 	lea    0x6248(%rip),%rax        # 943d <_IO_stdin_used+0x43d>
    31f5:	48 63 ed             	movslq %ebp,%rbp
    31f8:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    31fd:	4c 8d 2d 2d 62 00 00 	lea    0x622d(%rip),%r13        # 9431 <_IO_stdin_used+0x431>
    3204:	48 89 04 24          	mov    %rax,(%rsp)
    3208:	4d 8d 3c ec          	lea    (%r12,%rbp,8),%r15
    320c:	48 89 fb             	mov    %rdi,%rbx
    char * c = calloc(250, sizeof(char));
    320f:	be 01 00 00 00       	mov    $0x1,%esi
    3214:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    3219:	49 83 c4 08          	add    $0x8,%r12
    char * c = calloc(250, sizeof(char));
    321d:	e8 de f1 ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3222:	4c 89 e9             	mov    %r13,%rcx
    3225:	ba fa 00 00 00       	mov    $0xfa,%edx
    322a:	be 01 00 00 00       	mov    $0x1,%esi
    322f:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    3232:	49 8b 44 24 f8       	mov    -0x8(%r12),%rax
    3237:	48 89 ef             	mov    %rbp,%rdi
    323a:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3241:	31 c0                	xor    %eax,%eax
    3243:	e8 78 f3 ff ff       	call   25c0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3248:	48 8b 34 24          	mov    (%rsp),%rsi
    324c:	48 89 ea             	mov    %rbp,%rdx
    324f:	31 c0                	xor    %eax,%eax
    3251:	bf 01 00 00 00       	mov    $0x1,%edi
    3256:	e8 55 f2 ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    325b:	48 89 de             	mov    %rbx,%rsi
    325e:	48 89 ef             	mov    %rbp,%rdi
    3261:	e8 5a f1 ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    3266:	4d 39 e7             	cmp    %r12,%r15
    3269:	75 a4                	jne    320f <main+0xb3f>
    326b:	48 89 df             	mov    %rbx,%rdi
    326e:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    3273:	e8 e8 f0 ff ff       	call   2360 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3278:	48 8d 3d 90 61 00 00 	lea    0x6190(%rip),%rdi        # 940f <_IO_stdin_used+0x40f>
    327f:	49 89 dc             	mov    %rbx,%r12
    3282:	4c 8d 3d c9 61 00 00 	lea    0x61c9(%rip),%r15        # 9452 <_IO_stdin_used+0x452>
    3289:	e8 a2 f0 ff ff       	call   2330 <puts@plt>
    328e:	31 d2                	xor    %edx,%edx
    3290:	48 8d 35 90 61 00 00 	lea    0x6190(%rip),%rsi        # 9427 <_IO_stdin_used+0x427>
    3297:	31 c0                	xor    %eax,%eax
    3299:	bf 01 00 00 00       	mov    $0x1,%edi
    329e:	4c 8d 2d b8 61 00 00 	lea    0x61b8(%rip),%r13        # 945d <_IO_stdin_used+0x45d>
    32a5:	e8 06 f2 ff ff       	call   24b0 <__printf_chk@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    32aa:	c7 44 24 40 00 00 00 00 	movl   $0x0,0x40(%rsp)
    32b2:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    32b7:	8b 54 24 40          	mov    0x40(%rsp),%edx
    32bb:	48 8d 35 7e 61 00 00 	lea    0x617e(%rip),%rsi        # 9440 <_IO_stdin_used+0x440>
    32c2:	bf 01 00 00 00       	mov    $0x1,%edi
    32c7:	31 c0                	xor    %eax,%eax
    32c9:	89 d1                	mov    %edx,%ecx
    32cb:	e8 e0 f1 ff ff       	call   24b0 <__printf_chk@plt>
    32d0:	44 89 74 24 18       	mov    %r14d,0x18(%rsp)
    32d5:	45 31 c0             	xor    %r8d,%r8d
    32d8:	44 89 c2             	mov    %r8d,%edx
    32db:	4c 89 fe             	mov    %r15,%rsi
    32de:	bf 01 00 00 00       	mov    $0x1,%edi
    32e3:	31 c0                	xor    %eax,%eax
    32e5:	4c 89 04 24          	mov    %r8,(%rsp)
    32e9:	31 ed                	xor    %ebp,%ebp
    32eb:	e8 c0 f1 ff ff       	call   24b0 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    32f0:	48 8b 1c 24          	mov    (%rsp),%rbx
    32f4:	48 c1 e3 09          	shl    $0x9,%rbx
          char * mailbox_kind = calloc(100, sizeof(char));
    32f8:	be 01 00 00 00       	mov    $0x1,%esi
    32fd:	bf 64 00 00 00       	mov    $0x64,%edi
    3302:	41 89 ee             	mov    %ebp,%r14d
    3305:	e8 f6 f0 ff ff       	call   2400 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    330a:	4d 8b 04 24          	mov    (%r12),%r8
    330e:	48 89 ef             	mov    %rbp,%rdi
          char * mailbox_kind = calloc(100, sizeof(char));
    3311:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3314:	48 c1 e7 08          	shl    $0x8,%rdi
    3318:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3320:	48 01 f8             	add    %rdi,%rax
    3323:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    3329:	83 fe 02             	cmp    $0x2,%esi
    332c:	74 5f                	je     338d <main+0xcbd>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    332e:	83 fe 01             	cmp    $0x1,%esi
    3331:	74 74                	je     33a7 <main+0xcd7>
    3333:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    333a:	44 89 f2             	mov    %r14d,%edx
    333d:	31 c0                	xor    %eax,%eax
    333f:	4c 89 ee             	mov    %r13,%rsi
    3342:	bf 01 00 00 00       	mov    $0x1,%edi
    3347:	e8 64 f1 ff ff       	call   24b0 <__printf_chk@plt>
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    334c:	48 85 ed             	test   %rbp,%rbp
    334f:	75 07                	jne    3358 <main+0xc88>
    3351:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    3356:	eb a0                	jmp    32f8 <main+0xc28>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3358:	4c 8b 04 24          	mov    (%rsp),%r8
    335c:	49 83 c0 01          	add    $0x1,%r8
    3360:	49 83 f8 03          	cmp    $0x3,%r8
    3364:	0f 85 6e ff ff ff    	jne    32d8 <main+0xc08>
    for (int d = 0 ; d < threads_per_group ; d++) {
    336a:	8b 44 24 40          	mov    0x40(%rsp),%eax
    336e:	48 89 6c 24 38       	mov    %rbp,0x38(%rsp)
    3373:	49 81 c4 30 01 00 00 	add    $0x130,%r12
    337a:	44 8b 74 24 18       	mov    0x18(%rsp),%r14d
    337f:	85 c0                	test   %eax,%eax
    3381:	75 41                	jne    33c4 <main+0xcf4>
    3383:	44 89 74 24 40       	mov    %r14d,0x40(%rsp)
    3388:	e9 2a ff ff ff       	jmp    32b7 <main+0xbe7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    338d:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    3397:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    339a:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    33a2:	48 01 f8             	add    %rdi,%rax
    33a5:	eb 8c                	jmp    3333 <main+0xc63>
    33a7:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    33ad:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    33b4:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    33bc:	48 01 f8             	add    %rdi,%rax
    33bf:	e9 6f ff ff ff       	jmp    3333 <main+0xc63>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    33c4:	ba 03 00 00 00       	mov    $0x3,%edx
    33c9:	48 8d 35 a8 60 00 00 	lea    0x60a8(%rip),%rsi        # 9478 <_IO_stdin_used+0x478>
    33d0:	bf 01 00 00 00       	mov    $0x1,%edi
    33d5:	31 c0                	xor    %eax,%eax
    33d7:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    33dc:	e8 cf f0 ff ff       	call   24b0 <__printf_chk@plt>
  

  printf("io index = %d\n", io_index);
  int io_mode = 0;
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    33e1:	be 08 00 00 00       	mov    $0x8,%esi
    33e6:	bf 02 00 00 00       	mov    $0x2,%edi
    33eb:	e8 10 f0 ff ff       	call   2400 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    33f0:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    33f5:	be 08 00 00 00       	mov    $0x8,%esi
    33fa:	bf 02 00 00 00       	mov    $0x2,%edi
    my_thread_data[0] = &thread_data[x]; 
    33ff:	49 8d ae 90 03 00 00 	lea    0x390(%r14),%rbp
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3406:	4c 89 70 08          	mov    %r14,0x8(%rax)
    340a:	4d 8d ae 30 01 00 00 	lea    0x130(%r14),%r13
    my_thread_data[0] = &thread_data[x]; 
    3411:	48 89 28             	mov    %rbp,(%rax)
    3414:	4d 8d be c0 04 00 00 	lea    0x4c0(%r14),%r15

    io_mode = (io_mode + 1) % 2;
    thread_data[x].threads = my_thread_data;
    341b:	49 89 86 a8 03 00 00 	mov    %rax,0x3a8(%r14)
    thread_data[x].thread_count = 2;
    3422:	41 c7 86 b8 03 00 00 02 00 00 00 	movl   $0x2,0x3b8(%r14)
    thread_data[x].thread_index = 0;
    342d:	41 c7 86 94 03 00 00 00 00 00 00 	movl   $0x0,0x394(%r14)
    thread_data[x].task_count = total_barrier_count;
    3438:	41 c7 86 d0 03 00 00 03 00 00 00 	movl   $0x3,0x3d0(%r14)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    3443:	e8 b8 ef ff ff       	call   2400 <calloc@plt>
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3448:	be 38 00 00 00       	mov    $0x38,%esi
    344d:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[x].thread_count = 2;
    3452:	41 c7 86 e8 04 00 00 02 00 00 00 	movl   $0x2,0x4e8(%r14)
    thread_data[x].threads = my_thread_data;
    345d:	49 89 86 d8 04 00 00 	mov    %rax,0x4d8(%r14)
    my_thread_data[0] = &thread_data[x]; 
    3464:	4c 89 38             	mov    %r15,(%rax)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3467:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    346b:	49 8b 46 38          	mov    0x38(%r14),%rax
    thread_data[x].thread_index = 0;
    346f:	41 c7 86 c4 04 00 00 00 00 00 00 	movl   $0x0,0x4c4(%r14)
    thread_data[x].task_count = total_barrier_count;
    347a:	41 c7 86 00 05 00 00 03 00 00 00 	movl   $0x3,0x500(%r14)
    thread_data[n].tasks[0].scheduled = 1;
    3485:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    348f:	49 8b 86 68 01 00 00 	mov    0x168(%r14),%rax
    3496:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
    349b:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34a5:	e8 56 ef ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34aa:	be 38 00 00 00       	mov    $0x38,%esi
    34af:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34b4:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34b7:	e8 44 ef ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34bc:	be 38 00 00 00       	mov    $0x38,%esi
    34c1:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34c6:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34ca:	e8 31 ef ff ff       	call   2400 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34cf:	be 38 00 00 00       	mov    $0x38,%esi
    34d4:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34d9:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34de:	e8 1d ef ff ff       	call   2400 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    34e3:	be 08 00 00 00       	mov    $0x8,%esi
    34e8:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34ed:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    34f2:	e8 09 ef ff ff       	call   2400 <calloc@plt>


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
    34f7:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    34fc:	be 08 00 00 00       	mov    $0x8,%esi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3501:	49 89 c4             	mov    %rax,%r12
  thread_data[timer_threadi].task_count = total_barrier_count;
    3504:	48 8b 05 1d 6a 00 00 	mov    0x6a1d(%rip),%rax        # 9f28 <_IO_stdin_used+0xf28>
  thread_data[timer_threadi].type = TIMER;
    350b:	c7 87 6c 02 00 00 00 00 00 00 	movl   $0x0,0x26c(%rdi)
  thread_data[timer_threadi].task_count = total_barrier_count;
    3515:	48 89 87 a0 02 00 00 	mov    %rax,0x2a0(%rdi)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    351c:	bf 07 00 00 00       	mov    $0x7,%edi
    3521:	e8 da ee ff ff       	call   2400 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3526:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    352b:	48 8d 35 55 5f 00 00 	lea    0x5f55(%rip),%rsi        # 9487 <_IO_stdin_used+0x487>
    3532:	4c 89 78 20          	mov    %r15,0x20(%rax)
    3536:	48 8d 8f 60 02 00 00 	lea    0x260(%rdi),%rcx
    353d:	49 89 ff             	mov    %rdi,%r15
    3540:	48 89 38             	mov    %rdi,(%rax)
    3543:	48 8d bf f0 05 00 00 	lea    0x5f0(%rdi),%rdi
    354a:	48 89 78 28          	mov    %rdi,0x28(%rax)
    354e:	49 8d 97 20 07 00 00 	lea    0x720(%r15),%rdx
    3555:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
  }
  thread_data[timer_threadi].threads = my_thread_data;
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    355a:	48 8b 3d b7 69 00 00 	mov    0x69b7(%rip),%rdi        # 9f18 <_IO_stdin_used+0xf18>
    my_thread_data[n] = &thread_data[n]; 
    3561:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3565:	48 89 48 10          	mov    %rcx,0x10(%rax)
    3569:	48 89 68 18          	mov    %rbp,0x18(%rax)
    356d:	48 89 50 30          	mov    %rdx,0x30(%rax)
    3571:	ba 02 00 00 00       	mov    $0x2,%edx
  thread_data[timer_threadi].threads = my_thread_data;
    3576:	49 89 87 78 02 00 00 	mov    %rax,0x278(%r15)
    357d:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    357f:	49 89 bf 88 02 00 00 	mov    %rdi,0x288(%r15)
    3586:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    358b:	41 c7 87 90 02 00 00 02 00 00 00 	movl   $0x2,0x290(%r15)
  thread_data[timer_threadi].thread_index = 0;
    3596:	41 c7 87 64 02 00 00 00 00 00 00 	movl   $0x0,0x264(%r15)
    my_thread_data[n] = &thread_data[n]; 
    35a1:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    35a6:	e8 05 ef ff ff       	call   24b0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    35ab:	48 8b 34 24          	mov    (%rsp),%rsi
    35af:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    35b4:	49 8d 7c 24 10       	lea    0x10(%r12),%rdi
    35b9:	48 8d 15 e0 0e 00 00 	lea    0xee0(%rip),%rdx        # 44a0 <timer_thread>
    35c0:	48 83 c6 70          	add    $0x70,%rsi
    35c4:	e8 07 ef ff ff       	call   24d0 <pthread_create@plt>
    35c9:	4c 8d 05 28 64 00 00 	lea    0x6428(%rip),%r8        # 99f8 <_IO_stdin_used+0x9f8>
    35d0:	31 c9                	xor    %ecx,%ecx
    35d2:	31 d2                	xor    %edx,%edx
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    35d4:	41 c7 47 0c 01 00 00 00 	movl   $0x1,0xc(%r15)
    35dc:	4c 89 c6             	mov    %r8,%rsi
    35df:	bf 01 00 00 00       	mov    $0x1,%edi
    35e4:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    35e6:	41 c7 47 44 01 00 00 00 	movl   $0x1,0x44(%r15)
    35ee:	e8 bd ee ff ff       	call   24b0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    35f3:	4c 89 f9             	mov    %r15,%rcx
    35f6:	4c 89 7c 24 30       	mov    %r15,0x30(%rsp)
    35fb:	4c 89 f6             	mov    %r14,%rsi
    35fe:	4c 8d 3d 2b 3c 00 00 	lea    0x3c2b(%rip),%r15        # 7230 <barriered_thread>
    3605:	4c 89 e7             	mov    %r12,%rdi
    3608:	4c 89 fa             	mov    %r15,%rdx
    360b:	e8 c0 ee ff ff       	call   24d0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3610:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3615:	49 8b 3c 24          	mov    (%r12),%rdi
    3619:	be 08 00 00 00       	mov    $0x8,%esi
    361e:	48 8b 90 c0 00 00 00 	mov    0xc0(%rax),%rdx
    3625:	e8 f6 ec ff ff       	call   2320 <pthread_setaffinity_np@plt>
      thread_data[x].type = WORKER;
    362a:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    362f:	31 c9                	xor    %ecx,%ecx
    3631:	4c 8d 05 c0 63 00 00 	lea    0x63c0(%rip),%r8        # 99f8 <_IO_stdin_used+0x9f8>
    3638:	4c 89 c6             	mov    %r8,%rsi
    363b:	ba 01 00 00 00       	mov    $0x1,%edx
    3640:	bf 01 00 00 00       	mov    $0x1,%edi
    3645:	c7 80 3c 01 00 00 01 00 00 00 	movl   $0x1,0x13c(%rax)
      thread_data[x].running = 1;
    364f:	c7 80 74 01 00 00 01 00 00 00 	movl   $0x1,0x174(%rax)
    3659:	31 c0                	xor    %eax,%eax
    365b:	e8 50 ee ff ff       	call   24b0 <__printf_chk@plt>
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3660:	4c 89 e9             	mov    %r13,%rcx
    3663:	49 8d 76 38          	lea    0x38(%r14),%rsi
    3667:	4c 89 fa             	mov    %r15,%rdx
    366a:	49 8d 7c 24 08       	lea    0x8(%r12),%rdi
    366f:	e8 5c ee ff ff       	call   24d0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3674:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3679:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    367e:	be 08 00 00 00       	mov    $0x8,%esi
    3683:	48 8b 90 f0 01 00 00 	mov    0x1f0(%rax),%rdx
    368a:	e8 91 ec ff ff       	call   2320 <pthread_setaffinity_np@plt>
    }
  }
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    368f:	be 08 00 00 00       	mov    $0x8,%esi
    3694:	bf 02 00 00 00       	mov    $0x2,%edi
    3699:	e8 62 ed ff ff       	call   2400 <calloc@plt>

  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    369e:	be d8 00 00 00       	mov    $0xd8,%esi
    36a3:	bf 01 00 00 00       	mov    $0x1,%edi
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    36a8:	49 89 c6             	mov    %rax,%r14
    36ab:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    36b0:	e8 4b ed ff ff       	call   2400 <calloc@plt>
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    36b5:	be d8 00 00 00       	mov    $0xd8,%esi
    36ba:	bf 01 00 00 00       	mov    $0x1,%edi
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    36bf:	49 89 06             	mov    %rax,(%r14)
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    36c2:	e8 39 ed ff ff       	call   2400 <calloc@plt>

  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    36c7:	be 10 00 00 00       	mov    $0x10,%esi
    36cc:	bf 02 00 00 00       	mov    $0x2,%edi
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    36d1:	49 89 46 08          	mov    %rax,0x8(%r14)
  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    36d5:	e8 26 ed ff ff       	call   2400 <calloc@plt>
    36da:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    36df:	49 89 c6             	mov    %rax,%r14
  long iomailboxes_size = 10000;
  for (int x = 0 ; x < io_threads; x++) {
    36e2:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    36e7:	48 8d 40 20          	lea    0x20(%rax),%rax
    36eb:	48 89 04 24          	mov    %rax,(%rsp)
    36ef:	4c 89 e8             	mov    %r13,%rax
    36f2:	49 89 ed             	mov    %rbp,%r13
    36f5:	4c 89 f5             	mov    %r14,%rbp
    36f8:	49 89 c7             	mov    %rax,%r15
    iomailboxes[x].count = iomailboxes_size;
    36fb:	c7 45 00 10 27 00 00 	movl   $0x2710,0x0(%rbp)
    iomailboxes[x].buffer = calloc(iomailboxes_size, sizeof(struct Buffer));
    3702:	be 28 00 00 00       	mov    $0x28,%esi
    3707:	bf 10 27 00 00       	mov    $0x2710,%edi
    370c:	e8 ef ec ff ff       	call   2400 <calloc@plt>
    3711:	48 89 45 08          	mov    %rax,0x8(%rbp)
    3715:	48 89 c3             	mov    %rax,%rbx
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3718:	4c 8d 60 08          	lea    0x8(%rax),%r12
    371c:	48 81 c3 88 1a 06 00 	add    $0x61a88,%rbx
    3723:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      iomailboxes[x].buffer[y].available = 0;
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3728:	be 20 00 00 00       	mov    $0x20,%esi
    372d:	bf 64 00 00 00       	mov    $0x64,%edi
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3732:	49 83 c4 28          	add    $0x28,%r12
      iomailboxes[x].buffer[y].available = 0;
    3736:	41 c7 44 24 d8 00 00 00 00 	movl   $0x0,-0x28(%r12)
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
    373f:	41 c7 44 24 e8 64 00 00 00 	movl   $0x64,-0x18(%r12)
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3748:	e8 b3 ec ff ff       	call   2400 <calloc@plt>
    374d:	49 89 44 24 e0       	mov    %rax,-0x20(%r12)
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3752:	4c 39 e3             	cmp    %r12,%rbx
    3755:	75 d1                	jne    3728 <main+0x1058>
  for (int x = 0 ; x < io_threads; x++) {
    3757:	48 83 c5 10          	add    $0x10,%rbp
    375b:	48 39 2c 24          	cmp    %rbp,(%rsp)
    375f:	75 9a                	jne    36fb <main+0x102b>
  char * recv_identity = "recv-thread";
  char * unknown_identity = "unknown-thread";
  int counter = 0;

  int dataeventfds[2];
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
    3761:	be 00 08 00 00       	mov    $0x800,%esi
    3766:	31 ff                	xor    %edi,%edi
    3768:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    376d:	4c 89 ed             	mov    %r13,%rbp
    3770:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    3775:	4d 89 fd             	mov    %r15,%r13
    3778:	49 89 ef             	mov    %rbp,%r15
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);

  for (int x = io_index ; x < io_index + io_threads ; x++) {
    377b:	bd 03 00 00 00       	mov    $0x3,%ebp
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
    3780:	e8 ab ed ff ff       	call   2530 <eventfd@plt>
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);
    3785:	be 00 08 00 00       	mov    $0x800,%esi
    378a:	31 ff                	xor    %edi,%edi
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
    378c:	89 04 24             	mov    %eax,(%rsp)
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);
    378f:	e8 9c ed ff ff       	call   2530 <eventfd@plt>
    3794:	48 89 5c 24 58       	mov    %rbx,0x58(%rsp)
    3799:	89 44 24 08          	mov    %eax,0x8(%rsp)
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    379d:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    37a2:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    37a7:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    37ac:	48 05 a8 00 00 00    	add    $0xa8,%rax
    37b2:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    37b7:	48 8b 05 72 67 00 00 	mov    0x6772(%rip),%rax        # 9f30 <_IO_stdin_used+0xf30>
    thread_data[x].io_mode = myring;
    thread_data[x].my_io = myring;
    thread_data[x].other_io = otherring;
    thread_data[x].iomailboxes = iomailboxes; 
    printf("%d myring %d other is %d\n", x, myring, otherring);
    thread_data[x].ring = rings[myring]; 
    37be:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    thread_data[x].type = IO;
    37c3:	41 c7 47 0c 02 00 00 00 	movl   $0x2,0xc(%r15)
    thread_data[x].task_count = 0;
    37cb:	49 89 47 40          	mov    %rax,0x40(%r15)
    thread_data[x].ring = rings[myring]; 
    37cf:	89 e8                	mov    %ebp,%eax
    37d1:	83 e0 01             	and    $0x1,%eax
    37d4:	48 8d 1c c3          	lea    (%rbx,%rax,8),%rbx
    if (myring == IO_MODE_SEND) {
    37d8:	40 f6 c5 01          	test   $0x1,%bpl
    37dc:	0f 84 1e 01 00 00    	je     3900 <main+0x1230>
      thread_data[x].identity = recv_identity;
    37e2:	48 8d 05 04 5e 00 00 	lea    0x5e04(%rip),%rax        # 95ed <_IO_stdin_used+0x5ed>
    thread_data[x].iomailboxes = iomailboxes; 
    37e9:	4d 89 b7 10 01 00 00 	mov    %r14,0x110(%r15)
    37f0:	89 ea                	mov    %ebp,%edx
    37f2:	45 31 c0             	xor    %r8d,%r8d
    37f5:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
    thread_data[x].other_io = otherring;
    37fc:	31 c0                	xor    %eax,%eax
    37fe:	b9 01 00 00 00       	mov    $0x1,%ecx
    3803:	48 8d 35 c9 5d 00 00 	lea    0x5dc9(%rip),%rsi        # 95d3 <_IO_stdin_used+0x5d3>
    380a:	41 89 87 18 01 00 00 	mov    %eax,0x118(%r15)
    3811:	bf 01 00 00 00       	mov    $0x1,%edi
    3816:	31 c0                	xor    %eax,%eax
    thread_data[x].io_mode = myring;
    3818:	41 c7 87 0c 01 00 00 01 00 00 00 	movl   $0x1,0x10c(%r15)
    thread_data[x].my_io = myring;
    3823:	41 c7 87 1c 01 00 00 01 00 00 00 	movl   $0x1,0x11c(%r15)
    382e:	e8 7d ec ff ff       	call   24b0 <__printf_chk@plt>
    thread_data[x].ring = rings[myring]; 
    3833:	48 8b 03             	mov    (%rbx),%rax
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3836:	be 00 08 00 00       	mov    $0x800,%esi
    383b:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = rings[myring]; 
    383d:	49 89 47 60          	mov    %rax,0x60(%r15)
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3841:	e8 ea ec ff ff       	call   2530 <eventfd@plt>
    if (x % 2 == 0) {
      otherdataeventfd = dataeventfds[0];
      datafd = dataeventfds[1];
    } else {
      otherdataeventfd = dataeventfds[1];
      datafd = dataeventfds[0];
    3846:	8b 14 24             	mov    (%rsp),%edx
      otherdataeventfd = dataeventfds[1];
    3849:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    thread_data[x]._eventfd = myeventfd; 
    384d:	41 89 47 68          	mov    %eax,0x68(%r15)
    3851:	48 8d 35 d0 61 00 00 	lea    0x61d0(%rip),%rsi        # 9a28 <_IO_stdin_used+0xa28>
    3858:	bf 01 00 00 00       	mov    $0x1,%edi
    385d:	31 c0                	xor    %eax,%eax
    385f:	89 4c 24 70          	mov    %ecx,0x70(%rsp)
    3863:	89 54 24 68          	mov    %edx,0x68(%rsp)
    3867:	e8 44 ec ff ff       	call   24b0 <__printf_chk@plt>
    }
    printf("my data event fd is %d other is %d\n", datafd, otherdataeventfd);
    thread_data[x].dataeventfd = datafd; 
    thread_data[x].otherdataeventfd = otherdataeventfd; 
    386c:	8b 4c 24 70          	mov    0x70(%rsp),%ecx
    thread_data[x].dataeventfd = datafd; 
    3870:	8b 54 24 68          	mov    0x68(%rsp),%edx
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3874:	be 08 00 00 00       	mov    $0x8,%esi
    3879:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x].otherdataeventfd = otherdataeventfd; 
    387e:	41 89 4f 70          	mov    %ecx,0x70(%r15)
    thread_data[x].dataeventfd = datafd; 
    3882:	41 89 57 6c          	mov    %edx,0x6c(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3886:	e8 75 eb ff ff       	call   2400 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    388b:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].thread_index = x;
    3890:	41 89 6f 04          	mov    %ebp,0x4(%r15)
    3894:	89 ea                	mov    %ebp,%edx
    thread_data[x].threads = my_thread_data;
    3896:	49 89 47 18          	mov    %rax,0x18(%r15)
    389a:	48 8d 35 04 5c 00 00 	lea    0x5c04(%rip),%rsi        # 94a5 <_IO_stdin_used+0x4a5>
    38a1:	bf 01 00 00 00       	mov    $0x1,%edi
      my_thread_data[n] = &thread_data[n]; 
    38a6:	48 89 18             	mov    %rbx,(%rax)
    38a9:	4c 89 68 08          	mov    %r13,0x8(%rax)
    38ad:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_count = thread_count;
    38af:	41 c7 47 28 02 00 00 00 	movl   $0x2,0x28(%r15)
    38b7:	e8 f4 eb ff ff       	call   24b0 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    38bc:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    38c1:	4c 89 f9             	mov    %r15,%rcx
    38c4:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    38c9:	48 8d 15 00 21 00 00 	lea    0x2100(%rip),%rdx        # 59d0 <io_thread>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    38d0:	49 81 c7 30 01 00 00 	add    $0x130,%r15
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    38d7:	48 89 df             	mov    %rbx,%rdi
    38da:	e8 f1 eb ff ff       	call   24d0 <pthread_create@plt>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    38df:	48 89 d8             	mov    %rbx,%rax
    38e2:	48 83 44 24 18 38    	addq   $0x38,0x18(%rsp)
    38e8:	48 83 c0 08          	add    $0x8,%rax
    38ec:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    38f1:	83 fd 03             	cmp    $0x3,%ebp
    38f4:	75 7c                	jne    3972 <main+0x12a2>
    38f6:	bd 04 00 00 00       	mov    $0x4,%ebp
    38fb:	e9 b7 fe ff ff       	jmp    37b7 <main+0x10e7>
    3900:	48 8d 05 c0 5c 00 00 	lea    0x5cc0(%rip),%rax        # 95c7 <_IO_stdin_used+0x5c7>
    3907:	31 c9                	xor    %ecx,%ecx
    3909:	89 ea                	mov    %ebp,%edx
    390b:	bf 01 00 00 00       	mov    $0x1,%edi
    3910:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
    3917:	31 c0                	xor    %eax,%eax
    3919:	41 b8 01 00 00 00    	mov    $0x1,%r8d
    391f:	48 8d 35 ad 5c 00 00 	lea    0x5cad(%rip),%rsi        # 95d3 <_IO_stdin_used+0x5d3>
    thread_data[x].io_mode = myring;
    3926:	41 c7 87 0c 01 00 00 00 00 00 00 	movl   $0x0,0x10c(%r15)
    thread_data[x].my_io = myring;
    3931:	41 c7 87 1c 01 00 00 00 00 00 00 	movl   $0x0,0x11c(%r15)
    thread_data[x].other_io = otherring;
    393c:	41 c7 87 18 01 00 00 01 00 00 00 	movl   $0x1,0x118(%r15)
    thread_data[x].iomailboxes = iomailboxes; 
    3947:	4d 89 b7 10 01 00 00 	mov    %r14,0x110(%r15)
    394e:	e8 5d eb ff ff       	call   24b0 <__printf_chk@plt>
    thread_data[x].ring = rings[myring]; 
    3953:	48 8b 03             	mov    (%rbx),%rax
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3956:	be 00 08 00 00       	mov    $0x800,%esi
    395b:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = rings[myring]; 
    395d:	49 89 47 60          	mov    %rax,0x60(%r15)
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3961:	e8 ca eb ff ff       	call   2530 <eventfd@plt>
      datafd = dataeventfds[1];
    3966:	8b 54 24 08          	mov    0x8(%rsp),%edx
      otherdataeventfd = dataeventfds[0];
    396a:	8b 0c 24             	mov    (%rsp),%ecx
    396d:	e9 db fe ff ff       	jmp    384d <main+0x117d>
    3972:	ba 05 00 00 00       	mov    $0x5,%edx
    3977:	48 8d 35 3e 5b 00 00 	lea    0x5b3e(%rip),%rsi        # 94bc <_IO_stdin_used+0x4bc>
    397e:	bf 01 00 00 00       	mov    $0x1,%edi
    3983:	31 c0                	xor    %eax,%eax
    3985:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
    398a:	49 8d 6c 24 28       	lea    0x28(%r12),%rbp
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    398f:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    3995:	e8 16 eb ff ff       	call   24b0 <__printf_chk@plt>
    399a:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    399f:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    39a4:	48 05 18 01 00 00    	add    $0x118,%rax
    39aa:	48 89 04 24          	mov    %rax,(%rsp)
    39ae:	44 89 fa             	mov    %r15d,%edx
    39b1:	48 8d 35 1a 5b 00 00 	lea    0x5b1a(%rip),%rsi        # 94d2 <_IO_stdin_used+0x4d2>
    39b8:	bf 01 00 00 00       	mov    $0x1,%edi
    39bd:	31 c0                	xor    %eax,%eax
    39bf:	e8 ec ea ff ff       	call   24b0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    39c4:	be 08 00 00 00       	mov    $0x8,%esi
    39c9:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    39ce:	48 8b 05 5b 65 00 00 	mov    0x655b(%rip),%rax        # 9f30 <_IO_stdin_used+0xf30>
    thread_data[x].type = EXTERNAL;
    39d5:	41 c7 46 0c 03 00 00 00 	movl   $0x3,0xc(%r14)
    thread_data[x].task_count = 0;
    39dd:	49 89 46 40          	mov    %rax,0x40(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    39e1:	e8 1a ea ff ff       	call   2400 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    39e6:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39ee:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    39f3:	41 c7 86 cc 00 00 00 01 00 00 00 	movl   $0x1,0xcc(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    39fe:	49 89 46 50          	mov    %rax,0x50(%r14)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3a02:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a05:	bf 02 00 00 00       	mov    $0x2,%edi
    3a0a:	e8 f1 e9 ff ff       	call   2400 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3a0f:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a14:	4c 89 f1             	mov    %r14,%rcx
    3a17:	48 89 ef             	mov    %rbp,%rdi
    thread_data[x].threads = my_thread_data;
    3a1a:	49 89 46 18          	mov    %rax,0x18(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a1e:	48 8d 15 7b 09 00 00 	lea    0x97b(%rip),%rdx        # 43a0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a25:	48 83 c5 08          	add    $0x8,%rbp
    3a29:	49 81 c6 30 01 00 00 	add    $0x130,%r14
      my_thread_data[n] = &thread_data[n]; 
    3a30:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a33:	48 8b 34 24          	mov    (%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3a37:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3a3b:	48 8b 05 d6 64 00 00 	mov    0x64d6(%rip),%rax        # 9f18 <_IO_stdin_used+0xf18>
    thread_data[x].thread_index = x;
    3a42:	45 89 be d4 fe ff ff 	mov    %r15d,-0x12c(%r14)
    thread_data[x].thread_count = thread_count;
    3a49:	49 89 86 f8 fe ff ff 	mov    %rax,-0x108(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a50:	e8 7b ea ff ff       	call   24d0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a55:	48 83 04 24 38       	addq   $0x38,(%rsp)
    3a5a:	48 83 84 24 80 00 00 00 10 	addq   $0x10,0x80(%rsp)
    3a63:	41 83 ff 05          	cmp    $0x5,%r15d
    3a67:	75 2b                	jne    3a94 <main+0x13c4>
    3a69:	41 bf 06 00 00 00    	mov    $0x6,%r15d
    3a6f:	e9 3a ff ff ff       	jmp    39ae <main+0x12de>
        my_thread_data[1] = &thread_data[other]; 
    3a74:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3a79:	4c 89 6c 24 50       	mov    %r13,0x50(%rsp)
    3a7e:	48 89 da             	mov    %rbx,%rdx
    3a81:	45 31 c0             	xor    %r8d,%r8d
        other = (x + 1) % total_threads;
    3a84:	bd 01 00 00 00       	mov    $0x1,%ebp
        my_thread_data[1] = &thread_data[other]; 
    3a89:	48 05 30 01 00 00    	add    $0x130,%rax
        thread_data[x].protected_state = &protected_state[k];
    3a8f:	e9 4b f1 ff ff       	jmp    2bdf <main+0x50f>
    3a94:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3a99:	48 8d 2d 4f 5a 00 00 	lea    0x5a4f(%rip),%rbp        # 94ef <_IO_stdin_used+0x4ef>
    3aa0:	4c 8d 70 04          	lea    0x4(%rax),%r14
    3aa4:	4c 8d a8 54 08 00 00 	lea    0x854(%rax),%r13
    3aab:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3aaf:	41 8b 16             	mov    (%r14),%edx
    3ab2:	48 89 ee             	mov    %rbp,%rsi
    3ab5:	bf 01 00 00 00       	mov    $0x1,%edi
    3aba:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3abc:	49 81 c6 30 01 00 00 	add    $0x130,%r14
    3ac3:	e8 e8 e9 ff ff       	call   24b0 <__printf_chk@plt>
    3ac8:	4d 39 ee             	cmp    %r13,%r14
    3acb:	75 de                	jne    3aab <main+0x13db>
    3acd:	48 8d 3d 2e 5a 00 00 	lea    0x5a2e(%rip),%rdi        # 9502 <_IO_stdin_used+0x502>
    3ad4:	45 31 f6             	xor    %r14d,%r14d
    3ad7:	4c 8d ac 24 b0 00 00 00 	lea    0xb0(%rsp),%r13
    3adf:	e8 4c e8 ff ff       	call   2330 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3ae4:	48 8d 2d 35 5a 00 00 	lea    0x5a35(%rip),%rbp        # 9520 <_IO_stdin_used+0x520>
    void * result; 
    pthread_join(thread[x], &result);
    3aeb:	4b 8b 3c f4          	mov    (%r12,%r14,8),%rdi
    3aef:	4c 89 ee             	mov    %r13,%rsi
    3af2:	e8 79 ea ff ff       	call   2570 <pthread_join@plt>
    3af7:	44 89 f2             	mov    %r14d,%edx
    3afa:	48 89 ee             	mov    %rbp,%rsi
    3afd:	bf 01 00 00 00       	mov    $0x1,%edi
    3b02:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3b04:	49 83 c6 01          	add    $0x1,%r14
    3b08:	e8 a3 e9 ff ff       	call   24b0 <__printf_chk@plt>
    3b0d:	49 83 fe 07          	cmp    $0x7,%r14
    3b11:	75 d8                	jne    3aeb <main+0x141b>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3b13:	bf 00 04 00 00       	mov    $0x400,%edi
    3b18:	be 08 00 00 00       	mov    $0x8,%esi
    3b1d:	31 ed                	xor    %ebp,%ebp
    3b1f:	e8 dc e8 ff ff       	call   2400 <calloc@plt>
    3b24:	48 89 df             	mov    %rbx,%rdi
    3b27:	49 89 c6             	mov    %rax,%r14
  int datas2_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3b2a:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    3b2e:	45 85 c0             	test   %r8d,%r8d
    3b31:	7e 5b                	jle    3b8e <main+0x14be>
    3b33:	48 8b 17             	mov    (%rdi),%rdx
    3b36:	49 63 f0             	movslq %r8d,%rsi
    3b39:	48 63 c5             	movslq %ebp,%rax
    3b3c:	48 c1 e6 09          	shl    $0x9,%rsi
    3b40:	49 8d 0c c6          	lea    (%r14,%rax,8),%rcx
    3b44:	48 01 d6             	add    %rdx,%rsi
    3b47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b50:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3b57:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    3b5e:	48 83 c1 20          	add    $0x20,%rcx
    3b62:	f3 0f 7e 80 00 01 00 00 	movq   0x100(%rax),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b6a:	f3 0f 7e 08          	movq   (%rax),%xmm1
    3b6e:	0f 16 80 80 01 00 00 	movhps 0x180(%rax),%xmm0
    3b75:	0f 16 88 80 00 00 00 	movhps 0x80(%rax),%xmm1
    3b7c:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    3b80:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3b84:	48 39 f2             	cmp    %rsi,%rdx
    3b87:	75 c7                	jne    3b50 <main+0x1480>
    3b89:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3b8e:	48 81 c7 30 01 00 00 	add    $0x130,%rdi
    3b95:	48 39 7c 24 10       	cmp    %rdi,0x10(%rsp)
    3b9a:	75 8e                	jne    3b2a <main+0x145a>
    3b9c:	48 8d 3d 91 59 00 00 	lea    0x5991(%rip),%rdi        # 9534 <_IO_stdin_used+0x534>
    3ba3:	e8 88 e7 ff ff       	call   2330 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3ba8:	48 8d 35 55 58 00 00 	lea    0x5855(%rip),%rsi        # 9404 <_IO_stdin_used+0x404>
    3baf:	48 8d 3d 96 59 00 00 	lea    0x5996(%rip),%rdi        # 954c <_IO_stdin_used+0x54c>
    3bb6:	e8 45 e9 ff ff       	call   2500 <fopen@plt>
    3bbb:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas2_size; x++) {
    3bbe:	85 ed                	test   %ebp,%ebp
    3bc0:	0f 8e 80 00 00 00    	jle    3c46 <main+0x1576>
    3bc6:	48 8d 05 70 58 00 00 	lea    0x5870(%rip),%rax        # 943d <_IO_stdin_used+0x43d>
    3bcd:	48 63 ed             	movslq %ebp,%rbp
    3bd0:	4c 8d 2d 5a 58 00 00 	lea    0x585a(%rip),%r13        # 9431 <_IO_stdin_used+0x431>
    3bd7:	48 89 04 24          	mov    %rax,(%rsp)
    3bdb:	48 89 d8             	mov    %rbx,%rax
    3bde:	4d 8d 24 ee          	lea    (%r14,%rbp,8),%r12
    3be2:	4c 89 f3             	mov    %r14,%rbx
    3be5:	49 89 c6             	mov    %rax,%r14
    char * c = calloc(250, sizeof(char));
    3be8:	be 01 00 00 00       	mov    $0x1,%esi
    3bed:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3bf2:	48 83 c3 08          	add    $0x8,%rbx
    char * c = calloc(250, sizeof(char));
    3bf6:	e8 05 e8 ff ff       	call   2400 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3bfb:	4c 89 e9             	mov    %r13,%rcx
    3bfe:	ba fa 00 00 00       	mov    $0xfa,%edx
    3c03:	be 01 00 00 00       	mov    $0x1,%esi
    3c08:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3c0b:	48 8b 43 f8          	mov    -0x8(%rbx),%rax
    3c0f:	48 89 ef             	mov    %rbp,%rdi
    3c12:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3c19:	31 c0                	xor    %eax,%eax
    3c1b:	e8 a0 e9 ff ff       	call   25c0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3c20:	48 8b 34 24          	mov    (%rsp),%rsi
    3c24:	48 89 ea             	mov    %rbp,%rdx
    3c27:	31 c0                	xor    %eax,%eax
    3c29:	bf 01 00 00 00       	mov    $0x1,%edi
    3c2e:	e8 7d e8 ff ff       	call   24b0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3c33:	4c 89 fe             	mov    %r15,%rsi
    3c36:	48 89 ef             	mov    %rbp,%rdi
    3c39:	e8 82 e7 ff ff       	call   23c0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3c3e:	4c 39 e3             	cmp    %r12,%rbx
    3c41:	75 a5                	jne    3be8 <main+0x1518>
    3c43:	4c 89 f3             	mov    %r14,%rbx
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    3c46:	4c 89 ff             	mov    %r15,%rdi
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c49:	45 31 ed             	xor    %r13d,%r13d
  fclose(m2);
    3c4c:	45 31 e4             	xor    %r12d,%r12d
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3c4f:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    3c59:	e8 02 e7 ff ff       	call   2360 <fclose@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c5e:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  fclose(m2);
    3c63:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    3c6c:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3c75:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3c7a:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
    3c83:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3c8c:	bf 0a 00 00 00       	mov    $0xa,%edi
    3c91:	45 89 ee             	mov    %r13d,%r14d
    3c94:	e8 77 e6 ff ff       	call   2310 <putchar@plt>
    3c99:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3c9e:	48 8d 35 b0 58 00 00 	lea    0x58b0(%rip),%rsi        # 9555 <_IO_stdin_used+0x555>
    3ca5:	bf 01 00 00 00       	mov    $0x1,%edi
    3caa:	41 83 f6 01          	xor    $0x1,%r14d
    3cae:	48 8b 10             	mov    (%rax),%rdx
    3cb1:	31 c0                	xor    %eax,%eax
    3cb3:	e8 f8 e7 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3cb8:	8b 53 08             	mov    0x8(%rbx),%edx
    3cbb:	85 d2                	test   %edx,%edx
    3cbd:	0f 8e f6 04 00 00    	jle    41b9 <main+0x1ae9>
    3cc3:	48 63 ca             	movslq %edx,%rcx
    3cc6:	48 8b 03             	mov    (%rbx),%rax
      long v = 0;
    3cc9:	31 d2                	xor    %edx,%edx
    3ccb:	48 c1 e1 09          	shl    $0x9,%rcx
    3ccf:	48 01 c1             	add    %rax,%rcx
    3cd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3cd8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3cdf:	48 05 00 02 00 00    	add    $0x200,%rax
    3ce5:	48 39 c8             	cmp    %rcx,%rax
    3ce8:	75 ee                	jne    3cd8 <main+0x1608>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3cea:	4c 89 f0             	mov    %r14,%rax
    3ced:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    3cf2:	48 f7 d8             	neg    %rax
    3cf5:	25 30 01 00 00       	and    $0x130,%eax
    3cfa:	48 01 f8             	add    %rdi,%rax
    3cfd:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3d01:	85 c9                	test   %ecx,%ecx
    3d03:	7e 1d                	jle    3d22 <main+0x1652>
    3d05:	48 8b 40 38          	mov    0x38(%rax),%rax
    3d09:	48 c1 e1 09          	shl    $0x9,%rcx
    3d0d:	48 01 c1             	add    %rax,%rcx
        v += thread_data[other].tasks[n].v;
    3d10:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3d17:	48 05 00 02 00 00    	add    $0x200,%rax
    3d1d:	48 39 c8             	cmp    %rcx,%rax
    3d20:	75 ee                	jne    3d10 <main+0x1640>
    3d22:	48 8d 35 41 58 00 00 	lea    0x5841(%rip),%rsi        # 956a <_IO_stdin_used+0x56a>
    3d29:	bf 01 00 00 00       	mov    $0x1,%edi
    3d2e:	31 c0                	xor    %eax,%eax
    3d30:	e8 7b e7 ff ff       	call   24b0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3d35:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3d3a:	bf 01 00 00 00       	mov    $0x1,%edi
    3d3f:	48 8d 35 0a 5d 00 00 	lea    0x5d0a(%rip),%rsi        # 9a50 <_IO_stdin_used+0xa50>
    3d46:	48 8b 08             	mov    (%rax),%rcx
    3d49:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3d53:	48 f7 e9             	imul   %rcx
    3d56:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3d5a:	31 c0                	xor    %eax,%eax
    3d5c:	48 c1 fa 02          	sar    $0x2,%rdx
    3d60:	48 29 ca             	sub    %rcx,%rdx
    3d63:	e8 48 e7 ff ff       	call   24b0 <__printf_chk@plt>
    3d68:	bf 0a 00 00 00       	mov    $0xa,%edi
    3d6d:	e8 9e e5 ff ff       	call   2310 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3d72:	44 8b 73 08          	mov    0x8(%rbx),%r14d
    3d76:	45 85 f6             	test   %r14d,%r14d
    3d79:	0f 8e 3f 01 00 00    	jle    3ebe <main+0x17ee>
    3d7f:	4c 8b 54 24 28       	mov    0x28(%rsp),%r10
    3d84:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3d89:	44 89 2c 24          	mov    %r13d,(%rsp)
    3d8d:	31 d2                	xor    %edx,%edx
    3d8f:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    3d94:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    3d99:	49 89 dd             	mov    %rbx,%r13
    3d9c:	0f 1f 40 00          	nopl   0x0(%rax)
        total += thread_data[x].tasks[n].n;
    3da0:	49 8b 45 00          	mov    0x0(%r13),%rax
    3da4:	49 89 d1             	mov    %rdx,%r9
    3da7:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    3dac:	89 d3                	mov    %edx,%ebx
    3dae:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    3db2:	45 31 f6             	xor    %r14d,%r14d
        total += thread_data[x].tasks[n].n;
    3db5:	4c 01 c8             	add    %r9,%rax
    3db8:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    3dbd:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
        ingests += thread_data[x].tasks[n].ingest_count;
    3dc4:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
        sends += thread_data[x].tasks[n].sends;
    3dcb:	48 03 b8 80 01 00 00 	add    0x180(%rax),%rdi
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3dd2:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    3dd7:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3ddc:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3de1:	8b 14 24             	mov    (%rsp),%edx
    3de4:	45 89 f0             	mov    %r14d,%r8d
    3de7:	89 d9                	mov    %ebx,%ecx
    3de9:	48 8d 35 87 57 00 00 	lea    0x5787(%rip),%rsi        # 9577 <_IO_stdin_used+0x577>
    3df0:	bf 01 00 00 00       	mov    $0x1,%edi
    3df5:	31 c0                	xor    %eax,%eax
    3df7:	e8 b4 e6 ff ff       	call   24b0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3dfc:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3e01:	4c 89 f0             	mov    %r14,%rax
    3e04:	45 89 f0             	mov    %r14d,%r8d
    3e07:	49 8b 55 00          	mov    0x0(%r13),%rdx
    3e0b:	48 c1 e0 08          	shl    $0x8,%rax
    3e0f:	48 83 ec 08          	sub    $0x8,%rsp
    3e13:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    3e1b:	48 8b 38             	mov    (%rax),%rdi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3e1e:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3e25:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3e2c:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3e33:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e3a:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    3e41:	bf 01 00 00 00       	mov    $0x1,%edi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3e46:	49 01 c4             	add    %rax,%r12
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3e49:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e4c:	49 01 cf             	add    %rcx,%r15
    3e4f:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3e53:	49 01 f4             	add    %rsi,%r12
    3e56:	50                   	push   %rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3e57:	49 01 d7             	add    %rdx,%r15
    3e5a:	8b 54 24 10          	mov    0x10(%rsp),%edx
    3e5e:	89 d9                	mov    %ebx,%ecx
    3e60:	48 8d 35 09 5c 00 00 	lea    0x5c09(%rip),%rsi        # 9a70 <_IO_stdin_used+0xa70>
    3e67:	31 c0                	xor    %eax,%eax
    3e69:	e8 42 e6 ff ff       	call   24b0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3e6e:	41 5a                	pop    %r10
    3e70:	41 5b                	pop    %r11
    3e72:	4d 85 f6             	test   %r14,%r14
    3e75:	75 0a                	jne    3e81 <main+0x17b1>
    3e77:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3e7c:	e9 60 ff ff ff       	jmp    3de1 <main+0x1711>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3e81:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    3e86:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3e8b:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3e90:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3e95:	48 83 c2 01          	add    $0x1,%rdx
    3e99:	41 39 55 08          	cmp    %edx,0x8(%r13)
    3e9d:	0f 8f fd fe ff ff    	jg     3da0 <main+0x16d0>
    3ea3:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    3ea8:	4c 89 eb             	mov    %r13,%rbx
    3eab:	44 8b 2c 24          	mov    (%rsp),%r13d
    3eaf:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    3eb4:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
    3eb9:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3ebe:	45 31 ff             	xor    %r15d,%r15d
    3ec1:	48 83 7b 78 00       	cmpq   $0x0,0x78(%rbx)
    3ec6:	4c 8d 35 c3 5b 00 00 	lea    0x5bc3(%rip),%r14        # 9a90 <_IO_stdin_used+0xa90>
    3ecd:	7e 53                	jle    3f22 <main+0x1852>
    3ecf:	90                   	nop
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3ed0:	48 8b 43 68          	mov    0x68(%rbx),%rax
    3ed4:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    3ed8:	48 83 ec 08          	sub    $0x8,%rsp
    3edc:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3ee1:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3ee5:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3ee9:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3eed:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3ef1:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3ef4:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3ef8:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3efb:	48 f7 e5             	mul    %rbp
    3efe:	8b 49 20             	mov    0x20(%rcx),%ecx
    3f01:	56                   	push   %rsi
    3f02:	31 c0                	xor    %eax,%eax
    3f04:	4c 89 f6             	mov    %r14,%rsi
    3f07:	48 c1 ea 12          	shr    $0x12,%rdx
    3f0b:	49 89 d1             	mov    %rdx,%r9
    3f0e:	ba 02 00 00 00       	mov    $0x2,%edx
    3f13:	e8 98 e5 ff ff       	call   24b0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3f18:	41 58                	pop    %r8
    3f1a:	41 59                	pop    %r9
    3f1c:	4c 39 7b 78          	cmp    %r15,0x78(%rbx)
    3f20:	7f ae                	jg     3ed0 <main+0x1800>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3f22:	8b 93 94 00 00 00    	mov    0x94(%rbx),%edx
    3f28:	85 d2                	test   %edx,%edx
    3f2a:	0f 8e 0a 01 00 00    	jle    403a <main+0x196a>
    3f30:	4c 89 64 24 50       	mov    %r12,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3f35:	48 8b 7b 18          	mov    0x18(%rbx),%rdi
    3f39:	45 31 ff             	xor    %r15d,%r15d
    3f3c:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    3f41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3f48:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    3f4c:	45 89 fd             	mov    %r15d,%r13d
    3f4f:	4e 8d 24 fd 00 00 00 00 	lea    0x0(,%r15,8),%r12
    3f57:	8b 30                	mov    (%rax),%esi
    3f59:	85 f6                	test   %esi,%esi
    3f5b:	0f 8e c2 00 00 00    	jle    4023 <main+0x1953>
    3f61:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3f66:	31 d2                	xor    %edx,%edx
    3f68:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3f6c:	49 89 f8             	mov    %rdi,%r8
    3f6f:	48 89 d7             	mov    %rdx,%rdi
    3f72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3f78:	4c 8d 1c bf          	lea    (%rdi,%rdi,4),%r11
    3f7c:	45 31 ff             	xor    %r15d,%r15d
    3f7f:	4e 8d 34 dd 00 00 00 00 	lea    0x0(,%r11,8),%r14
    3f87:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    3f8b:	8b 50 1c             	mov    0x1c(%rax),%edx
    3f8e:	85 d2                	test   %edx,%edx
    3f90:	7e 77                	jle    4009 <main+0x1939>
    3f92:	48 89 3c 24          	mov    %rdi,(%rsp)
    3f96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3fa0:	4c 89 f9             	mov    %r15,%rcx
    3fa3:	48 83 ec 08          	sub    $0x8,%rsp
    3fa7:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3fac:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3fb0:	48 c1 e1 05          	shl    $0x5,%rcx
    3fb4:	48 03 48 10          	add    0x10(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3fb8:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3fbc:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3fc0:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3fc3:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3fc7:	4c 2b 01             	sub    (%rcx),%r8
    3fca:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3fcb:	48 f7 e5             	mul    %rbp
    3fce:	44 89 e9             	mov    %r13d,%ecx
    3fd1:	48 8d 35 08 5b 00 00 	lea    0x5b08(%rip),%rsi        # 9ae0 <_IO_stdin_used+0xae0>
    3fd8:	31 c0                	xor    %eax,%eax
    3fda:	48 c1 ea 12          	shr    $0x12,%rdx
    3fde:	49 89 d1             	mov    %rdx,%r9
    3fe1:	ba 02 00 00 00       	mov    $0x2,%edx
    3fe6:	e8 c5 e4 ff ff       	call   24b0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3feb:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    3fef:	5e                   	pop    %rsi
    3ff0:	5f                   	pop    %rdi
    3ff1:	4b 8b 14 20          	mov    (%r8,%r12,1),%rdx
    3ff5:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    3ff9:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    3ffd:	44 39 78 1c          	cmp    %r15d,0x1c(%rax)
    4001:	7f 9d                	jg     3fa0 <main+0x18d0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4003:	48 8b 3c 24          	mov    (%rsp),%rdi
    4007:	8b 32                	mov    (%rdx),%esi
    4009:	48 83 c7 01          	add    $0x1,%rdi
    400d:	39 fe                	cmp    %edi,%esi
    400f:	0f 8f 63 ff ff ff    	jg     3f78 <main+0x18a8>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4015:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    401a:	8b 93 94 00 00 00    	mov    0x94(%rbx),%edx
    4020:	4c 89 c7             	mov    %r8,%rdi
    4023:	49 83 c7 01          	add    $0x1,%r15
    4027:	44 39 fa             	cmp    %r15d,%edx
    402a:	0f 8f 18 ff ff ff    	jg     3f48 <main+0x1878>
    4030:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    4035:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    403a:	48 83 44 24 48 18    	addq   $0x18,0x48(%rsp)
    4040:	48 81 c3 30 01 00 00 	add    $0x130,%rbx
    4047:	45 85 ed             	test   %r13d,%r13d
    404a:	75 0a                	jne    4056 <main+0x1986>
    404c:	44 8b 6c 24 40       	mov    0x40(%rsp),%r13d
    4051:	e9 36 fc ff ff       	jmp    3c8c <main+0x15bc>
    4056:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    405b:	48 8d 35 25 55 00 00 	lea    0x5525(%rip),%rsi        # 9587 <_IO_stdin_used+0x587>
    4062:	bf 01 00 00 00       	mov    $0x1,%edi
    4067:	31 c0                	xor    %eax,%eax
    4069:	4c 89 f2             	mov    %r14,%rdx
    406c:	e8 3f e4 ff ff       	call   24b0 <__printf_chk@plt>
    4071:	bf 0a 00 00 00       	mov    $0xa,%edi
    4076:	e8 95 e2 ff ff       	call   2310 <putchar@plt>
    407b:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
    4080:	48 8d 35 b1 5a 00 00 	lea    0x5ab1(%rip),%rsi        # 9b38 <_IO_stdin_used+0xb38>
    4087:	31 c0                	xor    %eax,%eax
    4089:	bf 01 00 00 00       	mov    $0x1,%edi
    408e:	48 8b 53 08          	mov    0x8(%rbx),%rdx
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    4092:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    409c:	e8 0f e4 ff ff       	call   24b0 <__printf_chk@plt>
    40a1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    40a6:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    40ab:	48 8d 35 ae 5a 00 00 	lea    0x5aae(%rip),%rsi        # 9b60 <_IO_stdin_used+0xb60>
    40b2:	48 f7 eb             	imul   %rbx
    40b5:	48 c1 ff 3f          	sar    $0x3f,%rdi
    40b9:	31 c0                	xor    %eax,%eax
    40bb:	48 c1 fa 02          	sar    $0x2,%rdx
    40bf:	48 29 fa             	sub    %rdi,%rdx
    40c2:	bf 01 00 00 00       	mov    $0x1,%edi
    40c7:	e8 e4 e3 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    40cc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    40d1:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    40d6:	48 8d 35 b3 5a 00 00 	lea    0x5ab3(%rip),%rsi        # 9b90 <_IO_stdin_used+0xb90>
    40dd:	48 f7 eb             	imul   %rbx
    40e0:	48 c1 ff 3f          	sar    $0x3f,%rdi
    40e4:	31 c0                	xor    %eax,%eax
    40e6:	48 c1 fa 02          	sar    $0x2,%rdx
    40ea:	48 29 fa             	sub    %rdi,%rdx
    40ed:	bf 01 00 00 00       	mov    $0x1,%edi
    40f2:	e8 b9 e3 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    40f7:	4c 89 f0             	mov    %r14,%rax
    40fa:	bf 01 00 00 00       	mov    $0x1,%edi
    40ff:	48 8d 35 ba 5a 00 00 	lea    0x5aba(%rip),%rsi        # 9bc0 <_IO_stdin_used+0xbc0>
    4106:	48 f7 eb             	imul   %rbx
    4109:	4c 89 f0             	mov    %r14,%rax
    410c:	48 c1 f8 3f          	sar    $0x3f,%rax
    4110:	48 c1 fa 02          	sar    $0x2,%rdx
    4114:	48 29 c2             	sub    %rax,%rdx
    4117:	31 c0                	xor    %eax,%eax
    4119:	e8 92 e3 ff ff       	call   24b0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    411e:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4123:	bf 01 00 00 00       	mov    $0x1,%edi
    4128:	48 8d 35 6c 54 00 00 	lea    0x546c(%rip),%rsi        # 959b <_IO_stdin_used+0x59b>
    412f:	48 f7 eb             	imul   %rbx
    4132:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4137:	48 c1 f8 3f          	sar    $0x3f,%rax
    413b:	48 c1 fa 02          	sar    $0x2,%rdx
    413f:	48 29 c2             	sub    %rax,%rdx
    4142:	31 c0                	xor    %eax,%eax
    4144:	48 89 d5             	mov    %rdx,%rbp
    4147:	e8 64 e3 ff ff       	call   24b0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
    414c:	4c 89 e0             	mov    %r12,%rax
    414f:	bf 01 00 00 00       	mov    $0x1,%edi
    4154:	48 8d 35 85 5a 00 00 	lea    0x5a85(%rip),%rsi        # 9be0 <_IO_stdin_used+0xbe0>
    415b:	48 f7 eb             	imul   %rbx
    415e:	4c 89 e0             	mov    %r12,%rax
    4161:	48 c1 f8 3f          	sar    $0x3f,%rax
    4165:	48 89 d3             	mov    %rdx,%rbx
    4168:	48 c1 fb 02          	sar    $0x2,%rbx
    416c:	48 29 c3             	sub    %rax,%rbx
    416f:	31 c0                	xor    %eax,%eax
    4171:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    4174:	48 29 eb             	sub    %rbp,%rbx
    4177:	e8 34 e3 ff ff       	call   24b0 <__printf_chk@plt>
    417c:	31 c0                	xor    %eax,%eax
    417e:	48 89 da             	mov    %rbx,%rdx
    4181:	bf 01 00 00 00       	mov    $0x1,%edi
    4186:	48 8d 35 2a 54 00 00 	lea    0x542a(%rip),%rsi        # 95b7 <_IO_stdin_used+0x5b7>
    418d:	e8 1e e3 ff ff       	call   24b0 <__printf_chk@plt>
  return 0;

}
    4192:	48 8b 84 24 b8 00 00 00 	mov    0xb8(%rsp),%rax
    419a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    41a3:	75 25                	jne    41ca <main+0x1afa>
    41a5:	48 81 c4 c8 00 00 00 	add    $0xc8,%rsp
    41ac:	31 c0                	xor    %eax,%eax
    41ae:	5b                   	pop    %rbx
    41af:	5d                   	pop    %rbp
    41b0:	41 5c                	pop    %r12
    41b2:	41 5d                	pop    %r13
    41b4:	41 5e                	pop    %r14
    41b6:	41 5f                	pop    %r15
    41b8:	c3                   	ret
      long v = 0;
    41b9:	31 d2                	xor    %edx,%edx
    41bb:	e9 2a fb ff ff       	jmp    3cea <main+0x161a>
            exit(1);
    41c0:	bf 01 00 00 00       	mov    $0x1,%edi
    41c5:	e8 56 e3 ff ff       	call   2520 <exit@plt>
}
    41ca:	e8 b1 e1 ff ff       	call   2380 <__stack_chk_fail@plt>
    41cf:	90                   	nop

00000000000041d0 <_start>:
    41d0:	f3 0f 1e fa          	endbr64
    41d4:	31 ed                	xor    %ebp,%ebp
    41d6:	49 89 d1             	mov    %rdx,%r9
    41d9:	5e                   	pop    %rsi
    41da:	48 89 e2             	mov    %rsp,%rdx
    41dd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    41e1:	50                   	push   %rax
    41e2:	54                   	push   %rsp
    41e3:	45 31 c0             	xor    %r8d,%r8d
    41e6:	31 c9                	xor    %ecx,%ecx
    41e8:	48 8d 3d e1 e4 ff ff 	lea    -0x1b1f(%rip),%rdi        # 26d0 <main>
    41ef:	ff 15 e3 7d 00 00    	call   *0x7de3(%rip)        # bfd8 <__libc_start_main@GLIBC_2.34>
    41f5:	f4                   	hlt
    41f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004200 <deregister_tm_clones>:
    4200:	48 8d 3d 19 7e 00 00 	lea    0x7e19(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4207:	48 8d 05 12 7e 00 00 	lea    0x7e12(%rip),%rax        # c020 <stderr@GLIBC_2.2.5>
    420e:	48 39 f8             	cmp    %rdi,%rax
    4211:	74 15                	je     4228 <deregister_tm_clones+0x28>
    4213:	48 8b 05 c6 7d 00 00 	mov    0x7dc6(%rip),%rax        # bfe0 <_ITM_deregisterTMCloneTable@Base>
    421a:	48 85 c0             	test   %rax,%rax
    421d:	74 09                	je     4228 <deregister_tm_clones+0x28>
    421f:	ff e0                	jmp    *%rax
    4221:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4228:	c3                   	ret
    4229:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004230 <register_tm_clones>:
    4230:	48 8d 3d e9 7d 00 00 	lea    0x7de9(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4237:	48 8d 35 e2 7d 00 00 	lea    0x7de2(%rip),%rsi        # c020 <stderr@GLIBC_2.2.5>
    423e:	48 29 fe             	sub    %rdi,%rsi
    4241:	48 89 f0             	mov    %rsi,%rax
    4244:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4248:	48 c1 f8 03          	sar    $0x3,%rax
    424c:	48 01 c6             	add    %rax,%rsi
    424f:	48 d1 fe             	sar    %rsi
    4252:	74 14                	je     4268 <register_tm_clones+0x38>
    4254:	48 8b 05 95 7d 00 00 	mov    0x7d95(%rip),%rax        # bff0 <_ITM_registerTMCloneTable@Base>
    425b:	48 85 c0             	test   %rax,%rax
    425e:	74 08                	je     4268 <register_tm_clones+0x38>
    4260:	ff e0                	jmp    *%rax
    4262:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4268:	c3                   	ret
    4269:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004270 <__do_global_dtors_aux>:
    4270:	f3 0f 1e fa          	endbr64
    4274:	80 3d ad 7d 00 00 00 	cmpb   $0x0,0x7dad(%rip)        # c028 <completed.0>
    427b:	75 2b                	jne    42a8 <__do_global_dtors_aux+0x38>
    427d:	55                   	push   %rbp
    427e:	48 83 3d 72 7d 00 00 00 	cmpq   $0x0,0x7d72(%rip)        # bff8 <__cxa_finalize@GLIBC_2.2.5>
    4286:	48 89 e5             	mov    %rsp,%rbp
    4289:	74 0c                	je     4297 <__do_global_dtors_aux+0x27>
    428b:	48 8b 3d 76 7d 00 00 	mov    0x7d76(%rip),%rdi        # c008 <__dso_handle>
    4292:	e8 69 e0 ff ff       	call   2300 <__cxa_finalize@plt>
    4297:	e8 64 ff ff ff       	call   4200 <deregister_tm_clones>
    429c:	c6 05 85 7d 00 00 01 	movb   $0x1,0x7d85(%rip)        # c028 <completed.0>
    42a3:	5d                   	pop    %rbp
    42a4:	c3                   	ret
    42a5:	0f 1f 00             	nopl   (%rax)
    42a8:	c3                   	ret
    42a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000042b0 <frame_dummy>:
    42b0:	f3 0f 1e fa          	endbr64
    42b4:	e9 77 ff ff ff       	jmp    4230 <register_tm_clones>
    42b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000042c0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    42c0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    42c4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    42cb:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    42cf:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    42d7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    42db:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    42df:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    42e6:	48 85 c9             	test   %rcx,%rcx
    42e9:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    42f0:	48 0f 4f d6          	cmovg  %rsi,%rdx
    42f4:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    42f8:	31 c0                	xor    %eax,%eax
    42fa:	c3                   	ret
    42fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004300 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4300:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4304:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    430b:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    for (int x = 0 ; x < data->task_count ; x++) {
    4312:	85 c9                	test   %ecx,%ecx
    4314:	7e 48                	jle    435e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4316:	48 63 97 30 01 00 00 	movslq 0x130(%rdi),%rdx
    431d:	49 8b 40 18          	mov    0x18(%r8),%rax
    4321:	48 c1 e1 09          	shl    $0x9,%rcx
      data->thread->tasks[x].available = 1; 
    4325:	49 8b 70 38          	mov    0x38(%r8),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4329:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    432d:	48 8b 50 38          	mov    0x38(%rax),%rdx
      data->thread->tasks[x].available = 1; 
    4331:	31 c0                	xor    %eax,%eax
    4333:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4338:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4340:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4348:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    4353:	48 05 00 02 00 00    	add    $0x200,%rax
    4359:	48 39 c1             	cmp    %rax,%rcx
    435c:	75 da                	jne    4338 <barriered_reset+0x38>
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    435e:	49 8b 88 00 01 00 00 	mov    0x100(%r8),%rcx
    4365:	8b 01                	mov    (%rcx),%eax
    4367:	83 f8 ff             	cmp    $0xffffffff,%eax
    436a:	74 0e                	je     437a <barriered_reset+0x7a>
    436c:	41 8b b8 d0 00 00 00 	mov    0xd0(%r8),%edi
    4373:	8d 57 ff             	lea    -0x1(%rdi),%edx
    4376:	39 d0                	cmp    %edx,%eax
    4378:	74 06                	je     4380 <barriered_reset+0x80>
}
    437a:	31 c0                	xor    %eax,%eax
    437c:	c3                   	ret
    437d:	0f 1f 00             	nopl   (%rax)
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    4380:	41 83 78 04 01       	cmpl   $0x1,0x4(%r8)
    4385:	75 f3                	jne    437a <barriered_reset+0x7a>
    data->thread->group_data->arrived++;
    4387:	49 8b 80 e8 00 00 00 	mov    0xe8(%r8),%rax
    438e:	83 00 01             	addl   $0x1,(%rax)
    data->thread->global->request_group_sync = -1;
    4391:	c7 01 ff ff ff ff    	movl   $0xffffffff,(%rcx)
    4397:	eb e1                	jmp    437a <barriered_reset+0x7a>
    4399:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000043a0 <external_thread>:
void * external_thread(void *arg) {
    43a0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    43a4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    43a8:	0f 85 ec 00 00 00    	jne    449a <external_thread+0xfa>
void * external_thread(void *arg) {
    43ae:	41 57                	push   %r15
    43b0:	4c 8d 3d 4d 4c 00 00 	lea    0x4c4d(%rip),%r15        # 9004 <_IO_stdin_used+0x4>
    43b7:	41 56                	push   %r14
    43b9:	49 89 fe             	mov    %rdi,%r14
    43bc:	41 55                	push   %r13
    43be:	41 54                	push   %r12
    43c0:	55                   	push   %rbp
    43c1:	53                   	push   %rbx
    43c2:	48 83 ec 08          	sub    $0x8,%rsp
    43c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int b = 0; b < data->buffers_count; b++) {
    43d0:	41 8b 8e cc 00 00 00 	mov    0xcc(%r14),%ecx
    43d7:	85 c9                	test   %ecx,%ecx
    43d9:	7e 55                	jle    4430 <external_thread+0x90>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    43db:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    43df:	45 31 ed             	xor    %r13d,%r13d
    43e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    43e8:	4e 8d 24 ed 00 00 00 00 	lea    0x0(,%r13,8),%r12
    43f0:	31 db                	xor    %ebx,%ebx
    43f2:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    43f6:	48 8b 06             	mov    (%rsi),%rax
    43f9:	8b 10                	mov    (%rax),%edx
    43fb:	85 d2                	test   %edx,%edx
    43fd:	7e 28                	jle    4427 <external_thread+0x87>
    43ff:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    4403:	48 8d 2c 9b          	lea    (%rbx,%rbx,4),%rbp
    4407:	48 c1 e5 03          	shl    $0x3,%rbp
    440b:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    440f:	44 8b 40 08          	mov    0x8(%rax),%r8d
    4413:	45 85 c0             	test   %r8d,%r8d
    4416:	74 38                	je     4450 <external_thread+0xb0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4418:	48 83 c3 01          	add    $0x1,%rbx
    441c:	39 da                	cmp    %ebx,%edx
    441e:	7f e3                	jg     4403 <external_thread+0x63>
    for (int b = 0; b < data->buffers_count; b++) {
    4420:	41 8b 8e cc 00 00 00 	mov    0xcc(%r14),%ecx
    4427:	49 83 c5 01          	add    $0x1,%r13
    442b:	44 39 e9             	cmp    %r13d,%ecx
    442e:	7f b8                	jg     43e8 <external_thread+0x48>
  while (data->running == 1) {
    4430:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    4435:	74 99                	je     43d0 <external_thread+0x30>
}
    4437:	48 83 c4 08          	add    $0x8,%rsp
    443b:	31 c0                	xor    %eax,%eax
    443d:	5b                   	pop    %rbx
    443e:	5d                   	pop    %rbp
    443f:	41 5c                	pop    %r12
    4441:	41 5d                	pop    %r13
    4443:	41 5e                	pop    %r14
    4445:	41 5f                	pop    %r15
    4447:	c3                   	ret
    4448:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    4450:	4c 89 38             	mov    %r15,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    4453:	48 8b 06             	mov    (%rsi),%rax
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4456:	48 83 c3 01          	add    $0x1,%rbx
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    445a:	48 8b 78 08          	mov    0x8(%rax),%rdi
    445e:	48 01 ef             	add    %rbp,%rdi
    4461:	48 63 77 1c          	movslq 0x1c(%rdi),%rsi
    4465:	48 c1 e6 05          	shl    $0x5,%rsi
    4469:	48 03 77 10          	add    0x10(%rdi),%rsi
    446d:	bf 04 00 00 00       	mov    $0x4,%edi
    4472:	e8 d9 de ff ff       	call   2350 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4477:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    447b:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    447f:	48 8b 06             	mov    (%rsi),%rax
    4482:	48 8b 50 08          	mov    0x8(%rax),%rdx
    4486:	c7 44 2a 08 01 00 00 00 	movl   $0x1,0x8(%rdx,%rbp,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
    448e:	8b 10                	mov    (%rax),%edx
    4490:	39 da                	cmp    %ebx,%edx
    4492:	0f 8f 67 ff ff ff    	jg     43ff <external_thread+0x5f>
    4498:	eb 86                	jmp    4420 <external_thread+0x80>
}
    449a:	31 c0                	xor    %eax,%eax
    449c:	c3                   	ret
    449d:	0f 1f 00             	nopl   (%rax)

00000000000044a0 <timer_thread>:
void* timer_thread(void *arg) {
    44a0:	f3 0f 1e fa          	endbr64
    44a4:	41 57                	push   %r15
    44a6:	48 8d 35 63 4b 00 00 	lea    0x4b63(%rip),%rsi        # 9010 <_IO_stdin_used+0x10>
    44ad:	49 89 ff             	mov    %rdi,%r15
    44b0:	41 56                	push   %r14
    44b2:	41 55                	push   %r13
    44b4:	41 54                	push   %r12
    44b6:	55                   	push   %rbp
    44b7:	53                   	push   %rbx
    44b8:	48 83 ec 58          	sub    $0x58,%rsp
    44bc:	8b 57 04             	mov    0x4(%rdi),%edx
    44bf:	bf 01 00 00 00       	mov    $0x1,%edi
    44c4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    44cd:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    44d2:	31 c0                	xor    %eax,%eax
    44d4:	e8 d7 df ff ff       	call   24b0 <__printf_chk@plt>
  struct timespec preempt = {
    44d9:	66 0f 6f 05 1f 59 00 00 	movdqa 0x591f(%rip),%xmm0        # 9e00 <_IO_stdin_used+0xe00>
    44e1:	ba 10 27 00 00       	mov    $0x2710,%edx
    44e6:	31 c0                	xor    %eax,%eax
    44e8:	48 8d 35 33 4b 00 00 	lea    0x4b33(%rip),%rsi        # 9022 <_IO_stdin_used+0x22>
    44ef:	bf 01 00 00 00       	mov    $0x1,%edi
    44f4:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    44f9:	e8 b2 df ff ff       	call   24b0 <__printf_chk@plt>
  while (data->running && n < times) {
    44fe:	41 8b 47 44          	mov    0x44(%r15),%eax
    4502:	89 c3                	mov    %eax,%ebx
    4504:	85 c0                	test   %eax,%eax
    4506:	0f 84 97 00 00 00    	je     45a3 <timer_thread+0x103>
  int n = 0;
    450c:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    450f:	31 db                	xor    %ebx,%ebx
    4511:	49 89 e5             	mov    %rsp,%r13
    y++;
    4514:	31 ed                	xor    %ebp,%ebp
    4516:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    nanosleep(&preempt , &rem2);
    451b:	4c 89 e7             	mov    %r12,%rdi
    451e:	4c 89 ee             	mov    %r13,%rsi
    n++;
    4521:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    4525:	e8 76 de ff ff       	call   23a0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    452a:	49 63 47 30          	movslq 0x30(%r15),%rax
    y++;
    452e:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4531:	85 c0                	test   %eax,%eax
    4533:	7e 4a                	jle    457f <timer_thread+0xdf>
    4535:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4539:	4c 63 c3             	movslq %ebx,%r8
    453c:	49 c1 e0 09          	shl    $0x9,%r8
    4540:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4544:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4548:	48 8b 19             	mov    (%rcx),%rbx
    454b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    454d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4551:	99                   	cltd
    4552:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4555:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4559:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    455c:	48 63 d2             	movslq %edx,%rdx
    455f:	48 c1 e2 09          	shl    $0x9,%rdx
    4563:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    456e:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    457a:	49 39 c9             	cmp    %rcx,%r9
    457d:	75 c9                	jne    4548 <timer_thread+0xa8>
    if (y >= data->threads[0]->task_count) {
    457f:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
    4583:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    y++;
    4587:	89 fb                	mov    %edi,%ebx
    if (y >= data->threads[0]->task_count) {
    4589:	48 8b 00             	mov    (%rax),%rax
    y++;
    458c:	39 78 40             	cmp    %edi,0x40(%rax)
    458f:	0f 4e dd             	cmovle %ebp,%ebx
  while (data->running && n < times) {
    4592:	85 c9                	test   %ecx,%ecx
    4594:	74 0d                	je     45a3 <timer_thread+0x103>
    4596:	41 81 fe 10 27 00 00 	cmp    $0x2710,%r14d
    459d:	0f 85 78 ff ff ff    	jne    451b <timer_thread+0x7b>
    45a3:	48 8d 3d 8e 4a 00 00 	lea    0x4a8e(%rip),%rdi        # 9038 <_IO_stdin_used+0x38>
    45aa:	e8 81 dd ff ff       	call   2330 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    45af:	49 63 57 30          	movslq 0x30(%r15),%rdx
    45b3:	85 d2                	test   %edx,%edx
    45b5:	7e 6e                	jle    4625 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    45b7:	49 63 47 40          	movslq 0x40(%r15),%rax
    45bb:	85 c0                	test   %eax,%eax
    45bd:	7e 66                	jle    4625 <timer_thread+0x185>
    45bf:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    45c3:	4d 8b 47 18          	mov    0x18(%r15),%r8
    45c7:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    45cf:	31 c9                	xor    %ecx,%ecx
    45d1:	48 89 c6             	mov    %rax,%rsi
    45d4:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    45d8:	48 8b 40 38          	mov    0x38(%rax),%rax
    45dc:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    45e0:	f7 c6 00 02 00 00    	test   $0x200,%esi
    45e6:	74 18                	je     4600 <timer_thread+0x160>
    45e8:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    45f2:	48 05 00 02 00 00    	add    $0x200,%rax
    45f8:	48 39 c2             	cmp    %rax,%rdx
    45fb:	74 1f                	je     461c <timer_thread+0x17c>
    45fd:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->tasks[y].sending = 0;
    4600:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    460a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4610:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4617:	48 39 c2             	cmp    %rax,%rdx
    461a:	75 e4                	jne    4600 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    461c:	48 83 c1 08          	add    $0x8,%rcx
    4620:	48 39 cf             	cmp    %rcx,%rdi
    4623:	75 af                	jne    45d4 <timer_thread+0x134>
  struct timespec drain = {
    4625:	66 0f 6f 05 e3 57 00 00 	movdqa 0x57e3(%rip),%xmm0        # 9e10 <_IO_stdin_used+0xe10>
    462d:	41 89 dc             	mov    %ebx,%r12d
    4630:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4635:	49 63 47 28          	movslq 0x28(%r15),%rax
    y++;
    4639:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    463e:	85 c0                	test   %eax,%eax
    4640:	7e 49                	jle    468b <timer_thread+0x1eb>
    4642:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4646:	49 63 ec             	movslq %r12d,%rbp
    4649:	48 c1 e5 09          	shl    $0x9,%rbp
    464d:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4651:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4658:	48 8b 19             	mov    (%rcx),%rbx
    465b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    465d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4661:	99                   	cltd
    4662:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4665:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4669:	48 63 d2             	movslq %edx,%rdx
    466c:	48 c1 e2 09          	shl    $0x9,%rdx
    4670:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    467b:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4686:	49 39 c8             	cmp    %rcx,%r8
    4689:	75 cd                	jne    4658 <timer_thread+0x1b8>
    if (y >= data->threads[0]->task_count) {
    468b:	49 8b 77 18          	mov    0x18(%r15),%rsi
    y++;
    468f:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    4692:	48 8b 06             	mov    (%rsi),%rax
    y++;
    4695:	39 78 40             	cmp    %edi,0x40(%rax)
    4698:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    469c:	41 8b 7f 30          	mov    0x30(%r15),%edi
    46a0:	85 ff                	test   %edi,%edi
    46a2:	0f 8e ac 01 00 00    	jle    4854 <timer_thread+0x3b4>
    46a8:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    46ab:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    46b1:	4c 89 f5             	mov    %r14,%rbp
    46b4:	0f 1f 40 00          	nopl   0x0(%rax)
    46b8:	89 eb                	mov    %ebp,%ebx
      for (int y = 0 ; y < 2 ; y++) {
    46ba:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    46c2:	45 31 f6             	xor    %r14d,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    46c5:	85 ff                	test   %edi,%edi
    46c7:	7e 7f                	jle    4748 <timer_thread+0x2a8>
    46c9:	4c 89 f6             	mov    %r14,%rsi
    46cc:	48 63 cf             	movslq %edi,%rcx
    46cf:	45 31 c0             	xor    %r8d,%r8d
    46d2:	48 c1 e6 09          	shl    $0x9,%rsi
    46d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (x == k) { continue; }
    46e0:	41 39 e8             	cmp    %ebp,%r8d
    46e3:	74 45                	je     472a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    46e5:	49 8b 47 18          	mov    0x18(%r15),%rax
    46e9:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    46ed:	48 8b 50 38          	mov    0x38(%rax),%rdx
    46f1:	4c 89 c0             	mov    %r8,%rax
    46f4:	48 c1 e0 08          	shl    $0x8,%rax
    46f8:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4700:	48 8b 10             	mov    (%rax),%rdx
    4703:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    470a:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4711:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4718:	4d 85 c9             	test   %r9,%r9
    471b:	0f 8f 97 00 00 00    	jg     47b8 <timer_thread+0x318>
    4721:	4d 85 db             	test   %r11,%r11
    4724:	0f 8f 8e 00 00 00    	jg     47b8 <timer_thread+0x318>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    472a:	49 83 c0 01          	add    $0x1,%r8
    472e:	4c 39 c1             	cmp    %r8,%rcx
    4731:	75 ad                	jne    46e0 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    4733:	49 83 fe 01          	cmp    $0x1,%r14
    4737:	74 0f                	je     4748 <timer_thread+0x2a8>
    4739:	41 be 01 00 00 00    	mov    $0x1,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    473f:	85 ff                	test   %edi,%edi
    4741:	7f 86                	jg     46c9 <timer_thread+0x229>
    4743:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4748:	48 83 c5 01          	add    $0x1,%rbp
    474c:	39 ef                	cmp    %ebp,%edi
    474e:	0f 8f 64 ff ff ff    	jg     46b8 <timer_thread+0x218>
    4754:	44 89 d5             	mov    %r10d,%ebp
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4757:	85 ff                	test   %edi,%edi
    4759:	7e 3b                	jle    4796 <timer_thread+0x2f6>
    475b:	31 db                	xor    %ebx,%ebx
    int all_waited = 1;
    475d:	bf 01 00 00 00       	mov    $0x1,%edi
    4762:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4766:	41 8b 57 40          	mov    0x40(%r15),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    476a:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    476e:	48 8b 40 38          	mov    0x38(%rax),%rax
    4772:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    4778:	39 d1                	cmp    %edx,%ecx
    477a:	0f 8c a8 00 00 00    	jl     4828 <timer_thread+0x388>
    4780:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    4786:	39 d0                	cmp    %edx,%eax
    4788:	7c 6e                	jl     47f8 <timer_thread+0x358>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    478a:	48 83 c3 01          	add    $0x1,%rbx
    478e:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4792:	7f d6                	jg     476a <timer_thread+0x2ca>
    4794:	21 fd                	and    %edi,%ebp
    if (all_empty == 1 && all_waited == 1) {
    4796:	85 ed                	test   %ebp,%ebp
    4798:	0f 85 b6 00 00 00    	jne    4854 <timer_thread+0x3b4>
      nanosleep(&drain , &drainrem);
    479e:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    47a3:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    47a8:	e8 f3 db ff ff       	call   23a0 <nanosleep@plt>
    47ad:	e9 83 fe ff ff       	jmp    4635 <timer_thread+0x195>
    47b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    47b8:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    47be:	48 83 ec 08          	sub    $0x8,%rsp
    47c2:	bf 01 00 00 00       	mov    $0x1,%edi
    47c7:	44 89 f1             	mov    %r14d,%ecx
    47ca:	48 8d 35 8c 48 00 00 	lea    0x488c(%rip),%rsi        # 905d <_IO_stdin_used+0x5d>
    47d1:	50                   	push   %rax
    47d2:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    47d8:	89 da                	mov    %ebx,%edx
    47da:	50                   	push   %rax
    47db:	31 c0                	xor    %eax,%eax
    47dd:	41 53                	push   %r11
    47df:	e8 cc dc ff ff       	call   24b0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    47e4:	41 8b 7f 30          	mov    0x30(%r15),%edi
    47e8:	48 83 c4 20          	add    $0x20,%rsp
            all_empty = 0;
    47ec:	45 31 d2             	xor    %r10d,%r10d
    47ef:	e9 3f ff ff ff       	jmp    4733 <timer_thread+0x293>
    47f4:	0f 1f 40 00          	nopl   0x0(%rax)
    47f8:	89 c2                	mov    %eax,%edx
    47fa:	bf 01 00 00 00       	mov    $0x1,%edi
    47ff:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4801:	48 83 c3 01          	add    $0x1,%rbx
    4805:	48 8d 35 1c 4b 00 00 	lea    0x4b1c(%rip),%rsi        # 9328 <_IO_stdin_used+0x328>
    480c:	e8 9f dc ff ff       	call   24b0 <__printf_chk@plt>
          all_waited = 0; 
    4811:	31 ff                	xor    %edi,%edi
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4813:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4817:	0f 8f 45 ff ff ff    	jg     4762 <timer_thread+0x2c2>
    481d:	e9 72 ff ff ff       	jmp    4794 <timer_thread+0x2f4>
    4822:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4828:	89 ca                	mov    %ecx,%edx
    482a:	48 8d 35 f7 4a 00 00 	lea    0x4af7(%rip),%rsi        # 9328 <_IO_stdin_used+0x328>
    4831:	bf 01 00 00 00       	mov    $0x1,%edi
    4836:	31 c0                	xor    %eax,%eax
    4838:	e8 73 dc ff ff       	call   24b0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    483d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4841:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    4845:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4847:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    484b:	48 8b 40 38          	mov    0x38(%rax),%rax
    484f:	e9 2c ff ff ff       	jmp    4780 <timer_thread+0x2e0>
    4854:	48 8d 3d f9 47 00 00 	lea    0x47f9(%rip),%rdi        # 9054 <_IO_stdin_used+0x54>
    485b:	e8 d0 da ff ff       	call   2330 <puts@plt>
  while (data->running) {
    4860:	41 8b 57 44          	mov    0x44(%r15),%edx
    4864:	85 d2                	test   %edx,%edx
    4866:	0f 84 e8 00 00 00    	je     4954 <timer_thread+0x4b4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    486c:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4870:	31 db                	xor    %ebx,%ebx
    4872:	48 8d 2d 01 48 00 00 	lea    0x4801(%rip),%rbp        # 907a <_IO_stdin_used+0x7a>
    4879:	4c 8d 25 15 48 00 00 	lea    0x4815(%rip),%r12        # 9095 <_IO_stdin_used+0x95>
    4880:	85 c0                	test   %eax,%eax
    4882:	7e 38                	jle    48bc <timer_thread+0x41c>
    4884:	0f 1f 40 00          	nopl   0x0(%rax)
    4888:	31 c0                	xor    %eax,%eax
    488a:	89 da                	mov    %ebx,%edx
    488c:	48 89 ee             	mov    %rbp,%rsi
    488f:	bf 01 00 00 00       	mov    $0x1,%edi
    4894:	e8 17 dc ff ff       	call   24b0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4899:	49 8b 47 18          	mov    0x18(%r15),%rax
    489d:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    48a1:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    48a5:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    48ac:	0f 84 cf 00 00 00    	je     4981 <timer_thread+0x4e1>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    48b2:	48 83 c3 01          	add    $0x1,%rbx
    48b6:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    48ba:	7f cc                	jg     4888 <timer_thread+0x3e8>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48bc:	49 63 57 30          	movslq 0x30(%r15),%rdx
    48c0:	85 d2                	test   %edx,%edx
    48c2:	7e 7c                	jle    4940 <timer_thread+0x4a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    48c4:	41 8b 47 40          	mov    0x40(%r15),%eax
    48c8:	85 c0                	test   %eax,%eax
    48ca:	7e 74                	jle    4940 <timer_thread+0x4a0>
    48cc:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    48cf:	4d 8b 47 18          	mov    0x18(%r15),%r8
    48d3:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    48db:	31 c9                	xor    %ecx,%ecx
    48dd:	48 c1 e6 09          	shl    $0x9,%rsi
    48e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    48e8:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    48ec:	48 8b 40 38          	mov    0x38(%rax),%rax
    48f0:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    48f4:	f7 c6 00 02 00 00    	test   $0x200,%esi
    48fa:	74 1c                	je     4918 <timer_thread+0x478>
    48fc:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4906:	48 05 00 02 00 00    	add    $0x200,%rax
    490c:	48 39 d0             	cmp    %rdx,%rax
    490f:	74 26                	je     4937 <timer_thread+0x497>
    4911:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4918:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4922:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4928:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4932:	48 39 d0             	cmp    %rdx,%rax
    4935:	75 e1                	jne    4918 <timer_thread+0x478>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4937:	48 83 c1 08          	add    $0x8,%rcx
    493b:	48 39 cf             	cmp    %rcx,%rdi
    493e:	75 a8                	jne    48e8 <timer_thread+0x448>
    4940:	48 8d 3d 60 47 00 00 	lea    0x4760(%rip),%rdi        # 90a7 <_IO_stdin_used+0xa7>
    4947:	e8 e4 d9 ff ff       	call   2330 <puts@plt>
    data->running = 0;
    494c:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4954:	48 8d 3d 53 47 00 00 	lea    0x4753(%rip),%rdi        # 90ae <_IO_stdin_used+0xae>
    495b:	e8 d0 d9 ff ff       	call   2330 <puts@plt>
}
    4960:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4965:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    496e:	75 41                	jne    49b1 <timer_thread+0x511>
    4970:	48 83 c4 58          	add    $0x58,%rsp
    4974:	31 c0                	xor    %eax,%eax
    4976:	5b                   	pop    %rbx
    4977:	5d                   	pop    %rbp
    4978:	41 5c                	pop    %r12
    497a:	41 5d                	pop    %r13
    497c:	41 5e                	pop    %r14
    497e:	41 5f                	pop    %r15
    4980:	c3                   	ret
    4981:	4c 89 e7             	mov    %r12,%rdi
    4984:	e8 a7 d9 ff ff       	call   2330 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4989:	49 8b 47 18          	mov    0x18(%r15),%rax
    498d:	be 01 00 00 00       	mov    $0x1,%esi
    4992:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4996:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    499a:	8b 78 68             	mov    0x68(%rax),%edi
    499d:	e8 be da ff ff       	call   2460 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    49a2:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    49a6:	0f 8f dc fe ff ff    	jg     4888 <timer_thread+0x3e8>
    49ac:	e9 0b ff ff ff       	jmp    48bc <timer_thread+0x41c>
}
    49b1:	e8 ca d9 ff ff       	call   2380 <__stack_chk_fail@plt>
    49b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000049c0 <minf>:
int minf(int a, int b) {
    49c0:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    49c4:	39 f7                	cmp    %esi,%edi
    49c6:	89 f0                	mov    %esi,%eax
    49c8:	0f 4e c7             	cmovle %edi,%eax
}
    49cb:	c3                   	ret
    49cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000049d0 <maxf>:
int maxf(int a, int b) {
    49d0:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    49d4:	39 f7                	cmp    %esi,%edi
    49d6:	89 f0                	mov    %esi,%eax
    49d8:	0f 4d c7             	cmovge %edi,%eax
}
    49db:	c3                   	ret
    49dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000049e0 <strtolower>:
void strtolower(char *str) {
    49e0:	f3 0f 1e fa          	endbr64
    49e4:	55                   	push   %rbp
    49e5:	53                   	push   %rbx
    49e6:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    49ea:	48 0f be 1f          	movsbq (%rdi),%rbx
    49ee:	84 db                	test   %bl,%bl
    49f0:	74 24                	je     4a16 <strtolower+0x36>
    49f2:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    49f5:	e8 b6 db ff ff       	call   25b0 <__ctype_tolower_loc@plt>
    49fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a00:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4a03:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4a07:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4a0a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    4a0d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4a12:	84 db                	test   %bl,%bl
    4a14:	75 ea                	jne    4a00 <strtolower+0x20>
}
    4a16:	48 83 c4 08          	add    $0x8,%rsp
    4a1a:	5b                   	pop    %rbx
    4a1b:	5d                   	pop    %rbp
    4a1c:	c3                   	ret
    4a1d:	0f 1f 00             	nopl   (%rax)

0000000000004a20 <zh_malloc>:
void *zh_malloc(size_t size) {
    4a20:	f3 0f 1e fa          	endbr64
    4a24:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4a28:	e8 43 da ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4a2d:	48 85 c0             	test   %rax,%rax
    4a30:	74 05                	je     4a37 <zh_malloc+0x17>
}
    4a32:	48 83 c4 08          	add    $0x8,%rsp
    4a36:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4a37:	48 8b 0d e2 75 00 00 	mov    0x75e2(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    4a3e:	ba 28 00 00 00       	mov    $0x28,%edx
    4a43:	be 01 00 00 00       	mov    $0x1,%esi
    4a48:	48 8d 3d b1 4b 00 00 	lea    0x4bb1(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    4a4f:	e8 ec da ff ff       	call   2540 <fwrite@plt>
        exit(1);
    4a54:	bf 01 00 00 00       	mov    $0x1,%edi
    4a59:	e8 c2 da ff ff       	call   2520 <exit@plt>
    4a5e:	66 90                	xchg   %ax,%ax

0000000000004a60 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4a60:	f3 0f 1e fa          	endbr64
    4a64:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4a65:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4a6a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4a6d:	e8 3e d9 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    4a72:	48 85 c0             	test   %rax,%rax
    4a75:	74 11                	je     4a88 <get_filename_ext+0x28>
    4a77:	48 39 c3             	cmp    %rax,%rbx
    4a7a:	74 0c                	je     4a88 <get_filename_ext+0x28>
    return dot + 1;
    4a7c:	48 83 c0 01          	add    $0x1,%rax
}
    4a80:	5b                   	pop    %rbx
    4a81:	c3                   	ret
    4a82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4a88:	48 8d 05 67 46 00 00 	lea    0x4667(%rip),%rax        # 90f6 <_IO_stdin_used+0xf6>
}
    4a8f:	5b                   	pop    %rbx
    4a90:	c3                   	ret
    4a91:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4a9c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004aa0 <send_headers>:
void send_headers(struct KernelThread *data, struct Buffers *buffers, const char *path, off_t len, struct iovec *iov) {
    4aa0:	f3 0f 1e fa          	endbr64
    4aa4:	41 55                	push   %r13
    4aa6:	48 89 d6             	mov    %rdx,%rsi
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4aa9:	ba 00 04 00 00       	mov    $0x400,%edx
    4aae:	49 89 cd             	mov    %rcx,%r13
    4ab1:	41 54                	push   %r12
    4ab3:	55                   	push   %rbp
    4ab4:	4c 89 c5             	mov    %r8,%rbp
    4ab7:	53                   	push   %rbx
    4ab8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4abf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4ac8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4ad0:	31 c0                	xor    %eax,%eax
    4ad2:	49 89 e4             	mov    %rsp,%r12
    4ad5:	4c 89 e7             	mov    %r12,%rdi
    4ad8:	e8 b3 d9 ff ff       	call   2490 <__strcpy_chk@plt>
    for (; *str; ++str)
    4add:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4ae2:	84 db                	test   %bl,%bl
    4ae4:	74 24                	je     4b0a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4ae6:	e8 c5 da ff ff       	call   25b0 <__ctype_tolower_loc@plt>
    4aeb:	48 8b 08             	mov    (%rax),%rcx
    4aee:	4c 89 e0             	mov    %r12,%rax
    4af1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4af8:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4afb:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4aff:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4b02:	48 0f be 18          	movsbq (%rax),%rbx
    4b06:	84 db                	test   %bl,%bl
    4b08:	75 ee                	jne    4af8 <send_headers+0x58>
    void *buf = malloc(size);
    4b0a:	bf 11 00 00 00       	mov    $0x11,%edi
    4b0f:	e8 5c d9 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4b14:	48 85 c0             	test   %rax,%rax
    4b17:	0f 84 7e 04 00 00    	je     4f9b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4b1d:	66 0f 6f 05 fb 52 00 00 	movdqa 0x52fb(%rip),%xmm0        # 9e20 <_IO_stdin_used+0xe20>
    iov[0].iov_base = zh_malloc(slen);
    4b25:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4b29:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4b2e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4b36:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4b3a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4b3d:	e8 2e d9 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4b42:	48 85 c0             	test   %rax,%rax
    4b45:	0f 84 50 04 00 00    	je     4f9b <send_headers+0x4fb>
    4b4b:	66 0f 6f 05 dd 52 00 00 	movdqa 0x52dd(%rip),%xmm0        # 9e30 <_IO_stdin_used+0xe30>
    iov[1].iov_base = zh_malloc(slen);
    4b53:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4b57:	4c 89 e7             	mov    %r12,%rdi
    4b5a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4b64:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4b6c:	0f 11 00             	movups %xmm0,(%rax)
    4b6f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4b73:	be 2e 00 00 00       	mov    $0x2e,%esi
    4b78:	e8 33 d8 ff ff       	call   23b0 <strrchr@plt>
    if (!dot || dot == filename)
    4b7d:	48 85 c0             	test   %rax,%rax
    4b80:	0f 84 ea 02 00 00    	je     4e70 <send_headers+0x3d0>
    4b86:	4c 39 e0             	cmp    %r12,%rax
    4b89:	0f 84 e1 02 00 00    	je     4e70 <send_headers+0x3d0>
    return dot + 1;
    4b8f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4b93:	48 8d 3d 2a 45 00 00 	lea    0x452a(%rip),%rdi        # 90c4 <_IO_stdin_used+0xc4>
    4b9a:	48 89 de             	mov    %rbx,%rsi
    4b9d:	e8 6e d8 ff ff       	call   2410 <strcmp@plt>
    4ba2:	85 c0                	test   %eax,%eax
    4ba4:	75 20                	jne    4bc6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ba6:	66 0f 6f 05 92 52 00 00 	movdqa 0x5292(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4bae:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4bb6:	66 0f 6f 05 92 52 00 00 	movdqa 0x5292(%rip),%xmm0        # 9e50 <_IO_stdin_used+0xe50>
    4bbe:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4bc6:	48 89 de             	mov    %rbx,%rsi
    4bc9:	48 8d 3d f8 44 00 00 	lea    0x44f8(%rip),%rdi        # 90c8 <_IO_stdin_used+0xc8>
    4bd0:	e8 3b d8 ff ff       	call   2410 <strcmp@plt>
    4bd5:	85 c0                	test   %eax,%eax
    4bd7:	75 20                	jne    4bf9 <send_headers+0x159>
    4bd9:	66 0f 6f 05 5f 52 00 00 	movdqa 0x525f(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4be1:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4be9:	66 0f 6f 05 5f 52 00 00 	movdqa 0x525f(%rip),%xmm0        # 9e50 <_IO_stdin_used+0xe50>
    4bf1:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4bf9:	48 89 de             	mov    %rbx,%rsi
    4bfc:	48 8d 3d ca 44 00 00 	lea    0x44ca(%rip),%rdi        # 90cd <_IO_stdin_used+0xcd>
    4c03:	e8 08 d8 ff ff       	call   2410 <strcmp@plt>
    4c08:	85 c0                	test   %eax,%eax
    4c0a:	0f 84 10 02 00 00    	je     4e20 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4c10:	48 89 de             	mov    %rbx,%rsi
    4c13:	48 8d 3d b7 44 00 00 	lea    0x44b7(%rip),%rdi        # 90d1 <_IO_stdin_used+0xd1>
    4c1a:	e8 f1 d7 ff ff       	call   2410 <strcmp@plt>
    4c1f:	85 c0                	test   %eax,%eax
    4c21:	0f 84 a9 02 00 00    	je     4ed0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4c27:	48 89 de             	mov    %rbx,%rsi
    4c2a:	48 8d 3d a4 44 00 00 	lea    0x44a4(%rip),%rdi        # 90d5 <_IO_stdin_used+0xd5>
    4c31:	e8 da d7 ff ff       	call   2410 <strcmp@plt>
    4c36:	85 c0                	test   %eax,%eax
    4c38:	0f 84 6a 02 00 00    	je     4ea8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4c3e:	48 89 de             	mov    %rbx,%rsi
    4c41:	48 8d 3d ed 44 00 00 	lea    0x44ed(%rip),%rdi        # 9135 <_IO_stdin_used+0x135>
    4c48:	e8 c3 d7 ff ff       	call   2410 <strcmp@plt>
    4c4d:	85 c0                	test   %eax,%eax
    4c4f:	0f 84 2b 02 00 00    	je     4e80 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4c55:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4c58:	0f 84 52 01 00 00    	je     4db0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4c5e:	48 89 de             	mov    %rbx,%rsi
    4c61:	48 8d 3d 71 44 00 00 	lea    0x4471(%rip),%rdi        # 90d9 <_IO_stdin_used+0xd9>
    4c68:	e8 a3 d7 ff ff       	call   2410 <strcmp@plt>
    4c6d:	85 c0                	test   %eax,%eax
    4c6f:	0f 84 ab 02 00 00    	je     4f20 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4c75:	48 89 de             	mov    %rbx,%rsi
    4c78:	48 8d 3d 5e 44 00 00 	lea    0x445e(%rip),%rdi        # 90dd <_IO_stdin_used+0xdd>
    4c7f:	e8 8c d7 ff ff       	call   2410 <strcmp@plt>
    4c84:	85 c0                	test   %eax,%eax
    4c86:	0f 84 6c 02 00 00    	je     4ef8 <send_headers+0x458>
    slen = strlen(send_buffer);
    4c8c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4c94:	4c 89 e7             	mov    %r12,%rdi
    4c97:	e8 d4 d6 ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    4c9c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4c9f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4ca2:	e8 c9 d7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4ca7:	48 85 c0             	test   %rax,%rax
    4caa:	0f 84 eb 02 00 00    	je     4f9b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4cb0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4cb4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4cb8:	83 fb 08             	cmp    $0x8,%ebx
    4cbb:	0f 83 3f 01 00 00    	jae    4e00 <send_headers+0x360>
    4cc1:	f6 c3 04             	test   $0x4,%bl
    4cc4:	0f 85 7b 02 00 00    	jne    4f45 <send_headers+0x4a5>
    4cca:	85 db                	test   %ebx,%ebx
    4ccc:	74 13                	je     4ce1 <send_headers+0x241>
    4cce:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4cd6:	88 10                	mov    %dl,(%rax)
    4cd8:	f6 c3 02             	test   $0x2,%bl
    4cdb:	0f 85 96 02 00 00    	jne    4f77 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4ce1:	4d 89 e8             	mov    %r13,%r8
    4ce4:	48 8d 0d f6 43 00 00 	lea    0x43f6(%rip),%rcx        # 90e1 <_IO_stdin_used+0xe1>
    4ceb:	4c 89 e7             	mov    %r12,%rdi
    4cee:	31 c0                	xor    %eax,%eax
    4cf0:	ba 00 04 00 00       	mov    $0x400,%edx
    4cf5:	be 01 00 00 00       	mov    $0x1,%esi
    4cfa:	e8 c1 d8 ff ff       	call   25c0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4cff:	4c 89 e7             	mov    %r12,%rdi
    4d02:	e8 69 d6 ff ff       	call   2370 <strlen@plt>
    void *buf = malloc(size);
    4d07:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4d0a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4d0d:	e8 5e d7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4d12:	48 85 c0             	test   %rax,%rax
    4d15:	0f 84 80 02 00 00    	je     4f9b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4d1b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4d1f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4d23:	83 fb 08             	cmp    $0x8,%ebx
    4d26:	0f 83 1c 01 00 00    	jae    4e48 <send_headers+0x3a8>
    4d2c:	f6 c3 04             	test   $0x4,%bl
    4d2f:	0f 85 29 02 00 00    	jne    4f5e <send_headers+0x4be>
    4d35:	85 db                	test   %ebx,%ebx
    4d37:	74 13                	je     4d4c <send_headers+0x2ac>
    4d39:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4d41:	88 10                	mov    %dl,(%rax)
    4d43:	f6 c3 02             	test   $0x2,%bl
    4d46:	0f 85 3d 02 00 00    	jne    4f89 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d4c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4d51:	bf 02 00 00 00       	mov    $0x2,%edi
    4d56:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4d5e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4d66:	e8 05 d7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4d6b:	48 85 c0             	test   %rax,%rax
    4d6e:	0f 84 27 02 00 00    	je     4f9b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4d74:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4d7c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4d80:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4d88:	66 89 10             	mov    %dx,(%rax)
}
    4d8b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4d93:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4d9c:	0f 85 20 02 00 00    	jne    4fc2 <send_headers+0x522>
    4da2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4da9:	5b                   	pop    %rbx
    4daa:	5d                   	pop    %rbp
    4dab:	41 5c                	pop    %r12
    4dad:	41 5d                	pop    %r13
    4daf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4db0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4db4:	0f 85 a4 fe ff ff    	jne    4c5e <send_headers+0x1be>
    4dba:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4dbe:	0f 85 9a fe ff ff    	jne    4c5e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4dc4:	66 0f 6f 05 d4 50 00 00 	movdqa 0x50d4(%rip),%xmm0        # 9ea0 <_IO_stdin_used+0xea0>
    4dcc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4dd6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4dde:	66 0f 6f 05 ca 50 00 00 	movdqa 0x50ca(%rip),%xmm0        # 9eb0 <_IO_stdin_used+0xeb0>
    4de6:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4dee:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4df6:	e9 63 fe ff ff       	jmp    4c5e <send_headers+0x1be>
    4dfb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4e00:	89 da                	mov    %ebx,%edx
    4e02:	48 89 c7             	mov    %rax,%rdi
    4e05:	4c 89 e6             	mov    %r12,%rsi
    4e08:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4e0d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4e12:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4e15:	c1 e9 03             	shr    $0x3,%ecx
    4e18:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4e1b:	e9 c1 fe ff ff       	jmp    4ce1 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4e20:	66 0f 6f 05 18 50 00 00 	movdqa 0x5018(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4e28:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e30:	66 0f 6f 05 28 50 00 00 	movdqa 0x5028(%rip),%xmm0        # 9e60 <_IO_stdin_used+0xe60>
    4e38:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e40:	e9 cb fd ff ff       	jmp    4c10 <send_headers+0x170>
    4e45:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4e48:	89 da                	mov    %ebx,%edx
    4e4a:	48 89 c7             	mov    %rax,%rdi
    4e4d:	4c 89 e6             	mov    %r12,%rsi
    4e50:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4e55:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4e5a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4e5d:	c1 e9 03             	shr    $0x3,%ecx
    4e60:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4e63:	e9 e4 fe ff ff       	jmp    4d4c <send_headers+0x2ac>
    4e68:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4e70:	48 8d 1d 7f 42 00 00 	lea    0x427f(%rip),%rbx        # 90f6 <_IO_stdin_used+0xf6>
    4e77:	e9 94 fd ff ff       	jmp    4c10 <send_headers+0x170>
    4e7c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4e80:	66 0f 6f 05 f8 4f 00 00 	movdqa 0x4ff8(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4e88:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e90:	66 0f 6f 05 f8 4f 00 00 	movdqa 0x4ff8(%rip),%xmm0        # 9e90 <_IO_stdin_used+0xe90>
    4e98:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ea0:	e9 b0 fd ff ff       	jmp    4c55 <send_headers+0x1b5>
    4ea5:	0f 1f 00             	nopl   (%rax)
    4ea8:	66 0f 6f 05 d0 4f 00 00 	movdqa 0x4fd0(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4eb0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4eb8:	66 0f 6f 05 d0 4f 00 00 	movdqa 0x4fd0(%rip),%xmm0        # 9e90 <_IO_stdin_used+0xe90>
    4ec0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ec8:	e9 71 fd ff ff       	jmp    4c3e <send_headers+0x19e>
    4ecd:	0f 1f 00             	nopl   (%rax)
    4ed0:	66 0f 6f 05 68 4f 00 00 	movdqa 0x4f68(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4ed8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ee0:	66 0f 6f 05 88 4f 00 00 	movdqa 0x4f88(%rip),%xmm0        # 9e70 <_IO_stdin_used+0xe70>
    4ee8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ef0:	e9 32 fd ff ff       	jmp    4c27 <send_headers+0x187>
    4ef5:	0f 1f 00             	nopl   (%rax)
    4ef8:	66 0f 6f 05 80 4f 00 00 	movdqa 0x4f80(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4f00:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f08:	66 0f 6f 05 c0 4f 00 00 	movdqa 0x4fc0(%rip),%xmm0        # 9ed0 <_IO_stdin_used+0xed0>
    4f10:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4f18:	e9 6f fd ff ff       	jmp    4c8c <send_headers+0x1ec>
    4f1d:	0f 1f 00             	nopl   (%rax)
    4f20:	66 0f 6f 05 58 4f 00 00 	movdqa 0x4f58(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4f28:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f30:	66 0f 6f 05 88 4f 00 00 	movdqa 0x4f88(%rip),%xmm0        # 9ec0 <_IO_stdin_used+0xec0>
    4f38:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4f40:	e9 30 fd ff ff       	jmp    4c75 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f45:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4f4c:	89 db                	mov    %ebx,%ebx
    4f4e:	89 10                	mov    %edx,(%rax)
    4f50:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4f55:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4f59:	e9 83 fd ff ff       	jmp    4ce1 <send_headers+0x241>
    4f5e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4f65:	89 db                	mov    %ebx,%ebx
    4f67:	89 10                	mov    %edx,(%rax)
    4f69:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4f6e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4f72:	e9 d5 fd ff ff       	jmp    4d4c <send_headers+0x2ac>
    4f77:	89 db                	mov    %ebx,%ebx
    4f79:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4f7f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4f84:	e9 58 fd ff ff       	jmp    4ce1 <send_headers+0x241>
    4f89:	89 db                	mov    %ebx,%ebx
    4f8b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4f91:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4f96:	e9 b1 fd ff ff       	jmp    4d4c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4f9b:	48 8b 0d 7e 70 00 00 	mov    0x707e(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    4fa2:	ba 28 00 00 00       	mov    $0x28,%edx
    4fa7:	be 01 00 00 00       	mov    $0x1,%esi
    4fac:	48 8d 3d 4d 46 00 00 	lea    0x464d(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    4fb3:	e8 88 d5 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    4fb8:	bf 01 00 00 00       	mov    $0x1,%edi
    4fbd:	e8 5e d5 ff ff       	call   2520 <exit@plt>
}
    4fc2:	e8 b9 d3 ff ff       	call   2380 <__stack_chk_fail@plt>
    4fc7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000004fd0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4fd0:	f3 0f 1e fa          	endbr64
    4fd4:	41 55                	push   %r13
    4fd6:	49 89 d5             	mov    %rdx,%r13
    4fd9:	41 54                	push   %r12
    4fdb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    4fde:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    4fe1:	55                   	push   %rbp
    4fe2:	53                   	push   %rbx
    4fe3:	48 89 f3             	mov    %rsi,%rbx
    4fe6:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4fea:	e8 81 d4 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    4fef:	48 85 c0             	test   %rax,%rax
    4ff2:	74 6b                	je     505f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    4ff4:	4c 89 e7             	mov    %r12,%rdi
    4ff7:	48 89 c5             	mov    %rax,%rbp
    4ffa:	31 f6                	xor    %esi,%esi
    4ffc:	31 c0                	xor    %eax,%eax
    4ffe:	e8 ed d4 ff ff       	call   24f0 <open@plt>
    5003:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    5006:	85 c0                	test   %eax,%eax
    5008:	0f 88 e8 d5 ff ff    	js     25f6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    500e:	48 89 da             	mov    %rbx,%rdx
    5011:	48 89 ee             	mov    %rbp,%rsi
    5014:	89 c7                	mov    %eax,%edi
    5016:	e8 d5 d3 ff ff       	call   23f0 <read@plt>
    if (ret < file_size) {
    501b:	48 98                	cltq
    501d:	48 39 d8             	cmp    %rbx,%rax
    5020:	7c 1e                	jl     5040 <copy_file_contents+0x70>
    close(fd);
    5022:	44 89 e7             	mov    %r12d,%edi
    5025:	e8 a6 d3 ff ff       	call   23d0 <close@plt>
    iov->iov_base = buf;
    502a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    502e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    5032:	48 83 c4 08          	add    $0x8,%rsp
    5036:	5b                   	pop    %rbx
    5037:	5d                   	pop    %rbp
    5038:	41 5c                	pop    %r12
    503a:	41 5d                	pop    %r13
    503c:	c3                   	ret
    503d:	0f 1f 00             	nopl   (%rax)
    5040:	48 8b 0d d9 6f 00 00 	mov    0x6fd9(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5047:	ba 1a 00 00 00       	mov    $0x1a,%edx
    504c:	be 01 00 00 00       	mov    $0x1,%esi
    5051:	48 8d 3d 9f 40 00 00 	lea    0x409f(%rip),%rdi        # 90f7 <_IO_stdin_used+0xf7>
    5058:	e8 e3 d4 ff ff       	call   2540 <fwrite@plt>
    505d:	eb c3                	jmp    5022 <copy_file_contents+0x52>
    505f:	48 8b 0d ba 6f 00 00 	mov    0x6fba(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5066:	ba 28 00 00 00       	mov    $0x28,%edx
    506b:	be 01 00 00 00       	mov    $0x1,%esi
    5070:	48 8d 3d 89 45 00 00 	lea    0x4589(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    5077:	e8 c4 d4 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    507c:	bf 01 00 00 00       	mov    $0x1,%edi
    5081:	e8 9a d4 ff ff       	call   2520 <exit@plt>
    5086:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005090 <add_write_request>:
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    5090:	f3 0f 1e fa          	endbr64
    5094:	55                   	push   %rbp
    struct Write *write = calloc(1, sizeof(struct Write));
    5095:	be 10 00 00 00       	mov    $0x10,%esi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    509a:	48 89 d5             	mov    %rdx,%rbp
    509d:	53                   	push   %rbx
    509e:	48 89 fb             	mov    %rdi,%rbx
    struct Write *write = calloc(1, sizeof(struct Write));
    50a1:	bf 01 00 00 00       	mov    $0x1,%edi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    50a6:	48 83 ec 08          	sub    $0x8,%rsp
    struct Write *write = calloc(1, sizeof(struct Write));
    50aa:	e8 51 d3 ff ff       	call   2400 <calloc@plt>
    write->client_socket = req->client_socket;
    50af:	f3 0f 7e 45 08       	movq   0x8(%rbp),%xmm0
    req->event_type = EVENT_TYPE_WRITE;
    50b4:	c7 45 00 02 00 00 00 	movl   $0x2,0x0(%rbp)
    if (write->client_socket == -1) {
    50bb:	66 0f 7e c2          	movd   %xmm0,%edx
    write->client_socket = req->client_socket;
    50bf:	66 0f d6 40 08       	movq   %xmm0,0x8(%rax)
    50c4:	66 0f 70 c8 e5       	pshufd $0xe5,%xmm0,%xmm1
    if (write->client_socket == -1) {
    50c9:	83 fa ff             	cmp    $0xffffffff,%edx
    50cc:	74 69                	je     5137 <add_write_request+0xa7>
    buffersend_filter(data, &data->iomailboxes[data->other_io], IO_WRITE, write, write->sockettoken);
    50ce:	48 63 b3 18 01 00 00 	movslq 0x118(%rbx),%rsi
    write->request = req;
    50d5:	48 89 28             	mov    %rbp,(%rax)
    50d8:	66 0f 7e cf          	movd   %xmm1,%edi
    buffersend_filter(data, &data->iomailboxes[data->other_io], IO_WRITE, write, write->sockettoken);
    50dc:	48 c1 e6 04          	shl    $0x4,%rsi
    50e0:	48 03 b3 10 01 00 00 	add    0x110(%rbx),%rsi
  while (data->running == 1) {
    50e7:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    50eb:	75 41                	jne    512e <add_write_request+0x9e>
      for (int x = 0 ; x < buffers->count ; x++) {
    50ed:	48 63 0e             	movslq (%rsi),%rcx
    50f0:	85 c9                	test   %ecx,%ecx
    50f2:	7e f3                	jle    50e7 <add_write_request+0x57>
    50f4:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    50f8:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    50fc:	48 8d 0c ca          	lea    (%rdx,%rcx,8),%rcx
    5100:	eb 0f                	jmp    5111 <add_write_request+0x81>
    5102:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5108:	48 83 c2 28          	add    $0x28,%rdx
    510c:	48 39 ca             	cmp    %rcx,%rdx
    510f:	74 d6                	je     50e7 <add_write_request+0x57>
        if (buffers->buffer[x].available == 0) {
    5111:	44 8b 42 08          	mov    0x8(%rdx),%r8d
    5115:	45 85 c0             	test   %r8d,%r8d
    5118:	75 ee                	jne    5108 <add_write_request+0x78>
          buffers->buffer[x].data = send;
    511a:	48 89 02             	mov    %rax,(%rdx)
          buffers->buffer[x].kind = kind;
    511d:	c7 42 20 03 00 00 00 	movl   $0x3,0x20(%rdx)
          buffers->buffer[x].filter = filter;
    5124:	89 7a 24             	mov    %edi,0x24(%rdx)
          buffers->buffer[x].available = 1;
    5127:	c7 42 08 01 00 00 00 	movl   $0x1,0x8(%rdx)
}
    512e:	48 83 c4 08          	add    $0x8,%rsp
    5132:	31 c0                	xor    %eax,%eax
    5134:	5b                   	pop    %rbx
    5135:	5d                   	pop    %rbp
    5136:	c3                   	ret
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5137:	bf 01 00 00 00       	mov    $0x1,%edi
    513c:	48 8d 35 ed 44 00 00 	lea    0x44ed(%rip),%rsi        # 9630 <_IO_stdin_used+0x630>
    5143:	31 c0                	xor    %eax,%eax
    5145:	e8 66 d3 ff ff       	call   24b0 <__printf_chk@plt>
      exit(1);
    514a:	bf 01 00 00 00       	mov    $0x1,%edi
    514f:	e8 cc d3 ff ff       	call   2520 <exit@plt>
    5154:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    515f:	90                   	nop

0000000000005160 <add_read_request>:
int add_read_request(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5160:	f3 0f 1e fa          	endbr64
    5164:	41 56                	push   %r14
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    5166:	41 8b 40 44          	mov    0x44(%r8),%eax
    516a:	41 89 ce             	mov    %ecx,%r14d
    516d:	41 55                	push   %r13
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    516f:	41 8b 88 c0 00 00 00 	mov    0xc0(%r8),%ecx
    5176:	41 89 d5             	mov    %edx,%r13d
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5179:	49 8b 10             	mov    (%r8),%rdx
    517c:	41 54                	push   %r12
	unsigned int head, next = sq->sqe_tail + 1;
    517e:	83 c0 01             	add    $0x1,%eax
    5181:	55                   	push   %rbp
    5182:	53                   	push   %rbx
    5183:	4c 89 c3             	mov    %r8,%rbx
		head = IO_URING_READ_ONCE(*sq->khead);
    5186:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5188:	f6 c1 02             	test   $0x2,%cl
    518b:	74 00                	je     518d <add_read_request+0x2d>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    518d:	89 c2                	mov    %eax,%edx
    518f:	29 f2                	sub    %esi,%edx
    5191:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5194:	0f 82 68 d4 ff ff    	jb     2602 <add_read_request.cold>
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    519a:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    519d:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    51a0:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    51a3:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    51a8:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    51ab:	23 6b 58             	and    0x58(%rbx),%ebp
    51ae:	d3 e5                	shl    %cl,%ebp
    51b0:	48 c1 e5 06          	shl    $0x6,%rbp
    51b4:	48 03 6b 38          	add    0x38(%rbx),%rbp
    51b8:	e8 b3 d2 ff ff       	call   2470 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    51bd:	be 01 00 00 00       	mov    $0x1,%esi
    51c2:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    51c7:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    51ca:	e8 31 d2 ff ff       	call   2400 <calloc@plt>
    req->client_socket = client_socket;
    51cf:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    51d4:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    51d8:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    51db:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    51e0:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->sockettoken = sockettoken;
    51e5:	45 89 74 24 0c       	mov    %r14d,0xc(%r12)
    req->iov[0].iov_len = READ_SZ;
    51ea:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    51f3:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    51fb:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    51ff:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    5203:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    520a:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    5212:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    5216:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    521e:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    5226:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    522a:	e8 61 d1 ff ff       	call   2390 <io_uring_submit@plt>
}
    522f:	5b                   	pop    %rbx
    5230:	31 c0                	xor    %eax,%eax
    5232:	5d                   	pop    %rbp
    5233:	41 5c                	pop    %r12
    5235:	41 5d                	pop    %r13
    5237:	41 5e                	pop    %r14
    5239:	c3                   	ret
    523a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005240 <_send_static_string_content>:
void _send_static_string_content(struct KernelThread *data, struct Buffers *buffers, const char *str, int client_socket, int sockettoken, struct io_uring *ring) {
    5240:	f3 0f 1e fa          	endbr64
    5244:	41 57                	push   %r15
    5246:	4d 89 cf             	mov    %r9,%r15
    5249:	41 56                	push   %r14
    524b:	49 89 f6             	mov    %rsi,%r14
    524e:	41 55                	push   %r13
    5250:	41 54                	push   %r12
    5252:	45 89 c4             	mov    %r8d,%r12d
    5255:	55                   	push   %rbp
    5256:	48 89 d5             	mov    %rdx,%rbp
    5259:	53                   	push   %rbx
    525a:	89 cb                	mov    %ecx,%ebx
    525c:	48 83 ec 18          	sub    $0x18,%rsp
    5260:	48 89 3c 24          	mov    %rdi,(%rsp)
    void *buf = malloc(size);
    5264:	bf 20 00 00 00       	mov    $0x20,%edi
    5269:	e8 02 d2 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    526e:	48 85 c0             	test   %rax,%rax
    5271:	74 6a                	je     52dd <_send_static_string_content+0x9d>
    5273:	49 89 c5             	mov    %rax,%r13
    unsigned long slen = strlen(str);
    5276:	48 89 ef             	mov    %rbp,%rdi
    5279:	e8 f2 d0 ff ff       	call   2370 <strlen@plt>
    req->iovec_count = 1;
    527e:	41 c7 45 04 01 00 00 00 	movl   $0x1,0x4(%r13)
    req->client_socket = client_socket;
    5286:	41 89 5d 08          	mov    %ebx,0x8(%r13)
    req->sockettoken = sockettoken;
    528a:	45 89 65 0c          	mov    %r12d,0xc(%r13)
    if (req->client_socket == -1) {
    528e:	83 fb ff             	cmp    $0xffffffff,%ebx
    5291:	74 71                	je     5304 <_send_static_string_content+0xc4>
    void *buf = malloc(size);
    5293:	48 89 c7             	mov    %rax,%rdi
    5296:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    529b:	e8 d0 d1 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    52a0:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    52a5:	48 85 c0             	test   %rax,%rax
    void *buf = malloc(size);
    52a8:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    52ab:	74 30                	je     52dd <_send_static_string_content+0x9d>
    req->iov[0].iov_len = slen;
    52ad:	49 89 55 18          	mov    %rdx,0x18(%r13)
    52b1:	48 89 ee             	mov    %rbp,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    52b4:	49 89 45 10          	mov    %rax,0x10(%r13)
    52b8:	e8 83 d1 ff ff       	call   2440 <memcpy@plt>
    add_write_request(data, buffers, req, ring);
    52bd:	48 8b 3c 24          	mov    (%rsp),%rdi
}
    52c1:	48 83 c4 18          	add    $0x18,%rsp
    add_write_request(data, buffers, req, ring);
    52c5:	4c 89 f9             	mov    %r15,%rcx
}
    52c8:	5b                   	pop    %rbx
    add_write_request(data, buffers, req, ring);
    52c9:	4c 89 ea             	mov    %r13,%rdx
}
    52cc:	5d                   	pop    %rbp
    add_write_request(data, buffers, req, ring);
    52cd:	4c 89 f6             	mov    %r14,%rsi
}
    52d0:	41 5c                	pop    %r12
    52d2:	41 5d                	pop    %r13
    52d4:	41 5e                	pop    %r14
    52d6:	41 5f                	pop    %r15
    add_write_request(data, buffers, req, ring);
    52d8:	e9 b3 fd ff ff       	jmp    5090 <add_write_request>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    52dd:	48 8b 0d 3c 6d 00 00 	mov    0x6d3c(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    52e4:	ba 28 00 00 00       	mov    $0x28,%edx
    52e9:	be 01 00 00 00       	mov    $0x1,%esi
    52ee:	48 8d 3d 0b 43 00 00 	lea    0x430b(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    52f5:	e8 46 d2 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    52fa:	bf 01 00 00 00       	mov    $0x1,%edi
    52ff:	e8 1c d2 ff ff       	call   2520 <exit@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5304:	48 8d 3d 07 3e 00 00 	lea    0x3e07(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    530b:	e8 20 d0 ff ff       	call   2330 <puts@plt>
      exit(1);
    5310:	bf 01 00 00 00       	mov    $0x1,%edi
    5315:	e8 06 d2 ff ff       	call   2520 <exit@plt>
    531a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005320 <handle_unimplemented_method>:
void handle_unimplemented_method(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5320:	f3 0f 1e fa          	endbr64
    5324:	41 57                	push   %r15
    5326:	41 56                	push   %r14
    5328:	4d 89 c6             	mov    %r8,%r14
    532b:	41 55                	push   %r13
    532d:	49 89 f5             	mov    %rsi,%r13
    5330:	41 54                	push   %r12
    5332:	55                   	push   %rbp
    5333:	89 cd                	mov    %ecx,%ebp
    5335:	53                   	push   %rbx
    5336:	89 d3                	mov    %edx,%ebx
    5338:	48 83 ec 18          	sub    $0x18,%rsp
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, sockettoken, ring);
    533c:	4c 8b 3d d5 6c 00 00 	mov    0x6cd5(%rip),%r15        # c018 <unimplemented_content>
void handle_unimplemented_method(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5343:	48 89 3c 24          	mov    %rdi,(%rsp)
    void *buf = malloc(size);
    5347:	bf 20 00 00 00       	mov    $0x20,%edi
    534c:	e8 1f d1 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5351:	48 85 c0             	test   %rax,%rax
    5354:	74 6f                	je     53c5 <handle_unimplemented_method+0xa5>
    5356:	49 89 c4             	mov    %rax,%r12
    unsigned long slen = strlen(str);
    5359:	4c 89 ff             	mov    %r15,%rdi
    535c:	e8 0f d0 ff ff       	call   2370 <strlen@plt>
    req->client_socket = client_socket;
    5361:	41 89 5c 24 08       	mov    %ebx,0x8(%r12)
    req->iovec_count = 1;
    5366:	41 c7 44 24 04 01 00 00 00 	movl   $0x1,0x4(%r12)
    req->sockettoken = sockettoken;
    536f:	41 89 6c 24 0c       	mov    %ebp,0xc(%r12)
    if (req->client_socket == -1) {
    5374:	83 fb ff             	cmp    $0xffffffff,%ebx
    5377:	74 73                	je     53ec <handle_unimplemented_method+0xcc>
    void *buf = malloc(size);
    5379:	48 89 c7             	mov    %rax,%rdi
    537c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5381:	e8 ea d0 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5386:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    538b:	48 85 c0             	test   %rax,%rax
    void *buf = malloc(size);
    538e:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    5391:	74 32                	je     53c5 <handle_unimplemented_method+0xa5>
    req->iov[0].iov_len = slen;
    5393:	49 89 54 24 18       	mov    %rdx,0x18(%r12)
    5398:	4c 89 fe             	mov    %r15,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    539b:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    53a0:	e8 9b d0 ff ff       	call   2440 <memcpy@plt>
    add_write_request(data, buffers, req, ring);
    53a5:	48 8b 3c 24          	mov    (%rsp),%rdi
}
    53a9:	48 83 c4 18          	add    $0x18,%rsp
    add_write_request(data, buffers, req, ring);
    53ad:	4c 89 f1             	mov    %r14,%rcx
}
    53b0:	5b                   	pop    %rbx
    add_write_request(data, buffers, req, ring);
    53b1:	4c 89 e2             	mov    %r12,%rdx
}
    53b4:	5d                   	pop    %rbp
    add_write_request(data, buffers, req, ring);
    53b5:	4c 89 ee             	mov    %r13,%rsi
}
    53b8:	41 5c                	pop    %r12
    53ba:	41 5d                	pop    %r13
    53bc:	41 5e                	pop    %r14
    53be:	41 5f                	pop    %r15
    add_write_request(data, buffers, req, ring);
    53c0:	e9 cb fc ff ff       	jmp    5090 <add_write_request>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    53c5:	48 8b 0d 54 6c 00 00 	mov    0x6c54(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    53cc:	ba 28 00 00 00       	mov    $0x28,%edx
    53d1:	be 01 00 00 00       	mov    $0x1,%esi
    53d6:	48 8d 3d 23 42 00 00 	lea    0x4223(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    53dd:	e8 5e d1 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    53e2:	bf 01 00 00 00       	mov    $0x1,%edi
    53e7:	e8 34 d1 ff ff       	call   2520 <exit@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    53ec:	48 8d 3d 1f 3d 00 00 	lea    0x3d1f(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    53f3:	e8 38 cf ff ff       	call   2330 <puts@plt>
      exit(1);
    53f8:	bf 01 00 00 00       	mov    $0x1,%edi
    53fd:	e8 1e d1 ff ff       	call   2520 <exit@plt>
    5402:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    540d:	0f 1f 00             	nopl   (%rax)

0000000000005410 <handle_http_404>:
void handle_http_404(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5410:	f3 0f 1e fa          	endbr64
    5414:	41 57                	push   %r15
    5416:	41 56                	push   %r14
    5418:	4d 89 c6             	mov    %r8,%r14
    541b:	41 55                	push   %r13
    541d:	49 89 f5             	mov    %rsi,%r13
    5420:	41 54                	push   %r12
    5422:	55                   	push   %rbp
    5423:	89 cd                	mov    %ecx,%ebp
    5425:	53                   	push   %rbx
    5426:	89 d3                	mov    %edx,%ebx
    5428:	48 83 ec 18          	sub    $0x18,%rsp
    _send_static_string_content(data, buffers, http_404_content, client_socket, sockettoken, ring);
    542c:	4c 8b 3d dd 6b 00 00 	mov    0x6bdd(%rip),%r15        # c010 <http_404_content>
void handle_http_404(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5433:	48 89 3c 24          	mov    %rdi,(%rsp)
    void *buf = malloc(size);
    5437:	bf 20 00 00 00       	mov    $0x20,%edi
    543c:	e8 2f d0 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5441:	48 85 c0             	test   %rax,%rax
    5444:	74 6f                	je     54b5 <handle_http_404+0xa5>
    5446:	49 89 c4             	mov    %rax,%r12
    unsigned long slen = strlen(str);
    5449:	4c 89 ff             	mov    %r15,%rdi
    544c:	e8 1f cf ff ff       	call   2370 <strlen@plt>
    req->client_socket = client_socket;
    5451:	41 89 5c 24 08       	mov    %ebx,0x8(%r12)
    req->iovec_count = 1;
    5456:	41 c7 44 24 04 01 00 00 00 	movl   $0x1,0x4(%r12)
    req->sockettoken = sockettoken;
    545f:	41 89 6c 24 0c       	mov    %ebp,0xc(%r12)
    if (req->client_socket == -1) {
    5464:	83 fb ff             	cmp    $0xffffffff,%ebx
    5467:	74 73                	je     54dc <handle_http_404+0xcc>
    void *buf = malloc(size);
    5469:	48 89 c7             	mov    %rax,%rdi
    546c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5471:	e8 fa cf ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5476:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    547b:	48 85 c0             	test   %rax,%rax
    void *buf = malloc(size);
    547e:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    5481:	74 32                	je     54b5 <handle_http_404+0xa5>
    req->iov[0].iov_len = slen;
    5483:	49 89 54 24 18       	mov    %rdx,0x18(%r12)
    5488:	4c 89 fe             	mov    %r15,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    548b:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    5490:	e8 ab cf ff ff       	call   2440 <memcpy@plt>
    add_write_request(data, buffers, req, ring);
    5495:	48 8b 3c 24          	mov    (%rsp),%rdi
}
    5499:	48 83 c4 18          	add    $0x18,%rsp
    add_write_request(data, buffers, req, ring);
    549d:	4c 89 f1             	mov    %r14,%rcx
}
    54a0:	5b                   	pop    %rbx
    add_write_request(data, buffers, req, ring);
    54a1:	4c 89 e2             	mov    %r12,%rdx
}
    54a4:	5d                   	pop    %rbp
    add_write_request(data, buffers, req, ring);
    54a5:	4c 89 ee             	mov    %r13,%rsi
}
    54a8:	41 5c                	pop    %r12
    54aa:	41 5d                	pop    %r13
    54ac:	41 5e                	pop    %r14
    54ae:	41 5f                	pop    %r15
    add_write_request(data, buffers, req, ring);
    54b0:	e9 db fb ff ff       	jmp    5090 <add_write_request>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    54b5:	48 8b 0d 64 6b 00 00 	mov    0x6b64(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    54bc:	ba 28 00 00 00       	mov    $0x28,%edx
    54c1:	be 01 00 00 00       	mov    $0x1,%esi
    54c6:	48 8d 3d 33 41 00 00 	lea    0x4133(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    54cd:	e8 6e d0 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    54d2:	bf 01 00 00 00       	mov    $0x1,%edi
    54d7:	e8 44 d0 ff ff       	call   2520 <exit@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    54dc:	48 8d 3d 2f 3c 00 00 	lea    0x3c2f(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    54e3:	e8 48 ce ff ff       	call   2330 <puts@plt>
      exit(1);
    54e8:	bf 01 00 00 00       	mov    $0x1,%edi
    54ed:	e8 2e d0 ff ff       	call   2520 <exit@plt>
    54f2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    54fd:	0f 1f 00             	nopl   (%rax)

0000000000005500 <handle_get_method>:
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, int sockettoken, struct io_uring *ring) {
    5500:	f3 0f 1e fa          	endbr64
    5504:	41 57                	push   %r15
    5506:	41 56                	push   %r14
    5508:	41 89 ce             	mov    %ecx,%r14d
    550b:	41 55                	push   %r13
    550d:	45 89 c5             	mov    %r8d,%r13d
    5510:	41 54                	push   %r12
    5512:	4d 89 cc             	mov    %r9,%r12
    5515:	55                   	push   %rbp
    5516:	48 89 f5             	mov    %rsi,%rbp
    5519:	53                   	push   %rbx
    551a:	48 89 fb             	mov    %rdi,%rbx
    if (path[strlen(path) - 1] == '/') {
    551d:	48 89 d7             	mov    %rdx,%rdi
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, int sockettoken, struct io_uring *ring) {
    5520:	48 81 ec b8 04 00 00 	sub    $0x4b8,%rsp
    5527:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5530:	48 89 84 24 a8 04 00 00 	mov    %rax,0x4a8(%rsp)
    5538:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    553a:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    553f:	e8 2c ce ff ff       	call   2370 <strlen@plt>
    5544:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5549:	48 89 c2             	mov    %rax,%rdx
    554c:	80 7c 06 ff 2f       	cmpb   $0x2f,-0x1(%rsi,%rax,1)
    5551:	0f 84 a9 00 00 00    	je     5600 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5557:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    555c:	48 83 c2 01          	add    $0x1,%rdx
    5560:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
    5568:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    556d:	66 89 84 24 a4 00 00 00 	mov    %ax,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5575:	4c 8d bc 24 a0 00 00 00 	lea    0xa0(%rsp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    557d:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5588:	e8 93 ce ff ff       	call   2420 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    558d:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
    5592:	4c 89 ff             	mov    %r15,%rdi
    5595:	e8 96 ce ff ff       	call   2430 <stat@plt>
    559a:	83 f8 ff             	cmp    $0xffffffff,%eax
    559d:	74 14                	je     55b3 <handle_get_method+0xb3>
        if (S_ISREG(path_stat.st_mode)) {
    559f:	8b 44 24 28          	mov    0x28(%rsp),%eax
    55a3:	25 00 f0 00 00       	and    $0xf000,%eax
    55a8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    55ad:	0f 84 ad 00 00 00    	je     5660 <handle_get_method+0x160>
    _send_static_string_content(data, buffers, http_404_content, client_socket, sockettoken, ring);
    55b3:	48 8b 15 56 6a 00 00 	mov    0x6a56(%rip),%rdx        # c010 <http_404_content>
    55ba:	4d 89 e1             	mov    %r12,%r9
    55bd:	45 89 e8             	mov    %r13d,%r8d
    55c0:	44 89 f1             	mov    %r14d,%ecx
    55c3:	48 89 ee             	mov    %rbp,%rsi
    55c6:	48 89 df             	mov    %rbx,%rdi
    55c9:	e8 72 fc ff ff       	call   5240 <_send_static_string_content>
}
    55ce:	48 8b 84 24 a8 04 00 00 	mov    0x4a8(%rsp),%rax
    55d6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    55df:	0f 85 e3 00 00 00    	jne    56c8 <handle_get_method+0x1c8>
    55e5:	48 81 c4 b8 04 00 00 	add    $0x4b8,%rsp
    55ec:	5b                   	pop    %rbx
    55ed:	5d                   	pop    %rbp
    55ee:	41 5c                	pop    %r12
    55f0:	41 5d                	pop    %r13
    55f2:	41 5e                	pop    %r14
    55f4:	41 5f                	pop    %r15
    55f6:	c3                   	ret
    55f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5600:	b9 69 63 00 00       	mov    $0x6369,%ecx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5605:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    560d:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
    5618:	4c 8d bc 24 a0 00 00 00 	lea    0xa0(%rsp),%r15
    5620:	66 89 8c 24 a4 00 00 00 	mov    %cx,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5628:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    562d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5632:	e8 e9 cd ff ff       	call   2420 <__memcpy_chk@plt>
    5637:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    563c:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5641:	48 8d 35 e7 3a 00 00 	lea    0x3ae7(%rip),%rsi        # 912f <_IO_stdin_used+0x12f>
    5648:	48 29 d1             	sub    %rdx,%rcx
    564b:	49 8d 7c 17 06       	lea    0x6(%r15,%rdx,1),%rdi
    5650:	ba 0b 00 00 00       	mov    $0xb,%edx
    5655:	e8 c6 cd ff ff       	call   2420 <__memcpy_chk@plt>
    565a:	e9 2e ff ff ff       	jmp    558d <handle_get_method+0x8d>
    565f:	90                   	nop
    void *buf = malloc(size);
    5660:	bf 70 00 00 00       	mov    $0x70,%edi
    5665:	e8 06 ce ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    566a:	48 85 c0             	test   %rax,%rax
    566d:	74 5e                	je     56cd <handle_get_method+0x1cd>
            req->client_socket = client_socket;
    566f:	44 89 70 08          	mov    %r14d,0x8(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    5673:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    5678:	4c 8d 40 10          	lea    0x10(%rax),%r8
    567c:	4c 89 fa             	mov    %r15,%rdx
            req->sockettoken = sockettoken;
    567f:	44 89 68 0c          	mov    %r13d,0xc(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    5683:	48 89 ee             	mov    %rbp,%rsi
    5686:	48 89 df             	mov    %rbx,%rdi
            req->iovec_count = 6;
    5689:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    5690:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5695:	e8 06 f4 ff ff       	call   4aa0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    569a:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    569f:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    56a4:	4c 89 ff             	mov    %r15,%rdi
    56a7:	48 8d 50 60          	lea    0x60(%rax),%rdx
    56ab:	e8 20 f9 ff ff       	call   4fd0 <copy_file_contents>
            add_write_request(data, buffers, req, ring);
    56b0:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    56b5:	4c 89 e1             	mov    %r12,%rcx
    56b8:	48 89 ee             	mov    %rbp,%rsi
    56bb:	48 89 df             	mov    %rbx,%rdi
    56be:	e8 cd f9 ff ff       	call   5090 <add_write_request>
}
    56c3:	e9 06 ff ff ff       	jmp    55ce <handle_get_method+0xce>
    56c8:	e8 b3 cc ff ff       	call   2380 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    56cd:	48 8b 0d 4c 69 00 00 	mov    0x694c(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    56d4:	ba 28 00 00 00       	mov    $0x28,%edx
    56d9:	be 01 00 00 00       	mov    $0x1,%esi
    56de:	48 8d 3d 1b 3f 00 00 	lea    0x3f1b(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    56e5:	e8 56 ce ff ff       	call   2540 <fwrite@plt>
        exit(1);
    56ea:	bf 01 00 00 00       	mov    $0x1,%edi
    56ef:	e8 2c ce ff ff       	call   2520 <exit@plt>
    56f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    56ff:	90                   	nop

0000000000005700 <handle_http_method>:
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    5700:	f3 0f 1e fa          	endbr64
    5704:	41 57                	push   %r15
    5706:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5708:	4c 8d 35 9d 39 00 00 	lea    0x399d(%rip),%r14        # 90ac <_IO_stdin_used+0xac>
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    570f:	41 55                	push   %r13
    5711:	4d 89 cd             	mov    %r9,%r13
    5714:	41 54                	push   %r12
    5716:	45 89 c4             	mov    %r8d,%r12d
    5719:	55                   	push   %rbp
    571a:	89 cd                	mov    %ecx,%ebp
    571c:	53                   	push   %rbx
    571d:	48 83 ec 38          	sub    $0x38,%rsp
    5721:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    method = strtok_r(method_buffer, " ", &saveptr);
    5726:	4c 8d 7c 24 20       	lea    0x20(%rsp),%r15
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    572b:	48 89 d7             	mov    %rdx,%rdi
    572e:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    method = strtok_r(method_buffer, " ", &saveptr);
    5733:	4c 89 fa             	mov    %r15,%rdx
    5736:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    5739:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5742:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    5747:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5749:	e8 92 cc ff ff       	call   23e0 <strtok_r@plt>
    for (; *str; ++str)
    574e:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    5751:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    5754:	84 d2                	test   %dl,%dl
    5756:	88 54 24 1f          	mov    %dl,0x1f(%rsp)
    575a:	74 29                	je     5785 <handle_http_method+0x85>
        *str = (char)tolower(*str);
    575c:	e8 4f ce ff ff       	call   25b0 <__ctype_tolower_loc@plt>
    5761:	48 0f be 54 24 1f    	movsbq 0x1f(%rsp),%rdx
    5767:	48 89 d9             	mov    %rbx,%rcx
    576a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5770:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    5773:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    5777:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    577a:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    577d:	48 0f be 11          	movsbq (%rcx),%rdx
    5781:	84 d2                	test   %dl,%dl
    5783:	75 eb                	jne    5770 <handle_http_method+0x70>
    path = strtok_r(NULL, " ", &saveptr);
    5785:	4c 89 f6             	mov    %r14,%rsi
    5788:	4c 89 fa             	mov    %r15,%rdx
    578b:	31 ff                	xor    %edi,%edi
    578d:	e8 4e cc ff ff       	call   23e0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5792:	48 8d 35 a1 39 00 00 	lea    0x39a1(%rip),%rsi        # 913a <_IO_stdin_used+0x13a>
    5799:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    579c:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    579f:	e8 6c cc ff ff       	call   2410 <strcmp@plt>
        handle_get_method(data, buffers, path, client_socket, sockettoken, ring);
    57a4:	4d 89 e9             	mov    %r13,%r9
    57a7:	45 89 e0             	mov    %r12d,%r8d
    57aa:	89 e9                	mov    %ebp,%ecx
    if (strcmp(method, "get") == 0) {
    57ac:	85 c0                	test   %eax,%eax
    57ae:	75 38                	jne    57e8 <handle_http_method+0xe8>
        handle_get_method(data, buffers, path, client_socket, sockettoken, ring);
    57b0:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    57b5:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    57ba:	4c 89 f2             	mov    %r14,%rdx
    57bd:	e8 3e fd ff ff       	call   5500 <handle_get_method>
}
    57c2:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    57c7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    57d0:	75 2e                	jne    5800 <handle_http_method+0x100>
    57d2:	48 83 c4 38          	add    $0x38,%rsp
    57d6:	5b                   	pop    %rbx
    57d7:	5d                   	pop    %rbp
    57d8:	41 5c                	pop    %r12
    57da:	41 5d                	pop    %r13
    57dc:	41 5e                	pop    %r14
    57de:	41 5f                	pop    %r15
    57e0:	c3                   	ret
    57e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, sockettoken, ring);
    57e8:	48 8b 15 29 68 00 00 	mov    0x6829(%rip),%rdx        # c018 <unimplemented_content>
    57ef:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    57f4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    57f9:	e8 42 fa ff ff       	call   5240 <_send_static_string_content>
}
    57fe:	eb c2                	jmp    57c2 <handle_http_method+0xc2>
    5800:	e8 7b cb ff ff       	call   2380 <__stack_chk_fail@plt>
    5805:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005810 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5810:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5814:	85 d2                	test   %edx,%edx
    5816:	7e 38                	jle    5850 <get_line+0x40>
    5818:	48 63 d2             	movslq %edx,%rdx
    581b:	48 83 c7 01          	add    $0x1,%rdi
    581f:	48 01 f2             	add    %rsi,%rdx
    5822:	eb 11                	jmp    5835 <get_line+0x25>
    5824:	0f 1f 40 00          	nopl   0x0(%rax)
    5828:	48 83 c6 01          	add    $0x1,%rsi
    582c:	48 83 c7 01          	add    $0x1,%rdi
    5830:	48 39 d6             	cmp    %rdx,%rsi
    5833:	74 1b                	je     5850 <get_line+0x40>
        dest[i] = src[i];
    5835:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5839:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    583b:	3c 0d                	cmp    $0xd,%al
    583d:	75 e9                	jne    5828 <get_line+0x18>
    583f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5842:	75 e4                	jne    5828 <get_line+0x18>
            dest[i] = '\0';
    5844:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5847:	31 c0                	xor    %eax,%eax
    5849:	c3                   	ret
    584a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5850:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5855:	c3                   	ret
    5856:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005860 <handle_client_request>:
int handle_client_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    5860:	f3 0f 1e fa          	endbr64
    5864:	53                   	push   %rbx
    5865:	49 89 fa             	mov    %rdi,%r10
    5868:	48 89 f3             	mov    %rsi,%rbx
    586b:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    5872:	48 8b 72 10          	mov    0x10(%rdx),%rsi
    5876:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    587f:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5887:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5889:	49 89 e3             	mov    %rsp,%r11
    588c:	4c 8d 84 24 00 04 00 00 	lea    0x400(%rsp),%r8
    5894:	4c 89 d8             	mov    %r11,%rax
    5897:	eb 14                	jmp    58ad <handle_client_request+0x4d>
    5899:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    58a0:	48 83 c0 01          	add    $0x1,%rax
    58a4:	48 83 c6 01          	add    $0x1,%rsi
    58a8:	4c 39 c0             	cmp    %r8,%rax
    58ab:	74 53                	je     5900 <handle_client_request+0xa0>
        dest[i] = src[i];
    58ad:	0f b6 3e             	movzbl (%rsi),%edi
    58b0:	40 88 38             	mov    %dil,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    58b3:	40 80 ff 0d          	cmp    $0xd,%dil
    58b7:	75 e7                	jne    58a0 <handle_client_request+0x40>
    58b9:	80 7e 01 0a          	cmpb   $0xa,0x1(%rsi)
    58bd:	75 e1                	jne    58a0 <handle_client_request+0x40>
            dest[i] = '\0';
    58bf:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    58c2:	8b 42 08             	mov    0x8(%rdx),%eax
    58c5:	49 89 c9             	mov    %rcx,%r9
    58c8:	48 89 de             	mov    %rbx,%rsi
    58cb:	44 8b 42 0c          	mov    0xc(%rdx),%r8d
    58cf:	4c 89 d7             	mov    %r10,%rdi
    58d2:	4c 89 da             	mov    %r11,%rdx
    58d5:	89 c1                	mov    %eax,%ecx
    58d7:	e8 24 fe ff ff       	call   5700 <handle_http_method>
}
    58dc:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    58e4:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    58ed:	75 38                	jne    5927 <handle_client_request+0xc7>
    58ef:	48 81 c4 10 04 00 00 	add    $0x410,%rsp
    58f6:	31 c0                	xor    %eax,%eax
    58f8:	5b                   	pop    %rbx
    58f9:	c3                   	ret
    58fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5900:	48 8b 0d 19 67 00 00 	mov    0x6719(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5907:	ba 12 00 00 00       	mov    $0x12,%edx
    590c:	be 01 00 00 00       	mov    $0x1,%esi
    5911:	48 8d 3d 26 38 00 00 	lea    0x3826(%rip),%rdi        # 913e <_IO_stdin_used+0x13e>
    5918:	e8 23 cc ff ff       	call   2540 <fwrite@plt>
        exit(1);
    591d:	bf 01 00 00 00       	mov    $0x1,%edi
    5922:	e8 f9 cb ff ff       	call   2520 <exit@plt>
}
    5927:	e8 54 ca ff ff       	call   2380 <__stack_chk_fail@plt>
    592c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005930 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5930:	f3 0f 1e fa          	endbr64
    5934:	55                   	push   %rbp
    5935:	53                   	push   %rbx
    5936:	48 89 cb             	mov    %rcx,%rbx
    5939:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    593d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5940:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5943:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5949:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    594c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    594f:	f6 c1 02             	test   $0x2,%cl
    5952:	74 00                	je     5954 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5954:	41 89 c0             	mov    %eax,%r8d
    5957:	45 29 c8             	sub    %r9d,%r8d
    595a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    595e:	0f 82 a8 cc ff ff    	jb     260c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5964:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5967:	8b 6b 44             	mov    0x44(%rbx),%ebp
    596a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    596d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5970:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5973:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5977:	d3 e5                	shl    %cl,%ebp
    5979:	48 c1 e5 06          	shl    $0x6,%rbp
    597d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5981:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5984:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5989:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5990:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5994:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5998:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    59a0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    59a8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    59ac:	e8 bf ca ff ff       	call   2470 <malloc@plt>
  io_uring_submit(ring);
    59b1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    59b4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    59ba:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    59be:	48 83 c4 08          	add    $0x8,%rsp
    59c2:	5b                   	pop    %rbx
    59c3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    59c4:	e9 c7 c9 ff ff       	jmp    2390 <io_uring_submit@plt>
    59c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000059d0 <io_thread>:
void* io_thread(void *arg) {
    59d0:	f3 0f 1e fa          	endbr64
    59d4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    59d6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    59d8:	41 56                	push   %r14
    59da:	41 55                	push   %r13
    59dc:	41 54                	push   %r12
    59de:	49 89 fc             	mov    %rdi,%r12
    59e1:	55                   	push   %rbp
    59e2:	53                   	push   %rbx
    59e3:	48 81 ec 68 05 00 00 	sub    $0x568,%rsp
  struct io_uring ring = *data->ring;
    59ea:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    59f3:	48 89 84 24 58 05 00 00 	mov    %rax,0x558(%rsp)
    59fb:	48 8b 47 60          	mov    0x60(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    59ff:	4c 8d 6c 24 70       	lea    0x70(%rsp),%r13
    5a04:	bf 00 01 00 00       	mov    $0x100,%edi
    5a09:	4c 89 ee             	mov    %r13,%rsi
  struct io_uring ring = *data->ring;
    5a0c:	f3 0f 6f 18          	movdqu (%rax),%xmm3
    5a10:	0f 29 5c 24 70       	movaps %xmm3,0x70(%rsp)
    5a15:	f3 0f 6f 60 10       	movdqu 0x10(%rax),%xmm4
    5a1a:	0f 29 a4 24 80 00 00 00 	movaps %xmm4,0x80(%rsp)
    5a22:	f3 0f 6f 68 20       	movdqu 0x20(%rax),%xmm5
    5a27:	0f 29 ac 24 90 00 00 00 	movaps %xmm5,0x90(%rsp)
    5a2f:	f3 0f 6f 70 30       	movdqu 0x30(%rax),%xmm6
    5a34:	0f 29 b4 24 a0 00 00 00 	movaps %xmm6,0xa0(%rsp)
    5a3c:	f3 0f 6f 78 40       	movdqu 0x40(%rax),%xmm7
    5a41:	0f 29 bc 24 b0 00 00 00 	movaps %xmm7,0xb0(%rsp)
    5a49:	f3 0f 6f 48 50       	movdqu 0x50(%rax),%xmm1
    5a4e:	0f 29 8c 24 c0 00 00 00 	movaps %xmm1,0xc0(%rsp)
    5a56:	f3 0f 6f 58 60       	movdqu 0x60(%rax),%xmm3
    5a5b:	0f 29 9c 24 d0 00 00 00 	movaps %xmm3,0xd0(%rsp)
    5a63:	f3 0f 6f 60 70       	movdqu 0x70(%rax),%xmm4
    5a68:	0f 29 a4 24 e0 00 00 00 	movaps %xmm4,0xe0(%rsp)
    5a70:	f3 0f 6f a8 80 00 00 00 	movdqu 0x80(%rax),%xmm5
    5a78:	0f 29 ac 24 f0 00 00 00 	movaps %xmm5,0xf0(%rsp)
    5a80:	f3 0f 6f b0 90 00 00 00 	movdqu 0x90(%rax),%xmm6
    5a88:	0f 29 b4 24 00 01 00 00 	movaps %xmm6,0x100(%rsp)
    5a90:	f3 0f 6f b8 a0 00 00 00 	movdqu 0xa0(%rax),%xmm7
    5a98:	0f 29 bc 24 10 01 00 00 	movaps %xmm7,0x110(%rsp)
    5aa0:	f3 0f 6f 88 b0 00 00 00 	movdqu 0xb0(%rax),%xmm1
    5aa8:	0f 29 8c 24 20 01 00 00 	movaps %xmm1,0x120(%rsp)
    5ab0:	f3 0f 6f 98 c0 00 00 00 	movdqu 0xc0(%rax),%xmm3
    5ab8:	0f 29 9c 24 30 01 00 00 	movaps %xmm3,0x130(%rsp)
    5ac0:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5ac7:	48 89 84 24 40 01 00 00 	mov    %rax,0x140(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5acf:	e8 7c c9 ff ff       	call   2450 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, data->_eventfd);
    5ad4:	41 8b 74 24 68       	mov    0x68(%r12),%esi
    5ad9:	49 8b 7c 24 60       	mov    0x60(%r12),%rdi
    5ade:	e8 7d ca ff ff       	call   2560 <io_uring_register_eventfd@plt>
  if (data->io_mode == IO_MODE_RECV) {
    5ae3:	41 8b 84 24 0c 01 00 00 	mov    0x10c(%r12),%eax
    5aeb:	83 f8 01             	cmp    $0x1,%eax
    5aee:	0f 84 a0 0b 00 00    	je     6694 <io_thread+0xcc4>
  if (data->io_mode == IO_MODE_SEND) {
    5af4:	85 c0                	test   %eax,%eax
    5af6:	0f 85 ad 07 00 00    	jne    62a9 <io_thread+0x8d9>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5afc:	48 8d 3d ed 3b 00 00 	lea    0x3bed(%rip),%rdi        # 96f0 <_IO_stdin_used+0x6f0>
    5b03:	e8 28 c8 ff ff       	call   2330 <puts@plt>
    int epollfd = epoll_create1(0);
    5b08:	31 ff                	xor    %edi,%edi
    5b0a:	e8 91 ca ff ff       	call   25a0 <epoll_create1@plt>
    5b0f:	89 04 24             	mov    %eax,(%rsp)
				if (epollfd == -1) {
    5b12:	83 f8 ff             	cmp    $0xffffffff,%eax
    5b15:	0f 84 19 cb ff ff    	je     2634 <io_thread.cold+0x1e>
    5b1b:	89 c2                	mov    %eax,%edx
    5b1d:	48 8d 35 ae 36 00 00 	lea    0x36ae(%rip),%rsi        # 91d2 <_IO_stdin_used+0x1d2>
    5b24:	bf 01 00 00 00       	mov    $0x1,%edi
    5b29:	31 c0                	xor    %eax,%eax
    5b2b:	e8 80 c9 ff ff       	call   24b0 <__printf_chk@plt>
    5b30:	48 8d 3d f1 3b 00 00 	lea    0x3bf1(%rip),%rdi        # 9728 <_IO_stdin_used+0x728>
    5b37:	e8 f4 c7 ff ff       	call   2330 <puts@plt>
    5b3c:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    5b44:	31 c0                	xor    %eax,%eax
    5b46:	41 8b 8c 24 1c 01 00 00 	mov    0x11c(%r12),%ecx
    5b4e:	45 8b 84 24 18 01 00 00 	mov    0x118(%r12),%r8d
    5b56:	48 8d 35 03 3c 00 00 	lea    0x3c03(%rip),%rsi        # 9760 <_IO_stdin_used+0x760>
    5b5d:	bf 01 00 00 00       	mov    $0x1,%edi
    5b62:	e8 49 c9 ff ff       	call   24b0 <__printf_chk@plt>
    void * _reply = bufferrecv("waitsocketreply", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET, &reply, 0); 
    5b67:	49 63 94 24 1c 01 00 00 	movslq 0x11c(%r12),%rdx
    5b6f:	48 c1 e2 04          	shl    $0x4,%rdx
    5b73:	49 03 94 24 10 01 00 00 	add    0x110(%r12),%rdx
  while (data->running == 1) {
    5b7b:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5b81:	0f 85 99 ca ff ff    	jne    2620 <io_thread.cold+0xa>
      for (int x = 0 ; x < buffers->count ; x++) {
    5b87:	48 63 02             	movslq (%rdx),%rax
    5b8a:	85 c0                	test   %eax,%eax
    5b8c:	7e ed                	jle    5b7b <io_thread+0x1ab>
    5b8e:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    5b92:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    5b96:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    5b9a:	eb 0d                	jmp    5ba9 <io_thread+0x1d9>
    5b9c:	0f 1f 40 00          	nopl   0x0(%rax)
    5ba0:	48 83 c3 28          	add    $0x28,%rbx
    5ba4:	48 39 c3             	cmp    %rax,%rbx
    5ba7:	74 d2                	je     5b7b <io_thread+0x1ab>
        if (buffers->buffer[x].available == 1) {
    5ba9:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    5bad:	75 f1                	jne    5ba0 <io_thread+0x1d0>
          if (buffers->buffer[x].kind == kind) {
    5baf:	44 8b 43 20          	mov    0x20(%rbx),%r8d
    5bb3:	45 85 c0             	test   %r8d,%r8d
    5bb6:	75 e8                	jne    5ba0 <io_thread+0x1d0>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    5bb8:	be 28 00 00 00       	mov    $0x28,%esi
    5bbd:	bf 01 00 00 00       	mov    $0x1,%edi
    5bc2:	e8 39 c8 ff ff       	call   2400 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    5bc7:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    5bca:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            reply->kind = buffers->buffer[x].kind;
    5bd1:	c7 40 20 00 00 00 00 	movl   $0x0,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    5bd8:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    5bdb:	0f ae f8             	sfence
    struct NewSocketMessage *msg = bufferreply->data;
    5bde:	48 8b 18             	mov    (%rax),%rbx
    5be1:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    5be9:	48 8d 35 b0 3b 00 00 	lea    0x3bb0(%rip),%rsi        # 97a0 <_IO_stdin_used+0x7a0>
    5bf0:	31 c0                	xor    %eax,%eax
    5bf2:	bf 01 00 00 00       	mov    $0x1,%edi
    5bf7:	8b 0b                	mov    (%rbx),%ecx
    5bf9:	e8 b2 c8 ff ff       	call   24b0 <__printf_chk@plt>
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    5bfe:	be 04 00 00 00       	mov    $0x4,%esi
    5c03:	bf 01 00 00 00       	mov    $0x1,%edi
    5c08:	e8 f3 c7 ff ff       	call   2400 <calloc@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    5c0d:	49 63 8c 24 18 01 00 00 	movslq 0x118(%r12),%rcx
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    5c15:	48 89 c6             	mov    %rax,%rsi
    ourreply->nothing = msg->socket;
    5c18:	8b 03                	mov    (%rbx),%eax
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    5c1a:	48 c1 e1 04          	shl    $0x4,%rcx
    5c1e:	49 03 8c 24 10 01 00 00 	add    0x110(%r12),%rcx
  while (data->running == 1) {
    5c26:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    ourreply->nothing = msg->socket;
    5c2c:	89 06                	mov    %eax,(%rsi)
  while (data->running == 1) {
    5c2e:	75 45                	jne    5c75 <io_thread+0x2a5>
      for (int x = 0 ; x < buffers->count ; x++) {
    5c30:	48 63 11             	movslq (%rcx),%rdx
    5c33:	85 d2                	test   %edx,%edx
    5c35:	0f 8e 48 0a 00 00    	jle    6683 <io_thread+0xcb3>
    5c3b:	48 8b 41 08          	mov    0x8(%rcx),%rax
    5c3f:	48 8d 14 92          	lea    (%rdx,%rdx,4),%rdx
    5c43:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    5c47:	eb 14                	jmp    5c5d <io_thread+0x28d>
    5c49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5c50:	48 83 c0 28          	add    $0x28,%rax
    5c54:	48 39 d0             	cmp    %rdx,%rax
    5c57:	0f 84 26 0a 00 00    	je     6683 <io_thread+0xcb3>
        if (buffers->buffer[x].available == 0) {
    5c5d:	8b 78 08             	mov    0x8(%rax),%edi
    5c60:	85 ff                	test   %edi,%edi
    5c62:	75 ec                	jne    5c50 <io_thread+0x280>
          buffers->buffer[x].data = send;
    5c64:	48 89 30             	mov    %rsi,(%rax)
          buffers->buffer[x].kind = kind;
    5c67:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
          buffers->buffer[x].available = 1;
    5c6e:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    5c75:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    5c7d:	48 8d 35 54 3b 00 00 	lea    0x3b54(%rip),%rsi        # 97d8 <_IO_stdin_used+0x7d8>
    5c84:	bf 01 00 00 00       	mov    $0x1,%edi
    5c89:	31 c0                	xor    %eax,%eax
    5c8b:	e8 20 c8 ff ff       	call   24b0 <__printf_chk@plt>
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    5c90:	49 63 94 24 1c 01 00 00 	movslq 0x11c(%r12),%rdx
    5c98:	48 c1 e2 04          	shl    $0x4,%rdx
    5c9c:	49 03 94 24 10 01 00 00 	add    0x110(%r12),%rdx
  while (data->running == 1) {
    5ca4:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5caa:	0f 85 05 06 00 00    	jne    62b5 <io_thread+0x8e5>
      for (int x = 0 ; x < buffers->count ; x++) {
    5cb0:	48 63 02             	movslq (%rdx),%rax
    5cb3:	85 c0                	test   %eax,%eax
    5cb5:	7e ed                	jle    5ca4 <io_thread+0x2d4>
    5cb7:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    5cbb:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    5cbf:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    5cc3:	eb 0c                	jmp    5cd1 <io_thread+0x301>
    5cc5:	0f 1f 00             	nopl   (%rax)
    5cc8:	48 83 c3 28          	add    $0x28,%rbx
    5ccc:	48 39 c3             	cmp    %rax,%rbx
    5ccf:	74 d3                	je     5ca4 <io_thread+0x2d4>
        if (buffers->buffer[x].available == 1) {
    5cd1:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    5cd5:	75 f1                	jne    5cc8 <io_thread+0x2f8>
          if (buffers->buffer[x].kind == kind) {
    5cd7:	83 7b 20 02          	cmpl   $0x2,0x20(%rbx)
    5cdb:	75 eb                	jne    5cc8 <io_thread+0x2f8>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    5cdd:	be 28 00 00 00       	mov    $0x28,%esi
    5ce2:	bf 01 00 00 00       	mov    $0x1,%edi
    5ce7:	e8 14 c7 ff ff       	call   2400 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    5cec:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    5cef:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            reply->kind = buffers->buffer[x].kind;
    5cf6:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    5cfd:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    5d00:	0f ae f8             	sfence
  struct NewClientMessage *newclientmsg = newclient->data;
    5d03:	4c 8b 38             	mov    (%rax),%r15
    if (newclient_message == NULL) {
    5d06:	4d 85 ff             	test   %r15,%r15
    5d09:	0f 84 a6 05 00 00    	je     62b5 <io_thread+0x8e5>
    int new_client_socket = newclient_message->socket;
    5d0f:	45 8b 37             	mov    (%r15),%r14d
    if (new_client_socket == -1) {
    5d12:	41 83 fe ff          	cmp    $0xffffffff,%r14d
    5d16:	0f 84 50 11 00 00    	je     6e6c <io_thread+0x149c>
    5d1c:	44 89 f2             	mov    %r14d,%edx
    5d1f:	48 8d 35 c1 34 00 00 	lea    0x34c1(%rip),%rsi        # 91e7 <_IO_stdin_used+0x1e7>
    5d26:	bf 01 00 00 00       	mov    $0x1,%edi
    5d2b:	31 c0                	xor    %eax,%eax
    5d2d:	e8 7e c7 ff ff       	call   24b0 <__printf_chk@plt>
    struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    5d32:	be 0c 00 00 00       	mov    $0xc,%esi
    5d37:	bf 01 00 00 00       	mov    $0x1,%edi
    5d3c:	e8 bf c6 ff ff       	call   2400 <calloc@plt>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    5d41:	bf 01 00 00 00       	mov    $0x1,%edi
    5d46:	be 10 00 00 00       	mov    $0x10,%esi
    ev->events = EPOLLOUT;
    5d4b:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
    ev->data.fd = new_client_socket;
    5d51:	44 89 70 04          	mov    %r14d,0x4(%rax)
    struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    5d55:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    5d5a:	e8 a1 c6 ff ff       	call   2400 <calloc@plt>
    void *buf = malloc(size);
    5d5f:	bf 0a 00 00 00       	mov    $0xa,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    5d64:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    5d67:	e8 04 c7 ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    5d6c:	48 85 c0             	test   %rax,%rax
    5d6f:	0f 84 cb 10 00 00    	je     6e40 <io_thread+0x1470>
    iov->iov_base = zh_malloc(10);
    5d75:	48 89 03             	mov    %rax,(%rbx)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    5d78:	be 20 00 00 00       	mov    $0x20,%esi
    5d7d:	bf 01 00 00 00       	mov    $0x1,%edi
    iov->iov_len = 10;
    5d82:	48 c7 43 08 0a 00 00 00 	movq   $0xa,0x8(%rbx)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    5d8a:	e8 71 c6 ff ff       	call   2400 <calloc@plt>
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    5d8f:	be 20 00 00 00       	mov    $0x20,%esi
    5d94:	bf 01 00 00 00       	mov    $0x1,%edi
    eventfdstop->kind = 3; 
    5d99:	c7 00 03 00 00 00    	movl   $0x3,(%rax)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    5d9f:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    5da4:	e8 57 c6 ff ff       	call   2400 <calloc@plt>
    io_uring_register_eventfd(data->ring, data->dataeventfd);
    5da9:	41 8b 74 24 6c       	mov    0x6c(%r12),%esi
    5dae:	49 8b 7c 24 60       	mov    0x60(%r12),%rdi
    removed->kind = 7; 
    5db3:	c7 00 07 00 00 00    	movl   $0x7,(%rax)
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    5db9:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    io_uring_register_eventfd(data->ring, data->dataeventfd);
    5dbe:	e8 9d c7 ff ff       	call   2560 <io_uring_register_eventfd@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5dc3:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5dca:	8b 94 24 30 01 00 00 	mov    0x130(%rsp),%edx
	unsigned int head, next = sq->sqe_tail + 1;
    5dd1:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    5dd4:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    5dd9:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5ddb:	f6 c2 02             	test   $0x2,%dl
    5dde:	0f 85 c4 0e 00 00    	jne    6ca8 <io_thread+0x12d8>
	if (next - head <= sq->ring_entries) {
    5de4:	89 f1                	mov    %esi,%ecx
    5de6:	29 c1                	sub    %eax,%ecx
    5de8:	39 8c 24 cc 00 00 00 	cmp    %ecx,0xcc(%rsp)
    5def:	0f 82 66 c8 ff ff    	jb     265b <io_thread.cold+0x45>
	if (ring->flags & IORING_SETUP_SQE128)
    5df5:	c1 ea 0a             	shr    $0xa,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5df8:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	sqe->addr3 = 0;
    5dff:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e03:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5e0a:	89 d1                	mov    %edx,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e0c:	41 89 c1             	mov    %eax,%r9d
	sqe->fd = fd;
    5e0f:	8b 04 24             	mov    (%rsp),%eax
		sq->sqe_tail = next;
    5e12:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
    5e19:	83 e1 01             	and    $0x1,%ecx
          struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    5e1c:	be 20 00 00 00       	mov    $0x20,%esi
    5e21:	bf 01 00 00 00       	mov    $0x1,%edi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e26:	41 d3 e1             	shl    %cl,%r9d
    5e29:	49 c1 e1 06          	shl    $0x6,%r9
    5e2d:	4c 03 8c 24 a8 00 00 00 	add    0xa8(%rsp),%r9
	sqe->fd = fd;
    5e35:	41 89 41 04          	mov    %eax,0x4(%r9)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    5e39:	44 89 f0             	mov    %r14d,%eax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e3c:	4c 89 cd             	mov    %r9,%rbp
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    5e3f:	49 89 41 08          	mov    %rax,0x8(%r9)
	sqe->addr = (unsigned long) addr;
    5e43:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
	sqe->opcode = (__u8) op;
    5e48:	41 c7 01 1d 00 00 00 	movl   $0x1d,(%r9)
	sqe->addr = (unsigned long) addr;
    5e4f:	49 89 41 10          	mov    %rax,0x10(%r9)
	sqe->len = len;
    5e53:	49 c7 41 18 01 00 00 00 	movq   $0x1,0x18(%r9)
	sqe->buf_index = 0;
    5e5b:	49 c7 41 28 00 00 00 00 	movq   $0x0,0x28(%r9)
	sqe->addr3 = 0;
    5e63:	41 0f 11 41 30       	movups %xmm0,0x30(%r9)
    5e68:	e8 93 c5 ff ff       	call   2400 <calloc@plt>
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    5e6d:	be 18 00 00 00       	mov    $0x18,%esi
    5e72:	bf 01 00 00 00       	mov    $0x1,%edi
          readywriting->kind = 4; 
    5e77:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
    5e7d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    5e82:	e8 79 c5 ff ff       	call   2400 <calloc@plt>
          rr->sockettoken = newclient_message->sockettoken; 
    5e87:	41 8b 4f 04          	mov    0x4(%r15),%ecx
          readywriting->data = rr; 
    5e8b:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
          io_uring_submit(&ring);
    5e90:	4c 89 ef             	mov    %r13,%rdi
          rr->client_socket = new_client_socket; 
    5e93:	44 89 30             	mov    %r14d,(%rax)
          rr->sockettoken = newclient_message->sockettoken; 
    5e96:	89 48 10             	mov    %ecx,0x10(%rax)
          readywriting->data = rr; 
    5e99:	48 89 42 08          	mov    %rax,0x8(%rdx)
          readywriting->event = ev; 
    5e9d:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    5ea2:	48 89 42 10          	mov    %rax,0x10(%rdx)
	sqe->user_data = (unsigned long) data;
    5ea6:	48 89 55 20          	mov    %rdx,0x20(%rbp)
          io_uring_submit(&ring);
    5eaa:	e8 e1 c4 ff ff       	call   2390 <io_uring_submit@plt>
    struct SendUserData *dataavailable = calloc(1, sizeof(struct SendUserData));
    5eaf:	be 20 00 00 00       	mov    $0x20,%esi
    5eb4:	bf 01 00 00 00       	mov    $0x1,%edi
    5eb9:	e8 42 c5 ff ff       	call   2400 <calloc@plt>
    5ebe:	41 8b 54 24 6c       	mov    0x6c(%r12),%edx
    5ec3:	bf 01 00 00 00       	mov    $0x1,%edi
    5ec8:	48 8d 35 2b 33 00 00 	lea    0x332b(%rip),%rsi        # 91fa <_IO_stdin_used+0x1fa>
    dataavailable->kind = 8; 
    5ecf:	c7 00 08 00 00 00    	movl   $0x8,(%rax)
    struct SendUserData *dataavailable = calloc(1, sizeof(struct SendUserData));
    5ed5:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5eda:	31 c0                	xor    %eax,%eax
    5edc:	e8 cf c5 ff ff       	call   24b0 <__printf_chk@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5ee1:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    5ee8:	8d 50 01             	lea    0x1(%rax),%edx
	if (ring->flags & IORING_SETUP_SQE128)
    5eeb:	8b 84 24 30 01 00 00 	mov    0x130(%rsp),%eax
    5ef2:	89 c1                	mov    %eax,%ecx
    5ef4:	c1 e9 0a             	shr    $0xa,%ecx
    5ef7:	83 e1 01             	and    $0x1,%ecx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5efa:	a8 02                	test   $0x2,%al
		head = IO_URING_READ_ONCE(*sq->khead);
    5efc:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    5f01:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5f03:	0f 85 a4 0d 00 00    	jne    6cad <io_thread+0x12dd>
	if (next - head <= sq->ring_entries) {
    5f09:	89 d6                	mov    %edx,%esi
    5f0b:	29 c6                	sub    %eax,%esi
    5f0d:	39 b4 24 cc 00 00 00 	cmp    %esi,0xcc(%rsp)
    5f14:	0f 82 10 c7 ff ff    	jb     262a <io_thread.cold+0x14>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f1a:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	sqe->addr3 = 0;
    5f21:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(&ring);
    5f25:	4c 89 ef             	mov    %r13,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f28:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
		sq->sqe_tail = next;
    5f2f:	89 94 24 b4 00 00 00 	mov    %edx,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f36:	d3 e0                	shl    %cl,%eax
    io_uring_prep_readv(sqe, data->dataeventfd, iov, 1, 0);
    5f38:	41 8b 54 24 6c       	mov    0x6c(%r12),%edx
	sqe->user_data = (unsigned long) data;
    5f3d:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f42:	48 c1 e0 06          	shl    $0x6,%rax
    5f46:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->opcode = (__u8) op;
    5f4e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5f54:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5f57:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5f5f:	48 89 58 10          	mov    %rbx,0x10(%rax)
	sqe->len = len;
    5f63:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5f6b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5f73:	48 89 48 20          	mov    %rcx,0x20(%rax)
	sqe->addr3 = 0;
    5f77:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(&ring);
    5f7b:	e8 10 c4 ff ff       	call   2390 <io_uring_submit@plt>
    while (data->running == 1) {
    5f80:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5f86:	0f 85 11 03 00 00    	jne    629d <io_thread+0x8cd>
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
    5f8c:	0f 1f 40 00          	nopl   0x0(%rax)
    5f90:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5f96:	0f 85 ac 01 00 00    	jne    6148 <io_thread+0x778>
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    5f9c:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    5fa4:	48 c1 e0 04          	shl    $0x4,%rax
    5fa8:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
      for (int x = 0 ; x < buffers->count ; x++) {
    5fb0:	48 63 10             	movslq (%rax),%rdx
    5fb3:	85 d2                	test   %edx,%edx
    5fb5:	0f 8e 8d 01 00 00    	jle    6148 <io_thread+0x778>
    5fbb:	4c 8b 70 08          	mov    0x8(%rax),%r14
    5fbf:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    5fc3:	49 8d 04 c6          	lea    (%r14,%rax,8),%rax
    5fc7:	eb 14                	jmp    5fdd <io_thread+0x60d>
    5fc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5fd0:	49 83 c6 28          	add    $0x28,%r14
    5fd4:	49 39 c6             	cmp    %rax,%r14
    5fd7:	0f 84 6b 01 00 00    	je     6148 <io_thread+0x778>
        if (buffers->buffer[x].available == 1) {
    5fdd:	41 83 7e 08 01       	cmpl   $0x1,0x8(%r14)
    5fe2:	75 ec                	jne    5fd0 <io_thread+0x600>
          if (buffers->buffer[x].kind == kind) {
    5fe4:	41 83 7e 20 02       	cmpl   $0x2,0x20(%r14)
    5fe9:	75 e5                	jne    5fd0 <io_thread+0x600>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    5feb:	be 28 00 00 00       	mov    $0x28,%esi
    5ff0:	bf 01 00 00 00       	mov    $0x1,%edi
    5ff5:	e8 06 c4 ff ff       	call   2400 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    5ffa:	49 8b 16             	mov    (%r14),%rdx
            buffers->buffer[x].available = 0;
    5ffd:	41 c7 46 08 00 00 00 00 	movl   $0x0,0x8(%r14)
            reply->kind = buffers->buffer[x].kind;
    6005:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    600c:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    600f:	0f ae f8             	sfence
  struct NewClientMessage *newclientmsg = newclient->data;
    6012:	4c 8b 38             	mov    (%rax),%r15
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
    6015:	4d 85 ff             	test   %r15,%r15
    6018:	0f 84 2a 01 00 00    	je     6148 <io_thread+0x778>
    601e:	45 8b 37             	mov    (%r15),%r14d
    6021:	45 85 f6             	test   %r14d,%r14d
    6024:	0f 84 1e 01 00 00    	je     6148 <io_thread+0x778>
          if (new_client_socket != -1) {
    602a:	41 83 fe ff          	cmp    $0xffffffff,%r14d
    602e:	0f 84 5c ff ff ff    	je     5f90 <io_thread+0x5c0>
            struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    6034:	be 0c 00 00 00       	mov    $0xc,%esi
    6039:	bf 01 00 00 00       	mov    $0x1,%edi
    603e:	e8 bd c3 ff ff       	call   2400 <calloc@plt>
            struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    6043:	be 20 00 00 00       	mov    $0x20,%esi
    6048:	bf 01 00 00 00       	mov    $0x1,%edi
            ev->events = EPOLLOUT;
    604d:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
            ev->data.fd = new_client_socket;
    6053:	44 89 70 04          	mov    %r14d,0x4(%rax)
    6057:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
            struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    605c:	e8 9f c3 ff ff       	call   2400 <calloc@plt>
            readywriting->event = ev;
    6061:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
            readywriting->sockettoken = ncm->sockettoken;
    6066:	45 8b 7f 04          	mov    0x4(%r15),%r15d
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    606a:	be 18 00 00 00       	mov    $0x18,%esi
            readywriting->kind = 4; 
    606f:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    6075:	bf 01 00 00 00       	mov    $0x1,%edi
            readywriting->event = ev;
    607a:	4c 89 40 10          	mov    %r8,0x10(%rax)
            readywriting->sockettoken = ncm->sockettoken;
    607e:	44 89 78 18          	mov    %r15d,0x18(%rax)
            readywriting->event = ev;
    6082:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
            readywriting->sockettoken = ncm->sockettoken;
    6087:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    608c:	e8 6f c3 ff ff       	call   2400 <calloc@plt>
            readywriting->data = rr; 
    6091:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
		head = IO_URING_READ_ONCE(*sq->khead);
    6096:	48 8b 7c 24 70       	mov    0x70(%rsp),%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    609b:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    60a2:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
            rr->client_socket = new_client_socket; 
    60a7:	44 89 30             	mov    %r14d,(%rax)
            rr->sockettoken = ncm->sockettoken; 
    60aa:	44 89 78 10          	mov    %r15d,0x10(%rax)
            readywriting->data = rr; 
    60ae:	48 89 42 08          	mov    %rax,0x8(%rdx)
	unsigned int head, next = sq->sqe_tail + 1;
    60b2:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    60b9:	f6 c1 02             	test   $0x2,%cl
	unsigned int head, next = sq->sqe_tail + 1;
    60bc:	8d 70 01             	lea    0x1(%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    60bf:	0f 85 c8 02 00 00    	jne    638d <io_thread+0x9bd>
		head = IO_URING_READ_ONCE(*sq->khead);
    60c5:	44 8b 0f             	mov    (%rdi),%r9d
	if (next - head <= sq->ring_entries) {
    60c8:	89 f7                	mov    %esi,%edi
    60ca:	44 29 cf             	sub    %r9d,%edi
    60cd:	39 bc 24 cc 00 00 00 	cmp    %edi,0xcc(%rsp)
    60d4:	0f 82 9c 0d 00 00    	jb     6e76 <io_thread+0x14a6>
	if (ring->flags & IORING_SETUP_SQE128)
    60da:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    60dd:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
	sqe->addr3 = 0;
    60e4:	66 0f ef c0          	pxor   %xmm0,%xmm0
            io_uring_submit(&ring);
    60e8:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    60eb:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    60ee:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    60f5:	d3 e0                	shl    %cl,%eax
	sqe->fd = fd;
    60f7:	8b 0c 24             	mov    (%rsp),%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    60fa:	48 c1 e0 06          	shl    $0x6,%rax
    60fe:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->fd = fd;
    6106:	89 48 04             	mov    %ecx,0x4(%rax)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6109:	44 89 f1             	mov    %r14d,%ecx
	sqe->opcode = (__u8) op;
    610c:	c7 00 1d 00 00 00    	movl   $0x1d,(%rax)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6112:	48 89 48 08          	mov    %rcx,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    6116:	4c 89 40 10          	mov    %r8,0x10(%rax)
	sqe->len = len;
    611a:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    6122:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    612a:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    612e:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    6132:	e8 59 c2 ff ff       	call   2390 <io_uring_submit@plt>
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
    6137:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    613d:	0f 84 59 fe ff ff    	je     5f9c <io_thread+0x5cc>
    6143:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        struct __kernel_timespec delay = {
    6148:	66 0f 6f 15 c0 3c 00 00 	movdqa 0x3cc0(%rip),%xmm2        # 9e10 <_IO_stdin_used+0xe10>
        int ret = io_uring_wait_cqe_timeout(&ring, &cqe, &delay);
    6150:	48 8d 54 24 40       	lea    0x40(%rsp),%rdx
    6155:	48 8d 74 24 38       	lea    0x38(%rsp),%rsi
    615a:	4c 89 ef             	mov    %r13,%rdi
        struct __kernel_timespec delay = {
    615d:	0f 29 54 24 40       	movaps %xmm2,0x40(%rsp)
        int ret = io_uring_wait_cqe_timeout(&ring, &cqe, &delay);
    6162:	e8 79 c3 ff ff       	call   24e0 <io_uring_wait_cqe_timeout@plt>
        if (ret < 0) { continue; }
    6167:	85 c0                	test   %eax,%eax
    6169:	0f 88 11 fe ff ff    	js     5f80 <io_thread+0x5b0>
        if (((struct SendUserData*) cqe->user_data)->kind == 3) {
    616f:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    6174:	4c 8b 3a             	mov    (%rdx),%r15
    6177:	41 8b 07             	mov    (%r15),%eax
    617a:	4c 89 f9             	mov    %r15,%rcx
    617d:	83 f8 03             	cmp    $0x3,%eax
    6180:	0f 84 9d 0b 00 00    	je     6d23 <io_thread+0x1353>
        if (((struct SendUserData*) cqe->user_data)->kind == 8) {
    6186:	83 f8 08             	cmp    $0x8,%eax
    6189:	0f 84 1d 02 00 00    	je     63ac <io_thread+0x9dc>
        if (((struct SendUserData*) cqe->user_data)->kind == 4) {
    618f:	83 f8 04             	cmp    $0x4,%eax
    6192:	0f 84 3a 02 00 00    	je     63d2 <io_thread+0xa02>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
    6198:	83 f8 05             	cmp    $0x5,%eax
    619b:	0f 84 3f 01 00 00    	je     62e0 <io_thread+0x910>
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    61a1:	83 f8 07             	cmp    $0x7,%eax
    61a4:	0f 84 cf 01 00 00    	je     6379 <io_thread+0x9a9>
	unsigned int head, next = sq->sqe_tail + 1;
    61aa:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    61b1:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    61b8:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    61bb:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    61c0:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    61c2:	f6 c1 02             	test   $0x2,%cl
    61c5:	74 00                	je     61c7 <io_thread+0x7f7>
	if (next - head <= sq->ring_entries) {
    61c7:	89 d0                	mov    %edx,%eax
    61c9:	29 f0                	sub    %esi,%eax
    61cb:	39 84 24 cc 00 00 00 	cmp    %eax,0xcc(%rsp)
    61d2:	0f 82 8d c4 ff ff    	jb     2665 <io_thread.cold+0x4f>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    61d8:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    61df:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    61e2:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
          io_uring_submit(&ring);
    61e9:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    61ec:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    61ef:	41 89 c7             	mov    %eax,%r15d
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    61f2:	41 8b 44 24 68       	mov    0x68(%r12),%eax
	sqe->addr3 = 0;
    61f7:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    61fb:	41 d3 e7             	shl    %cl,%r15d
		sq->sqe_tail = next;
    61fe:	89 94 24 b4 00 00 00 	mov    %edx,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6205:	49 c1 e7 06          	shl    $0x6,%r15
    6209:	4c 03 bc 24 a8 00 00 00 	add    0xa8(%rsp),%r15
	sqe->fd = fd;
    6211:	41 89 47 04          	mov    %eax,0x4(%r15)
	sqe->user_data = (unsigned long) data;
    6215:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
	sqe->opcode = (__u8) op;
    621a:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
	sqe->off = offset;
    6221:	49 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%r15)
	sqe->addr = (unsigned long) addr;
    6229:	49 89 5f 10          	mov    %rbx,0x10(%r15)
	sqe->len = len;
    622d:	49 c7 47 18 01 00 00 00 	movq   $0x1,0x18(%r15)
	sqe->buf_index = 0;
    6235:	49 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%r15)
	sqe->user_data = (unsigned long) data;
    623d:	49 89 47 20          	mov    %rax,0x20(%r15)
	sqe->addr3 = 0;
    6241:	41 0f 11 47 30       	movups %xmm0,0x30(%r15)
          io_uring_submit(&ring);
    6246:	e8 45 c1 ff ff       	call   2390 <io_uring_submit@plt>
          io_uring_prep_readv(sqe, data->dataeventfd, iov, 1, 0);
    624b:	41 8b 44 24 6c       	mov    0x6c(%r12),%eax
	sqe->addr = (unsigned long) addr;
    6250:	49 89 5f 10          	mov    %rbx,0x10(%r15)
	sqe->addr3 = 0;
    6254:	66 0f ef c0          	pxor   %xmm0,%xmm0
	sqe->opcode = (__u8) op;
    6258:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
          io_uring_submit(&ring);
    625f:	4c 89 ef             	mov    %r13,%rdi
	sqe->fd = fd;
    6262:	41 89 47 04          	mov    %eax,0x4(%r15)
	sqe->user_data = (unsigned long) data;
    6266:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
	sqe->off = offset;
    626b:	49 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%r15)
	sqe->len = len;
    6273:	49 c7 47 18 01 00 00 00 	movq   $0x1,0x18(%r15)
	sqe->buf_index = 0;
    627b:	49 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%r15)
	sqe->user_data = (unsigned long) data;
    6283:	49 89 47 20          	mov    %rax,0x20(%r15)
	sqe->addr3 = 0;
    6287:	41 0f 11 47 30       	movups %xmm0,0x30(%r15)
    628c:	e8 ff c0 ff ff       	call   2390 <io_uring_submit@plt>
    while (data->running == 1) {
    6291:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6297:	0f 84 ef fc ff ff    	je     5f8c <io_thread+0x5bc>
    629d:	48 8d 3d 6b 2f 00 00 	lea    0x2f6b(%rip),%rdi        # 920f <_IO_stdin_used+0x20f>
    62a4:	e8 87 c0 ff ff       	call   2330 <puts@plt>
    62a9:	48 8d 3d 6e 2f 00 00 	lea    0x2f6e(%rip),%rdi        # 921e <_IO_stdin_used+0x21e>
    62b0:	e8 7b c0 ff ff       	call   2330 <puts@plt>
}
    62b5:	48 8b 84 24 58 05 00 00 	mov    0x558(%rsp),%rax
    62bd:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    62c6:	0f 85 9b 0b 00 00    	jne    6e67 <io_thread+0x1497>
    62cc:	48 81 c4 68 05 00 00 	add    $0x568,%rsp
    62d3:	31 c0                	xor    %eax,%eax
    62d5:	5b                   	pop    %rbx
    62d6:	5d                   	pop    %rbp
    62d7:	41 5c                	pop    %r12
    62d9:	41 5d                	pop    %r13
    62db:	41 5e                	pop    %r14
    62dd:	41 5f                	pop    %r15
    62df:	c3                   	ret
          struct Request *req = ((struct SendUserData *) cqe->user_data)->data;
    62e0:	4c 8b 79 08          	mov    0x8(%rcx),%r15
          if (cqe->res < 0) {
    62e4:	8b 42 08             	mov    0x8(%rdx),%eax
              fprintf(stderr, "Async request failed: %s for event: %d\n",
    62e7:	45 8b 37             	mov    (%r15),%r14d
          if (cqe->res < 0) {
    62ea:	85 c0                	test   %eax,%eax
    62ec:	0f 88 5d 0a 00 00    	js     6d4f <io_thread+0x137f>
          switch (req->event_type) {
    62f2:	41 83 fe 01          	cmp    $0x1,%r14d
    62f6:	0f 84 61 03 00 00    	je     665d <io_thread+0xc8d>
    62fc:	41 83 fe 02          	cmp    $0x2,%r14d
    6300:	0f 85 5f 03 00 00    	jne    6665 <io_thread+0xc95>
	sqe->fd = fd;
    6306:	8b 04 24             	mov    (%rsp),%eax
                  io_uring_prep_epoll_ctl(sqe, epollfd, req->client_socket, EPOLL_CTL_DEL, ((struct SendUserData *) cqe->user_data)->event);
    6309:	f3 0f 7e 49 10       	movq   0x10(%rcx),%xmm1
                  io_uring_submit(&ring);
    630e:	4c 89 ef             	mov    %r13,%rdi
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6311:	66 41 0f 6e 47 08    	movd   0x8(%r15),%xmm0
	sqe->opcode = (__u8) op;
    6317:	c7 45 00 1d 00 00 00 	movl   $0x1d,0x0(%rbp)
	sqe->fd = fd;
    631e:	89 45 04             	mov    %eax,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    6321:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
	sqe->off = offset;
    6326:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
	sqe->len = len;
    632a:	48 c7 45 18 02 00 00 00 	movq   $0x2,0x18(%rbp)
	sqe->buf_index = 0;
    6332:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->user_data = (unsigned long) data;
    633a:	48 89 45 20          	mov    %rax,0x20(%rbp)
	sqe->off = offset;
    633e:	0f 11 45 08          	movups %xmm0,0x8(%rbp)
	sqe->addr3 = 0;
    6342:	66 0f ef c0          	pxor   %xmm0,%xmm0
    6346:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    634a:	e8 41 c0 ff ff       	call   2390 <io_uring_submit@plt>
                  close(req->client_socket);
    634f:	41 8b 7f 08          	mov    0x8(%r15),%edi
    6353:	e8 78 c0 ff ff       	call   23d0 <close@plt>
            io_uring_cqe_seen(&ring, cqe);
    6358:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    635d:	48 85 c0             	test   %rax,%rax
    6360:	0f 85 ff 02 00 00    	jne    6665 <io_thread+0xc95>
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    6366:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    636e:	8b 00                	mov    (%rax),%eax
    6370:	83 f8 07             	cmp    $0x7,%eax
    6373:	0f 85 31 fe ff ff    	jne    61aa <io_thread+0x7da>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6379:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6381:	8b 02                	mov    (%rdx),%eax
    6383:	83 c0 01             	add    $0x1,%eax
    6386:	89 02                	mov    %eax,(%rdx)
}
    6388:	e9 1d fe ff ff       	jmp    61aa <io_thread+0x7da>
		head = io_uring_smp_load_acquire(sq->khead);
    638d:	8b 3f                	mov    (%rdi),%edi
	if (next - head <= sq->ring_entries) {
    638f:	89 f0                	mov    %esi,%eax
    6391:	29 f8                	sub    %edi,%eax
    6393:	39 84 24 cc 00 00 00 	cmp    %eax,0xcc(%rsp)
    639a:	0f 82 09 c3 ff ff    	jb     26a9 <io_thread.cold+0x93>
    63a0:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    63a7:	e9 2e fd ff ff       	jmp    60da <io_thread+0x70a>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    63ac:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    63b4:	8b 02                	mov    (%rdx),%eax
    63b6:	83 c0 01             	add    $0x1,%eax
    63b9:	89 02                	mov    %eax,(%rdx)
        if (((struct SendUserData*) cqe->user_data)->kind == 4) {
    63bb:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    63c0:	4c 8b 3a             	mov    (%rdx),%r15
    63c3:	41 8b 07             	mov    (%r15),%eax
    63c6:	4c 89 f9             	mov    %r15,%rcx
    63c9:	83 f8 04             	cmp    $0x4,%eax
    63cc:	0f 85 c6 fd ff ff    	jne    6198 <io_thread+0x7c8>
          struct ReadyWriting *rr = readywriting->data; 
    63d2:	49 8b 47 08          	mov    0x8(%r15),%rax
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
    63d6:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
          struct ReadyWriting *rr = readywriting->data; 
    63dc:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
    63e1:	0f 85 c3 fd ff ff    	jne    61aa <io_thread+0x7da>
    63e7:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    63ec:	48 89 dd             	mov    %rbx,%rbp
    63ef:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    63f4:	8b 70 10             	mov    0x10(%rax),%esi
    63f7:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    63ff:	48 c1 e0 04          	shl    $0x4,%rax
    6403:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
      for (int x = 0 ; x < buffers->count ; x++) {
    640b:	8b 08                	mov    (%rax),%ecx
    640d:	85 c9                	test   %ecx,%ecx
    640f:	0f 8e 31 02 00 00    	jle    6646 <io_thread+0xc76>
    6415:	4c 8b 70 08          	mov    0x8(%rax),%r14
    6419:	48 63 c1             	movslq %ecx,%rax
    641c:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6420:	49 8d 04 c6          	lea    (%r14,%rax,8),%rax
    6424:	eb 17                	jmp    643d <io_thread+0xa6d>
    6426:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6430:	49 83 c6 28          	add    $0x28,%r14
    6434:	49 39 c6             	cmp    %rax,%r14
    6437:	0f 84 09 02 00 00    	je     6646 <io_thread+0xc76>
        if (buffers->buffer[x].available == 1) {
    643d:	41 83 7e 08 01       	cmpl   $0x1,0x8(%r14)
    6442:	75 ec                	jne    6430 <io_thread+0xa60>
          if (buffers->buffer[x].kind == kind && buffers->buffer[x].filter == filter) {
    6444:	41 83 7e 20 03       	cmpl   $0x3,0x20(%r14)
    6449:	75 e5                	jne    6430 <io_thread+0xa60>
    644b:	41 3b 76 24          	cmp    0x24(%r14),%esi
    644f:	75 df                	jne    6430 <io_thread+0xa60>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6451:	be 28 00 00 00       	mov    $0x28,%esi
    6456:	bf 01 00 00 00       	mov    $0x1,%edi
    645b:	e8 a0 bf ff ff       	call   2400 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    6460:	49 8b 0e             	mov    (%r14),%rcx
            buffers->buffer[x].available = 0;
    6463:	41 c7 46 08 00 00 00 00 	movl   $0x0,0x8(%r14)
            reply->kind = buffers->buffer[x].kind;
    646b:	c7 40 20 03 00 00 00 	movl   $0x3,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    6472:	48 89 08             	mov    %rcx,(%rax)
            asm volatile ("mfence" ::: "memory");
    6475:	0f ae f0             	mfence
	unsigned int head, next = sq->sqe_tail + 1;
    6478:	8b 8c 24 b4 00 00 00 	mov    0xb4(%rsp),%ecx
            struct Write *write = send->data;
    647f:	48 8b 00             	mov    (%rax),%rax
    6482:	8d 71 01             	lea    0x1(%rcx),%esi
	if (ring->flags & IORING_SETUP_SQE128)
    6485:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
            int client_socket = write->client_socket; 
    648c:	8b 78 08             	mov    0x8(%rax),%edi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    648f:	f6 c1 02             	test   $0x2,%cl
    6492:	0f 84 1a 08 00 00    	je     6cb2 <io_thread+0x12e2>
		head = io_uring_smp_load_acquire(sq->khead);
    6498:	4c 8b 44 24 70       	mov    0x70(%rsp),%r8
    649d:	45 8b 00             	mov    (%r8),%r8d
            struct Request *req = write->request;
    64a0:	4c 8b 30             	mov    (%rax),%r14
	if (next - head <= sq->ring_entries) {
    64a3:	89 f0                	mov    %esi,%eax
    64a5:	44 29 c0             	sub    %r8d,%eax
    64a8:	39 84 24 cc 00 00 00 	cmp    %eax,0xcc(%rsp)
    64af:	0f 82 95 c1 ff ff    	jb     264a <io_thread.cold+0x34>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    64b5:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    64bc:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
    64bf:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    64c3:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    64ca:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    64cd:	89 c3                	mov    %eax,%ebx
            io_uring_prep_writev(sqe, client_socket, req->iov, req->iovec_count, 0);
    64cf:	41 8b 46 04          	mov    0x4(%r14),%eax
		sq->sqe_tail = next;
    64d3:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    64da:	d3 e3                	shl    %cl,%ebx
    64dc:	49 8d 4e 10          	lea    0x10(%r14),%rcx
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    64e0:	be 20 00 00 00       	mov    $0x20,%esi
    64e5:	48 c1 e3 06          	shl    $0x6,%rbx
    64e9:	48 03 9c 24 a8 00 00 00 	add    0xa8(%rsp),%rbx
            req->event_type = EVENT_TYPE_WRITE;
    64f1:	41 c7 06 02 00 00 00 	movl   $0x2,(%r14)
	sqe->fd = fd;
    64f8:	89 7b 04             	mov    %edi,0x4(%rbx)
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    64fb:	bf 01 00 00 00       	mov    $0x1,%edi
            io_uring_prep_writev(sqe, client_socket, req->iov, req->iovec_count, 0);
    6500:	48 89 4b 10          	mov    %rcx,0x10(%rbx)
	sqe->opcode = (__u8) op;
    6504:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->off = offset;
    650a:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
	sqe->len = len;
    6512:	89 43 18             	mov    %eax,0x18(%rbx)
	sqe->rw_flags = 0;
    6515:	c7 43 1c 00 00 00 00 	movl   $0x0,0x1c(%rbx)
	sqe->buf_index = 0;
    651c:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->addr3 = 0;
    6524:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    6528:	e8 d3 be ff ff       	call   2400 <calloc@plt>
            finishedwrite->data = req;
    652d:	66 49 0f 6e c6       	movq   %r14,%xmm0
            io_uring_submit(&ring);
    6532:	4c 89 ef             	mov    %r13,%rdi
            finishedwrite->data = req;
    6535:	41 0f 16 47 10       	movhps 0x10(%r15),%xmm0
            finishedwrite->kind = 5; 
    653a:	c7 00 05 00 00 00    	movl   $0x5,(%rax)
            finishedwrite->data = req;
    6540:	0f 11 40 08          	movups %xmm0,0x8(%rax)
	sqe->user_data = (unsigned long) data;
    6544:	48 89 43 20          	mov    %rax,0x20(%rbx)
            io_uring_submit(&ring);
    6548:	e8 43 be ff ff       	call   2390 <io_uring_submit@plt>
	if (cqe)
    654d:	48 83 7c 24 38 00    	cmpq   $0x0,0x38(%rsp)
    6553:	74 0f                	je     6564 <io_thread+0xb94>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6555:	48 8b 8c 24 d8 00 00 00 	mov    0xd8(%rsp),%rcx
    655d:	8b 01                	mov    (%rcx),%eax
    655f:	83 c0 01             	add    $0x1,%eax
    6562:	89 01                	mov    %eax,(%rcx)
	unsigned int head, next = sq->sqe_tail + 1;
    6564:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    656b:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    6572:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    6575:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    657a:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    657c:	f6 c1 02             	test   $0x2,%cl
    657f:	74 00                	je     6581 <io_thread+0xbb1>
	if (next - head <= sq->ring_entries) {
    6581:	89 f7                	mov    %esi,%edi
    6583:	29 c7                	sub    %eax,%edi
    6585:	39 bc 24 cc 00 00 00 	cmp    %edi,0xcc(%rsp)
    658c:	0f 82 84 c0 ff ff    	jb     2616 <io_thread.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    6592:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6595:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    659c:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
              io_uring_submit(&ring);
    65a3:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    65a6:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    65a9:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	sqe->addr3 = 0;
    65b0:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    65b4:	d3 e0                	shl    %cl,%eax
              io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    65b6:	41 8b 4c 24 68       	mov    0x68(%r12),%ecx
    65bb:	48 c1 e0 06          	shl    $0x6,%rax
    65bf:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->fd = fd;
    65c7:	89 48 04             	mov    %ecx,0x4(%rax)
	sqe->user_data = (unsigned long) data;
    65ca:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
	sqe->opcode = (__u8) op;
    65cf:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->user_data = (unsigned long) data;
    65d5:	48 89 48 20          	mov    %rcx,0x20(%rax)
	sqe->off = offset;
    65d9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    65e1:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->len = len;
    65e5:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    65ed:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    65f5:	0f 11 40 30          	movups %xmm0,0x30(%rax)
              io_uring_submit(&ring);
    65f9:	e8 92 bd ff ff       	call   2390 <io_uring_submit@plt>
	sqe->fd = fd;
    65fe:	8b 04 24             	mov    (%rsp),%eax
	sqe->addr = (unsigned long) addr;
    6601:	48 89 6b 10          	mov    %rbp,0x10(%rbx)
	sqe->addr3 = 0;
    6605:	66 0f ef c0          	pxor   %xmm0,%xmm0
	sqe->opcode = (__u8) op;
    6609:	c7 03 01 00 00 00    	movl   $0x1,(%rbx)
          io_uring_submit(&ring);
    660f:	4c 89 ef             	mov    %r13,%rdi
	sqe->fd = fd;
    6612:	89 43 04             	mov    %eax,0x4(%rbx)
	sqe->off = offset;
    6615:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
	sqe->len = len;
    661d:	48 c7 43 18 01 00 00 00 	movq   $0x1,0x18(%rbx)
	sqe->buf_index = 0;
    6625:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->user_data = (unsigned long) data;
    662d:	4c 89 7b 20          	mov    %r15,0x20(%rbx)
	sqe->addr3 = 0;
    6631:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
    6635:	e8 56 bd ff ff       	call   2390 <io_uring_submit@plt>
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
    663a:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6640:	0f 84 a9 fd ff ff    	je     63ef <io_thread+0xa1f>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
    6646:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    664b:	48 89 eb             	mov    %rbp,%rbx
    664e:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    6653:	48 8b 0a             	mov    (%rdx),%rcx
    6656:	8b 01                	mov    (%rcx),%eax
    6658:	e9 3b fb ff ff       	jmp    6198 <io_thread+0x7c8>
                  if (!cqe->res) {
    665d:	85 c0                	test   %eax,%eax
    665f:	0f 84 86 06 00 00    	je     6ceb <io_thread+0x131b>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6665:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    666d:	8b 02                	mov    (%rdx),%eax
    666f:	83 c0 01             	add    $0x1,%eax
    6672:	89 02                	mov    %eax,(%rdx)
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    6674:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    6679:	48 8b 00             	mov    (%rax),%rax
    667c:	8b 00                	mov    (%rax),%eax
}
    667e:	e9 1e fb ff ff       	jmp    61a1 <io_thread+0x7d1>
  while (data->running == 1) {
    6683:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6689:	0f 84 a1 f5 ff ff    	je     5c30 <io_thread+0x260>
    668f:	e9 e1 f5 ff ff       	jmp    5c75 <io_thread+0x2a5>
    sock = socket(PF_INET, SOCK_STREAM, 0);
    6694:	31 d2                	xor    %edx,%edx
    6696:	be 01 00 00 00       	mov    $0x1,%esi
    669b:	bf 02 00 00 00       	mov    $0x2,%edi
    66a0:	e8 2b bf ff ff       	call   25d0 <socket@plt>
    66a5:	89 c3                	mov    %eax,%ebx
    if (sock == -1)
    66a7:	83 f8 ff             	cmp    $0xffffffff,%eax
    66aa:	0f 84 c9 bf ff ff    	je     2679 <io_thread.cold+0x63>
    if (setsockopt(sock,
    66b0:	48 8d 4c 24 34       	lea    0x34(%rsp),%rcx
    66b5:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    66bb:	ba 02 00 00 00       	mov    $0x2,%edx
    66c0:	89 c7                	mov    %eax,%edi
    66c2:	be 01 00 00 00       	mov    $0x1,%esi
    int enable = 1;
    66c7:	c7 44 24 34 01 00 00 00 	movl   $0x1,0x34(%rsp)
    if (setsockopt(sock,
    66cf:	e8 6c bc ff ff       	call   2340 <setsockopt@plt>
    66d4:	85 c0                	test   %eax,%eax
    66d6:	0f 88 a9 bf ff ff    	js     2685 <io_thread.cold+0x6f>
  return __builtin___memset_chk (__dest, __ch, __len,
    66dc:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
    if (bind(sock,
    66e1:	ba 10 00 00 00       	mov    $0x10,%edx
    66e6:	89 df                	mov    %ebx,%edi
    66e8:	48 c7 44 24 54 00 00 00 00 	movq   $0x0,0x54(%rsp)
    66f1:	c7 44 24 5c 00 00 00 00 	movl   $0x0,0x5c(%rsp)
    srv_addr.sin_family = AF_INET;
    66f9:	c7 44 24 50 02 00 18 db 	movl   $0xdb180002,0x50(%rsp)
    if (bind(sock,
    6701:	e8 ba bd ff ff       	call   24c0 <bind@plt>
    6706:	85 c0                	test   %eax,%eax
    6708:	0f 88 83 bf ff ff    	js     2691 <io_thread.cold+0x7b>
    if (listen(sock, 10) < 0) {
    670e:	be 0a 00 00 00       	mov    $0xa,%esi
    6713:	89 df                	mov    %ebx,%edi
    6715:	e8 66 bd ff ff       	call   2480 <listen@plt>
    671a:	85 c0                	test   %eax,%eax
    671c:	0f 88 7b bf ff ff    	js     269d <io_thread.cold+0x87>
    6722:	89 d9                	mov    %ebx,%ecx
    6724:	ba db 18 00 00       	mov    $0x18db,%edx
    6729:	48 8d 35 28 2f 00 00 	lea    0x2f28(%rip),%rsi        # 9658 <_IO_stdin_used+0x658>
    6730:	31 c0                	xor    %eax,%eax
    6732:	bf 01 00 00 00       	mov    $0x1,%edi
    6737:	e8 74 bd ff ff       	call   24b0 <__printf_chk@plt>
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    673c:	be 04 00 00 00       	mov    $0x4,%esi
    6741:	bf 01 00 00 00       	mov    $0x1,%edi
    6746:	e8 b5 bc ff ff       	call   2400 <calloc@plt>
    674b:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    6753:	bf 01 00 00 00       	mov    $0x1,%edi
    6758:	48 8d 35 19 2f 00 00 	lea    0x2f19(%rip),%rsi        # 9678 <_IO_stdin_used+0x678>
    msg->socket = sock;
    675f:	89 18                	mov    %ebx,(%rax)
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    6761:	48 89 c5             	mov    %rax,%rbp
    6764:	31 c0                	xor    %eax,%eax
    6766:	e8 45 bd ff ff       	call   24b0 <__printf_chk@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET, msg);
    676b:	49 63 94 24 18 01 00 00 	movslq 0x118(%r12),%rdx
    6773:	48 c1 e2 04          	shl    $0x4,%rdx
    6777:	49 03 94 24 10 01 00 00 	add    0x110(%r12),%rdx
  while (data->running == 1) {
    677f:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6785:	0f 85 b5 00 00 00    	jne    6840 <io_thread+0xe70>
      for (int x = 0 ; x < buffers->count ; x++) {
    678b:	48 63 0a             	movslq (%rdx),%rcx
    678e:	85 c9                	test   %ecx,%ecx
    6790:	7e ed                	jle    677f <io_thread+0xdaf>
    6792:	48 8b 42 08          	mov    0x8(%rdx),%rax
    6796:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    679a:	48 8d 0c c8          	lea    (%rax,%rcx,8),%rcx
    679e:	eb 09                	jmp    67a9 <io_thread+0xdd9>
    67a0:	48 83 c0 28          	add    $0x28,%rax
    67a4:	48 39 c1             	cmp    %rax,%rcx
    67a7:	74 d6                	je     677f <io_thread+0xdaf>
        if (buffers->buffer[x].available == 0) {
    67a9:	44 8b 50 08          	mov    0x8(%rax),%r10d
    67ad:	45 85 d2             	test   %r10d,%r10d
    67b0:	75 ee                	jne    67a0 <io_thread+0xdd0>
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
    67b2:	49 63 94 24 1c 01 00 00 	movslq 0x11c(%r12),%rdx
          buffers->buffer[x].data = send;
    67ba:	48 89 28             	mov    %rbp,(%rax)
          buffers->buffer[x].kind = kind;
    67bd:	c7 40 20 00 00 00 00 	movl   $0x0,0x20(%rax)
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
    67c4:	48 c1 e2 04          	shl    $0x4,%rdx
    67c8:	49 03 94 24 10 01 00 00 	add    0x110(%r12),%rdx
  while (data->running == 1) {
    67d0:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
          buffers->buffer[x].available = 1;
    67d6:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
  while (data->running == 1) {
    67dd:	75 61                	jne    6840 <io_thread+0xe70>
      for (int x = 0 ; x < buffers->count ; x++) {
    67df:	48 63 02             	movslq (%rdx),%rax
    67e2:	85 c0                	test   %eax,%eax
    67e4:	0f 8e 28 05 00 00    	jle    6d12 <io_thread+0x1342>
    67ea:	48 8b 6a 08          	mov    0x8(%rdx),%rbp
    67ee:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    67f2:	48 8d 44 c5 00       	lea    0x0(%rbp,%rax,8),%rax
    67f7:	eb 14                	jmp    680d <io_thread+0xe3d>
    67f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6800:	48 83 c5 28          	add    $0x28,%rbp
    6804:	48 39 e8             	cmp    %rbp,%rax
    6807:	0f 84 05 05 00 00    	je     6d12 <io_thread+0x1342>
        if (buffers->buffer[x].available == 1) {
    680d:	83 7d 08 01          	cmpl   $0x1,0x8(%rbp)
    6811:	75 ed                	jne    6800 <io_thread+0xe30>
          if (buffers->buffer[x].kind == kind) {
    6813:	83 7d 20 01          	cmpl   $0x1,0x20(%rbp)
    6817:	75 e7                	jne    6800 <io_thread+0xe30>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6819:	be 28 00 00 00       	mov    $0x28,%esi
    681e:	bf 01 00 00 00       	mov    $0x1,%edi
    6823:	e8 d8 bb ff ff       	call   2400 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    6828:	48 8b 55 00          	mov    0x0(%rbp),%rdx
            buffers->buffer[x].available = 0;
    682c:	c7 45 08 00 00 00 00 	movl   $0x0,0x8(%rbp)
            reply->kind = buffers->buffer[x].kind;
    6833:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    683a:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    683d:	0f ae f8             	sfence
    6840:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    6848:	48 8d 35 51 2e 00 00 	lea    0x2e51(%rip),%rsi        # 96a0 <_IO_stdin_used+0x6a0>
    684f:	bf 01 00 00 00       	mov    $0x1,%edi
    6854:	31 c0                	xor    %eax,%eax
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6856:	4c 8d 74 24 38       	lea    0x38(%rsp),%r14
    685b:	e8 50 bc ff ff       	call   24b0 <__printf_chk@plt>
    6860:	48 8d 44 24 60       	lea    0x60(%rsp),%rax
    6865:	4c 89 e9             	mov    %r13,%rcx
    6868:	4c 89 f2             	mov    %r14,%rdx
    686b:	48 89 c6             	mov    %rax,%rsi
    686e:	89 df                	mov    %ebx,%edi
    socklen_t client_addr_len = sizeof(client_addr);
    6870:	c7 44 24 38 10 00 00 00 	movl   $0x10,0x38(%rsp)
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6878:	48 89 04 24          	mov    %rax,(%rsp)
    687c:	e8 af f0 ff ff       	call   5930 <add_accept_request>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    6881:	bf 01 00 00 00       	mov    $0x1,%edi
    6886:	be 10 00 00 00       	mov    $0x10,%esi
    688b:	e8 70 bb ff ff       	call   2400 <calloc@plt>
    void *buf = malloc(size);
    6890:	bf e8 03 00 00       	mov    $0x3e8,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    6895:	48 89 c5             	mov    %rax,%rbp
    void *buf = malloc(size);
    6898:	e8 d3 bb ff ff       	call   2470 <malloc@plt>
    if (!buf) {
    689d:	48 85 c0             	test   %rax,%rax
    68a0:	0f 84 73 05 00 00    	je     6e19 <io_thread+0x1449>
    iov->iov_base = zh_malloc(1000);
    68a6:	48 89 45 00          	mov    %rax,0x0(%rbp)
	unsigned int head, next = sq->sqe_tail + 1;
    68aa:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    68b1:	8b 94 24 30 01 00 00 	mov    0x130(%rsp),%edx
    iov->iov_len = 1000;
    68b8:	48 c7 45 08 e8 03 00 00 	movq   $0x3e8,0x8(%rbp)
	unsigned int head, next = sq->sqe_tail + 1;
    68c0:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    68c3:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    68c8:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    68ca:	f6 c2 02             	test   $0x2,%dl
    68cd:	0f 85 13 04 00 00    	jne    6ce6 <io_thread+0x1316>
	if (next - head <= sq->ring_entries) {
    68d3:	89 f1                	mov    %esi,%ecx
    68d5:	29 c1                	sub    %eax,%ecx
    68d7:	39 8c 24 cc 00 00 00 	cmp    %ecx,0xcc(%rsp)
    68de:	0f 82 8b bd ff ff    	jb     266f <io_thread.cold+0x59>
	if (ring->flags & IORING_SETUP_SQE128)
    68e4:	c1 ea 0a             	shr    $0xa,%edx
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
    68e7:	4d 8d 7c 24 68       	lea    0x68(%r12),%r15
	sqe->addr3 = 0;
    68ec:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(&ring);
    68f0:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    68f3:	89 d1                	mov    %edx,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    68f5:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    68fc:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
		sq->sqe_tail = next;
    6903:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
    690a:	83 e1 01             	and    $0x1,%ecx
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    690d:	41 8b 54 24 68       	mov    0x68(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6912:	d3 e0                	shl    %cl,%eax
    6914:	48 c1 e0 06          	shl    $0x6,%rax
    6918:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->opcode = (__u8) op;
    6920:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    6926:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    6929:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    6931:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->len = len;
    6935:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    693d:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    6945:	4c 89 78 20          	mov    %r15,0x20(%rax)
	sqe->addr3 = 0;
    6949:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(&ring);
    694d:	e8 3e ba ff ff       	call   2390 <io_uring_submit@plt>
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    6952:	48 8d 44 24 40       	lea    0x40(%rsp),%rax
    6957:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    while (data->running == 1) {
    695c:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6962:	0f 85 1b 03 00 00    	jne    6c83 <io_thread+0x12b3>
	if (ring->flags & IORING_SETUP_CQE32)
    6968:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    696f:	8b bc 24 20 01 00 00 	mov    0x120(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    6976:	c1 e9 0b             	shr    $0xb,%ecx
    6979:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    697c:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
    6984:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    6986:	48 8b b4 24 d8 00 00 00 	mov    0xd8(%rsp),%rsi
    698e:	8b 16                	mov    (%rsi),%edx
		if (!available)
    6990:	39 d0                	cmp    %edx,%eax
    6992:	74 36                	je     69ca <io_thread+0xffa>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    6994:	89 f8                	mov    %edi,%eax
    6996:	21 d0                	and    %edx,%eax
    6998:	d3 e0                	shl    %cl,%eax
    699a:	48 c1 e0 04          	shl    $0x4,%rax
    699e:	48 03 84 24 08 01 00 00 	add    0x108(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    69a6:	f6 84 24 39 01 00 00 01 	testb  $0x1,0x139(%rsp)
    69ae:	0f 85 99 02 00 00    	jne    6c4d <io_thread+0x127d>
    69b4:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    69b8:	0f 85 51 04 00 00    	jne    6e0f <io_thread+0x143f>
			if (cqe->res < 0)
    69be:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    69c1:	83 c2 01             	add    $0x1,%edx
    69c4:	89 16                	mov    %edx,(%rsi)
			if (!err)
    69c6:	85 c0                	test   %eax,%eax
    69c8:	79 b2                	jns    697c <io_thread+0xfac>
	*cqe_ptr = cqe;
    69ca:	48 c7 44 24 40 00 00 00 00 	movq   $0x0,0x40(%rsp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    69d3:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    69d8:	b9 01 00 00 00       	mov    $0x1,%ecx
    69dd:	31 d2                	xor    %edx,%edx
    69df:	45 31 c0             	xor    %r8d,%r8d
    69e2:	4c 89 ef             	mov    %r13,%rdi
    69e5:	e8 b6 ba ff ff       	call   24a0 <__io_uring_get_cqe@plt>
    69ea:	89 c1                	mov    %eax,%ecx
        if (cqe->user_data == 1) {
    69ec:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    69f1:	48 8b 10             	mov    (%rax),%rdx
    69f4:	48 83 fa 01          	cmp    $0x1,%rdx
    69f8:	0f 84 6a 02 00 00    	je     6c68 <io_thread+0x1298>
        if (ret < 0)
    69fe:	85 c9                	test   %ecx,%ecx
    6a00:	0f 88 ad bc ff ff    	js     26b3 <io_thread.cold+0x9d>
        if (cqe->res < 0) {
    6a06:	8b 40 08             	mov    0x8(%rax),%eax
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    6a09:	44 8b 02             	mov    (%rdx),%r8d
        if (cqe->res < 0) {
    6a0c:	85 c0                	test   %eax,%eax
    6a0e:	0f 88 84 03 00 00    	js     6d98 <io_thread+0x13c8>
        switch (req->event_type) {
    6a14:	45 85 c0             	test   %r8d,%r8d
    6a17:	0f 84 a2 00 00 00    	je     6abf <io_thread+0x10ef>
    6a1d:	41 83 f8 01          	cmp    $0x1,%r8d
    6a21:	0f 85 7b 01 00 00    	jne    6ba2 <io_thread+0x11d2>
                if (!cqe->res) {
    6a27:	85 c0                	test   %eax,%eax
    6a29:	0f 84 90 02 00 00    	je     6cbf <io_thread+0x12ef>
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    6a2f:	48 8d b4 24 50 01 00 00 	lea    0x150(%rsp),%rsi
    6a37:	4d 8b 8c 24 10 01 00 00 	mov    0x110(%r12),%r9
    6a3f:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    6a43:	4c 8d 94 24 50 05 00 00 	lea    0x550(%rsp),%r10
    6a4b:	41 8b bc 24 18 01 00 00 	mov    0x118(%r12),%edi
    for (int i = 0; i < dest_sz; i++) {
    6a53:	48 89 f0             	mov    %rsi,%rax
    6a56:	eb 19                	jmp    6a71 <io_thread+0x10a1>
    6a58:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6a60:	48 83 c0 01          	add    $0x1,%rax
    6a64:	48 83 c1 01          	add    $0x1,%rcx
    6a68:	4c 39 d0             	cmp    %r10,%rax
    6a6b:	0f 84 77 03 00 00    	je     6de8 <io_thread+0x1418>
        dest[i] = src[i];
    6a71:	44 0f b6 01          	movzbl (%rcx),%r8d
    6a75:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    6a78:	41 80 f8 0d          	cmp    $0xd,%r8b
    6a7c:	75 e2                	jne    6a60 <io_thread+0x1090>
    6a7e:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    6a82:	75 dc                	jne    6a60 <io_thread+0x1090>
            dest[i] = '\0';
    6a84:	c6 00 00             	movb   $0x0,(%rax)
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    6a87:	48 63 c7             	movslq %edi,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    6a8a:	8b 4a 08             	mov    0x8(%rdx),%ecx
    6a8d:	4c 89 e7             	mov    %r12,%rdi
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    6a90:	48 c1 e0 04          	shl    $0x4,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    6a94:	44 8b 42 0c          	mov    0xc(%rdx),%r8d
    6a98:	48 89 f2             	mov    %rsi,%rdx
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    6a9b:	4c 01 c8             	add    %r9,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    6a9e:	4d 89 e9             	mov    %r13,%r9
    6aa1:	48 89 c6             	mov    %rax,%rsi
    6aa4:	e8 57 ec ff ff       	call   5700 <handle_http_method>
                eventfd_write(data->otherdataeventfd, 0);
    6aa9:	41 8b 7c 24 70       	mov    0x70(%r12),%edi
    6aae:	31 f6                	xor    %esi,%esi
    6ab0:	e8 ab b9 ff ff       	call   2460 <eventfd_write@plt>
          io_uring_cqe_seen(&ring, cqe);
    6ab5:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
                break;
    6aba:	e9 de 00 00 00       	jmp    6b9d <io_thread+0x11cd>
                add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6abf:	48 8b 34 24          	mov    (%rsp),%rsi
    6ac3:	4c 89 e9             	mov    %r13,%rcx
    6ac6:	4c 89 f2             	mov    %r14,%rdx
    6ac9:	89 df                	mov    %ebx,%edi
    6acb:	e8 60 ee ff ff       	call   5930 <add_accept_request>
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
    6ad0:	be 08 00 00 00       	mov    $0x8,%esi
    6ad5:	bf 01 00 00 00       	mov    $0x1,%edi
    6ada:	e8 21 b9 ff ff       	call   2400 <calloc@plt>
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
    6adf:	49 63 b4 24 18 01 00 00 	movslq 0x118(%r12),%rsi
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
    6ae7:	48 89 c7             	mov    %rax,%rdi
                newclientmsg->socket = cqe->res;
    6aea:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
    6aef:	48 c1 e6 04          	shl    $0x4,%rsi
    6af3:	49 03 b4 24 10 01 00 00 	add    0x110(%r12),%rsi
  while (data->running == 1) {
    6afb:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
                newclientmsg->socket = cqe->res;
    6b01:	8b 50 08             	mov    0x8(%rax),%edx
                data->sockettoken++;
    6b04:	41 8b 84 24 28 01 00 00 	mov    0x128(%r12),%eax
    6b0c:	8d 48 01             	lea    0x1(%rax),%ecx
                newclientmsg->socket = cqe->res;
    6b0f:	66 0f 6e c2          	movd   %edx,%xmm0
    6b13:	66 0f 6e e1          	movd   %ecx,%xmm4
                data->sockettoken++;
    6b17:	41 89 8c 24 28 01 00 00 	mov    %ecx,0x128(%r12)
                newclientmsg->socket = cqe->res;
    6b1f:	66 0f 62 c4          	punpckldq %xmm4,%xmm0
    6b23:	66 0f d6 07          	movq   %xmm0,(%rdi)
  while (data->running == 1) {
    6b27:	75 64                	jne    6b8d <io_thread+0x11bd>
      for (int x = 0 ; x < buffers->count ; x++) {
    6b29:	48 63 16             	movslq (%rsi),%rdx
    6b2c:	85 d2                	test   %edx,%edx
    6b2e:	0f 8e 5c 01 00 00    	jle    6c90 <io_thread+0x12c0>
    6b34:	48 8b 46 08          	mov    0x8(%rsi),%rax
    6b38:	48 8d 14 92          	lea    (%rdx,%rdx,4),%rdx
    6b3c:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    6b40:	eb 0d                	jmp    6b4f <io_thread+0x117f>
    6b42:	48 83 c0 28          	add    $0x28,%rax
    6b46:	48 39 d0             	cmp    %rdx,%rax
    6b49:	0f 84 41 01 00 00    	je     6c90 <io_thread+0x12c0>
        if (buffers->buffer[x].available == 0) {
    6b4f:	44 8b 48 08          	mov    0x8(%rax),%r9d
    6b53:	45 85 c9             	test   %r9d,%r9d
    6b56:	75 ea                	jne    6b42 <io_thread+0x1172>
          buffers->buffer[x].data = send;
    6b58:	48 89 38             	mov    %rdi,(%rax)
          buffers->buffer[x].kind = kind;
    6b5b:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
          buffers->buffer[x].available = 1;
    6b62:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
                add_read_request(data, &data->iomailboxes[data->other_io], cqe->res, data->sockettoken, &ring);
    6b69:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6b6e:	49 63 b4 24 18 01 00 00 	movslq 0x118(%r12),%rsi
    6b76:	41 8b 8c 24 28 01 00 00 	mov    0x128(%r12),%ecx
    6b7e:	8b 50 08             	mov    0x8(%rax),%edx
    6b81:	48 c1 e6 04          	shl    $0x4,%rsi
    6b85:	49 03 b4 24 10 01 00 00 	add    0x110(%r12),%rsi
    6b8d:	4d 89 e8             	mov    %r13,%r8
    6b90:	4c 89 e7             	mov    %r12,%rdi
    6b93:	e8 c8 e5 ff ff       	call   5160 <add_read_request>
          io_uring_cqe_seen(&ring, cqe);
    6b98:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
	if (cqe)
    6b9d:	48 85 c0             	test   %rax,%rax
    6ba0:	74 0f                	je     6bb1 <io_thread+0x11e1>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6ba2:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6baa:	8b 02                	mov    (%rdx),%eax
    6bac:	83 c0 01             	add    $0x1,%eax
    6baf:	89 02                	mov    %eax,(%rdx)
	unsigned int head, next = sq->sqe_tail + 1;
    6bb1:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6bb8:	8b 94 24 30 01 00 00 	mov    0x130(%rsp),%edx
	unsigned int head, next = sq->sqe_tail + 1;
    6bbf:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    6bc2:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    6bc7:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6bc9:	f6 c2 02             	test   $0x2,%dl
    6bcc:	74 00                	je     6bce <io_thread+0x11fe>
	if (next - head <= sq->ring_entries) {
    6bce:	89 f1                	mov    %esi,%ecx
    6bd0:	29 c1                	sub    %eax,%ecx
    6bd2:	39 8c 24 cc 00 00 00 	cmp    %ecx,0xcc(%rsp)
    6bd9:	0f 82 e0 ba ff ff    	jb     26bf <io_thread.cold+0xa9>
	if (ring->flags & IORING_SETUP_SQE128)
    6bdf:	c1 ea 0a             	shr    $0xa,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6be2:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    6be9:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
        io_uring_submit(&ring);
    6bf0:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    6bf3:	89 d1                	mov    %edx,%ecx
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6bf5:	41 8b 54 24 68       	mov    0x68(%r12),%edx
		sq->sqe_tail = next;
    6bfa:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	sqe->addr3 = 0;
    6c01:	66 0f ef ed          	pxor   %xmm5,%xmm5
	if (ring->flags & IORING_SETUP_SQE128)
    6c05:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6c08:	d3 e0                	shl    %cl,%eax
    6c0a:	48 c1 e0 06          	shl    $0x6,%rax
    6c0e:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->fd = fd;
    6c16:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->addr = (unsigned long) addr;
    6c19:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->user_data = (unsigned long) data;
    6c1d:	4c 89 78 20          	mov    %r15,0x20(%rax)
	sqe->opcode = (__u8) op;
    6c21:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->off = offset;
    6c27:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->len = len;
    6c2f:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    6c37:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    6c3f:	0f 11 68 30          	movups %xmm5,0x30(%rax)
        io_uring_submit(&ring);
    6c43:	e8 48 b7 ff ff       	call   2390 <io_uring_submit@plt>
    while (data->running == 1) {
    6c48:	e9 0f fd ff ff       	jmp    695c <io_thread+0xf8c>
	*cqe_ptr = cqe;
    6c4d:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    6c52:	48 85 c0             	test   %rax,%rax
    6c55:	0f 84 78 fd ff ff    	je     69d3 <io_thread+0x1003>
        if (cqe->user_data == 1) {
    6c5b:	48 8b 10             	mov    (%rax),%rdx
    6c5e:	48 83 fa 01          	cmp    $0x1,%rdx
    6c62:	0f 85 9e fd ff ff    	jne    6a06 <io_thread+0x1036>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6c68:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6c70:	48 8d 3d 0c 25 00 00 	lea    0x250c(%rip),%rdi        # 9183 <_IO_stdin_used+0x183>
    6c77:	8b 02                	mov    (%rdx),%eax
    6c79:	83 c0 01             	add    $0x1,%eax
    6c7c:	89 02                	mov    %eax,(%rdx)
    6c7e:	e8 ad b6 ff ff       	call   2330 <puts@plt>
  if (data->io_mode == IO_MODE_SEND) {
    6c83:	41 8b 84 24 0c 01 00 00 	mov    0x10c(%r12),%eax
    6c8b:	e9 64 ee ff ff       	jmp    5af4 <io_thread+0x124>
  while (data->running == 1) {
    6c90:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6c96:	0f 84 8d fe ff ff    	je     6b29 <io_thread+0x1159>
    6c9c:	e9 c8 fe ff ff       	jmp    6b69 <io_thread+0x1199>
    6ca1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    6ca8:	e9 37 f1 ff ff       	jmp    5de4 <io_thread+0x414>
    6cad:	e9 57 f2 ff ff       	jmp    5f09 <io_thread+0x539>
		head = IO_URING_READ_ONCE(*sq->khead);
    6cb2:	4c 8b 44 24 70       	mov    0x70(%rsp),%r8
    6cb7:	45 8b 00             	mov    (%r8),%r8d
    6cba:	e9 e1 f7 ff ff       	jmp    64a0 <io_thread+0xad0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6cbf:	48 8b 0d 5a 53 00 00 	mov    0x535a(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6cc6:	ba 0f 00 00 00       	mov    $0xf,%edx
    6ccb:	be 01 00 00 00       	mov    $0x1,%esi
    6cd0:	48 8d 3d d2 24 00 00 	lea    0x24d2(%rip),%rdi        # 91a9 <_IO_stdin_used+0x1a9>
    6cd7:	e8 64 b8 ff ff       	call   2540 <fwrite@plt>
          io_uring_cqe_seen(&ring, cqe);
    6cdc:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6ce1:	e9 b7 fe ff ff       	jmp    6b9d <io_thread+0x11cd>
		head = io_uring_smp_load_acquire(sq->khead);
    6ce6:	e9 e8 fb ff ff       	jmp    68d3 <io_thread+0xf03>
    6ceb:	48 8b 0d 2e 53 00 00 	mov    0x532e(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6cf2:	ba 0f 00 00 00       	mov    $0xf,%edx
    6cf7:	be 01 00 00 00       	mov    $0x1,%esi
    6cfc:	48 8d 3d a6 24 00 00 	lea    0x24a6(%rip),%rdi        # 91a9 <_IO_stdin_used+0x1a9>
    6d03:	e8 38 b8 ff ff       	call   2540 <fwrite@plt>
            io_uring_cqe_seen(&ring, cqe);
    6d08:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    6d0d:	e9 4b f6 ff ff       	jmp    635d <io_thread+0x98d>
  while (data->running == 1) {
    6d12:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6d18:	0f 84 c1 fa ff ff    	je     67df <io_thread+0xe0f>
    6d1e:	e9 1d fb ff ff       	jmp    6840 <io_thread+0xe70>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6d23:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6d2b:	48 8d 3d 51 24 00 00 	lea    0x2451(%rip),%rdi        # 9183 <_IO_stdin_used+0x183>
    6d32:	8b 02                	mov    (%rdx),%eax
    6d34:	83 c0 01             	add    $0x1,%eax
    6d37:	89 02                	mov    %eax,(%rdx)
    6d39:	e8 f2 b5 ff ff       	call   2330 <puts@plt>
    6d3e:	48 8d 3d ca 24 00 00 	lea    0x24ca(%rip),%rdi        # 920f <_IO_stdin_used+0x20f>
    6d45:	e8 e6 b5 ff ff       	call   2330 <puts@plt>
    6d4a:	e9 5a f5 ff ff       	jmp    62a9 <io_thread+0x8d9>
              fprintf(stderr, "Async request failed: %s for event: %d\n",
    6d4f:	f7 d8                	neg    %eax
    6d51:	89 c7                	mov    %eax,%edi
    6d53:	e8 28 b8 ff ff       	call   2580 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6d58:	48 8b 3d c1 52 00 00 	mov    0x52c1(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    6d5f:	45 89 f0             	mov    %r14d,%r8d
    6d62:	48 8d 15 5f 29 00 00 	lea    0x295f(%rip),%rdx        # 96c8 <_IO_stdin_used+0x6c8>
    6d69:	48 89 c1             	mov    %rax,%rcx
    6d6c:	be 01 00 00 00       	mov    $0x1,%esi
    6d71:	31 c0                	xor    %eax,%eax
    6d73:	e8 d8 b7 ff ff       	call   2550 <__fprintf_chk@plt>
	if (cqe)
    6d78:	48 83 7c 24 38 00    	cmpq   $0x0,0x38(%rsp)
    6d7e:	0f 84 fc f1 ff ff    	je     5f80 <io_thread+0x5b0>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6d84:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6d8c:	8b 02                	mov    (%rdx),%eax
    6d8e:	83 c0 01             	add    $0x1,%eax
    6d91:	89 02                	mov    %eax,(%rdx)
}
    6d93:	e9 e8 f1 ff ff       	jmp    5f80 <io_thread+0x5b0>
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    6d98:	f7 d8                	neg    %eax
    6d9a:	44 89 44 24 10       	mov    %r8d,0x10(%rsp)
    6d9f:	89 c7                	mov    %eax,%edi
    6da1:	e8 da b7 ff ff       	call   2580 <strerror@plt>
    6da6:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
    6dab:	be 01 00 00 00       	mov    $0x1,%esi
    6db0:	48 8b 3d 69 52 00 00 	mov    0x5269(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    6db7:	48 89 c1             	mov    %rax,%rcx
    6dba:	48 8d 15 07 29 00 00 	lea    0x2907(%rip),%rdx        # 96c8 <_IO_stdin_used+0x6c8>
    6dc1:	31 c0                	xor    %eax,%eax
    6dc3:	e8 88 b7 ff ff       	call   2550 <__fprintf_chk@plt>
	if (cqe)
    6dc8:	48 83 7c 24 40 00    	cmpq   $0x0,0x40(%rsp)
    6dce:	0f 84 88 fb ff ff    	je     695c <io_thread+0xf8c>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6dd4:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6ddc:	8b 02                	mov    (%rdx),%eax
    6dde:	83 c0 01             	add    $0x1,%eax
    6de1:	89 02                	mov    %eax,(%rdx)
}
    6de3:	e9 74 fb ff ff       	jmp    695c <io_thread+0xf8c>
    6de8:	48 8b 0d 31 52 00 00 	mov    0x5231(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6def:	ba 12 00 00 00       	mov    $0x12,%edx
    6df4:	be 01 00 00 00       	mov    $0x1,%esi
    6df9:	48 8d 3d 3e 23 00 00 	lea    0x233e(%rip),%rdi        # 913e <_IO_stdin_used+0x13e>
    6e00:	e8 3b b7 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    6e05:	bf 01 00 00 00       	mov    $0x1,%edi
    6e0a:	e8 11 b7 ff ff       	call   2520 <exit@plt>
	*cqe_ptr = cqe;
    6e0f:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
	return err;
    6e14:	e9 42 fe ff ff       	jmp    6c5b <io_thread+0x128b>
    6e19:	48 8b 0d 00 52 00 00 	mov    0x5200(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6e20:	ba 28 00 00 00       	mov    $0x28,%edx
    6e25:	be 01 00 00 00       	mov    $0x1,%esi
    6e2a:	48 8d 3d cf 27 00 00 	lea    0x27cf(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    6e31:	e8 0a b7 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    6e36:	bf 01 00 00 00       	mov    $0x1,%edi
    6e3b:	e8 e0 b6 ff ff       	call   2520 <exit@plt>
    6e40:	48 8b 0d d9 51 00 00 	mov    0x51d9(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6e47:	ba 28 00 00 00       	mov    $0x28,%edx
    6e4c:	be 01 00 00 00       	mov    $0x1,%esi
    6e51:	48 8d 3d a8 27 00 00 	lea    0x27a8(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    6e58:	e8 e3 b6 ff ff       	call   2540 <fwrite@plt>
    6e5d:	bf 01 00 00 00       	mov    $0x1,%edi
    6e62:	e8 b9 b6 ff ff       	call   2520 <exit@plt>
}
    6e67:	e8 14 b5 ff ff       	call   2380 <__stack_chk_fail@plt>
      exit(1); 
    6e6c:	bf 01 00 00 00       	mov    $0x1,%edi
    6e71:	e8 aa b6 ff ff       	call   2520 <exit@plt>
    6e76:	e9 2e b8 ff ff       	jmp    26a9 <io_thread.cold+0x93>
    6e7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006e80 <buffersend>:
int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send) {
    6e80:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    6e84:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    6e88:	75 35                	jne    6ebf <buffersend+0x3f>
      for (int x = 0 ; x < buffers->count ; x++) {
    6e8a:	4c 63 06             	movslq (%rsi),%r8
    6e8d:	45 85 c0             	test   %r8d,%r8d
    6e90:	7e f2                	jle    6e84 <buffersend+0x4>
    6e92:	48 8b 46 08          	mov    0x8(%rsi),%rax
    6e96:	4f 8d 04 80          	lea    (%r8,%r8,4),%r8
    6e9a:	4e 8d 04 c0          	lea    (%rax,%r8,8),%r8
    6e9e:	eb 09                	jmp    6ea9 <buffersend+0x29>
    6ea0:	48 83 c0 28          	add    $0x28,%rax
    6ea4:	4c 39 c0             	cmp    %r8,%rax
    6ea7:	74 db                	je     6e84 <buffersend+0x4>
        if (buffers->buffer[x].available == 0) {
    6ea9:	44 8b 48 08          	mov    0x8(%rax),%r9d
    6ead:	45 85 c9             	test   %r9d,%r9d
    6eb0:	75 ee                	jne    6ea0 <buffersend+0x20>
          buffers->buffer[x].data = send;
    6eb2:	48 89 08             	mov    %rcx,(%rax)
          buffers->buffer[x].kind = kind;
    6eb5:	89 50 20             	mov    %edx,0x20(%rax)
          buffers->buffer[x].available = 1;
    6eb8:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
}
    6ebf:	31 c0                	xor    %eax,%eax
    6ec1:	c3                   	ret
    6ec2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6ecd:	0f 1f 00             	nopl   (%rax)

0000000000006ed0 <buffersend_filter>:
int buffersend_filter(struct KernelThread *data, struct Buffers *buffers, int kind, void * send, int filter) {
    6ed0:	f3 0f 1e fa          	endbr64
    6ed4:	49 89 f9             	mov    %rdi,%r9
    6ed7:	48 89 f7             	mov    %rsi,%rdi
  while (data->running == 1) {
    6eda:	41 83 79 44 01       	cmpl   $0x1,0x44(%r9)
    6edf:	75 42                	jne    6f23 <buffersend_filter+0x53>
      for (int x = 0 ; x < buffers->count ; x++) {
    6ee1:	48 63 37             	movslq (%rdi),%rsi
    6ee4:	85 f6                	test   %esi,%esi
    6ee6:	7e f2                	jle    6eda <buffersend_filter+0xa>
    6ee8:	48 8b 47 08          	mov    0x8(%rdi),%rax
    6eec:	48 8d 34 b6          	lea    (%rsi,%rsi,4),%rsi
    6ef0:	48 8d 34 f0          	lea    (%rax,%rsi,8),%rsi
    6ef4:	eb 13                	jmp    6f09 <buffersend_filter+0x39>
    6ef6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6f00:	48 83 c0 28          	add    $0x28,%rax
    6f04:	48 39 f0             	cmp    %rsi,%rax
    6f07:	74 d1                	je     6eda <buffersend_filter+0xa>
        if (buffers->buffer[x].available == 0) {
    6f09:	44 8b 50 08          	mov    0x8(%rax),%r10d
    6f0d:	45 85 d2             	test   %r10d,%r10d
    6f10:	75 ee                	jne    6f00 <buffersend_filter+0x30>
          buffers->buffer[x].data = send;
    6f12:	48 89 08             	mov    %rcx,(%rax)
          buffers->buffer[x].kind = kind;
    6f15:	89 50 20             	mov    %edx,0x20(%rax)
          buffers->buffer[x].filter = filter;
    6f18:	44 89 40 24          	mov    %r8d,0x24(%rax)
          buffers->buffer[x].available = 1;
    6f1c:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
}
    6f23:	31 c0                	xor    %eax,%eax
    6f25:	c3                   	ret
    6f26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006f30 <bufferrecv_filter>:
void * bufferrecv_filter(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking, int filter) {
    6f30:	f3 0f 1e fa          	endbr64
    6f34:	55                   	push   %rbp
    6f35:	89 cd                	mov    %ecx,%ebp
    6f37:	53                   	push   %rbx
    6f38:	48 83 ec 08          	sub    $0x8,%rsp
  while (data->running == 1) {
    6f3c:	83 7e 44 01          	cmpl   $0x1,0x44(%rsi)
void * bufferrecv_filter(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking, int filter) {
    6f40:	8b 4c 24 20          	mov    0x20(%rsp),%ecx
  while (data->running == 1) {
    6f44:	75 7b                	jne    6fc1 <bufferrecv_filter+0x91>
      for (int x = 0 ; x < buffers->count ; x++) {
    6f46:	48 63 02             	movslq (%rdx),%rax
    6f49:	85 c0                	test   %eax,%eax
    6f4b:	7e 5b                	jle    6fa8 <bufferrecv_filter+0x78>
    6f4d:	0f 1f 00             	nopl   (%rax)
    6f50:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    6f54:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6f58:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    6f5c:	eb 0b                	jmp    6f69 <bufferrecv_filter+0x39>
    6f5e:	66 90                	xchg   %ax,%ax
    6f60:	48 83 c3 28          	add    $0x28,%rbx
    6f64:	48 39 c3             	cmp    %rax,%rbx
    6f67:	74 3f                	je     6fa8 <bufferrecv_filter+0x78>
        if (buffers->buffer[x].available == 1) {
    6f69:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    6f6d:	75 f1                	jne    6f60 <bufferrecv_filter+0x30>
          if (buffers->buffer[x].kind == kind && buffers->buffer[x].filter == filter) {
    6f6f:	39 6b 20             	cmp    %ebp,0x20(%rbx)
    6f72:	75 ec                	jne    6f60 <bufferrecv_filter+0x30>
    6f74:	39 4b 24             	cmp    %ecx,0x24(%rbx)
    6f77:	75 e7                	jne    6f60 <bufferrecv_filter+0x30>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6f79:	be 28 00 00 00       	mov    $0x28,%esi
    6f7e:	bf 01 00 00 00       	mov    $0x1,%edi
    6f83:	e8 78 b4 ff ff       	call   2400 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    6f88:	48 8b 13             	mov    (%rbx),%rdx
            reply->kind = buffers->buffer[x].kind;
    6f8b:	89 68 20             	mov    %ebp,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    6f8e:	48 89 10             	mov    %rdx,(%rax)
            buffers->buffer[x].available = 0;
    6f91:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            asm volatile ("mfence" ::: "memory");
    6f98:	0f ae f0             	mfence
}
    6f9b:	48 83 c4 08          	add    $0x8,%rsp
    6f9f:	5b                   	pop    %rbx
    6fa0:	5d                   	pop    %rbp
    6fa1:	c3                   	ret
    6fa2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
     if (nonblocking == 1) { return NULL; }
    6fa8:	41 83 f9 01          	cmp    $0x1,%r9d
    6fac:	74 13                	je     6fc1 <bufferrecv_filter+0x91>
  while (data->running == 1) {
    6fae:	83 7e 44 01          	cmpl   $0x1,0x44(%rsi)
    6fb2:	75 0d                	jne    6fc1 <bufferrecv_filter+0x91>
      for (int x = 0 ; x < buffers->count ; x++) {
    6fb4:	48 63 02             	movslq (%rdx),%rax
    6fb7:	85 c0                	test   %eax,%eax
    6fb9:	7f 95                	jg     6f50 <bufferrecv_filter+0x20>
  while (data->running == 1) {
    6fbb:	83 7e 44 01          	cmpl   $0x1,0x44(%rsi)
    6fbf:	74 f3                	je     6fb4 <bufferrecv_filter+0x84>
}
    6fc1:	48 83 c4 08          	add    $0x8,%rsp
     if (nonblocking == 1) { return NULL; }
    6fc5:	31 c0                	xor    %eax,%eax
}
    6fc7:	5b                   	pop    %rbx
    6fc8:	5d                   	pop    %rbp
    6fc9:	c3                   	ret
    6fca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000006fd0 <bufferrecv>:
void * bufferrecv(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking) {
    6fd0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    6fd4:	83 7e 44 01          	cmpl   $0x1,0x44(%rsi)
    6fd8:	0f 85 80 00 00 00    	jne    705e <bufferrecv+0x8e>
void * bufferrecv(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking) {
    6fde:	55                   	push   %rbp
    6fdf:	89 cd                	mov    %ecx,%ebp
    6fe1:	53                   	push   %rbx
    6fe2:	48 83 ec 08          	sub    $0x8,%rsp
      for (int x = 0 ; x < buffers->count ; x++) {
    6fe6:	48 63 02             	movslq (%rdx),%rax
    6fe9:	85 c0                	test   %eax,%eax
    6feb:	7e 53                	jle    7040 <bufferrecv+0x70>
    6fed:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    6ff1:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6ff5:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    6ff9:	eb 0e                	jmp    7009 <bufferrecv+0x39>
    6ffb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7000:	48 83 c3 28          	add    $0x28,%rbx
    7004:	48 39 c3             	cmp    %rax,%rbx
    7007:	74 37                	je     7040 <bufferrecv+0x70>
        if (buffers->buffer[x].available == 1) {
    7009:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    700d:	75 f1                	jne    7000 <bufferrecv+0x30>
          if (buffers->buffer[x].kind == kind) {
    700f:	39 6b 20             	cmp    %ebp,0x20(%rbx)
    7012:	75 ec                	jne    7000 <bufferrecv+0x30>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    7014:	be 28 00 00 00       	mov    $0x28,%esi
    7019:	bf 01 00 00 00       	mov    $0x1,%edi
    701e:	e8 dd b3 ff ff       	call   2400 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    7023:	48 8b 13             	mov    (%rbx),%rdx
            reply->kind = buffers->buffer[x].kind;
    7026:	89 68 20             	mov    %ebp,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    7029:	48 89 10             	mov    %rdx,(%rax)
            buffers->buffer[x].available = 0;
    702c:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            asm volatile ("sfence" ::: "memory");
    7033:	0f ae f8             	sfence
}
    7036:	48 83 c4 08          	add    $0x8,%rsp
    703a:	5b                   	pop    %rbx
    703b:	5d                   	pop    %rbp
    703c:	c3                   	ret
    703d:	0f 1f 00             	nopl   (%rax)
     if (nonblocking == 1) { return NULL; }
    7040:	41 83 f9 01          	cmp    $0x1,%r9d
    7044:	74 0f                	je     7055 <bufferrecv+0x85>
  while (data->running == 1) {
    7046:	83 7e 44 01          	cmpl   $0x1,0x44(%rsi)
    704a:	75 09                	jne    7055 <bufferrecv+0x85>
      for (int x = 0 ; x < buffers->count ; x++) {
    704c:	48 63 02             	movslq (%rdx),%rax
    704f:	85 c0                	test   %eax,%eax
    7051:	7f 9a                	jg     6fed <bufferrecv+0x1d>
    7053:	eb f1                	jmp    7046 <bufferrecv+0x76>
}
    7055:	48 83 c4 08          	add    $0x8,%rsp
     if (nonblocking == 1) { return NULL; }
    7059:	31 c0                	xor    %eax,%eax
}
    705b:	5b                   	pop    %rbx
    705c:	5d                   	pop    %rbp
    705d:	c3                   	ret
     if (nonblocking == 1) { return NULL; }
    705e:	31 c0                	xor    %eax,%eax
}
    7060:	c3                   	ret
    7061:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    706c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000007070 <wait_for_new_client>:
struct NewClientMessage * wait_for_new_client(struct KernelThread *data, int nonblocking) {
    7070:	f3 0f 1e fa          	endbr64
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    7074:	48 63 97 1c 01 00 00 	movslq 0x11c(%rdi),%rdx
    707b:	48 c1 e2 04          	shl    $0x4,%rdx
    707f:	48 03 97 10 01 00 00 	add    0x110(%rdi),%rdx
  while (data->running == 1) {
    7086:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    708a:	0f 85 90 00 00 00    	jne    7120 <wait_for_new_client+0xb0>
      for (int x = 0 ; x < buffers->count ; x++) {
    7090:	48 63 02             	movslq (%rdx),%rax
    7093:	85 c0                	test   %eax,%eax
    7095:	7e 71                	jle    7108 <wait_for_new_client+0x98>
struct NewClientMessage * wait_for_new_client(struct KernelThread *data, int nonblocking) {
    7097:	53                   	push   %rbx
    7098:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    709c:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    70a0:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    70a4:	eb 13                	jmp    70b9 <wait_for_new_client+0x49>
    70a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    70b0:	48 83 c3 28          	add    $0x28,%rbx
    70b4:	48 39 c3             	cmp    %rax,%rbx
    70b7:	74 37                	je     70f0 <wait_for_new_client+0x80>
        if (buffers->buffer[x].available == 1) {
    70b9:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    70bd:	75 f1                	jne    70b0 <wait_for_new_client+0x40>
          if (buffers->buffer[x].kind == kind) {
    70bf:	83 7b 20 02          	cmpl   $0x2,0x20(%rbx)
    70c3:	75 eb                	jne    70b0 <wait_for_new_client+0x40>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    70c5:	be 28 00 00 00       	mov    $0x28,%esi
    70ca:	bf 01 00 00 00       	mov    $0x1,%edi
    70cf:	e8 2c b3 ff ff       	call   2400 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    70d4:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    70d7:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            reply->kind = buffers->buffer[x].kind;
    70de:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    70e5:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    70e8:	0f ae f8             	sfence
  struct NewClientMessage *newclientmsg = newclient->data;
    70eb:	48 8b 00             	mov    (%rax),%rax
}
    70ee:	5b                   	pop    %rbx
    70ef:	c3                   	ret
     if (nonblocking == 1) { return NULL; }
    70f0:	83 fe 01             	cmp    $0x1,%esi
    70f3:	74 0f                	je     7104 <wait_for_new_client+0x94>
  while (data->running == 1) {
    70f5:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    70f9:	75 09                	jne    7104 <wait_for_new_client+0x94>
      for (int x = 0 ; x < buffers->count ; x++) {
    70fb:	48 63 02             	movslq (%rdx),%rax
    70fe:	85 c0                	test   %eax,%eax
    7100:	7f 96                	jg     7098 <wait_for_new_client+0x28>
    7102:	eb f1                	jmp    70f5 <wait_for_new_client+0x85>
    return NULL;
    7104:	31 c0                	xor    %eax,%eax
}
    7106:	5b                   	pop    %rbx
    7107:	c3                   	ret
     if (nonblocking == 1) { return NULL; }
    7108:	83 fe 01             	cmp    $0x1,%esi
    710b:	74 13                	je     7120 <wait_for_new_client+0xb0>
  while (data->running == 1) {
    710d:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    7111:	75 0d                	jne    7120 <wait_for_new_client+0xb0>
      for (int x = 0 ; x < buffers->count ; x++) {
    7113:	48 63 02             	movslq (%rdx),%rax
    7116:	85 c0                	test   %eax,%eax
    7118:	0f 8f 79 ff ff ff    	jg     7097 <wait_for_new_client+0x27>
    711e:	eb ed                	jmp    710d <wait_for_new_client+0x9d>
    return NULL;
    7120:	31 c0                	xor    %eax,%eax
}
    7122:	c3                   	ret
    7123:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    712e:	66 90                	xchg   %ax,%ax

0000000000007130 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    7130:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    7134:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    713b:	8b 8e cc 00 00 00    	mov    0xcc(%rsi),%ecx
    7141:	85 c9                	test   %ecx,%ecx
    7143:	0f 8e d5 00 00 00    	jle    721e <barriered_work_ingest+0xee>
int barriered_work_ingest(struct BarrierTask *data) {
    7149:	41 56                	push   %r14
    714b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    714d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    7150:	41 54                	push   %r12
    7152:	49 89 fc             	mov    %rdi,%r12
    7155:	55                   	push   %rbp
    7156:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    7157:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    715b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7160:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    7164:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    716c:	31 ed                	xor    %ebp,%ebp
    716e:	8b 10                	mov    (%rax),%edx
    7170:	85 d2                	test   %edx,%edx
    7172:	7e 25                	jle    7199 <barriered_work_ingest+0x69>
    7174:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    7178:	48 8d 5c ad 00       	lea    0x0(%rbp,%rbp,4),%rbx
    717d:	48 c1 e3 03          	shl    $0x3,%rbx
    7181:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    7185:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    7189:	74 25                	je     71b0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    718b:	48 83 c5 01          	add    $0x1,%rbp
    718f:	39 ea                	cmp    %ebp,%edx
    7191:	7f e5                	jg     7178 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    7193:	8b 8e cc 00 00 00    	mov    0xcc(%rsi),%ecx
    7199:	49 83 c5 01          	add    $0x1,%r13
    719d:	44 39 e9             	cmp    %r13d,%ecx
    71a0:	7f be                	jg     7160 <barriered_work_ingest+0x30>
}
    71a2:	5b                   	pop    %rbx
    71a3:	31 c0                	xor    %eax,%eax
    71a5:	5d                   	pop    %rbp
    71a6:	41 5c                	pop    %r12
    71a8:	41 5d                	pop    %r13
    71aa:	41 5e                	pop    %r14
    71ac:	c3                   	ret
    71ad:	0f 1f 00             	nopl   (%rax)
        data->ingest_count++;
    71b0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    71b9:	48 63 70 1c          	movslq 0x1c(%rax),%rsi
    71bd:	bf 04 00 00 00       	mov    $0x4,%edi
    71c2:	48 c1 e6 05          	shl    $0x5,%rsi
    71c6:	48 03 70 10          	add    0x10(%rax),%rsi
    71ca:	48 83 c6 10          	add    $0x10,%rsi
    71ce:	e8 7d b1 ff ff       	call   2350 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    71d3:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    71db:	48 8b 40 50          	mov    0x50(%rax),%rax
    71df:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    71e3:	48 03 58 08          	add    0x8(%rax),%rbx
    71e7:	8b 43 1c             	mov    0x1c(%rbx),%eax
        data->thread->buffers[b]->buffer[x].available = 0;
    71ea:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    71f1:	83 c0 01             	add    $0x1,%eax
    71f4:	99                   	cltd
    71f5:	f7 7b 18             	idivl  0x18(%rbx)
    71f8:	89 53 1c             	mov    %edx,0x1c(%rbx)
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    71fb:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    7203:	48 83 c5 01          	add    $0x1,%rbp
    7207:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    720b:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    720f:	8b 10                	mov    (%rax),%edx
    7211:	39 ea                	cmp    %ebp,%edx
    7213:	0f 8f 5b ff ff ff    	jg     7174 <barriered_work_ingest+0x44>
    7219:	e9 75 ff ff ff       	jmp    7193 <barriered_work_ingest+0x63>
}
    721e:	31 c0                	xor    %eax,%eax
    7220:	c3                   	ret
    7221:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    722c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000007230 <barriered_thread>:
void* barriered_thread(void *arg) {
    7230:	f3 0f 1e fa          	endbr64
    7234:	41 56                	push   %r14
    7236:	41 55                	push   %r13
    7238:	41 54                	push   %r12
  int t = 0;
    723a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    723d:	55                   	push   %rbp
  int waiting = 0;
    723e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    7240:	53                   	push   %rbx
    7241:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    7244:	0f 1f 40 00          	nopl   0x0(%rax)
    7248:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    724c:	0f 85 8e 02 00 00    	jne    74e0 <barriered_thread+0x2b0>
    if (t >= data->task_count) {
    7252:	8b 43 40             	mov    0x40(%rbx),%eax
    7255:	44 39 e0             	cmp    %r12d,%eax
    7258:	7f 0f                	jg     7269 <barriered_thread+0x39>
      data->cycles++;
    725a:	48 83 83 b8 00 00 00 01 	addq   $0x1,0xb8(%rbx)
    for (; t < data->task_count; t++) {
    7262:	45 31 e4             	xor    %r12d,%r12d
    7265:	85 c0                	test   %eax,%eax
    7267:	7e df                	jle    7248 <barriered_thread+0x18>
    7269:	49 63 fc             	movslq %r12d,%rdi
    726c:	48 c1 e7 09          	shl    $0x9,%rdi
    7270:	49 89 fd             	mov    %rdi,%r13
    7273:	eb 2e                	jmp    72a3 <barriered_thread+0x73>
    7275:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    7278:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    727c:	48 8b 43 18          	mov    0x18(%rbx),%rax
    7280:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7284:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7288:	4c 01 ef             	add    %r13,%rdi
    728b:	e8 a0 fe ff ff       	call   7130 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    7290:	8b 43 40             	mov    0x40(%rbx),%eax
    7293:	41 83 c4 01          	add    $0x1,%r12d
    7297:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    729e:	44 39 e0             	cmp    %r12d,%eax
    72a1:	7e a5                	jle    7248 <barriered_thread+0x18>
      if (data->tasks[t].available == 1) {
    72a3:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    72a7:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    72ab:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    72b2:	75 c4                	jne    7278 <barriered_thread+0x48>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    72b4:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    72b8:	83 e8 01             	sub    $0x1,%eax
    72bb:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    72c0:	45 85 e4             	test   %r12d,%r12d
    72c3:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    72c6:	45 85 c0             	test   %r8d,%r8d
    72c9:	0f 8e 09 01 00 00    	jle    73d8 <barriered_thread+0x1a8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    72cf:	48 63 c8             	movslq %eax,%rcx
    72d2:	48 8b 43 18          	mov    0x18(%rbx),%rax
    72d6:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    72d9:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    72df:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    72e6:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    72ea:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    72ed:	45 31 f6             	xor    %r14d,%r14d
    72f0:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    72f4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    72f8:	48 8b 10             	mov    (%rax),%rdx
    72fb:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    72ff:	49 01 cb             	add    %rcx,%r11
    7302:	4c 89 da             	mov    %r11,%rdx
    7305:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    730c:	75 04                	jne    7312 <barriered_thread+0xe2>
            arrived++;
    730e:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    7312:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    7318:	75 04                	jne    731e <barriered_thread+0xee>
            prearrive++;
    731a:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    731e:	48 83 c0 08          	add    $0x8,%rax
    7322:	48 39 c6             	cmp    %rax,%rsi
    7325:	75 d1                	jne    72f8 <barriered_thread+0xc8>
        if (prearrive == 0 || prearrive == data->thread_count) {
    7327:	45 85 d2             	test   %r10d,%r10d
    732a:	0f 84 98 00 00 00    	je     73c8 <barriered_thread+0x198>
    7330:	45 39 d0             	cmp    %r10d,%r8d
    7333:	0f 84 8f 00 00 00    	je     73c8 <barriered_thread+0x198>
        if (arrived == 0 || arrived == data->thread_count) {
    7339:	45 85 f6             	test   %r14d,%r14d
    733c:	74 0a                	je     7348 <barriered_thread+0x118>
    733e:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    7342:	0f 85 76 01 00 00    	jne    74be <barriered_thread+0x28e>
    7348:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    734c:	4c 01 ea             	add    %r13,%rdx
    734f:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    7356:	45 85 e4             	test   %r12d,%r12d
    7359:	75 14                	jne    736f <barriered_thread+0x13f>
    735b:	48 8b b3 90 00 00 00 	mov    0x90(%rbx),%rsi
    7362:	48 3b b3 98 00 00 00 	cmp    0x98(%rbx),%rsi
    7369:	0f 8c 31 01 00 00    	jl     74a0 <barriered_thread+0x270>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    736f:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    7373:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    7377:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    7381:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    7385:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7389:	4c 01 ef             	add    %r13,%rdi
    738c:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    7392:	48 8b 43 38          	mov    0x38(%rbx),%rax
    7396:	4c 01 e8             	add    %r13,%rax
    7399:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    73a0:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    73a3:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    73ab:	83 e8 01             	sub    $0x1,%eax
    73ae:	44 39 e0             	cmp    %r12d,%eax
    73b1:	74 7d                	je     7430 <barriered_thread+0x200>
          if (waiting == 0) {
    73b3:	85 ed                	test   %ebp,%ebp
    73b5:	0f 84 b5 00 00 00    	je     7470 <barriered_thread+0x240>
        int arrived = 0; 
    73bb:	bd 01 00 00 00       	mov    $0x1,%ebp
    73c0:	e9 cb fe ff ff       	jmp    7290 <barriered_thread+0x60>
    73c5:	0f 1f 00             	nopl   (%rax)
          if (waiting == 1) {
    73c8:	83 fd 01             	cmp    $0x1,%ebp
    73cb:	74 1b                	je     73e8 <barriered_thread+0x1b8>
        int arrived = 0; 
    73cd:	31 ed                	xor    %ebp,%ebp
    73cf:	e9 65 ff ff ff       	jmp    7339 <barriered_thread+0x109>
    73d4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    73d8:	83 fd 01             	cmp    $0x1,%ebp
    73db:	0f 85 6b ff ff ff    	jne    734c <barriered_thread+0x11c>
        int arrived = 0; 
    73e1:	45 31 f6             	xor    %r14d,%r14d
    73e4:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    73e8:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    73ef:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    73f4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    73f6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    73fa:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    7401:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    7406:	e8 45 af ff ff       	call   2350 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    740b:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    7412:	48 83 c0 01          	add    $0x1,%rax
    7416:	48 99                	cqto
    7418:	48 f7 bb b0 00 00 00 	idivq  0xb0(%rbx)
    741f:	48 89 93 a8 00 00 00 	mov    %rdx,0xa8(%rbx)
            waiting = 0; 
    7426:	e9 0e ff ff ff       	jmp    7339 <barriered_thread+0x109>
    742b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7430:	48 8b b3 90 00 00 00 	mov    0x90(%rbx),%rsi
    7437:	48 3b b3 98 00 00 00 	cmp    0x98(%rbx),%rsi
    743e:	0f 8d 6f ff ff ff    	jge    73b3 <barriered_thread+0x183>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    7444:	48 c1 e6 04          	shl    $0x4,%rsi
    7448:	bf 04 00 00 00       	mov    $0x4,%edi
    744d:	48 03 b3 80 00 00 00 	add    0x80(%rbx),%rsi
    7454:	e8 f7 ae ff ff       	call   2350 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    7459:	48 83 83 90 00 00 00 01 	addq   $0x1,0x90(%rbx)
          if (waiting == 0) {
    7461:	85 ed                	test   %ebp,%ebp
    7463:	0f 85 52 ff ff ff    	jne    73bb <barriered_thread+0x18b>
    7469:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            data->task_snapshot[data->task_timestamp_count].task = t;
    7470:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    7477:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    747c:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    7480:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    7487:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    748b:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    748f:	e8 bc ae ff ff       	call   2350 <clock_gettime@plt>
            waiting = 1;
    7494:	e9 22 ff ff ff       	jmp    73bb <barriered_thread+0x18b>
    7499:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    74a0:	48 c1 e6 04          	shl    $0x4,%rsi
    74a4:	bf 04 00 00 00       	mov    $0x4,%edi
    74a9:	48 03 73 78          	add    0x78(%rbx),%rsi
    74ad:	e8 9e ae ff ff       	call   2350 <clock_gettime@plt>
          data->tasks[t].available = 0;
    74b2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    74b6:	4c 01 ea             	add    %r13,%rdx
    74b9:	e9 b1 fe ff ff       	jmp    736f <barriered_thread+0x13f>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    74be:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    74c2:	48 8b 43 18          	mov    0x18(%rbx),%rax
    74c6:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    74ca:	48 8b 78 38          	mov    0x38(%rax),%rdi
    74ce:	4c 01 ef             	add    %r13,%rdi
    74d1:	e8 5a fc ff ff       	call   7130 <barriered_work_ingest>
  while (data->running == 1) {
    74d6:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    74da:	0f 84 72 fd ff ff    	je     7252 <barriered_thread+0x22>
}
    74e0:	5b                   	pop    %rbx
    74e1:	31 c0                	xor    %eax,%eax
    74e3:	5d                   	pop    %rbp
    74e4:	41 5c                	pop    %r12
    74e6:	41 5d                	pop    %r13
    74e8:	41 5e                	pop    %r14
    74ea:	c3                   	ret
    74eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000074f0 <receive>:
int receive(struct BarrierTask *data) {
    74f0:	f3 0f 1e fa          	endbr64
    74f4:	41 56                	push   %r14
    74f6:	41 55                	push   %r13
    74f8:	41 54                	push   %r12
    74fa:	55                   	push   %rbp
    74fb:	53                   	push   %rbx
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    74fc:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    7503:	45 85 e4             	test   %r12d,%r12d
    7506:	0f 8e 27 01 00 00    	jle    7633 <receive+0x143>
    if (n == data->thread->real_thread_index) { continue; }
    750c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    7513:	48 89 fe             	mov    %rdi,%rsi
    7516:	31 db                	xor    %ebx,%ebx
    7518:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    751c:	49 89 ed             	mov    %rbp,%r13
    751f:	90                   	nop
    7520:	41 39 dd             	cmp    %ebx,%r13d
    7523:	0f 84 fd 00 00 00    	je     7626 <receive+0x136>
    struct Data *me = data->mailboxes[n].lower;
    7529:	48 89 d8             	mov    %rbx,%rax
    752c:	48 c1 e0 08          	shl    $0x8,%rax
    7530:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    7537:	48 8b 10             	mov    (%rax),%rdx
    if (me->available_reading == 1) {
    753a:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    7540:	83 f8 01             	cmp    $0x1,%eax
    7543:	74 11                	je     7556 <receive+0x66>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    7545:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    754c:	75 08                	jne    7556 <receive+0x66>
    754e:	85 c0                	test   %eax,%eax
    7550:	0f 84 d0 00 00 00    	je     7626 <receive+0x136>
    for (; me->messages_count > 0 ; ) {
    7556:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    755d:	48 85 ff             	test   %rdi,%rdi
    7560:	0f 8e a2 00 00 00    	jle    7608 <receive+0x118>
    7566:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    756d:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    7574:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
    7578:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    757b:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    757f:	49 01 f9             	add    %rdi,%r9
    7582:	49 01 f8             	add    %rdi,%r8
    7585:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    758c:	eb 08                	jmp    7596 <receive+0xa6>
    758e:	66 90                	xchg   %ax,%ax
    for (; me->messages_count > 0 ; ) {
    7590:	48 83 e8 01          	sub    $0x1,%rax
    7594:	72 72                	jb     7608 <receive+0x118>
      data->sends++;
    7596:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
    7599:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
    75a0:	48 29 c1             	sub    %rax,%rcx
    75a3:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      data->n++;
    75aa:	4c 89 c1             	mov    %r8,%rcx
    75ad:	48 29 c1             	sub    %rax,%rcx
    75b0:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
    75b7:	48 89 f9             	mov    %rdi,%rcx
    75ba:	48 29 c1             	sub    %rax,%rcx
    75bd:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
      if (me->messages[x]->group == data->group) {
    75c4:	48 63 c8             	movslq %eax,%rcx
    75c7:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    75cb:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    75cf:	75 bf                	jne    7590 <receive+0xa0>
    75d1:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    75d5:	75 b9                	jne    7590 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    75d7:	49 63 46 04          	movslq 0x4(%r14),%rax
    75db:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    75dd:	bf 01 00 00 00       	mov    $0x1,%edi
    75e2:	ba 01 00 00 00       	mov    $0x1,%edx
    75e7:	48 8d 35 22 22 00 00 	lea    0x2222(%rip),%rsi        # 9810 <_IO_stdin_used+0x810>
    75ee:	48 39 e8             	cmp    %rbp,%rax
    75f1:	0f 94 c1             	sete   %cl
    75f4:	31 c0                	xor    %eax,%eax
    75f6:	e8 b5 ae ff ff       	call   24b0 <__printf_chk@plt>
        exit(1);
    75fb:	bf 01 00 00 00       	mov    $0x1,%edi
    7600:	e8 1b af ff ff       	call   2520 <exit@plt>
    7605:	0f 1f 00             	nopl   (%rax)
      me->available_reading = 0;
    7608:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    7612:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
    761c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7626:	48 83 c3 01          	add    $0x1,%rbx
    762a:	49 39 dc             	cmp    %rbx,%r12
    762d:	0f 85 ed fe ff ff    	jne    7520 <receive+0x30>
}
    7633:	31 c0                	xor    %eax,%eax
    7635:	5b                   	pop    %rbx
    7636:	5d                   	pop    %rbp
    7637:	41 5c                	pop    %r12
    7639:	41 5d                	pop    %r13
    763b:	41 5e                	pop    %r14
    763d:	c3                   	ret
    763e:	66 90                	xchg   %ax,%ax

0000000000007640 <sendm>:
int sendm(struct BarrierTask *data) {
    7640:	f3 0f 1e fa          	endbr64
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7644:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    764a:	85 c0                	test   %eax,%eax
    764c:	0f 8e 96 02 00 00    	jle    78e8 <sendm+0x2a8>
int sendm(struct BarrierTask *data) {
    7652:	41 57                	push   %r15
    7654:	41 56                	push   %r14
    7656:	41 55                	push   %r13
        if (n == data->thread->real_thread_index) { continue; }
    7658:	45 31 ed             	xor    %r13d,%r13d
int sendm(struct BarrierTask *data) {
    765b:	41 54                	push   %r12
    765d:	4c 63 e0             	movslq %eax,%r12
    7660:	55                   	push   %rbp
    7661:	48 89 fd             	mov    %rdi,%rbp
    7664:	53                   	push   %rbx
        if (n == data->thread->real_thread_index) { continue; }
    7665:	48 8b 9f 28 01 00 00 	mov    0x128(%rdi),%rbx
    766c:	44 8b 7b 08          	mov    0x8(%rbx),%r15d
    7670:	48 89 5c 24 c8       	mov    %rbx,-0x38(%rsp)
    7675:	0f 1f 00             	nopl   (%rax)
    7678:	45 39 ef             	cmp    %r13d,%r15d
    767b:	0f 84 97 00 00 00    	je     7718 <sendm+0xd8>
        struct Data *them = data->mailboxes[n].higher;
    7681:	4c 89 e8             	mov    %r13,%rax
    7684:	48 c1 e0 08          	shl    $0x8,%rax
    7688:	48 03 85 70 01 00 00 	add    0x170(%rbp),%rax
        data->mailboxes[n].counter++;
    768f:	48 8b 98 b8 00 00 00 	mov    0xb8(%rax),%rbx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7696:	83 b8 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax)
        struct Data *them = data->mailboxes[n].higher;
    769d:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    76a4:	40 0f 94 c7          	sete   %dil
        data->mailboxes[n].counter++;
    76a8:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    76ac:	48 89 90 b8 00 00 00 	mov    %rdx,0xb8(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    76b3:	48 85 d2             	test   %rdx,%rdx
    76b6:	7f 05                	jg     76bd <sendm+0x7d>
    76b8:	40 84 ff             	test   %dil,%dil
    76bb:	75 5b                	jne    7718 <sendm+0xd8>
        if (them->messages_count > 0) {
    76bd:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    76c4:	48 85 f6             	test   %rsi,%rsi
    76c7:	7f 4f                	jg     7718 <sendm+0xd8>
        if (them->available_sending == 1) {
    76c9:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    76d0:	41 83 f8 01          	cmp    $0x1,%r8d
    76d4:	74 0e                	je     76e4 <sendm+0xa4>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    76d6:	83 b9 08 04 00 00 02 	cmpl   $0x2,0x408(%rcx)
    76dd:	75 05                	jne    76e4 <sendm+0xa4>
    76df:	45 85 c0             	test   %r8d,%r8d
    76e2:	74 34                	je     7718 <sendm+0xd8>
        if (data->sending == 1) {
    76e4:	83 bd 88 01 00 00 01 	cmpl   $0x1,0x188(%rbp)
    76eb:	74 4b                	je     7738 <sendm+0xf8>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter >= limit) {
    76ed:	48 85 d2             	test   %rdx,%rdx
    76f0:	7e 26                	jle    7718 <sendm+0xd8>
    76f2:	40 84 ff             	test   %dil,%dil
    76f5:	74 21                	je     7718 <sendm+0xd8>
          data->mailboxes[n].counter = 0;
    76f7:	48 c7 80 b8 00 00 00 00 00 00 00 	movq   $0x0,0xb8(%rax)
          data->thread->have_foreign = 1;
    7702:	48 8b 44 24 c8       	mov    -0x38(%rsp),%rax
    7707:	c7 80 08 01 00 00 01 00 00 00 	movl   $0x1,0x108(%rax)
    7711:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7718:	49 83 c5 01          	add    $0x1,%r13
    771c:	4d 39 ec             	cmp    %r13,%r12
    771f:	0f 85 53 ff ff ff    	jne    7678 <sendm+0x38>
}
    7725:	31 c0                	xor    %eax,%eax
    7727:	5b                   	pop    %rbx
    7728:	5d                   	pop    %rbp
    7729:	41 5c                	pop    %r12
    772b:	41 5d                	pop    %r13
    772d:	41 5e                	pop    %r14
    772f:	41 5f                	pop    %r15
    7731:	c3                   	ret
    7732:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (; them->messages_count < min;) {
    7738:	4c 63 99 88 00 00 00 	movslq 0x88(%rcx),%r11
    773f:	4c 39 de             	cmp    %r11,%rsi
    7742:	0f 8d c2 00 00 00    	jge    780a <sendm+0x1ca>
    7748:	48 8b 9d 08 01 00 00 	mov    0x108(%rbp),%rbx
    774f:	4d 89 de             	mov    %r11,%r14
            them->messages[them->messages_count++] = data->message; 
    7752:	4c 8b 11             	mov    (%rcx),%r10
    7755:	49 29 f6             	sub    %rsi,%r14
    7758:	48 89 5c 24 d8       	mov    %rbx,-0x28(%rsp)
    775d:	48 8b 99 80 03 00 00 	mov    0x380(%rcx),%rbx
    7764:	4d 8d 46 ff          	lea    -0x1(%r14),%r8
    7768:	48 89 5c 24 e0       	mov    %rbx,-0x20(%rsp)
    776d:	49 83 f8 02          	cmp    $0x2,%r8
    7771:	0f 86 51 01 00 00    	jbe    78c8 <sendm+0x288>
    7777:	48 8d 1c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rbx
    777f:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    7787:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    778c:	4c 01 d3             	add    %r10,%rbx
    778f:	4c 8d 85 90 01 00 00 	lea    0x190(%rbp),%r8
    7796:	48 89 5c 24 d0       	mov    %rbx,-0x30(%rsp)
    779b:	4b 8d 1c 0a          	lea    (%r10,%r9,1),%rbx
    779f:	49 39 d8             	cmp    %rbx,%r8
    77a2:	0f 83 88 00 00 00    	jae    7830 <sendm+0x1f0>
    77a8:	48 8d 9d 98 01 00 00 	lea    0x198(%rbp),%rbx
    77af:	48 39 5c 24 d0       	cmp    %rbx,-0x30(%rsp)
    77b4:	73 7a                	jae    7830 <sendm+0x1f0>
    77b6:	4c 8b 44 24 e8       	mov    -0x18(%rsp),%r8
    77bb:	4b 8d 34 0a          	lea    (%r10,%r9,1),%rsi
    77bf:	4d 01 d0             	add    %r10,%r8
    77c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    77c8:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
          for (; them->messages_count < min;) {
    77cf:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    77d3:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    77d7:	4c 39 c6             	cmp    %r8,%rsi
    77da:	75 ec                	jne    77c8 <sendm+0x188>
    77dc:	0f 1f 40 00          	nopl   0x0(%rax)
    77e0:	48 8b 74 24 d8       	mov    -0x28(%rsp),%rsi
    77e5:	4c 01 f6             	add    %r14,%rsi
    77e8:	48 89 b5 08 01 00 00 	mov    %rsi,0x108(%rbp)
    77ef:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    77f4:	4c 89 99 80 00 00 00 	mov    %r11,0x80(%rcx)
    77fb:	4c 01 f6             	add    %r14,%rsi
    77fe:	48 89 b1 80 03 00 00 	mov    %rsi,0x380(%rcx)
    7805:	4f 89 4c da f8       	mov    %r9,-0x8(%r10,%r11,8)
          them->available_sending = 0;
    780a:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_reading = 1;
    7814:	c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rcx)
          them->available_receiving = 1;
    781e:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    7828:	e9 c0 fe ff ff       	jmp    76ed <sendm+0xad>
    782d:	0f 1f 00             	nopl   (%rax)
    7830:	4c 89 f3             	mov    %r14,%rbx
    7833:	4c 8b 44 24 d0       	mov    -0x30(%rsp),%r8
    7838:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    783f:	48 d1 eb             	shr    %rbx
    7842:	48 c1 e3 04          	shl    $0x4,%rbx
    7846:	66 49 0f 6e c1       	movq   %r9,%xmm0
    784b:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    7850:	4c 01 c3             	add    %r8,%rbx
    7853:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    7857:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    785c:	48 8b 5c 24 e8       	mov    -0x18(%rsp),%rbx
    7861:	83 e3 10             	and    $0x10,%ebx
    7864:	75 4a                	jne    78b0 <sendm+0x270>
    7866:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    786b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    7870:	41 0f 11 00          	movups %xmm0,(%r8)
    7874:	49 83 c0 20          	add    $0x20,%r8
    7878:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    787d:	49 39 d8             	cmp    %rbx,%r8
    7880:	75 ee                	jne    7870 <sendm+0x230>
    7882:	4d 89 f0             	mov    %r14,%r8
    7885:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    7889:	49 01 f0             	add    %rsi,%r8
    788c:	41 f6 c6 01          	test   $0x1,%r14b
    7890:	0f 84 4a ff ff ff    	je     77e0 <sendm+0x1a0>
            them->messages[them->messages_count++] = data->message; 
    7896:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    789d:	4f 89 0c c2          	mov    %r9,(%r10,%r8,8)
          for (; them->messages_count < min;) {
    78a1:	e9 3a ff ff ff       	jmp    77e0 <sendm+0x1a0>
    78a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    78b0:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    78b5:	41 0f 11 00          	movups %xmm0,(%r8)
          for (; them->messages_count < min;) {
    78b9:	49 83 c0 10          	add    $0x10,%r8
    78bd:	49 39 d8             	cmp    %rbx,%r8
    78c0:	75 ae                	jne    7870 <sendm+0x230>
    78c2:	eb be                	jmp    7882 <sendm+0x242>
    78c4:	0f 1f 40 00          	nopl   0x0(%rax)
    78c8:	48 8d 34 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rsi
    78d0:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    78d8:	48 89 74 24 e8       	mov    %rsi,-0x18(%rsp)
    78dd:	e9 d4 fe ff ff       	jmp    77b6 <sendm+0x176>
    78e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
}
    78e8:	31 c0                	xor    %eax,%eax
    78ea:	c3                   	ret
    78eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000078f0 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    78f0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    78f4:	85 f6                	test   %esi,%esi
    78f6:	74 18                	je     7910 <mailboxkind+0x20>
  return NULL;
    78f8:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    78fa:	83 fe 01             	cmp    $0x1,%esi
    78fd:	74 01                	je     7900 <mailboxkind+0x10>
}
    78ff:	c3                   	ret
    return mailbox->higher;
    7900:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
}
    7907:	c3                   	ret
    7908:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    return mailbox->lower;
    7910:	48 8b 07             	mov    (%rdi),%rax
    7913:	c3                   	ret
    7914:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    791f:	90                   	nop

0000000000007920 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    7920:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    7924:	85 d2                	test   %edx,%edx
    7926:	75 08                	jne    7930 <setmailboxkind+0x10>
    mailbox->lower = data;
    7928:	48 89 37             	mov    %rsi,(%rdi)
}
    792b:	31 c0                	xor    %eax,%eax
    792d:	c3                   	ret
    792e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    7930:	83 fa 01             	cmp    $0x1,%edx
    7933:	74 13                	je     7948 <setmailboxkind+0x28>
  if (kind == 2) {
    7935:	83 fa 02             	cmp    $0x2,%edx
    7938:	75 1e                	jne    7958 <setmailboxkind+0x38>
    mailbox->pending_lower = data;
    793a:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
}
    7941:	31 c0                	xor    %eax,%eax
    7943:	c3                   	ret
    7944:	0f 1f 40 00          	nopl   0x0(%rax)
    mailbox->higher = data;
    7948:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
}
    794f:	31 c0                	xor    %eax,%eax
    7951:	c3                   	ret
    7952:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (kind == 3) {
    7958:	83 fa 03             	cmp    $0x3,%edx
    795b:	75 ce                	jne    792b <setmailboxkind+0xb>
    mailbox->pending_higher = data;
    795d:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
}
    7964:	31 c0                	xor    %eax,%eax
    7966:	c3                   	ret
    7967:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007970 <fswap>:
int fswap(struct BarrierTask *data) {
    7970:	f3 0f 1e fa          	endbr64
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    7974:	48 8b 8f 28 01 00 00 	mov    0x128(%rdi),%rcx
    797b:	8b 87 9c 01 00 00    	mov    0x19c(%rdi),%eax
    7981:	44 8b 97 30 01 00 00 	mov    0x130(%rdi),%r10d
  int t = data->task_index;
    7988:	48 63 57 04          	movslq 0x4(%rdi),%rdx
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    798c:	4c 63 99 d4 00 00 00 	movslq 0xd4(%rcx),%r11
    7993:	41 0f af c3          	imul   %r11d,%eax
    7997:	41 01 c2             	add    %eax,%r10d
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    799a:	45 85 db             	test   %r11d,%r11d
    799d:	0f 8e 18 01 00 00    	jle    7abb <fswap+0x14b>
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    79a3:	4d 63 d2             	movslq %r10d,%r10
int fswap(struct BarrierTask *data) {
    79a6:	41 56                	push   %r14
    79a8:	48 98                	cltq
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    79aa:	48 c1 e2 09          	shl    $0x9,%rdx
int fswap(struct BarrierTask *data) {
    79ae:	41 55                	push   %r13
    79b0:	48 89 c6             	mov    %rax,%rsi
    79b3:	49 01 c3             	add    %rax,%r11
    79b6:	41 54                	push   %r12
    79b8:	48 c1 e6 08          	shl    $0x8,%rsi
    79bc:	49 c1 e3 08          	shl    $0x8,%r11
    79c0:	55                   	push   %rbp
    79c1:	53                   	push   %rbx
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    79c2:	4c 8b 49 20          	mov    0x20(%rcx),%r9
    79c6:	4b 8d 0c d2          	lea    (%r10,%r10,8),%rcx
    79ca:	49 8d 0c 4a          	lea    (%r10,%rcx,2),%rcx
        int next_task = abs((t + 1) % (data->thread_count));
    79ce:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    79d5:	49 c1 e2 08          	shl    $0x8,%r10
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    79d9:	48 c1 e1 04          	shl    $0x4,%rcx
    79dd:	49 8b 5c 09 38       	mov    0x38(%r9,%rcx,1),%rbx
    79e2:	48 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%rbp
    79ea:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    79ee:	48 8d 14 50          	lea    (%rax,%rdx,2),%rdx
    79f2:	48 c1 e2 04          	shl    $0x4,%rdx
    79f6:	49 01 d1             	add    %rdx,%r9
    79f9:	eb 1c                	jmp    7a17 <fswap+0xa7>
    79fb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    7a00:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    7a07:	49 81 c1 30 01 00 00 	add    $0x130,%r9
    7a0e:	49 39 f3             	cmp    %rsi,%r11
    7a11:	0f 84 99 00 00 00    	je     7ab0 <fswap+0x140>
        if (kind == MAILBOX_FRIEND) {
    7a17:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    7a1f:	75 df                	jne    7a00 <fswap+0x90>
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    7a21:	49 8b 79 38          	mov    0x38(%r9),%rdi
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    7a25:	45 85 c0             	test   %r8d,%r8d
    7a28:	7e d6                	jle    7a00 <fswap+0x90>
    7a2a:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    7a31:	31 c9                	xor    %ecx,%ecx
    7a33:	eb 58                	jmp    7a8d <fswap+0x11d>
    7a35:	0f 1f 00             	nopl   (%rax)
              struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    7a38:	48 63 d2             	movslq %edx,%rdx
    7a3b:	48 c1 e2 09          	shl    $0x9,%rdx
    7a3f:	4c 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%r13
    7a47:	49 01 f5             	add    %rsi,%r13
    7a4a:	4c 89 ea             	mov    %r13,%rdx
    return mailbox->lower;
    7a4d:	4d 8b 6d 00          	mov    0x0(%r13),%r13
                if (dest->messages_count != 0) { 
    7a51:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    7a59:	75 22                	jne    7a7d <fswap+0x10d>
    mailbox->lower = data;
    7a5b:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    7a62:	4c 89 32             	mov    %r14,(%rdx)
    7a65:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    mailbox->higher = data;
    7a6c:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    mailbox->lower = data;
    7a73:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    7a76:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    7a7d:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    7a84:	41 39 c8             	cmp    %ecx,%r8d
    7a87:	0f 84 73 ff ff ff    	je     7a00 <fswap+0x90>
              int next_task = abs((nn + 1) % (data->thread_count));
    7a8d:	83 c1 01             	add    $0x1,%ecx
    7a90:	89 c8                	mov    %ecx,%eax
    7a92:	99                   	cltd
    7a93:	41 f7 f8             	idiv   %r8d
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7a96:	48 8b 07             	mov    (%rdi),%rax
    7a99:	4c 01 d0             	add    %r10,%rax
    return mailbox->lower;
    7a9c:	4c 8b 20             	mov    (%rax),%r12
                if (source2->messages_count != 0) { 
    7a9f:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    7aa8:	74 8e                	je     7a38 <fswap+0xc8>
    7aaa:	e9 51 ff ff ff       	jmp    7a00 <fswap+0x90>
    7aaf:	90                   	nop
}
    7ab0:	5b                   	pop    %rbx
    7ab1:	31 c0                	xor    %eax,%eax
    7ab3:	5d                   	pop    %rbp
    7ab4:	41 5c                	pop    %r12
    7ab6:	41 5d                	pop    %r13
    7ab8:	41 5e                	pop    %r14
    7aba:	c3                   	ret
    7abb:	31 c0                	xor    %eax,%eax
    7abd:	c3                   	ret
    7abe:	66 90                	xchg   %ax,%ax

0000000000007ac0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    7ac0:	f3 0f 1e fa          	endbr64
    7ac4:	41 57                	push   %r15
    7ac6:	41 56                	push   %r14
    7ac8:	41 55                	push   %r13
    7aca:	41 54                	push   %r12
    7acc:	55                   	push   %rbp
    7acd:	53                   	push   %rbx
    7ace:	48 89 fb             	mov    %rdi,%rbx
    7ad1:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
  struct timespec preempt = {
    7ad8:	66 0f 6f 05 20 23 00 00 	movdqa 0x2320(%rip),%xmm0        # 9e00 <_IO_stdin_used+0xe00>
int barriered_work(struct BarrierTask *data) {
    7ae0:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    7ae9:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    7aee:	31 c0                	xor    %eax,%eax
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    7af0:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  struct timespec preempt = {
    7af7:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    7afc:	48 8b 88 00 01 00 00 	mov    0x100(%rax),%rcx
  struct timespec rem = {
    7b03:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    7b08:	8b 11                	mov    (%rcx),%edx
    7b0a:	83 fa ff             	cmp    $0xffffffff,%edx
    7b0d:	0f 84 ed 02 00 00    	je     7e00 <barriered_work+0x340>
    7b13:	3b 90 f8 00 00 00    	cmp    0xf8(%rax),%edx
    7b19:	74 2d                	je     7b48 <barriered_work+0x88>
}
    7b1b:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    7b20:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    7b29:	0f 85 50 05 00 00    	jne    807f <barriered_work+0x5bf>
    7b2f:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    7b36:	31 c0                	xor    %eax,%eax
    7b38:	5b                   	pop    %rbx
    7b39:	5d                   	pop    %rbp
    7b3a:	41 5c                	pop    %r12
    7b3c:	41 5d                	pop    %r13
    7b3e:	41 5e                	pop    %r14
    7b40:	41 5f                	pop    %r15
    7b42:	c3                   	ret
    7b43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    7b48:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    7b4f:	8b 41 04             	mov    0x4(%rcx),%eax
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    7b52:	85 ed                	test   %ebp,%ebp
    7b54:	0f 85 a6 04 00 00    	jne    8000 <barriered_work+0x540>
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    7b5a:	85 c0                	test   %eax,%eax
    7b5c:	0f 84 a6 04 00 00    	je     8008 <barriered_work+0x548>
    7b62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          int t = data->task_index;
    7b68:	44 8b 63 04          	mov    0x4(%rbx),%r12d
      receive(data);
    7b6c:	48 89 df             	mov    %rbx,%rdi
    if (data->thread_index == data->task_index) {
    7b6f:	41 39 ec             	cmp    %ebp,%r12d
    7b72:	0f 85 d0 03 00 00    	jne    7f48 <barriered_work+0x488>
      receive(data);
    7b78:	e8 73 f9 ff ff       	call   74f0 <receive>
        if (data->thread->have_foreign == 1) {
    7b7d:	4c 8b bb 28 01 00 00 	mov    0x128(%rbx),%r15
    7b84:	41 83 bf 08 01 00 00 01 	cmpl   $0x1,0x108(%r15)
    7b8c:	0f 85 c6 02 00 00    	jne    7e58 <barriered_work+0x398>
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7b92:	44 8b b3 40 01 00 00 	mov    0x140(%rbx),%r14d
    7b99:	45 85 f6             	test   %r14d,%r14d
    7b9c:	0f 8e b6 02 00 00    	jle    7e58 <barriered_work+0x398>
                int next_task = abs((t + 1) % (data->thread_count));
    7ba2:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7ba8:	48 c1 e5 09          	shl    $0x9,%rbp
    7bac:	45 31 c0             	xor    %r8d,%r8d
    7baf:	31 f6                	xor    %esi,%esi
    7bb1:	49 89 ed             	mov    %rbp,%r13
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7bb4:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
                int next_task = abs((t + 1) % (data->thread_count));
    7bbc:	89 44 24 24          	mov    %eax,0x24(%rsp)
          int b = data->thread->real_thread_index;
    7bc0:	49 63 47 08          	movslq 0x8(%r15),%rax
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7bc4:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7bc9:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
          int b = data->thread->real_thread_index;
    7bcd:	48 89 c2             	mov    %rax,%rdx
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7bd0:	48 8d 0c 48          	lea    (%rax,%rcx,2),%rcx
    7bd4:	48 c1 e0 08          	shl    $0x8,%rax
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7bd8:	41 89 d3             	mov    %edx,%r11d
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7bdb:	48 c1 e1 04          	shl    $0x4,%rcx
    7bdf:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    7be4:	48 89 cd             	mov    %rcx,%rbp
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7be7:	48 89 d9             	mov    %rbx,%rcx
    7bea:	eb 24                	jmp    7c10 <barriered_work+0x150>
    7bec:	0f 1f 40 00          	nopl   0x0(%rax)
    7bf0:	83 44 24 0c 01       	addl   $0x1,0xc(%rsp)
    7bf5:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    7bf9:	48 81 c6 30 01 00 00 	add    $0x130,%rsi
    7c00:	49 81 c0 00 01 00 00 	add    $0x100,%r8
    7c07:	44 39 f0             	cmp    %r14d,%eax
    7c0a:	0f 84 40 02 00 00    	je     7e50 <barriered_work+0x390>
                if (y == b) { continue; }
    7c10:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    7c14:	41 39 c3             	cmp    %eax,%r11d
    7c17:	74 d7                	je     7bf0 <barriered_work+0x130>
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7c19:	49 8b 57 20          	mov    0x20(%r15),%rdx
    7c1d:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    7c22:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    7c26:	44 8b 88 a0 01 00 00 	mov    0x1a0(%rax),%r9d
    7c2d:	45 85 c9             	test   %r9d,%r9d
    7c30:	75 be                	jne    7bf0 <barriered_work+0x130>
    7c32:	4c 8b 4c 2a 38       	mov    0x38(%rdx,%rbp,1),%r9
    7c37:	4b 8d 14 29          	lea    (%r9,%r13,1),%rdx
    7c3b:	44 8b 92 a0 01 00 00 	mov    0x1a0(%rdx),%r10d
    7c42:	45 85 d2             	test   %r10d,%r10d
    7c45:	75 a9                	jne    7bf0 <barriered_work+0x130>
    7c47:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    7c4e:	42 83 bc 02 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r8,1)
    7c57:	75 97                	jne    7bf0 <barriered_work+0x130>
    7c59:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    7c60:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    7c65:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    7c6d:	75 81                	jne    7bf0 <barriered_work+0x130>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    7c6f:	48 63 44 24 24       	movslq 0x24(%rsp),%rax
    7c74:	85 c0                	test   %eax,%eax
    7c76:	0f 8e 74 ff ff ff    	jle    7bf0 <barriered_work+0x130>
    7c7c:	48 89 c2             	mov    %rax,%rdx
    7c7f:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    7c84:	41 bc 70 01 00 00    	mov    $0x170,%r12d
    7c8a:	48 c1 e2 09          	shl    $0x9,%rdx
    7c8e:	44 89 74 24 3c       	mov    %r14d,0x3c(%rsp)
    7c93:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    7c98:	48 8d 9a a0 01 00 00 	lea    0x1a0(%rdx),%rbx
    7c9f:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    7ca4:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    7ca9:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    7cae:	44 89 5c 24 38       	mov    %r11d,0x38(%rsp)
    7cb3:	44 8b 5c 24 24       	mov    0x24(%rsp),%r11d
    7cb8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                        int next_task = abs((nn + 1) % data->thread_count);
    7cc0:	41 83 c2 01          	add    $0x1,%r10d
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7cc4:	4b 8b 34 21          	mov    (%r9,%r12,1),%rsi
                        int next_task = abs((nn + 1) % data->thread_count);
    7cc8:	44 89 d0             	mov    %r10d,%eax
    7ccb:	99                   	cltd
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7ccc:	4c 01 c6             	add    %r8,%rsi
                        int next_task = abs((nn + 1) % data->thread_count);
    7ccf:	41 f7 fb             	idiv   %r11d
    return mailbox->lower;
    7cd2:	4c 8b 36             	mov    (%rsi),%r14
    7cd5:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    mailbox->lower = data;
    7cda:	4c 8b b6 80 00 00 00 	mov    0x80(%rsi),%r14
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    7ce1:	48 63 d2             	movslq %edx,%rdx
    7ce4:	48 c1 e2 09          	shl    $0x9,%rdx
    7ce8:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    7cf0:	4c 01 e8             	add    %r13,%rax
    return mailbox->lower;
    7cf3:	4c 8b 38             	mov    (%rax),%r15
    return mailbox->higher;
    7cf6:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    mailbox->lower = data;
    7cfd:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    7d00:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    7d05:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    mailbox->lower = data;
    7d0c:	48 89 16             	mov    %rdx,(%rsi)
    mailbox->higher = data;
    7d0f:	4c 89 be 80 00 00 00 	mov    %r15,0x80(%rsi)
    7d16:	be a0 01 00 00       	mov    $0x1a0,%esi
    7d1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
    7d20:	41 c7 04 31 01 00 00 00 	movl   $0x1,(%r9,%rsi,1)
                          data->thread->all_threads[t2].tasks[jj].swap = 1;
    7d28:	c7 04 37 01 00 00 00 	movl   $0x1,(%rdi,%rsi,1)
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
    7d2f:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    7d36:	48 39 de             	cmp    %rbx,%rsi
    7d39:	75 e5                	jne    7d20 <barriered_work+0x260>
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    7d3b:	4a 8b 34 27          	mov    (%rdi,%r12,1),%rsi
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    7d3f:	48 8b 00             	mov    (%rax),%rax
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    7d42:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    7d4d:	49 81 c4 00 02 00 00 	add    $0x200,%r12
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    7d54:	4a 8b b4 2e 80 00 00 00 	mov    0x80(%rsi,%r13,1),%rsi
    7d5c:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
                            ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    7d66:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    7d70:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    7d7a:	45 39 d3             	cmp    %r10d,%r11d
    7d7d:	0f 85 3d ff ff ff    	jne    7cc0 <barriered_work+0x200>
    7d83:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    7d88:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    7d8d:	b8 70 01 00 00       	mov    $0x170,%eax
    7d92:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    7d97:	44 8b 5c 24 38       	mov    0x38(%rsp),%r11d
    7d9c:	44 8b 74 24 3c       	mov    0x3c(%rsp),%r14d
    7da1:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    7da6:	48 8d 9a 70 01 00 00 	lea    0x170(%rdx),%rbx
    7dad:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    7db2:	eb 13                	jmp    7dc7 <barriered_work+0x307>
    7db4:	0f 1f 40 00          	nopl   0x0(%rax)
                        for (int nn = 0; nn < data->thread_count; nn++) {
    7db8:	48 05 00 02 00 00    	add    $0x200,%rax
    7dbe:	48 39 d8             	cmp    %rbx,%rax
    7dc1:	0f 84 29 fe ff ff    	je     7bf0 <barriered_work+0x130>
                          if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    7dc7:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    7dcb:	4d 8b 14 01          	mov    (%r9,%rax,1),%r10
    7dcf:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    7dd3:	4b 39 14 02          	cmp    %rdx,(%r10,%r8,1)
    7dd7:	75 df                	jne    7db8 <barriered_work+0x2f8>
    7dd9:	bf 01 00 00 00       	mov    $0x1,%edi
    7dde:	48 8d 35 69 14 00 00 	lea    0x1469(%rip),%rsi        # 924e <_IO_stdin_used+0x24e>
    7de5:	31 c0                	xor    %eax,%eax
    7de7:	e8 c4 a6 ff ff       	call   24b0 <__printf_chk@plt>
                            exit(1);
    7dec:	bf 01 00 00 00       	mov    $0x1,%edi
    7df1:	e8 2a a7 ff ff       	call   2520 <exit@plt>
    7df6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    7e00:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    7e07:	85 ed                	test   %ebp,%ebp
    7e09:	0f 85 59 fd ff ff    	jne    7b68 <barriered_work+0xa8>
    7e0f:	44 8b 90 f8 00 00 00 	mov    0xf8(%rax),%r10d
    7e16:	45 85 d2             	test   %r10d,%r10d
    7e19:	0f 85 49 fd ff ff    	jne    7b68 <barriered_work+0xa8>
    7e1f:	69 87 80 00 00 00 1d e6 cb 0b 	imul   $0xbcbe61d,0x80(%rdi),%eax
    7e29:	05 40 7c 0a 00       	add    $0xa7c40,%eax
    7e2e:	c1 c8 05             	ror    $0x5,%eax
    7e31:	3d c4 a7 00 00       	cmp    $0xa7c4,%eax
    7e36:	0f 87 2c fd ff ff    	ja     7b68 <barriered_work+0xa8>
      data->thread->global->request_group_sync = 0;
    7e3c:	48 c7 01 00 00 00 00 	movq   $0x0,(%rcx)
    7e43:	e9 20 fd ff ff       	jmp    7b68 <barriered_work+0xa8>
    7e48:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    7e50:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    7e55:	48 89 cb             	mov    %rcx,%rbx
        fswap(data); 
    7e58:	48 89 df             	mov    %rbx,%rdi
    7e5b:	e8 10 fb ff ff       	call   7970 <fswap>
        receive(data);
    7e60:	48 89 df             	mov    %rbx,%rdi
    7e63:	e8 88 f6 ff ff       	call   74f0 <receive>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    7e68:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    7e6f:	31 ff                	xor    %edi,%edi
    7e71:	48 c1 e6 05          	shl    $0x5,%rsi
    7e75:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    7e7c:	e8 cf a4 ff ff       	call   2350 <clock_gettime@plt>
      int modcount = ++data->thread->protected_state->modcount;
    7e81:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    7e88:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      int modcount = ++data->thread->protected_state->modcount;
    7e8f:	48 8b 50 48          	mov    0x48(%rax),%rdx
    7e93:	8b 4a 10             	mov    0x10(%rdx),%ecx
    7e96:	8d 69 01             	lea    0x1(%rcx),%ebp
    7e99:	89 6a 10             	mov    %ebp,0x10(%rdx)
      while (data->scheduled == 1) {
    7e9c:	75 50                	jne    7eee <barriered_work+0x42e>
    7e9e:	66 90                	xchg   %ax,%ax
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    7ea0:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    7ea7:	48 8b 40 18          	mov    0x18(%rax),%rax
    7eab:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
        data->n++;
    7eaf:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    7eb7:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7ebb:	48 c1 e7 09          	shl    $0x9,%rdi
    7ebf:	48 03 78 38          	add    0x38(%rax),%rdi
    7ec3:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      while (data->scheduled == 1) {
    7ec9:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      if (modcount != data->thread->protected_state->modcount) {
    7ed0:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    7ed7:	74 c7                	je     7ea0 <barriered_work+0x3e0>
      if (modcount != data->thread->protected_state->modcount) {
    7ed9:	48 8b 40 48          	mov    0x48(%rax),%rax
    7edd:	3b 68 10             	cmp    0x10(%rax),%ebp
    7ee0:	74 0c                	je     7eee <barriered_work+0x42e>
    7ee2:	48 8d 3d 80 13 00 00 	lea    0x1380(%rip),%rdi        # 9269 <_IO_stdin_used+0x269>
    7ee9:	e8 42 a4 ff ff       	call   2330 <puts@plt>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    7eee:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    7ef5:	31 ff                	xor    %edi,%edi
    7ef7:	48 c1 e6 05          	shl    $0x5,%rsi
    7efb:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    7f02:	48 83 c6 10          	add    $0x10,%rsi
    7f06:	e8 45 a4 ff ff       	call   2350 <clock_gettime@plt>
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    7f0b:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    7f12:	48 83 c0 01          	add    $0x1,%rax
    7f16:	48 99                	cqto
    7f18:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    if (t == data->thread_count - 1) {
    7f1f:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    7f25:	83 e8 01             	sub    $0x1,%eax
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    7f28:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    if (t == data->thread_count - 1) {
    7f2f:	44 39 e0             	cmp    %r12d,%eax
    7f32:	74 53                	je     7f87 <barriered_work+0x4c7>
    data->swap = 0;
    7f34:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    return 0;
    7f3e:	e9 d8 fb ff ff       	jmp    7b1b <barriered_work+0x5b>
    7f43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      receive(data);
    7f48:	e8 a3 f5 ff ff       	call   74f0 <receive>
      while (data->scheduled == 1) {
    7f4d:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    7f54:	75 1b                	jne    7f71 <barriered_work+0x4b1>
    7f56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        data->n++;
    7f60:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      while (data->scheduled == 1) {
    7f68:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    7f6f:	74 ef                	je     7f60 <barriered_work+0x4a0>
      sendm(data);
    7f71:	48 89 df             	mov    %rbx,%rdi
    7f74:	e8 c7 f6 ff ff       	call   7640 <sendm>
    if (t == data->thread_count - 1) {
    7f79:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    7f7f:	83 e8 01             	sub    $0x1,%eax
    7f82:	44 39 e0             	cmp    %r12d,%eax
    7f85:	75 ad                	jne    7f34 <barriered_work+0x474>
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    7f87:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    7f8e:	85 d2                	test   %edx,%edx
    7f90:	7e a2                	jle    7f34 <barriered_work+0x474>
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    7f92:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    7f99:	48 c1 e2 09          	shl    $0x9,%rdx
    7f9d:	48 63 41 08          	movslq 0x8(%rcx),%rax
    7fa1:	48 8d 34 c0          	lea    (%rax,%rax,8),%rsi
    7fa5:	48 8d 04 70          	lea    (%rax,%rsi,2),%rax
    7fa9:	48 c1 e0 04          	shl    $0x4,%rax
    7fad:	48 03 41 20          	add    0x20(%rcx),%rax
    7fb1:	48 8b 40 38          	mov    0x38(%rax),%rax
    7fb5:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    7fb9:	80 e6 02             	and    $0x2,%dh
    7fbc:	74 1a                	je     7fd8 <barriered_work+0x518>
    7fbe:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    7fc5:	48 05 00 02 00 00    	add    $0x200,%rax
    7fcb:	48 39 c8             	cmp    %rcx,%rax
    7fce:	0f 84 60 ff ff ff    	je     7f34 <barriered_work+0x474>
    7fd4:	0f 1f 40 00          	nopl   0x0(%rax)
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    7fd8:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    7fdf:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    7fe6:	48 05 00 04 00 00    	add    $0x400,%rax
    7fec:	48 39 c8             	cmp    %rcx,%rax
    7fef:	75 e7                	jne    7fd8 <barriered_work+0x518>
    7ff1:	e9 3e ff ff ff       	jmp    7f34 <barriered_work+0x474>
    7ff6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    8000:	39 c5                	cmp    %eax,%ebp
    8002:	0f 85 60 fb ff ff    	jne    7b68 <barriered_work+0xa8>
      struct ProtectedState *protected = data->thread->global->protected_state;
    8008:	48 8b 69 08          	mov    0x8(%rcx),%rbp
      nanosleep(&preempt , &rem);
    800c:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
    8011:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
      int modcount = ++protected->modcount;
    8016:	8b 45 10             	mov    0x10(%rbp),%eax
      protected->protected++;
    8019:	48 83 45 00 01       	addq   $0x1,0x0(%rbp)
      int modcount = ++protected->modcount;
    801e:	44 8d 60 01          	lea    0x1(%rax),%r12d
    8022:	44 89 65 10          	mov    %r12d,0x10(%rbp)
      nanosleep(&preempt , &rem);
    8026:	e8 75 a3 ff ff       	call   23a0 <nanosleep@plt>
      if (protected->modcount != modcount) {
    802b:	44 3b 65 10          	cmp    0x10(%rbp),%r12d
    802f:	74 0c                	je     803d <barriered_work+0x57d>
    8031:	48 8d 3d f9 11 00 00 	lea    0x11f9(%rip),%rdi        # 9231 <_IO_stdin_used+0x231>
    8038:	e8 f3 a2 ff ff       	call   2330 <puts@plt>
      data->thread->global->request_thread_sync = (data->thread_index + 1) % data->thread_count;
    803d:	48 63 ab 30 01 00 00 	movslq 0x130(%rbx),%rbp
    8044:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    804b:	8d 45 01             	lea    0x1(%rbp),%eax
    804e:	48 8b b1 00 01 00 00 	mov    0x100(%rcx),%rsi
    8055:	99                   	cltd
    8056:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    805c:	89 56 04             	mov    %edx,0x4(%rsi)
      if (data->thread_index == 1) {
    805f:	83 fd 01             	cmp    $0x1,%ebp
    8062:	0f 85 00 fb ff ff    	jne    7b68 <barriered_work+0xa8>
        data->thread->global->request_group_sync = (data->thread->group + 1) % data->thread->group_count;
    8068:	8b 81 f8 00 00 00    	mov    0xf8(%rcx),%eax
    806e:	83 c0 01             	add    $0x1,%eax
    8071:	99                   	cltd
    8072:	f7 b9 d0 00 00 00    	idivl  0xd0(%rcx)
    8078:	89 16                	mov    %edx,(%rsi)
    807a:	e9 e9 fa ff ff       	jmp    7b68 <barriered_work+0xa8>
}
    807f:	e8 fc a2 ff ff       	call   2380 <__stack_chk_fail@plt>
    8084:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    808f:	90                   	nop

0000000000008090 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    8090:	f3 0f 1e fa          	endbr64
    8094:	53                   	push   %rbx
    8095:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    8098:	e8 93 f0 ff ff       	call   7130 <barriered_work_ingest>
  barriered_work(data);
    809d:	48 89 df             	mov    %rbx,%rdi
}
    80a0:	5b                   	pop    %rbx
  barriered_work(data);
    80a1:	e9 1a fa ff ff       	jmp    7ac0 <barriered_work>
    80a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000080b0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    80b0:	f3 0f 1e fa          	endbr64
}
    80b4:	31 c0                	xor    %eax,%eax
    80b6:	c3                   	ret
    80b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000080c0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    80c0:	f3 0f 1e fa          	endbr64
    80c4:	31 c0                	xor    %eax,%eax
    80c6:	c3                   	ret
    80c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000080d0 <after>:
int after(struct timespec left, struct timespec right) {
    80d0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    80d4:	31 c0                	xor    %eax,%eax
    80d6:	48 39 d7             	cmp    %rdx,%rdi
    80d9:	7e 08                	jle    80e3 <after+0x13>
    80db:	31 c0                	xor    %eax,%eax
    80dd:	48 39 ce             	cmp    %rcx,%rsi
    80e0:	0f 9f c0             	setg   %al
}
    80e3:	c3                   	ret
    80e4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    80ef:	90                   	nop

00000000000080f0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    80f0:	f3 0f 1e fa          	endbr64
    80f4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    80f9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    80fe:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8100:	48 39 d7             	cmp    %rdx,%rdi
    8103:	7f 18                	jg     811d <within+0x2d>
    8105:	4d 39 d8             	cmp    %r11,%r8
    8108:	0f 9e c2             	setle  %dl
    810b:	48 39 ce             	cmp    %rcx,%rsi
    810e:	0f 9e c0             	setle  %al
    8111:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8113:	31 c0                	xor    %eax,%eax
    8115:	4d 39 d1             	cmp    %r10,%r9
    8118:	0f 9e c0             	setle  %al
    811b:	21 d0                	and    %edx,%eax
}
    811d:	c3                   	ret
    811e:	66 90                	xchg   %ax,%ax

0000000000008120 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    8120:	f3 0f 1e fa          	endbr64
    8124:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    8129:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    812e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    8133:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    8138:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    813d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    8142:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    8147:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    814c:	48 39 fe             	cmp    %rdi,%rsi
    814f:	7d 2f                	jge    8180 <overlap+0x60>
    8151:	48 39 ca             	cmp    %rcx,%rdx
    8154:	7d 62                	jge    81b8 <overlap+0x98>
    8156:	4d 39 da             	cmp    %r11,%r10
    8159:	7d 0e                	jge    8169 <overlap+0x49>
    return 1;
    815b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    8160:	4d 39 c1             	cmp    %r8,%r9
    8163:	0f 8c 7f 00 00 00    	jl     81e8 <overlap+0xc8>
  return 0;
    8169:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    816b:	4d 39 c1             	cmp    %r8,%r9
    816e:	7f 4c                	jg     81bc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8170:	31 c0                	xor    %eax,%eax
    8172:	4d 39 da             	cmp    %r11,%r10
    8175:	0f 9e c0             	setle  %al
    8178:	c3                   	ret
    8179:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    8180:	7e 4e                	jle    81d0 <overlap+0xb0>
    8182:	48 39 ca             	cmp    %rcx,%rdx
    8185:	7f 39                	jg     81c0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8187:	75 31                	jne    81ba <overlap+0x9a>
    8189:	4d 39 c1             	cmp    %r8,%r9
    818c:	7c 2c                	jl     81ba <overlap+0x9a>
    return 1;
    818e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8193:	4d 39 da             	cmp    %r11,%r10
    8196:	7d 24                	jge    81bc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8198:	48 39 ca             	cmp    %rcx,%rdx
    819b:	0f 94 c2             	sete   %dl
    819e:	48 39 fe             	cmp    %rdi,%rsi
    81a1:	0f 94 c0             	sete   %al
    81a4:	21 c2                	and    %eax,%edx
    81a6:	31 c0                	xor    %eax,%eax
    81a8:	4d 39 c1             	cmp    %r8,%r9
    81ab:	0f 94 c0             	sete   %al
    81ae:	21 d0                	and    %edx,%eax
    81b0:	c3                   	ret
    81b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    81b8:	74 af                	je     8169 <overlap+0x49>
  return 0;
    81ba:	31 c0                	xor    %eax,%eax
}
    81bc:	c3                   	ret
    81bd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    81c0:	4d 39 da             	cmp    %r11,%r10
    81c3:	7e c4                	jle    8189 <overlap+0x69>
    return 1;
    81c5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    81ca:	4d 39 c1             	cmp    %r8,%r9
    81cd:	7e ba                	jle    8189 <overlap+0x69>
    81cf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    81d0:	48 39 ca             	cmp    %rcx,%rdx
    81d3:	7c 94                	jl     8169 <overlap+0x49>
    81d5:	4d 39 c1             	cmp    %r8,%r9
    81d8:	7d b4                	jge    818e <overlap+0x6e>
    81da:	48 39 ca             	cmp    %rcx,%rdx
    81dd:	74 91                	je     8170 <overlap+0x50>
    81df:	eb d9                	jmp    81ba <overlap+0x9a>
    81e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    81e8:	c3                   	ret
    81e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000081f0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    81f0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    81f4:	85 f6                	test   %esi,%esi
    81f6:	0f 8e 44 03 00 00    	jle    8540 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    81fc:	41 57                	push   %r15
    81fe:	41 89 f7             	mov    %esi,%r15d
    8201:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    8203:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    8206:	41 55                	push   %r13
    8208:	41 54                	push   %r12
    820a:	55                   	push   %rbp
    820b:	53                   	push   %rbx
    820c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    8210:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    8214:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    8219:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    821e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    8221:	45 39 e6             	cmp    %r12d,%r14d
    8224:	0f 84 4e 02 00 00    	je     8478 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    822a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    822f:	8b 50 08             	mov    0x8(%rax),%edx
    8232:	85 d2                	test   %edx,%edx
    8234:	0f 8e 3e 02 00 00    	jle    8478 <verify+0x288>
    823a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    823f:	31 c9                	xor    %ecx,%ecx
    8241:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    8246:	31 c0                	xor    %eax,%eax
    8248:	44 89 f2             	mov    %r14d,%edx
    824b:	bf 01 00 00 00       	mov    $0x1,%edi
    8250:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    8255:	48 8d 35 1d 10 00 00 	lea    0x101d(%rip),%rsi        # 9279 <_IO_stdin_used+0x279>
    825c:	e8 4f a2 ff ff       	call   24b0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    8261:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    8266:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    826b:	8b 40 08             	mov    0x8(%rax),%eax
    826e:	85 c0                	test   %eax,%eax
    8270:	0f 8e e6 01 00 00    	jle    845c <verify+0x26c>
    8276:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    8279:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    827e:	31 db                	xor    %ebx,%ebx
    8280:	48 c1 e0 09          	shl    $0x9,%rax
    8284:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    8289:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    828e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8293:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    8298:	4c 8b 20             	mov    (%rax),%r12
    829b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    82a0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    82a5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    82aa:	49 89 de             	mov    %rbx,%r14
    82ad:	48 8d 35 da 0f 00 00 	lea    0xfda(%rip),%rsi        # 928e <_IO_stdin_used+0x28e>
    82b4:	49 c1 e6 09          	shl    $0x9,%r14
    82b8:	bf 01 00 00 00       	mov    $0x1,%edi
    82bd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    82c1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    82c9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    82ce:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    82d6:	31 c0                	xor    %eax,%eax
    82d8:	e8 d3 a1 ff ff       	call   24b0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    82dd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    82e2:	4c 8b 20             	mov    (%rax),%r12
    82e5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    82ee:	0f 8e 47 01 00 00    	jle    843b <verify+0x24b>
    82f4:	4c 03 75 00          	add    0x0(%rbp),%r14
    82f8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    82fd:	ba 01 00 00 00       	mov    $0x1,%edx
    8302:	4d 89 f5             	mov    %r14,%r13
    8305:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    830c:	4d 85 f6             	test   %r14,%r14
    830f:	0f 8e 21 01 00 00    	jle    8436 <verify+0x246>
    8315:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    8318:	48 89 d5             	mov    %rdx,%rbp
    831b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8320:	31 db                	xor    %ebx,%ebx
    8322:	4d 89 f2             	mov    %r14,%r10
    8325:	48 c1 e5 05          	shl    $0x5,%rbp
    8329:	48 83 ed 20          	sub    $0x20,%rbp
    832d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    8331:	49 89 ee             	mov    %rbp,%r14
    8334:	48 89 dd             	mov    %rbx,%rbp
    8337:	48 89 d3             	mov    %rdx,%rbx
    833a:	eb 31                	jmp    836d <verify+0x17d>
    833c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    8340:	4c 39 c2             	cmp    %r8,%rdx
    8343:	0f 8d 57 01 00 00    	jge    84a0 <verify+0x2b0>
    8349:	4c 39 df             	cmp    %r11,%rdi
    834c:	7e 05                	jle    8353 <verify+0x163>
    834e:	49 39 c1             	cmp    %rax,%r9
    8351:	7c 75                	jl     83c8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8353:	4c 39 df             	cmp    %r11,%rdi
    8356:	0f 8d ab 01 00 00    	jge    8507 <verify+0x317>
    835c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8360:	48 83 c5 01          	add    $0x1,%rbp
    8364:	49 39 ea             	cmp    %rbp,%r10
    8367:	0f 8e a9 00 00 00    	jle    8416 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    836d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    8374:	48 89 e8             	mov    %rbp,%rax
    8377:	48 c1 e0 05          	shl    $0x5,%rax
    837b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    8382:	4c 01 f2             	add    %r14,%rdx
    8385:	48 8b 08             	mov    (%rax),%rcx
    8388:	48 8b 78 10          	mov    0x10(%rax),%rdi
    838c:	48 8b 32             	mov    (%rdx),%rsi
    838f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    8393:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    8397:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    839b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    839f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    83a3:	48 39 f1             	cmp    %rsi,%rcx
    83a6:	7c 98                	jl     8340 <verify+0x150>
    83a8:	0f 8e 42 01 00 00    	jle    84f0 <verify+0x300>
    83ae:	4c 39 c2             	cmp    %r8,%rdx
    83b1:	0f 8f f9 00 00 00    	jg     84b0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    83b7:	75 a7                	jne    8360 <verify+0x170>
    83b9:	4c 39 df             	cmp    %r11,%rdi
    83bc:	7f a2                	jg     8360 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    83be:	49 39 c1             	cmp    %rax,%r9
    83c1:	7c 9d                	jl     8360 <verify+0x170>
    83c3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    83c8:	49 89 c1             	mov    %rax,%r9
    83cb:	48 89 f9             	mov    %rdi,%rcx
    83ce:	48 89 f2             	mov    %rsi,%rdx
    83d1:	bf 01 00 00 00       	mov    $0x1,%edi
    83d6:	48 8d 35 5b 14 00 00 	lea    0x145b(%rip),%rsi        # 9838 <_IO_stdin_used+0x838>
    83dd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    83df:	48 83 c5 01          	add    $0x1,%rbp
    83e3:	e8 c8 a0 ff ff       	call   24b0 <__printf_chk@plt>
    83e8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    83ed:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    83f2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    83f5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    83fa:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8401:	4c 8b 20             	mov    (%rax),%r12
    8404:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8409:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    840d:	49 39 ea             	cmp    %rbp,%r10
    8410:	0f 8f 57 ff ff ff    	jg     836d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8416:	48 89 da             	mov    %rbx,%rdx
    8419:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    8420:	7d 14                	jge    8436 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8422:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    8429:	48 83 c2 01          	add    $0x1,%rdx
    842d:	4d 85 f6             	test   %r14,%r14
    8430:	0f 8f e2 fe ff ff    	jg     8318 <verify+0x128>
    8436:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    843b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    8440:	48 83 c3 01          	add    $0x1,%rbx
    8444:	39 58 08             	cmp    %ebx,0x8(%rax)
    8447:	0f 8f 53 fe ff ff    	jg     82a0 <verify+0xb0>
    844d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    8452:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    8457:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    845c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8461:	48 83 c1 01          	add    $0x1,%rcx
    8465:	39 48 08             	cmp    %ecx,0x8(%rax)
    8468:	0f 8f d8 fd ff ff    	jg     8246 <verify+0x56>
    846e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    8473:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    8478:	48 81 44 24 10 30 01 00 00 	addq   $0x130,0x10(%rsp)
    8481:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    8486:	41 39 c7             	cmp    %eax,%r15d
    8489:	0f 84 86 00 00 00    	je     8515 <verify+0x325>
    848f:	41 89 c4             	mov    %eax,%r12d
    8492:	e9 8a fd ff ff       	jmp    8221 <verify+0x31>
    8497:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    84a0:	0f 85 ba fe ff ff    	jne    8360 <verify+0x170>
    84a6:	e9 a8 fe ff ff       	jmp    8353 <verify+0x163>
    84ab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    84b0:	49 39 c1             	cmp    %rax,%r9
    84b3:	7e 09                	jle    84be <verify+0x2ce>
    84b5:	4c 39 df             	cmp    %r11,%rdi
    84b8:	0f 8c 0a ff ff ff    	jl     83c8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    84be:	4c 39 df             	cmp    %r11,%rdi
    84c1:	0f 8f 99 fe ff ff    	jg     8360 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    84c7:	49 39 c1             	cmp    %rax,%r9
    84ca:	0f 8d f8 fe ff ff    	jge    83c8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    84d0:	48 39 f1             	cmp    %rsi,%rcx
    84d3:	0f 85 87 fe ff ff    	jne    8360 <verify+0x170>
    84d9:	4c 39 c2             	cmp    %r8,%rdx
    84dc:	0f 85 7e fe ff ff    	jne    8360 <verify+0x170>
    84e2:	4c 39 df             	cmp    %r11,%rdi
    84e5:	0f 84 dd fe ff ff    	je     83c8 <verify+0x1d8>
    84eb:	e9 70 fe ff ff       	jmp    8360 <verify+0x170>
    84f0:	4c 39 c2             	cmp    %r8,%rdx
    84f3:	0f 8c 5a fe ff ff    	jl     8353 <verify+0x163>
    84f9:	4c 39 df             	cmp    %r11,%rdi
    84fc:	7e c9                	jle    84c7 <verify+0x2d7>
    84fe:	4c 39 c2             	cmp    %r8,%rdx
    8501:	0f 85 59 fe ff ff    	jne    8360 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8507:	49 39 c1             	cmp    %rax,%r9
    850a:	0f 8f 50 fe ff ff    	jg     8360 <verify+0x170>
    8510:	e9 b3 fe ff ff       	jmp    83c8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    8515:	48 81 44 24 18 30 01 00 00 	addq   $0x130,0x18(%rsp)
    851e:	41 8d 46 01          	lea    0x1(%r14),%eax
    8522:	45 39 e6             	cmp    %r12d,%r14d
    8525:	74 08                	je     852f <verify+0x33f>
    8527:	41 89 c6             	mov    %eax,%r14d
    852a:	e9 ea fc ff ff       	jmp    8219 <verify+0x29>
}
    852f:	48 83 c4 58          	add    $0x58,%rsp
    8533:	31 c0                	xor    %eax,%eax
    8535:	5b                   	pop    %rbx
    8536:	5d                   	pop    %rbp
    8537:	41 5c                	pop    %r12
    8539:	41 5d                	pop    %r13
    853b:	41 5e                	pop    %r14
    853d:	41 5f                	pop    %r15
    853f:	c3                   	ret
    8540:	31 c0                	xor    %eax,%eax
    8542:	c3                   	ret

Disassembly of section .fini:

0000000000008544 <_fini>:
    8544:	f3 0f 1e fa          	endbr64
    8548:	48 83 ec 08          	sub    $0x8,%rsp
    854c:	48 83 c4 08          	add    $0x8,%rsp
    8550:	c3                   	ret
