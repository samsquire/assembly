
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
    2020:	ff 35 32 9e 00 00    	push   0x9e32(%rip)        # be58 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 34 9e 00 00    	jmp    *0x9e34(%rip)        # be60 <_GLOBAL_OFFSET_TABLE_+0x10>
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

Disassembly of section .plt.got:

0000000000002310 <__cxa_finalize@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 de 9c 00 00    	jmp    *0x9cde(%rip)        # bff8 <__cxa_finalize@GLIBC_2.2.5>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000002320 <free@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 3e 9b 00 00    	jmp    *0x9b3e(%rip)        # be68 <free@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <putchar@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 36 9b 00 00    	jmp    *0x9b36(%rip)        # be70 <putchar@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <pthread_setaffinity_np@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 2e 9b 00 00    	jmp    *0x9b2e(%rip)        # be78 <pthread_setaffinity_np@GLIBC_2.34>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <puts@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 26 9b 00 00    	jmp    *0x9b26(%rip)        # be80 <puts@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <setsockopt@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 1e 9b 00 00    	jmp    *0x9b1e(%rip)        # be88 <setsockopt@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <clock_gettime@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 16 9b 00 00    	jmp    *0x9b16(%rip)        # be90 <clock_gettime@GLIBC_2.17>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <fclose@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 0e 9b 00 00    	jmp    *0x9b0e(%rip)        # be98 <fclose@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <strlen@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 06 9b 00 00    	jmp    *0x9b06(%rip)        # bea0 <strlen@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <__stack_chk_fail@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 fe 9a 00 00    	jmp    *0x9afe(%rip)        # bea8 <__stack_chk_fail@GLIBC_2.4>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <io_uring_submit@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 f6 9a 00 00    	jmp    *0x9af6(%rip)        # beb0 <io_uring_submit@LIBURING_2.0>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <nanosleep@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 ee 9a 00 00    	jmp    *0x9aee(%rip)        # beb8 <nanosleep@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <strrchr@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 e6 9a 00 00    	jmp    *0x9ae6(%rip)        # bec0 <strrchr@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <fputs@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 de 9a 00 00    	jmp    *0x9ade(%rip)        # bec8 <fputs@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <close@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 d6 9a 00 00    	jmp    *0x9ad6(%rip)        # bed0 <close@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <strtok_r@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 ce 9a 00 00    	jmp    *0x9ace(%rip)        # bed8 <strtok_r@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <read@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 c6 9a 00 00    	jmp    *0x9ac6(%rip)        # bee0 <read@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <calloc@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 be 9a 00 00    	jmp    *0x9abe(%rip)        # bee8 <calloc@GLIBC_2.2.5>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <strcmp@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 b6 9a 00 00    	jmp    *0x9ab6(%rip)        # bef0 <strcmp@GLIBC_2.2.5>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <__memcpy_chk@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 ae 9a 00 00    	jmp    *0x9aae(%rip)        # bef8 <__memcpy_chk@GLIBC_2.3.4>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <stat@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 a6 9a 00 00    	jmp    *0x9aa6(%rip)        # bf00 <stat@GLIBC_2.33>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <memcpy@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 9e 9a 00 00    	jmp    *0x9a9e(%rip)        # bf08 <memcpy@GLIBC_2.14>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <io_uring_queue_init@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 96 9a 00 00    	jmp    *0x9a96(%rip)        # bf10 <io_uring_queue_init@LIBURING_2.0>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <eventfd_write@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 8e 9a 00 00    	jmp    *0x9a8e(%rip)        # bf18 <eventfd_write@GLIBC_2.7>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <malloc@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 86 9a 00 00    	jmp    *0x9a86(%rip)        # bf20 <malloc@GLIBC_2.2.5>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <listen@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 7e 9a 00 00    	jmp    *0x9a7e(%rip)        # bf28 <listen@GLIBC_2.2.5>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <__strcpy_chk@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 76 9a 00 00    	jmp    *0x9a76(%rip)        # bf30 <__strcpy_chk@GLIBC_2.3.4>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <__io_uring_get_cqe@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 6e 9a 00 00    	jmp    *0x9a6e(%rip)        # bf38 <__io_uring_get_cqe@LIBURING_2.0>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <__printf_chk@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 66 9a 00 00    	jmp    *0x9a66(%rip)        # bf40 <__printf_chk@GLIBC_2.3.4>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <bind@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 5e 9a 00 00    	jmp    *0x9a5e(%rip)        # bf48 <bind@GLIBC_2.2.5>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <pthread_create@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 56 9a 00 00    	jmp    *0x9a56(%rip)        # bf50 <pthread_create@GLIBC_2.34>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <io_uring_wait_cqe_timeout@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 4e 9a 00 00    	jmp    *0x9a4e(%rip)        # bf58 <io_uring_wait_cqe_timeout@LIBURING_2.0>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <open@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 46 9a 00 00    	jmp    *0x9a46(%rip)        # bf60 <open@GLIBC_2.2.5>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <fopen@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 3e 9a 00 00    	jmp    *0x9a3e(%rip)        # bf68 <fopen@GLIBC_2.2.5>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <perror@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 36 9a 00 00    	jmp    *0x9a36(%rip)        # bf70 <perror@GLIBC_2.2.5>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <exit@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 2e 9a 00 00    	jmp    *0x9a2e(%rip)        # bf78 <exit@GLIBC_2.2.5>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <eventfd@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 26 9a 00 00    	jmp    *0x9a26(%rip)        # bf80 <eventfd@GLIBC_2.7>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <fwrite@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 1e 9a 00 00    	jmp    *0x9a1e(%rip)        # bf88 <fwrite@GLIBC_2.2.5>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <__fprintf_chk@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 16 9a 00 00    	jmp    *0x9a16(%rip)        # bf90 <__fprintf_chk@GLIBC_2.3.4>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <io_uring_register_eventfd@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 0e 9a 00 00    	jmp    *0x9a0e(%rip)        # bf98 <io_uring_register_eventfd@LIBURING_2.0>
    258a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002590 <pthread_join@plt>:
    2590:	f3 0f 1e fa          	endbr64
    2594:	ff 25 06 9a 00 00    	jmp    *0x9a06(%rip)        # bfa0 <pthread_join@GLIBC_2.34>
    259a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025a0 <strerror@plt>:
    25a0:	f3 0f 1e fa          	endbr64
    25a4:	ff 25 fe 99 00 00    	jmp    *0x99fe(%rip)        # bfa8 <strerror@GLIBC_2.2.5>
    25aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025b0 <pthread_mutex_init@plt>:
    25b0:	f3 0f 1e fa          	endbr64
    25b4:	ff 25 f6 99 00 00    	jmp    *0x99f6(%rip)        # bfb0 <pthread_mutex_init@GLIBC_2.2.5>
    25ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025c0 <epoll_create1@plt>:
    25c0:	f3 0f 1e fa          	endbr64
    25c4:	ff 25 ee 99 00 00    	jmp    *0x99ee(%rip)        # bfb8 <epoll_create1@GLIBC_2.9>
    25ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025d0 <__ctype_tolower_loc@plt>:
    25d0:	f3 0f 1e fa          	endbr64
    25d4:	ff 25 e6 99 00 00    	jmp    *0x99e6(%rip)        # bfc0 <__ctype_tolower_loc@GLIBC_2.3>
    25da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025e0 <__sprintf_chk@plt>:
    25e0:	f3 0f 1e fa          	endbr64
    25e4:	ff 25 de 99 00 00    	jmp    *0x99de(%rip)        # bfc8 <__sprintf_chk@GLIBC_2.3.4>
    25ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025f0 <socket@plt>:
    25f0:	f3 0f 1e fa          	endbr64
    25f4:	ff 25 d6 99 00 00    	jmp    *0x99d6(%rip)        # bfd0 <socket@GLIBC_2.2.5>
    25fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000002600 <fatal_error>:
  return a;
}

int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send);
int buffersend_filter(struct KernelThread *data, struct Buffers *buffers, int kind, void * send, int filter);
void fatal_error(const char *syscall) {
    2600:	f3 0f 1e fa          	endbr64
    2604:	50                   	push   %rax
    2605:	58                   	pop    %rax
    2606:	50                   	push   %rax
    perror(syscall);
    2607:	e8 24 ff ff ff       	call   2530 <perror@plt>
    exit(1);
    260c:	bf 01 00 00 00       	mov    $0x1,%edi
    2611:	e8 2a ff ff ff       	call   2540 <exit@plt>

0000000000002616 <copy_file_contents.cold>:
    int fd;

    char *buf = zh_malloc(file_size);
    fd = open(file_path, O_RDONLY);
    if (fd < 0)
        fatal_error("read");
    2616:	48 8d 3d 0f 6c 00 00 	lea    0x6c0f(%rip),%rdi        # 922c <_IO_stdin_used+0x22c>
    261d:	e8 de ff ff ff       	call   2600 <fatal_error>

0000000000002622 <add_read_request.cold>:

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    2622:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    262a:	0f 0b                	ud2

000000000000262c <add_accept_request.cold>:
    262c:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2634:	0f 0b                	ud2

0000000000002636 <io_thread.cold>:

    sock = socket(PF_INET, SOCK_STREAM, 0);


    if (sock == -1)
        fatal_error("socket()");
    2636:	48 8d 3d 14 6b 00 00 	lea    0x6b14(%rip),%rdi        # 9151 <_IO_stdin_used+0x151>
    263d:	e8 be ff ff ff       	call   2600 <fatal_error>

    int enable = 1;
    if (setsockopt(sock,
                   SOL_SOCKET, SO_REUSEADDR,
                   &enable, sizeof(int)) < 0)
        fatal_error("setsockopt(SO_REUSEADDR)");
    2642:	48 8d 3d 11 6b 00 00 	lea    0x6b11(%rip),%rdi        # 915a <_IO_stdin_used+0x15a>
    2649:	e8 b2 ff ff ff       	call   2600 <fatal_error>
    srv_addr.sin_addr.s_addr = htonl(INADDR_ANY);

    if (bind(sock,
             (const struct sockaddr *)&srv_addr,
             sizeof(srv_addr)) < 0)
        fatal_error("bind()");
    264e:	48 8d 3d 1e 6b 00 00 	lea    0x6b1e(%rip),%rdi        # 9173 <_IO_stdin_used+0x173>
    2655:	e8 a6 ff ff ff       	call   2600 <fatal_error>
    265a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2662:	0f 0b                	ud2
            int client_socket = write->client_socket; 
            // printf("%p write\n", write);
            struct io_uring_sqe *sqe = io_uring_get_sqe(&ring);
            struct Request *req = write->request;
            // printf("req %p\n", req);
            req->event_type = EVENT_TYPE_WRITE;
    2664:	41 c7 06 02 00 00 00 	movl   $0x2,(%r14)
    266b:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2673:	0f 0b                	ud2
      fatal_error("listen()");
    2675:	48 8d 3d fe 6a 00 00 	lea    0x6afe(%rip),%rdi        # 917a <_IO_stdin_used+0x17a>
    267c:	e8 7f ff ff ff       	call   2600 <fatal_error>
            fatal_error("io_uring_wait_cqe");
    2681:	48 8d 3d 0f 6b 00 00 	lea    0x6b0f(%rip),%rdi        # 9197 <_IO_stdin_used+0x197>
    2688:	e8 73 ff ff ff       	call   2600 <fatal_error>
    268d:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2695:	0f 0b                	ud2
    int new_client_socket = newclient_message->socket;
    2697:	8b 04 25 00 00 00 00 	mov    0x0,%eax
    269e:	0f 0b                	ud2
    26a0:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26a8:	0f 0b                	ud2
    26aa:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26b2:	0f 0b                	ud2
				   perror("new client epoll_create1");
    26b4:	48 8d 3d fe 6a 00 00 	lea    0x6afe(%rip),%rdi        # 91b9 <_IO_stdin_used+0x1b9>
    26bb:	e8 70 fe ff ff       	call   2530 <perror@plt>
				   exit(EXIT_FAILURE);
    26c0:	bf 01 00 00 00       	mov    $0x1,%edi
    26c5:	e8 76 fe ff ff       	call   2540 <exit@plt>
    struct NewSocketMessage *msg = bufferreply->data;
    26ca:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    26d2:	0f 0b                	ud2
    26d4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26dc:	0f 0b                	ud2
    26de:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26e6:	0f 0b                	ud2
    26e8:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26f0:	0f 0b                	ud2
    26f2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    26fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000002700 <main>:
    }


  return 0;
}
int main() {
    2700:	f3 0f 1e fa          	endbr64
    2704:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    2706:	48 8d 3d 53 71 00 00 	lea    0x7153(%rip),%rdi        # 9860 <_IO_stdin_used+0x860>
    270d:	41 56                	push   %r14
    270f:	41 55                	push   %r13
    2711:	4c 8d 2d 87 6c 00 00 	lea    0x6c87(%rip),%r13        # 939f <_IO_stdin_used+0x39f>
    2718:	41 54                	push   %r12
    271a:	55                   	push   %rbp
    271b:	53                   	push   %rbx
    271c:	48 81 ec c8 00 00 00 	sub    $0xc8,%rsp
    2723:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    272c:	48 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%rsp)
    2734:	48 8d 05 f5 1b 00 00 	lea    0x1bf5(%rip),%rax        # 4330 <barriered_reset>
    273b:	66 48 0f 6e e8       	movq   %rax,%xmm5
    2740:	0f 16 2d 01 95 00 00 	movhps 0x9501(%rip),%xmm5        # bc48 <__do_global_dtors_aux_fini_array_entry+0x8>
    2747:	0f 29 6c 24 70       	movaps %xmm5,0x70(%rsp)
    274c:	e8 ff fb ff ff       	call   2350 <puts@plt>
    2751:	bf 0a 00 00 00       	mov    $0xa,%edi
    2756:	e8 d5 fb ff ff       	call   2330 <putchar@plt>
    275b:	ba 01 00 00 00       	mov    $0x1,%edx
    2760:	48 8d 35 30 6b 00 00 	lea    0x6b30(%rip),%rsi        # 9297 <_IO_stdin_used+0x297>
    2767:	31 c0                	xor    %eax,%eax
    2769:	bf 01 00 00 00       	mov    $0x1,%edi
    276e:	e8 5d fd ff ff       	call   24d0 <__printf_chk@plt>
    2773:	ba 02 00 00 00       	mov    $0x2,%edx
    2778:	48 8d 35 28 6b 00 00 	lea    0x6b28(%rip),%rsi        # 92a7 <_IO_stdin_used+0x2a7>
    277f:	31 c0                	xor    %eax,%eax
    2781:	bf 01 00 00 00       	mov    $0x1,%edi
    2786:	e8 45 fd ff ff       	call   24d0 <__printf_chk@plt>
    278b:	ba 01 00 00 00       	mov    $0x1,%edx
    2790:	48 8d 35 25 6b 00 00 	lea    0x6b25(%rip),%rsi        # 92bc <_IO_stdin_used+0x2bc>
    2797:	31 c0                	xor    %eax,%eax
    2799:	bf 01 00 00 00       	mov    $0x1,%edi
    279e:	e8 2d fd ff ff       	call   24d0 <__printf_chk@plt>
    27a3:	ba 02 00 00 00       	mov    $0x2,%edx
    27a8:	48 8d 35 1d 6b 00 00 	lea    0x6b1d(%rip),%rsi        # 92cc <_IO_stdin_used+0x2cc>
    27af:	31 c0                	xor    %eax,%eax
    27b1:	bf 01 00 00 00       	mov    $0x1,%edi
    27b6:	e8 15 fd ff ff       	call   24d0 <__printf_chk@plt>
    27bb:	48 8d 3d 20 6b 00 00 	lea    0x6b20(%rip),%rdi        # 92e2 <_IO_stdin_used+0x2e2>
    27c2:	e8 89 fb ff ff       	call   2350 <puts@plt>
    27c7:	ba 02 00 00 00       	mov    $0x2,%edx
    27cc:	48 8d 35 2b 6b 00 00 	lea    0x6b2b(%rip),%rsi        # 92fe <_IO_stdin_used+0x2fe>
    27d3:	31 c0                	xor    %eax,%eax
    27d5:	bf 01 00 00 00       	mov    $0x1,%edi
    27da:	e8 f1 fc ff ff       	call   24d0 <__printf_chk@plt>
    27df:	ba 07 00 00 00       	mov    $0x7,%edx
    27e4:	48 8d 35 2d 6b 00 00 	lea    0x6b2d(%rip),%rsi        # 9318 <_IO_stdin_used+0x318>
    27eb:	31 c0                	xor    %eax,%eax
    27ed:	bf 01 00 00 00       	mov    $0x1,%edi
    27f2:	e8 d9 fc ff ff       	call   24d0 <__printf_chk@plt>
    27f7:	ba 02 00 00 00       	mov    $0x2,%edx
    27fc:	48 8d 35 29 6b 00 00 	lea    0x6b29(%rip),%rsi        # 932c <_IO_stdin_used+0x32c>
    2803:	31 c0                	xor    %eax,%eax
    2805:	bf 01 00 00 00       	mov    $0x1,%edi
    280a:	e8 c1 fc ff ff       	call   24d0 <__printf_chk@plt>
    280f:	ba 01 00 00 00       	mov    $0x1,%edx
    2814:	48 8d 35 22 6b 00 00 	lea    0x6b22(%rip),%rsi        # 933d <_IO_stdin_used+0x33d>
    281b:	31 c0                	xor    %eax,%eax
    281d:	bf 01 00 00 00       	mov    $0x1,%edi
    2822:	e8 a9 fc ff ff       	call   24d0 <__printf_chk@plt>
    2827:	ba 02 00 00 00       	mov    $0x2,%edx
    282c:	48 8d 35 22 6b 00 00 	lea    0x6b22(%rip),%rsi        # 9355 <_IO_stdin_used+0x355>
    2833:	31 c0                	xor    %eax,%eax
    2835:	bf 01 00 00 00       	mov    $0x1,%edi
    283a:	e8 91 fc ff ff       	call   24d0 <__printf_chk@plt>
    283f:	ba 01 00 00 00       	mov    $0x1,%edx
    2844:	48 8d 35 7d 70 00 00 	lea    0x707d(%rip),%rsi        # 98c8 <_IO_stdin_used+0x8c8>
    284b:	31 c0                	xor    %eax,%eax
    284d:	bf 01 00 00 00       	mov    $0x1,%edi
    2852:	e8 79 fc ff ff       	call   24d0 <__printf_chk@plt>
    2857:	ba 01 00 00 00       	mov    $0x1,%edx
    285c:	48 8d 35 95 70 00 00 	lea    0x7095(%rip),%rsi        # 98f8 <_IO_stdin_used+0x8f8>
    2863:	31 c0                	xor    %eax,%eax
    2865:	bf 01 00 00 00       	mov    $0x1,%edi
    286a:	e8 61 fc ff ff       	call   24d0 <__printf_chk@plt>
    286f:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2874:	48 8d 35 f6 6a 00 00 	lea    0x6af6(%rip),%rsi        # 9371 <_IO_stdin_used+0x371>
    287b:	31 c0                	xor    %eax,%eax
    287d:	bf 01 00 00 00       	mov    $0x1,%edi
    2882:	e8 49 fc ff ff       	call   24d0 <__printf_chk@plt>
    2887:	ba 10 27 00 00       	mov    $0x2710,%edx
    288c:	48 8d 35 f8 6a 00 00 	lea    0x6af8(%rip),%rsi        # 938b <_IO_stdin_used+0x38b>
    2893:	31 c0                	xor    %eax,%eax
    2895:	bf 01 00 00 00       	mov    $0x1,%edi
    289a:	e8 31 fc ff ff       	call   24d0 <__printf_chk@plt>
    289f:	48 8d 3d 4f 68 00 00 	lea    0x684f(%rip),%rdi        # 90f5 <_IO_stdin_used+0xf5>
    28a6:	e8 a5 fa ff ff       	call   2350 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
    28ab:	be 18 00 00 00       	mov    $0x18,%esi
    28b0:	bf 01 00 00 00       	mov    $0x1,%edi
    28b5:	e8 66 fb ff ff       	call   2420 <calloc@plt>
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    28ba:	be 18 00 00 00       	mov    $0x18,%esi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
    28bf:	45 31 e4             	xor    %r12d,%r12d
  int cc = 0; 
    28c2:	45 31 ff             	xor    %r15d,%r15d
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    28c5:	bf 01 00 00 00       	mov    $0x1,%edi
  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
    28ca:	49 89 c6             	mov    %rax,%r14
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    28cd:	e8 4e fb ff ff       	call   2420 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28d2:	be 30 01 00 00       	mov    $0x130,%esi
    28d7:	bf 07 00 00 00       	mov    $0x7,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    28dc:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28e1:	e8 3a fb ff ff       	call   2420 <calloc@plt>
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28e6:	be 28 00 00 00       	mov    $0x28,%esi
    28eb:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28f0:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28f5:	e8 26 fb ff ff       	call   2420 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28fa:	be 28 00 00 00       	mov    $0x28,%esi
    28ff:	bf 31 00 00 00       	mov    $0x31,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    2904:	48 89 84 24 88 00 00 00 	mov    %rax,0x88(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    290c:	e8 0f fb ff ff       	call   2420 <calloc@plt>
    2911:	4c 89 34 24          	mov    %r14,(%rsp)
    2915:	48 89 84 24 90 00 00 00 	mov    %rax,0x90(%rsp)
  for (int x = 0 ; x < total_threads; x++) {
    291d:	49 89 c6             	mov    %rax,%r14
int main() {
    2920:	4c 89 f5             	mov    %r14,%rbp
    for (int y = 0 ; y < total_threads; y++) {
    2923:	31 db                	xor    %ebx,%ebx
    2925:	0f 1f 00             	nopl   (%rax)
    2928:	42 8d 14 3b          	lea    (%rbx,%r15,1),%edx
    292c:	41 89 d8             	mov    %ebx,%r8d
    292f:	44 89 e1             	mov    %r12d,%ecx
    2932:	4c 89 ee             	mov    %r13,%rsi
    2935:	bf 01 00 00 00       	mov    $0x1,%edi
    293a:	31 c0                	xor    %eax,%eax
    293c:	83 c3 01             	add    $0x1,%ebx
    293f:	e8 8c fb ff ff       	call   24d0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    2944:	48 89 ef             	mov    %rbp,%rdi
    2947:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    2949:	48 83 c5 28          	add    $0x28,%rbp
      pthread_mutex_init(&swapmutex[cc++], NULL);
    294d:	e8 5e fc ff ff       	call   25b0 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    2952:	83 fb 07             	cmp    $0x7,%ebx
    2955:	75 d1                	jne    2928 <main+0x228>
    2957:	41 83 c7 07          	add    $0x7,%r15d
  for (int x = 0 ; x < total_threads; x++) {
    295b:	41 83 c4 01          	add    $0x1,%r12d
    295f:	49 81 c6 18 01 00 00 	add    $0x118,%r14
    2966:	41 83 ff 31          	cmp    $0x31,%r15d
    296a:	75 b4                	jne    2920 <main+0x220>
    296c:	ba 02 00 00 00       	mov    $0x2,%edx
    2971:	bf 01 00 00 00       	mov    $0x1,%edi
    2976:	31 c0                	xor    %eax,%eax
    2978:	4c 8b 34 24          	mov    (%rsp),%r14
    297c:	48 8d 35 2c 6a 00 00 	lea    0x6a2c(%rip),%rsi        # 93af <_IO_stdin_used+0x3af>
    2983:	e8 48 fb ff ff       	call   24d0 <__printf_chk@plt>
    2988:	ba 04 00 00 00       	mov    $0x4,%edx
    298d:	48 8d 35 31 6a 00 00 	lea    0x6a31(%rip),%rsi        # 93c5 <_IO_stdin_used+0x3c5>
    2994:	31 c0                	xor    %eax,%eax
    2996:	bf 01 00 00 00       	mov    $0x1,%edi
    299b:	e8 30 fb ff ff       	call   24d0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    29a0:	be 10 00 00 00       	mov    $0x10,%esi
    29a5:	bf 04 00 00 00       	mov    $0x4,%edi
    29aa:	e8 71 fa ff ff       	call   2420 <calloc@plt>
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    29af:	be 10 00 00 00       	mov    $0x10,%esi
    29b4:	bf 02 00 00 00       	mov    $0x2,%edi
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    29b9:	49 89 c7             	mov    %rax,%r15
    29bc:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    29c1:	e8 5a fa ff ff       	call   2420 <calloc@plt>


  int snapshot_limit = 100;
  for (int x = 0 ; x < io_threads; x++) {
    iobuffers[x].count = buffer_size;
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29c6:	be 28 00 00 00       	mov    $0x28,%esi
    29cb:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int y = 0 ; y < buffer_size; y++) {
      iobuffers[x].buffer[y].available = 0;
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29d0:	4d 89 fd             	mov    %r15,%r13
    iobuffers[x].count = buffer_size;
    29d3:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    29d9:	48 89 c3             	mov    %rax,%rbx
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29dc:	e8 3f fa ff ff       	call   2420 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29e1:	be 20 00 00 00       	mov    $0x20,%esi
    29e6:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29eb:	48 89 43 08          	mov    %rax,0x8(%rbx)
    29ef:	49 89 c4             	mov    %rax,%r12
      iobuffers[x].buffer[y].available = 0;
    29f2:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    29f9:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a00:	e8 1b fa ff ff       	call   2420 <calloc@plt>
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a05:	be 28 00 00 00       	mov    $0x28,%esi
    2a0a:	bf 01 00 00 00       	mov    $0x1,%edi
    iobuffers[x].count = buffer_size;
    2a0f:	c7 43 10 01 00 00 00 	movl   $0x1,0x10(%rbx)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a16:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a1b:	e8 00 fa ff ff       	call   2420 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a20:	be 20 00 00 00       	mov    $0x20,%esi
    2a25:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a2a:	48 89 43 18          	mov    %rax,0x18(%rbx)
    2a2e:	49 89 c4             	mov    %rax,%r12
    2a31:	49 8d 5f 40          	lea    0x40(%r15),%rbx
      iobuffers[x].buffer[y].available = 0;
    2a35:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2a3c:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a43:	e8 d8 f9 ff ff       	call   2420 <calloc@plt>
    2a48:	4c 89 bc 24 80 00 00 00 	mov    %r15,0x80(%rsp)
    2a50:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    }
  }
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a55:	be 28 00 00 00       	mov    $0x28,%esi
    buffers[x].count = buffer_size;
    2a5a:	41 c7 45 00 01 00 00 00 	movl   $0x1,0x0(%r13)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a62:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2a67:	49 83 c5 10          	add    $0x10,%r13
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a6b:	e8 b0 f9 ff ff       	call   2420 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a70:	be 20 00 00 00       	mov    $0x20,%esi
    2a75:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a7a:	49 89 45 f8          	mov    %rax,-0x8(%r13)
    2a7e:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    2a81:	c7 40 08 00 00 00 00 	movl   $0x0,0x8(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2a88:	c7 40 18 64 00 00 00 	movl   $0x64,0x18(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a8f:	e8 8c f9 ff ff       	call   2420 <calloc@plt>
    2a94:	48 89 45 10          	mov    %rax,0x10(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    2a98:	49 39 dd             	cmp    %rbx,%r13
    2a9b:	75 b8                	jne    2a55 <main+0x355>
  int iocur_buffer = 0;
  int swap = 0;
  int groupcount = 0;
  int seq = 0;
  int seqs[] = {1, 3, 6};
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a9d:	be 08 00 00 00       	mov    $0x8,%esi
    2aa2:	bf 64 00 00 00       	mov    $0x64,%edi
    2aa7:	e8 74 f9 ff ff       	call   2420 <calloc@plt>
  struct Global *global = calloc(1, sizeof(struct Global));
    2aac:	be 10 00 00 00       	mov    $0x10,%esi
    2ab1:	bf 01 00 00 00       	mov    $0x1,%edi
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2ab6:	48 89 c3             	mov    %rax,%rbx
    2ab9:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  struct Global *global = calloc(1, sizeof(struct Global));
    2ac1:	e8 5a f9 ff ff       	call   2420 <calloc@plt>
  global->request_group_sync = -1;
  global->protected_state = global_protected_state;
  for (int k = 0 ; k < group_count ; k++) {
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2ac6:	be 00 01 00 00       	mov    $0x100,%esi
    2acb:	bf 01 00 00 00       	mov    $0x1,%edi
  global->request_group_sync = -1;
    2ad0:	c7 00 ff ff ff ff    	movl   $0xffffffff,(%rax)
  global->protected_state = global_protected_state;
    2ad6:	4c 89 70 08          	mov    %r14,0x8(%rax)
    2ada:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2adf:	e8 3c f9 ff ff       	call   2420 <calloc@plt>
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2ae4:	be 08 00 00 00       	mov    $0x8,%esi
    2ae9:	bf 64 00 00 00       	mov    $0x64,%edi
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2aee:	48 89 04 24          	mov    %rax,(%rsp)
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2af2:	e8 29 f9 ff ff       	call   2420 <calloc@plt>
    all_groups[groupcount++] = group_data;
    2af7:	48 8b 14 24          	mov    (%rsp),%rdx
    group_data->thread_count = threads_per_group * group_count;
    group_data->threads = group_threads;
    group_data->global = global;
    2afb:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    group_data->seq = seqs[seq++ % 3];
    2b00:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    2b09:	48 8b 6c 24 68       	mov    0x68(%rsp),%rbp
    2b0e:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    2b13:	c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%rsp)
    group_data->thread_count = threads_per_group * group_count;
    2b1b:	c7 82 90 00 00 00 02 00 00 00 	movl   $0x2,0x90(%rdx)
    group_data->threads = group_threads;
    2b25:	48 89 82 88 00 00 00 	mov    %rax,0x88(%rdx)
    group_data->global = global;
    2b2c:	4c 89 8a 98 00 00 00 	mov    %r9,0x98(%rdx)
    group_data->seq = seqs[seq++ % 3];
    2b33:	c7 82 a0 00 00 00 01 00 00 00 	movl   $0x1,0xa0(%rdx)
    2b3d:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
    2b45:	48 89 6c 24 58       	mov    %rbp,0x58(%rsp)
    2b4a:	4c 89 8c 24 a0 00 00 00 	mov    %r9,0xa0(%rsp)
    2b52:	48 89 94 24 a8 00 00 00 	mov    %rdx,0xa8(%rsp)
    all_groups[groupcount++] = group_data;
    2b5a:	48 89 13             	mov    %rdx,(%rbx)
    int group_thread_count = 0;
    for (int d = 0 ; d < threads_per_group ; d++) {
    2b5d:	4c 89 d3             	mov    %r10,%rbx
      int x = (k * threads_per_group) + d;
      thread_data[x].group_data = group_data;
      thread_data[x].all_groups = all_groups;
    2b60:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    2b68:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
      thread_data[x].group = k;
    2b6d:	c7 83 f8 00 00 00 00 00 00 00 	movl   $0x0,0xf8(%rbx)
    2b77:	31 d2                	xor    %edx,%edx
      thread_data[x].group_data = group_data;
    2b79:	48 8b ac 24 a8 00 00 00 	mov    0xa8(%rsp),%rbp
    2b81:	48 8d 35 98 6d 00 00 	lea    0x6d98(%rip),%rsi        # 9920 <_IO_stdin_used+0x920>
    2b88:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].all_groups = all_groups;
    2b8d:	48 89 83 f0 00 00 00 	mov    %rax,0xf0(%rbx)
    2b94:	44 89 f1             	mov    %r14d,%ecx
    2b97:	47 8d 24 36          	lea    (%r14,%r14,1),%r12d
    2b9b:	45 89 f7             	mov    %r14d,%r15d
      thread_data[x].global = global;
    2b9e:	48 8b 84 24 a0 00 00 00 	mov    0xa0(%rsp),%rax
      thread_data[x].group_data = group_data;
    2ba6:	48 89 ab e8 00 00 00 	mov    %rbp,0xe8(%rbx)
      thread_data[x].global = global;
    2bad:	48 89 83 00 01 00 00 	mov    %rax,0x100(%rbx)
    2bb4:	31 c0                	xor    %eax,%eax
    2bb6:	e8 15 f9 ff ff       	call   24d0 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2bbb:	be 08 00 00 00       	mov    $0x8,%esi
    2bc0:	bf 02 00 00 00       	mov    $0x2,%edi
    2bc5:	e8 56 f8 ff ff       	call   2420 <calloc@plt>
      
      group_data->threads[group_thread_count++] = &thread_data[x];  

      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2bca:	be 80 00 00 00       	mov    $0x80,%esi
    2bcf:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2bd4:	49 89 c5             	mov    %rax,%r13
      group_data->threads[group_thread_count++] = &thread_data[x];  
    2bd7:	48 8b 85 88 00 00 00 	mov    0x88(%rbp),%rax
    2bde:	4c 89 f5             	mov    %r14,%rbp
    2be1:	4a 89 1c f0          	mov    %rbx,(%rax,%r14,8)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2be5:	e8 36 f8 ff ff       	call   2420 <calloc@plt>
    2bea:	49 89 c6             	mov    %rax,%r14
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2bed:	48 85 ed             	test   %rbp,%rbp
    2bf0:	0f 84 ae 0e 00 00    	je     3aa4 <main+0x13a4>
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2bf6:	49 8d 45 08          	lea    0x8(%r13),%rax
    2bfa:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    2bff:	41 b8 01 00 00 00    	mov    $0x1,%r8d
        other = abs(x - 1) % total_threads;
    2c05:	31 ed                	xor    %ebp,%ebp
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2c07:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
    2c0c:	48 89 d8             	mov    %rbx,%rax
        my_thread_data[1] = &thread_data[x]; 
    2c0f:	49 89 45 08          	mov    %rax,0x8(%r13)
        thread_data[x].protected_state = &protected_state[k];
    2c13:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    2c18:	89 e9                	mov    %ebp,%ecx
    2c1a:	48 8d 35 2f 6d 00 00 	lea    0x6d2f(%rip),%rsi        # 9950 <_IO_stdin_used+0x950>
        thread_data[x].thread_index = 1;
    2c21:	44 89 43 04          	mov    %r8d,0x4(%rbx)
    2c25:	bf 01 00 00 00       	mov    $0x1,%edi
        my_thread_data[0] = &thread_data[other]; 
    2c2a:	49 89 55 00          	mov    %rdx,0x0(%r13)
    2c2e:	44 89 fa             	mov    %r15d,%edx
        thread_data[x].protected_state = &protected_state[k];
    2c31:	48 89 43 48          	mov    %rax,0x48(%rbx)
    2c35:	31 c0                	xor    %eax,%eax
    2c37:	e8 94 f8 ff ff       	call   24d0 <__printf_chk@plt>
      thread_data[x].other = other;
    2c3c:	89 ab c8 00 00 00    	mov    %ebp,0xc8(%rbx)
    2c42:	44 89 fa             	mov    %r15d,%edx
    2c45:	31 c0                	xor    %eax,%eax
    2c47:	44 89 e1             	mov    %r12d,%ecx
    2c4a:	48 8d 35 2f 6d 00 00 	lea    0x6d2f(%rip),%rsi        # 9980 <_IO_stdin_used+0x980>
    2c51:	bf 01 00 00 00       	mov    $0x1,%edi
    2c56:	e8 75 f8 ff ff       	call   24d0 <__printf_chk@plt>
          CPU_SET(curcpu, sendercpu);
    2c5b:	44 89 e1             	mov    %r12d,%ecx
    2c5e:	b8 01 00 00 00       	mov    $0x1,%eax
      thread_data[x].cpu_set = sendercpu;
    2c63:	4c 89 b3 c0 00 00 00 	mov    %r14,0xc0(%rbx)
          CPU_SET(curcpu, sendercpu);
    2c6a:	48 d3 e0             	shl    %cl,%rax
    2c6d:	49 09 06             	or     %rax,(%r14)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2c70:	be 10 00 00 00       	mov    $0x10,%esi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2c75:	49 89 de             	mov    %rbx,%r14
      thread_data[x].swapmutex = swapmutex;
    2c78:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2c80:	4c 89 6b 18          	mov    %r13,0x18(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2c84:	bf 64 00 00 00       	mov    $0x64,%edi
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2c89:	45 31 ed             	xor    %r13d,%r13d
      thread_data[x].kind = KERNEL_THREAD;
    2c8c:	c7 03 5f 00 00 00    	movl   $0x5f,(%rbx)
      thread_data[x].swapmutex = swapmutex;
    2c92:	48 89 83 d8 00 00 00 	mov    %rax,0xd8(%rbx)
      thread_data[x].mswapmutex = mswapmutex;
    2c99:	48 8b 84 24 88 00 00 00 	mov    0x88(%rsp),%rax
      thread_data[x].real_thread_index = x;
    2ca1:	44 89 7b 08          	mov    %r15d,0x8(%rbx)
      thread_data[x].mswapmutex = mswapmutex;
    2ca5:	48 89 83 e0 00 00 00 	mov    %rax,0xe0(%rbx)
      thread_data[x].all_threads = thread_data;
    2cac:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
      thread_data[x].task_count = total_barrier_count;
    2cb1:	c7 43 40 03 00 00 00 	movl   $0x3,0x40(%rbx)
      thread_data[x].all_threads = thread_data;
    2cb8:	48 89 43 20          	mov    %rax,0x20(%rbx)
      thread_data[x].group_count = group_count;
    2cbc:	48 8b 05 4d 72 00 00 	mov    0x724d(%rip),%rax        # 9f10 <_IO_stdin_used+0xf10>
    2cc3:	48 89 83 d0 00 00 00 	mov    %rax,0xd0(%rbx)
      thread_data[x].thread_count = 2;
    2cca:	48 8b 05 47 72 00 00 	mov    0x7247(%rip),%rax        # 9f18 <_IO_stdin_used+0xf18>
    2cd1:	48 89 43 28          	mov    %rax,0x28(%rbx)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2cd5:	e8 46 f7 ff ff       	call   2420 <calloc@plt>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2cda:	be 10 00 00 00       	mov    $0x10,%esi
    2cdf:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2ce4:	48 89 43 78          	mov    %rax,0x78(%rbx)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2ce8:	e8 33 f7 ff ff       	call   2420 <calloc@plt>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2ced:	be 28 00 00 00       	mov    $0x28,%esi
    2cf2:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].timestamp_count = 0;
    2cf7:	66 0f 6f 3d e1 71 00 00 	movdqa 0x71e1(%rip),%xmm7        # 9ee0 <_IO_stdin_used+0xee0>
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2cff:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
      thread_data[x].timestamp_count = 0;
    2d06:	0f 11 bb 90 00 00 00 	movups %xmm7,0x90(%rbx)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2d0d:	e8 0e f7 ff ff       	call   2420 <calloc@plt>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2d12:	be 00 02 00 00       	mov    $0x200,%esi
    2d17:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2d1c:	66 0f 6f 3d bc 71 00 00 	movdqa 0x71bc(%rip),%xmm7        # 9ee0 <_IO_stdin_used+0xee0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2d24:	48 89 83 a0 00 00 00 	mov    %rax,0xa0(%rbx)
      thread_data[x].task_timestamp_count = 0;
    2d2b:	0f 11 bb a8 00 00 00 	movups %xmm7,0xa8(%rbx)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2d32:	e8 e9 f6 ff ff       	call   2420 <calloc@plt>
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2d37:	44 89 7c 24 08       	mov    %r15d,0x8(%rsp)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2d3c:	48 89 c5             	mov    %rax,%rbp
        thread_data[x].tasks = barriers;
    2d3f:	48 89 43 38          	mov    %rax,0x38(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2d43:	44 89 f8             	mov    %r15d,%eax
    2d46:	83 f0 01             	xor    $0x1,%eax
    2d49:	48 89 ea             	mov    %rbp,%rdx
    2d4c:	89 44 24 10          	mov    %eax,0x10(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2d50:	49 63 c5             	movslq %r13d,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2d53:	be 00 01 00 00       	mov    $0x100,%esi
    2d58:	bf 02 00 00 00       	mov    $0x2,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d5d:	31 db                	xor    %ebx,%ebx
          thread_data[x].tasks[y].protected = do_protected_write; 
    2d5f:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2d64:	48 c1 e0 09          	shl    $0x9,%rax
    2d68:	48 8d 2c 02          	lea    (%rdx,%rax,1),%rbp
    2d6c:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
    2d71:	48 8d 05 78 15 00 00 	lea    0x1578(%rip),%rax        # 42f0 <do_protected_write>
    2d78:	48 89 85 20 01 00 00 	mov    %rax,0x120(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2d7f:	e8 9c f6 ff ff       	call   2420 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2d84:	44 8b 7c 24 28       	mov    0x28(%rsp),%r15d
    2d89:	4c 89 74 24 48       	mov    %r14,0x48(%rsp)
    2d8e:	41 89 de             	mov    %ebx,%r14d
    2d91:	48 89 85 70 01 00 00 	mov    %rax,0x170(%rbp)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2d98:	49 89 c4             	mov    %rax,%r12
    2d9b:	31 c9                	xor    %ecx,%ecx
    2d9d:	44 89 f2             	mov    %r14d,%edx
    2da0:	48 8d 35 38 66 00 00 	lea    0x6638(%rip),%rsi        # 93df <_IO_stdin_used+0x3df>
    2da7:	31 c0                	xor    %eax,%eax
    2da9:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2dae:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    2db5:	e8 16 f7 ff ff       	call   24d0 <__printf_chk@plt>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2dba:	be 08 00 00 00       	mov    $0x8,%esi
    2dbf:	bf 01 00 00 00       	mov    $0x1,%edi
    2dc4:	e8 57 f6 ff ff       	call   2420 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2dc9:	be 08 00 00 00       	mov    $0x8,%esi
    2dce:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2dd3:	48 89 04 24          	mov    %rax,(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2dd7:	e8 44 f6 ff ff       	call   2420 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2ddc:	be 80 04 00 00       	mov    $0x480,%esi
    2de1:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2de6:	48 89 c3             	mov    %rax,%rbx
              struct Data *data = calloc(3, sizeof(struct Data));
    2de9:	e8 32 f6 ff ff       	call   2420 <calloc@plt>
              data[0].a = x;
    2dee:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    2df2:	44 89 f2             	mov    %r14d,%edx
              mailboxes[b].pending_lower = NULL;
    2df5:	49 c7 44 24 88 00 00 00 00 	movq   $0x0,-0x78(%r12)
              struct Data *data = calloc(3, sizeof(struct Data));
    2dfe:	48 89 c5             	mov    %rax,%rbp
              data[0].b = y;
    2e01:	44 89 a8 10 04 00 00 	mov    %r13d,0x410(%rax)
    2e08:	48 8d 35 91 6b 00 00 	lea    0x6b91(%rip),%rsi        # 99a0 <_IO_stdin_used+0x9a0>
              data[0].a = x;
    2e0f:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
              data[0].kind = MAILBOX_LOWER;
    2e15:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
              data[0].c = b;
    2e1f:	44 89 b0 14 04 00 00 	mov    %r14d,0x414(%rax)
              data[0].id = dataid++;
    2e26:	41 8d 47 01          	lea    0x1(%r15),%eax
              data[1].id = dataid++;
    2e2a:	89 85 98 08 00 00    	mov    %eax,0x898(%rbp)
              mailboxes[b].higher = &data[1];
    2e30:	48 8d 85 80 04 00 00 	lea    0x480(%rbp),%rax
    2e37:	49 89 44 24 80       	mov    %rax,-0x80(%r12)
    2e3c:	8b 44 24 10          	mov    0x10(%rsp),%eax
              data[0].id = dataid++;
    2e40:	44 89 bd 18 04 00 00 	mov    %r15d,0x418(%rbp)
              data[1].id = dataid++;
    2e47:	41 83 c7 02          	add    $0x2,%r15d
    2e4b:	41 89 44 24 b4       	mov    %eax,-0x4c(%r12)
    2e50:	89 c1                	mov    %eax,%ecx
    2e52:	31 c0                	xor    %eax,%eax
              data[1].a = x;
    2e54:	89 bd 8c 08 00 00    	mov    %edi,0x88c(%rbp)
    2e5a:	bf 01 00 00 00       	mov    $0x1,%edi
              mailboxes[b].lower = &data[0];
    2e5f:	49 89 ac 24 00 ff ff ff 	mov    %rbp,-0x100(%r12)
              mailboxes[b].pending_higher = NULL;
    2e67:	49 c7 44 24 90 00 00 00 00 	movq   $0x0,-0x70(%r12)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2e70:	41 c7 44 24 b0 01 00 00 00 	movl   $0x1,-0x50(%r12)
              data[1].kind = MAILBOX_HIGHER;
    2e79:	c7 85 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%rbp)
              data[1].b = y;
    2e83:	44 89 ad 90 08 00 00 	mov    %r13d,0x890(%rbp)
              data[1].c = b;
    2e8a:	44 89 b5 94 08 00 00 	mov    %r14d,0x894(%rbp)
              data[0].finished_reading = 1;
    2e91:	c7 85 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rbp)
              data[1].finished_reading = 1;
    2e9b:	c7 85 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%rbp)
    2ea5:	e8 26 f6 ff ff       	call   24d0 <__printf_chk@plt>
              data[0].messages = messages;
    2eaa:	4c 8b 14 24          	mov    (%rsp),%r10
              data[0].messages_count = 0;
    2eae:	66 0f 6f 15 3a 70 00 00 	movdqa 0x703a(%rip),%xmm2        # 9ef0 <_IO_stdin_used+0xef0>
              data[1].messages = messages2;
    2eb6:	48 89 9d 80 04 00 00 	mov    %rbx,0x480(%rbp)
              data[0].messages = messages;
    2ebd:	4c 89 55 00          	mov    %r10,0x0(%rbp)
              data[0].messages_count = 0;
    2ec1:	0f 29 95 80 00 00 00 	movaps %xmm2,0x80(%rbp)
              data[1].messages_count = 0;
    2ec8:	0f 29 95 00 05 00 00 	movaps %xmm2,0x500(%rbp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ecf:	45 85 f6             	test   %r14d,%r14d
    2ed2:	75 0b                	jne    2edf <main+0x7df>
    2ed4:	41 be 01 00 00 00    	mov    $0x1,%r14d
    2eda:	e9 bc fe ff ff       	jmp    2d9b <main+0x69b>
          char *message = malloc(sizeof(char) * 256);
    2edf:	be 01 00 00 00       	mov    $0x1,%esi
    2ee4:	bf 00 01 00 00       	mov    $0x100,%edi
    2ee9:	83 44 24 28 04       	addl   $0x4,0x28(%rsp)
    2eee:	44 89 f3             	mov    %r14d,%ebx
    2ef1:	4c 8b 74 24 48       	mov    0x48(%rsp),%r14
    2ef6:	e8 25 f5 ff ff       	call   2420 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2efb:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2f00:	48 89 c5             	mov    %rax,%rbp
          struct Message *messaged = malloc(sizeof(struct Message));
    2f03:	e8 88 f5 ff ff       	call   2490 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2f08:	48 83 ec 08          	sub    $0x8,%rsp
    2f0c:	48 89 ef             	mov    %rbp,%rdi
    2f0f:	45 89 e9             	mov    %r13d,%r9d
    2f12:	6a 00                	push   $0x0
    2f14:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
    2f19:	49 89 c4             	mov    %rax,%r12
    2f1c:	ba 00 01 00 00       	mov    $0x100,%edx
    2f21:	48 8d 0d a0 6a 00 00 	lea    0x6aa0(%rip),%rcx        # 99c8 <_IO_stdin_used+0x9c8>
    2f28:	be 01 00 00 00       	mov    $0x1,%esi
    2f2d:	31 c0                	xor    %eax,%eax
    2f2f:	e8 ac f6 ff ff       	call   25e0 <__sprintf_chk@plt>
          messaged->task_index = y;
    2f34:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
          thread_data[x].tasks[y].swap = swap;
    2f39:	49 8b 56 38          	mov    0x38(%r14),%rdx
          messaged->message = message;
    2f3d:	49 89 2c 24          	mov    %rbp,(%r12)
          thread_data[x].tasks[y].swap = swap;
    2f41:	48 8b 6c 24 48       	mov    0x48(%rsp),%rbp
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2f46:	be 20 00 00 00       	mov    $0x20,%esi
    2f4b:	bf 63 00 00 00       	mov    $0x63,%edi
          messaged->group = k;
    2f50:	41 c7 44 24 18 00 00 00 00 	movl   $0x0,0x18(%r12)
          messaged->task_index = y;
    2f59:	49 89 44 24 10       	mov    %rax,0x10(%r12)
          messaged->thread_index = thread_data[x].real_thread_index;
    2f5e:	49 63 46 08          	movslq 0x8(%r14),%rax
          thread_data[x].tasks[y].swap = swap;
    2f62:	48 01 d5             	add    %rdx,%rbp
    2f65:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
          messaged->thread_index = thread_data[x].real_thread_index;
    2f6a:	49 89 44 24 08       	mov    %rax,0x8(%r12)
          thread_data[x].tasks[y].swap = swap;
    2f6f:	8b 44 24 28          	mov    0x28(%rsp),%eax
          thread_data[x].tasks[y].group = k;
    2f73:	c7 85 9c 01 00 00 00 00 00 00 	movl   $0x0,0x19c(%rbp)
          thread_data[x].tasks[y].swap = swap;
    2f7d:	89 85 a0 01 00 00    	mov    %eax,0x1a0(%rbp)
          swap += 1;
    2f83:	83 c0 01             	add    $0x1,%eax
    2f86:	89 44 24 28          	mov    %eax,0x28(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2f8a:	41 8d 45 01          	lea    0x1(%r13),%eax
    2f8e:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    2f91:	c7 45 00 41 00 00 00 	movl   $0x41,0x0(%rbp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    2f98:	89 85 98 01 00 00    	mov    %eax,0x198(%rbp)
          thread_data[x].tasks[y].message = messaged;
    2f9e:	4c 89 a5 90 01 00 00 	mov    %r12,0x190(%rbp)
          thread_data[x].tasks[y].sending = 1;
    2fa5:	c7 85 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbp)
          thread_data[x].tasks[y].snapshot_count = 99;
    2faf:	48 c7 85 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2fba:	e8 61 f4 ff ff       	call   2420 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    2fbf:	48 c7 85 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2fca:	48 89 85 50 01 00 00 	mov    %rax,0x150(%rbp)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2fd1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    2fd6:	48 8b 00             	mov    (%rax),%rax
    2fd9:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2fdc:	49 39 c6             	cmp    %rax,%r14
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    2fdf:	48 89 85 28 01 00 00 	mov    %rax,0x128(%rbp)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2fe6:	89 8d 30 01 00 00    	mov    %ecx,0x130(%rbp)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    2fec:	5a                   	pop    %rdx
    2fed:	59                   	pop    %rcx
    2fee:	48 8b 14 24          	mov    (%rsp),%rdx
    2ff2:	0f 85 f8 11 00 00    	jne    41f0 <main+0x1af0>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    2ff8:	66 0f 6f 25 00 6f 00 00 	movdqa 0x6f00(%rip),%xmm4        # 9f00 <_IO_stdin_used+0xf00>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    3000:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
          thread_data[x].tasks[y].available = 1;
    3004:	48 8b 05 15 6f 00 00 	mov    0x6f15(%rip),%rax        # 9f20 <_IO_stdin_used+0xf20>
          thread_data[x].tasks[y].arrived = 0;
    300b:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
          thread_data[x].tasks[y].worker_count = thread_count;
    3015:	c7 85 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rbp)
          thread_data[x].tasks[y].available = 1;
    301f:	48 89 85 44 01 00 00 	mov    %rax,0x144(%rbp)
          thread_data[x].tasks[y].thread_count = 2;
    3026:	0f 11 a5 34 01 00 00 	movups %xmm4,0x134(%rbp)
          if (y == barrier_count - 1) {
    302d:	41 83 fd 01          	cmp    $0x1,%r13d
    3031:	0f 84 18 01 00 00    	je     314f <main+0xa4f>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    3037:	45 85 ed             	test   %r13d,%r13d
    303a:	0f 84 f9 00 00 00    	je     3139 <main+0xa39>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    3040:	4c 89 f0             	mov    %r14,%rax
    3043:	49 89 ec             	mov    %rbp,%r12
    3046:	41 89 de             	mov    %ebx,%r14d
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3049:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    304e:	48 89 c3             	mov    %rax,%rbx
    3051:	48 8d 05 d8 4a 00 00 	lea    0x4ad8(%rip),%rax        # 7b30 <barriered_work>
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3058:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    305d:	48 89 d5             	mov    %rdx,%rbp
    3060:	49 89 84 24 18 01 00 00 	mov    %rax,0x118(%r12)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3068:	48 81 c3 30 01 00 00 	add    $0x130,%rbx
        thread_data[x].buffers_count = buffers_per_thread;
    306f:	c7 43 9c 01 00 00 00 	movl   $0x1,-0x64(%rbx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3076:	e8 a5 f3 ff ff       	call   2420 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    307b:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    3080:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
        }
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3085:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    308a:	48 89 83 20 ff ff ff 	mov    %rax,-0xe0(%rbx)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3091:	4c 89 f9             	mov    %r15,%rcx
    3094:	48 c1 e1 04          	shl    $0x4,%rcx
    3098:	48 01 f9             	add    %rdi,%rcx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    309b:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    30a0:	48 89 08             	mov    %rcx,(%rax)
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    30a3:	e8 78 f3 ff ff       	call   2420 <calloc@plt>
        for (int b = 0 ; b < io_threads; b++) {	
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    30a8:	48 8b 7c 24 58       	mov    0x58(%rsp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    30ad:	66 0f 6f 74 24 70    	movdqa 0x70(%rsp),%xmm6
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    30b3:	48 89 83 28 ff ff ff 	mov    %rax,-0xd8(%rbx)
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    30ba:	48 8d 4f 10          	lea    0x10(%rdi),%rcx
    30be:	48 89 38             	mov    %rdi,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    30c1:	48 83 c7 20          	add    $0x20,%rdi
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    30c5:	48 89 48 08          	mov    %rcx,0x8(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    30c9:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    30ce:	48 89 7c 24 58       	mov    %rdi,0x58(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    30d3:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    30d6:	0f 11 b5 18 05 00 00 	movups %xmm6,0x518(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    30dd:	c7 85 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rbp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    30e7:	48 89 85 28 05 00 00 	mov    %rax,0x528(%rbp)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    30ee:	c7 85 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rbp)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    30f8:	c7 85 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    3102:	8b 83 d4 fe ff ff    	mov    -0x12c(%rbx),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    3108:	c7 85 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rbp)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    3112:	89 85 30 05 00 00    	mov    %eax,0x530(%rbp)
        thread_data[x].tasks[barrier_count].available = 1; 
    3118:	48 8b 05 01 6e 00 00 	mov    0x6e01(%rip),%rax        # 9f20 <_IO_stdin_used+0xf20>
    311f:	48 89 85 44 05 00 00 	mov    %rax,0x544(%rbp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3126:	4d 85 ff             	test   %r15,%r15
    3129:	75 32                	jne    315d <main+0xa5d>
    312b:	48 c7 44 24 20 01 00 00 00 	movq   $0x1,0x20(%rsp)
    3134:	e9 27 fa ff ff       	jmp    2b60 <main+0x460>
    3139:	48 8d 05 c0 4f 00 00 	lea    0x4fc0(%rip),%rax        # 8100 <barriered_work_ingest_andwork>
            thread_data[x].tasks[y].run = barriered_work; 
    3140:	48 89 85 18 01 00 00 	mov    %rax,0x118(%rbp)
    3147:	41 89 dd             	mov    %ebx,%r13d
    314a:	e9 01 fc ff ff       	jmp    2d50 <main+0x650>
    314f:	48 8d 05 da 49 00 00 	lea    0x49da(%rip),%rax        # 7b30 <barriered_work>
    3156:	bb 02 00 00 00       	mov    $0x2,%ebx
    315b:	eb e3                	jmp    3140 <main+0xa40>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    315d:	bf 00 04 00 00       	mov    $0x400,%edi
    3162:	be 08 00 00 00       	mov    $0x8,%esi
    3167:	31 ed                	xor    %ebp,%ebp
    3169:	e8 b2 f2 ff ff       	call   2420 <calloc@plt>
    316e:	49 89 c4             	mov    %rax,%r12
  int datas_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3171:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3176:	48 8d 58 38          	lea    0x38(%rax),%rbx
    317a:	48 05 98 02 00 00    	add    $0x298,%rax
    3180:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3185:	48 89 df             	mov    %rbx,%rdi
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3188:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    318c:	45 85 c0             	test   %r8d,%r8d
    318f:	7e 55                	jle    31e6 <main+0xae6>
    3191:	48 8b 17             	mov    (%rdi),%rdx
    3194:	49 63 f0             	movslq %r8d,%rsi
    3197:	48 63 c5             	movslq %ebp,%rax
    319a:	48 c1 e6 09          	shl    $0x9,%rsi
    319e:	49 8d 0c c4          	lea    (%r12,%rax,8),%rcx
    31a2:	48 01 d6             	add    %rdx,%rsi
    31a5:	0f 1f 00             	nopl   (%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    31a8:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31af:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    31b6:	48 83 c1 20          	add    $0x20,%rcx
    31ba:	f3 0f 7e 80 00 01 00 00 	movq   0x100(%rax),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    31c2:	f3 0f 7e 08          	movq   (%rax),%xmm1
    31c6:	0f 16 80 80 01 00 00 	movhps 0x180(%rax),%xmm0
    31cd:	0f 16 88 80 00 00 00 	movhps 0x80(%rax),%xmm1
    31d4:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    31d8:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31dc:	48 39 d6             	cmp    %rdx,%rsi
    31df:	75 c7                	jne    31a8 <main+0xaa8>
    31e1:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    31e6:	48 81 c7 30 01 00 00 	add    $0x130,%rdi
    31ed:	48 39 7c 24 10       	cmp    %rdi,0x10(%rsp)
    31f2:	75 94                	jne    3188 <main+0xa88>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    31f4:	48 8d 3d f4 61 00 00 	lea    0x61f4(%rip),%rdi        # 93ef <_IO_stdin_used+0x3ef>
    31fb:	e8 50 f1 ff ff       	call   2350 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    3200:	48 8d 3d ff 61 00 00 	lea    0x61ff(%rip),%rdi        # 9406 <_IO_stdin_used+0x406>
    3207:	48 8d 35 f6 61 00 00 	lea    0x61f6(%rip),%rsi        # 9404 <_IO_stdin_used+0x404>
    320e:	e8 0d f3 ff ff       	call   2520 <fopen@plt>
    3213:	48 89 c7             	mov    %rax,%rdi
  for (int x = 0 ; x < datas_size; x++) {
    3216:	85 ed                	test   %ebp,%ebp
    3218:	0f 8e 85 00 00 00    	jle    32a3 <main+0xba3>
    321e:	48 8d 05 18 62 00 00 	lea    0x6218(%rip),%rax        # 943d <_IO_stdin_used+0x43d>
    3225:	48 63 ed             	movslq %ebp,%rbp
    3228:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    322d:	4c 8d 2d fd 61 00 00 	lea    0x61fd(%rip),%r13        # 9431 <_IO_stdin_used+0x431>
    3234:	48 89 04 24          	mov    %rax,(%rsp)
    3238:	4d 8d 3c ec          	lea    (%r12,%rbp,8),%r15
    323c:	48 89 fb             	mov    %rdi,%rbx
    char * c = calloc(250, sizeof(char));
    323f:	be 01 00 00 00       	mov    $0x1,%esi
    3244:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    3249:	49 83 c4 08          	add    $0x8,%r12
    char * c = calloc(250, sizeof(char));
    324d:	e8 ce f1 ff ff       	call   2420 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3252:	4c 89 e9             	mov    %r13,%rcx
    3255:	ba fa 00 00 00       	mov    $0xfa,%edx
    325a:	be 01 00 00 00       	mov    $0x1,%esi
    325f:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    3262:	49 8b 44 24 f8       	mov    -0x8(%r12),%rax
    3267:	48 89 ef             	mov    %rbp,%rdi
    326a:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3271:	31 c0                	xor    %eax,%eax
    3273:	e8 68 f3 ff ff       	call   25e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3278:	48 8b 34 24          	mov    (%rsp),%rsi
    327c:	48 89 ea             	mov    %rbp,%rdx
    327f:	31 c0                	xor    %eax,%eax
    3281:	bf 01 00 00 00       	mov    $0x1,%edi
    3286:	e8 45 f2 ff ff       	call   24d0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    328b:	48 89 de             	mov    %rbx,%rsi
    328e:	48 89 ef             	mov    %rbp,%rdi
    3291:	e8 4a f1 ff ff       	call   23e0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    3296:	4d 39 e7             	cmp    %r12,%r15
    3299:	75 a4                	jne    323f <main+0xb3f>
    329b:	48 89 df             	mov    %rbx,%rdi
    329e:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    32a3:	e8 d8 f0 ff ff       	call   2380 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    32a8:	48 8d 3d 60 61 00 00 	lea    0x6160(%rip),%rdi        # 940f <_IO_stdin_used+0x40f>
    32af:	49 89 dc             	mov    %rbx,%r12
    32b2:	4c 8d 3d 99 61 00 00 	lea    0x6199(%rip),%r15        # 9452 <_IO_stdin_used+0x452>
    32b9:	e8 92 f0 ff ff       	call   2350 <puts@plt>
    32be:	31 d2                	xor    %edx,%edx
    32c0:	48 8d 35 60 61 00 00 	lea    0x6160(%rip),%rsi        # 9427 <_IO_stdin_used+0x427>
    32c7:	31 c0                	xor    %eax,%eax
    32c9:	bf 01 00 00 00       	mov    $0x1,%edi
    32ce:	4c 8d 2d 88 61 00 00 	lea    0x6188(%rip),%r13        # 945d <_IO_stdin_used+0x45d>
    32d5:	e8 f6 f1 ff ff       	call   24d0 <__printf_chk@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    32da:	c7 44 24 40 00 00 00 00 	movl   $0x0,0x40(%rsp)
    32e2:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    32e7:	8b 54 24 40          	mov    0x40(%rsp),%edx
    32eb:	48 8d 35 4e 61 00 00 	lea    0x614e(%rip),%rsi        # 9440 <_IO_stdin_used+0x440>
    32f2:	bf 01 00 00 00       	mov    $0x1,%edi
    32f7:	31 c0                	xor    %eax,%eax
    32f9:	89 d1                	mov    %edx,%ecx
    32fb:	e8 d0 f1 ff ff       	call   24d0 <__printf_chk@plt>
    3300:	44 89 74 24 18       	mov    %r14d,0x18(%rsp)
    3305:	45 31 c0             	xor    %r8d,%r8d
    3308:	44 89 c2             	mov    %r8d,%edx
    330b:	4c 89 fe             	mov    %r15,%rsi
    330e:	bf 01 00 00 00       	mov    $0x1,%edi
    3313:	31 c0                	xor    %eax,%eax
    3315:	4c 89 04 24          	mov    %r8,(%rsp)
    3319:	31 ed                	xor    %ebp,%ebp
    331b:	e8 b0 f1 ff ff       	call   24d0 <__printf_chk@plt>
      int x = (k * threads_per_group) + d;
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3320:	48 8b 1c 24          	mov    (%rsp),%rbx
    3324:	48 c1 e3 09          	shl    $0x9,%rbx
          char * mailbox_kind = calloc(100, sizeof(char));
    3328:	be 01 00 00 00       	mov    $0x1,%esi
    332d:	bf 64 00 00 00       	mov    $0x64,%edi
    3332:	41 89 ee             	mov    %ebp,%r14d
    3335:	e8 e6 f0 ff ff       	call   2420 <calloc@plt>
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    333a:	4d 8b 04 24          	mov    (%r12),%r8
    333e:	48 89 ef             	mov    %rbp,%rdi
          char * mailbox_kind = calloc(100, sizeof(char));
    3341:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3344:	48 c1 e7 08          	shl    $0x8,%rdi
    3348:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3350:	48 01 f8             	add    %rdi,%rax
    3353:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    3359:	83 fe 02             	cmp    $0x2,%esi
    335c:	74 5f                	je     33bd <main+0xcbd>
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    335e:	83 fe 01             	cmp    $0x1,%esi
    3361:	74 74                	je     33d7 <main+0xcd7>
    3363:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    336a:	44 89 f2             	mov    %r14d,%edx
    336d:	31 c0                	xor    %eax,%eax
    336f:	4c 89 ee             	mov    %r13,%rsi
    3372:	bf 01 00 00 00       	mov    $0x1,%edi
    3377:	e8 54 f1 ff ff       	call   24d0 <__printf_chk@plt>
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    337c:	48 85 ed             	test   %rbp,%rbp
    337f:	75 07                	jne    3388 <main+0xc88>
    3381:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    3386:	eb a0                	jmp    3328 <main+0xc28>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    3388:	4c 8b 04 24          	mov    (%rsp),%r8
    338c:	49 83 c0 01          	add    $0x1,%r8
    3390:	49 83 f8 03          	cmp    $0x3,%r8
    3394:	0f 85 6e ff ff ff    	jne    3308 <main+0xc08>
    for (int d = 0 ; d < threads_per_group ; d++) {
    339a:	8b 44 24 40          	mov    0x40(%rsp),%eax
    339e:	48 89 6c 24 38       	mov    %rbp,0x38(%rsp)
    33a3:	49 81 c4 30 01 00 00 	add    $0x130,%r12
    33aa:	44 8b 74 24 18       	mov    0x18(%rsp),%r14d
    33af:	85 c0                	test   %eax,%eax
    33b1:	75 41                	jne    33f4 <main+0xcf4>
    33b3:	44 89 74 24 40       	mov    %r14d,0x40(%rsp)
    33b8:	e9 2a ff ff ff       	jmp    32e7 <main+0xbe7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    33bd:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    33c7:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    33ca:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    33d2:	48 01 f8             	add    %rdi,%rax
    33d5:	eb 8c                	jmp    3363 <main+0xc63>
    33d7:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    33dd:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
    33e4:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    33ec:	48 01 f8             	add    %rdi,%rax
    33ef:	e9 6f ff ff ff       	jmp    3363 <main+0xc63>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    33f4:	ba 03 00 00 00       	mov    $0x3,%edx
    33f9:	48 8d 35 78 60 00 00 	lea    0x6078(%rip),%rsi        # 9478 <_IO_stdin_used+0x478>
    3400:	bf 01 00 00 00       	mov    $0x1,%edi
    3405:	31 c0                	xor    %eax,%eax
    3407:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    340c:	e8 bf f0 ff ff       	call   24d0 <__printf_chk@plt>
  

  printf("io index = %d\n", io_index);
  int io_mode = 0;
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    3411:	be 08 00 00 00       	mov    $0x8,%esi
    3416:	bf 02 00 00 00       	mov    $0x2,%edi
    341b:	e8 00 f0 ff ff       	call   2420 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    3420:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    3425:	be 08 00 00 00       	mov    $0x8,%esi
    342a:	bf 02 00 00 00       	mov    $0x2,%edi
    my_thread_data[0] = &thread_data[x]; 
    342f:	49 8d ae 90 03 00 00 	lea    0x390(%r14),%rbp
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3436:	4c 89 70 08          	mov    %r14,0x8(%rax)
    343a:	4d 8d ae 30 01 00 00 	lea    0x130(%r14),%r13
    my_thread_data[0] = &thread_data[x]; 
    3441:	48 89 28             	mov    %rbp,(%rax)
    3444:	4d 8d be c0 04 00 00 	lea    0x4c0(%r14),%r15

    io_mode = (io_mode + 1) % 2;
    thread_data[x].threads = my_thread_data;
    344b:	49 89 86 a8 03 00 00 	mov    %rax,0x3a8(%r14)
    thread_data[x].thread_count = 2;
    3452:	41 c7 86 b8 03 00 00 02 00 00 00 	movl   $0x2,0x3b8(%r14)
    thread_data[x].thread_index = 0;
    345d:	41 c7 86 94 03 00 00 00 00 00 00 	movl   $0x0,0x394(%r14)
    thread_data[x].task_count = total_barrier_count;
    3468:	41 c7 86 d0 03 00 00 03 00 00 00 	movl   $0x3,0x3d0(%r14)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    3473:	e8 a8 ef ff ff       	call   2420 <calloc@plt>
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3478:	be 38 00 00 00       	mov    $0x38,%esi
    347d:	bf 07 00 00 00       	mov    $0x7,%edi
    thread_data[x].thread_count = 2;
    3482:	41 c7 86 e8 04 00 00 02 00 00 00 	movl   $0x2,0x4e8(%r14)
    thread_data[x].threads = my_thread_data;
    348d:	49 89 86 d8 04 00 00 	mov    %rax,0x4d8(%r14)
    my_thread_data[0] = &thread_data[x]; 
    3494:	4c 89 38             	mov    %r15,(%rax)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3497:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    349b:	49 8b 46 38          	mov    0x38(%r14),%rax
    thread_data[x].thread_index = 0;
    349f:	41 c7 86 c4 04 00 00 00 00 00 00 	movl   $0x0,0x4c4(%r14)
    thread_data[x].task_count = total_barrier_count;
    34aa:	41 c7 86 00 05 00 00 03 00 00 00 	movl   $0x3,0x500(%r14)
    thread_data[n].tasks[0].scheduled = 1;
    34b5:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    34bf:	49 8b 86 68 01 00 00 	mov    0x168(%r14),%rax
    34c6:	4c 89 74 24 30       	mov    %r14,0x30(%rsp)
    34cb:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34d5:	e8 46 ef ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34da:	be 38 00 00 00       	mov    $0x38,%esi
    34df:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34e4:	49 89 c6             	mov    %rax,%r14
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34e7:	e8 34 ef ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34ec:	be 38 00 00 00       	mov    $0x38,%esi
    34f1:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34f6:	48 89 04 24          	mov    %rax,(%rsp)
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34fa:	e8 21 ef ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    34ff:	be 38 00 00 00       	mov    $0x38,%esi
    3504:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3509:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    350e:	e8 0d ef ff ff       	call   2420 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3513:	be 08 00 00 00       	mov    $0x8,%esi
    3518:	bf 07 00 00 00       	mov    $0x7,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    351d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3522:	e8 f9 ee ff ff       	call   2420 <calloc@plt>


  int timer_threadi = group_count * thread_count;
  thread_data[timer_threadi].type = TIMER;
    3527:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    352c:	be 08 00 00 00       	mov    $0x8,%esi
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3531:	49 89 c4             	mov    %rax,%r12
  thread_data[timer_threadi].task_count = total_barrier_count;
    3534:	48 8b 05 ed 69 00 00 	mov    0x69ed(%rip),%rax        # 9f28 <_IO_stdin_used+0xf28>
  thread_data[timer_threadi].type = TIMER;
    353b:	c7 87 6c 02 00 00 00 00 00 00 	movl   $0x0,0x26c(%rdi)
  thread_data[timer_threadi].task_count = total_barrier_count;
    3545:	48 89 87 a0 02 00 00 	mov    %rax,0x2a0(%rdi)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    354c:	bf 07 00 00 00       	mov    $0x7,%edi
    3551:	e8 ca ee ff ff       	call   2420 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3556:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    355b:	48 8d 35 25 5f 00 00 	lea    0x5f25(%rip),%rsi        # 9487 <_IO_stdin_used+0x487>
    3562:	4c 89 78 20          	mov    %r15,0x20(%rax)
    3566:	48 8d 8f 60 02 00 00 	lea    0x260(%rdi),%rcx
    356d:	49 89 ff             	mov    %rdi,%r15
    3570:	48 89 38             	mov    %rdi,(%rax)
    3573:	48 8d bf f0 05 00 00 	lea    0x5f0(%rdi),%rdi
    357a:	48 89 78 28          	mov    %rdi,0x28(%rax)
    357e:	49 8d 97 20 07 00 00 	lea    0x720(%r15),%rdx
    3585:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
  }
  thread_data[timer_threadi].threads = my_thread_data;
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    358a:	48 8b 3d 87 69 00 00 	mov    0x6987(%rip),%rdi        # 9f18 <_IO_stdin_used+0xf18>
    my_thread_data[n] = &thread_data[n]; 
    3591:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3595:	48 89 48 10          	mov    %rcx,0x10(%rax)
    3599:	48 89 68 18          	mov    %rbp,0x18(%rax)
    359d:	48 89 50 30          	mov    %rdx,0x30(%rax)
    35a1:	ba 02 00 00 00       	mov    $0x2,%edx
  thread_data[timer_threadi].threads = my_thread_data;
    35a6:	49 89 87 78 02 00 00 	mov    %rax,0x278(%r15)
    35ad:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    35af:	49 89 bf 88 02 00 00 	mov    %rdi,0x288(%r15)
    35b6:	bf 01 00 00 00       	mov    $0x1,%edi
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    35bb:	41 c7 87 90 02 00 00 02 00 00 00 	movl   $0x2,0x290(%r15)
  thread_data[timer_threadi].thread_index = 0;
    35c6:	41 c7 87 64 02 00 00 00 00 00 00 	movl   $0x0,0x264(%r15)
    my_thread_data[n] = &thread_data[n]; 
    35d1:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    35d6:	e8 f5 ee ff ff       	call   24d0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    35db:	48 8b 34 24          	mov    (%rsp),%rsi
    35df:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    35e4:	49 8d 7c 24 10       	lea    0x10(%r12),%rdi
    35e9:	48 8d 15 e0 0e 00 00 	lea    0xee0(%rip),%rdx        # 44d0 <timer_thread>
    35f0:	48 83 c6 70          	add    $0x70,%rsi
    35f4:	e8 f7 ee ff ff       	call   24f0 <pthread_create@plt>
    35f9:	4c 8d 05 f8 63 00 00 	lea    0x63f8(%rip),%r8        # 99f8 <_IO_stdin_used+0x9f8>
    3600:	31 c9                	xor    %ecx,%ecx
    3602:	31 d2                	xor    %edx,%edx
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3604:	41 c7 47 0c 01 00 00 00 	movl   $0x1,0xc(%r15)
    360c:	4c 89 c6             	mov    %r8,%rsi
    360f:	bf 01 00 00 00       	mov    $0x1,%edi
    3614:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    3616:	41 c7 47 44 01 00 00 00 	movl   $0x1,0x44(%r15)
    361e:	e8 ad ee ff ff       	call   24d0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3623:	4c 89 f9             	mov    %r15,%rcx
    3626:	4c 89 7c 24 30       	mov    %r15,0x30(%rsp)
    362b:	4c 89 f6             	mov    %r14,%rsi
    362e:	4c 8d 3d 3b 3c 00 00 	lea    0x3c3b(%rip),%r15        # 7270 <barriered_thread>
    3635:	4c 89 e7             	mov    %r12,%rdi
    3638:	4c 89 fa             	mov    %r15,%rdx
    363b:	e8 b0 ee ff ff       	call   24f0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3640:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3645:	49 8b 3c 24          	mov    (%r12),%rdi
    3649:	be 08 00 00 00       	mov    $0x8,%esi
    364e:	48 8b 90 c0 00 00 00 	mov    0xc0(%rax),%rdx
    3655:	e8 e6 ec ff ff       	call   2340 <pthread_setaffinity_np@plt>
      thread_data[x].type = WORKER;
    365a:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    365f:	31 c9                	xor    %ecx,%ecx
    3661:	4c 8d 05 90 63 00 00 	lea    0x6390(%rip),%r8        # 99f8 <_IO_stdin_used+0x9f8>
    3668:	4c 89 c6             	mov    %r8,%rsi
    366b:	ba 01 00 00 00       	mov    $0x1,%edx
    3670:	bf 01 00 00 00       	mov    $0x1,%edi
    3675:	c7 80 3c 01 00 00 01 00 00 00 	movl   $0x1,0x13c(%rax)
      thread_data[x].running = 1;
    367f:	c7 80 74 01 00 00 01 00 00 00 	movl   $0x1,0x174(%rax)
    3689:	31 c0                	xor    %eax,%eax
    368b:	e8 40 ee ff ff       	call   24d0 <__printf_chk@plt>
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3690:	4c 89 e9             	mov    %r13,%rcx
    3693:	49 8d 76 38          	lea    0x38(%r14),%rsi
    3697:	4c 89 fa             	mov    %r15,%rdx
    369a:	49 8d 7c 24 08       	lea    0x8(%r12),%rdi
    369f:	e8 4c ee ff ff       	call   24f0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    36a4:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    36a9:	49 8b 7c 24 08       	mov    0x8(%r12),%rdi
    36ae:	be 08 00 00 00       	mov    $0x8,%esi
    36b3:	48 8b 90 f0 01 00 00 	mov    0x1f0(%rax),%rdx
    36ba:	e8 81 ec ff ff       	call   2340 <pthread_setaffinity_np@plt>
    }
  }
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    36bf:	be 08 00 00 00       	mov    $0x8,%esi
    36c4:	bf 02 00 00 00       	mov    $0x2,%edi
    36c9:	e8 52 ed ff ff       	call   2420 <calloc@plt>

  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    36ce:	be d8 00 00 00       	mov    $0xd8,%esi
    36d3:	bf 01 00 00 00       	mov    $0x1,%edi
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    36d8:	49 89 c6             	mov    %rax,%r14
    36db:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    36e0:	e8 3b ed ff ff       	call   2420 <calloc@plt>
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    36e5:	be d8 00 00 00       	mov    $0xd8,%esi
    36ea:	bf 01 00 00 00       	mov    $0x1,%edi
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    36ef:	49 89 06             	mov    %rax,(%r14)
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    36f2:	e8 29 ed ff ff       	call   2420 <calloc@plt>

  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    36f7:	be 10 00 00 00       	mov    $0x10,%esi
    36fc:	bf 02 00 00 00       	mov    $0x2,%edi
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3701:	49 89 46 08          	mov    %rax,0x8(%r14)
  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    3705:	e8 16 ed ff ff       	call   2420 <calloc@plt>
    370a:	4c 89 64 24 08       	mov    %r12,0x8(%rsp)
    370f:	49 89 c6             	mov    %rax,%r14
  long iomailboxes_size = 35000;
  for (int x = 0 ; x < io_threads; x++) {
    3712:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    3717:	48 8d 40 20          	lea    0x20(%rax),%rax
    371b:	48 89 04 24          	mov    %rax,(%rsp)
    371f:	4c 89 e8             	mov    %r13,%rax
    3722:	49 89 ed             	mov    %rbp,%r13
    3725:	4c 89 f5             	mov    %r14,%rbp
    3728:	49 89 c7             	mov    %rax,%r15
    iomailboxes[x].count = iomailboxes_size;
    372b:	c7 45 00 b8 88 00 00 	movl   $0x88b8,0x0(%rbp)
    iomailboxes[x].buffer = calloc(iomailboxes_size, sizeof(struct Buffer));
    3732:	be 28 00 00 00       	mov    $0x28,%esi
    3737:	bf b8 88 00 00       	mov    $0x88b8,%edi
    373c:	e8 df ec ff ff       	call   2420 <calloc@plt>
    3741:	48 89 45 08          	mov    %rax,0x8(%rbp)
    3745:	48 89 c3             	mov    %rax,%rbx
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3748:	4c 8d 60 08          	lea    0x8(%rax),%r12
    374c:	48 81 c3 c8 5c 15 00 	add    $0x155cc8,%rbx
    3753:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      iomailboxes[x].buffer[y].available = 0;
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3758:	be 20 00 00 00       	mov    $0x20,%esi
    375d:	bf 64 00 00 00       	mov    $0x64,%edi
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3762:	49 83 c4 28          	add    $0x28,%r12
      iomailboxes[x].buffer[y].available = 0;
    3766:	41 c7 44 24 d8 00 00 00 00 	movl   $0x0,-0x28(%r12)
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
    376f:	41 c7 44 24 e8 64 00 00 00 	movl   $0x64,-0x18(%r12)
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3778:	e8 a3 ec ff ff       	call   2420 <calloc@plt>
    377d:	49 89 44 24 e0       	mov    %rax,-0x20(%r12)
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3782:	4c 39 e3             	cmp    %r12,%rbx
    3785:	75 d1                	jne    3758 <main+0x1058>
  for (int x = 0 ; x < io_threads; x++) {
    3787:	48 83 c5 10          	add    $0x10,%rbp
    378b:	48 39 2c 24          	cmp    %rbp,(%rsp)
    378f:	75 9a                	jne    372b <main+0x102b>
  char * recv_identity = "recv-thread";
  char * unknown_identity = "unknown-thread";
  int counter = 0;

  int dataeventfds[2];
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
    3791:	be 00 08 00 00       	mov    $0x800,%esi
    3796:	31 ff                	xor    %edi,%edi
    3798:	4c 8b 64 24 08       	mov    0x8(%rsp),%r12
    379d:	4c 89 ed             	mov    %r13,%rbp
    37a0:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    37a5:	4d 89 fd             	mov    %r15,%r13
    37a8:	49 89 ef             	mov    %rbp,%r15
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);

  for (int x = io_index ; x < io_index + io_threads ; x++) {
    37ab:	bd 03 00 00 00       	mov    $0x3,%ebp
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
    37b0:	e8 9b ed ff ff       	call   2550 <eventfd@plt>
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);
    37b5:	be 00 08 00 00       	mov    $0x800,%esi
    37ba:	31 ff                	xor    %edi,%edi
  dataeventfds[0] = eventfd(0, EFD_NONBLOCK);
    37bc:	89 04 24             	mov    %eax,(%rsp)
  dataeventfds[1] = eventfd(0, EFD_NONBLOCK);
    37bf:	e8 8c ed ff ff       	call   2550 <eventfd@plt>
    37c4:	48 89 5c 24 58       	mov    %rbx,0x58(%rsp)
    37c9:	89 44 24 08          	mov    %eax,0x8(%rsp)
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    37cd:	49 8d 44 24 18       	lea    0x18(%r12),%rax
    37d2:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    37d7:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    37dc:	48 05 a8 00 00 00    	add    $0xa8,%rax
    37e2:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    37e7:	48 8b 05 42 67 00 00 	mov    0x6742(%rip),%rax        # 9f30 <_IO_stdin_used+0xf30>
    thread_data[x].io_mode = myring;
    thread_data[x].my_io = myring;
    thread_data[x].other_io = otherring;
    thread_data[x].iomailboxes = iomailboxes; 
    printf("%d myring %d other is %d\n", x, myring, otherring);
    thread_data[x].ring = rings[myring]; 
    37ee:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    thread_data[x].type = IO;
    37f3:	41 c7 47 0c 02 00 00 00 	movl   $0x2,0xc(%r15)
    thread_data[x].task_count = 0;
    37fb:	49 89 47 40          	mov    %rax,0x40(%r15)
    thread_data[x].ring = rings[myring]; 
    37ff:	89 e8                	mov    %ebp,%eax
    3801:	83 e0 01             	and    $0x1,%eax
    3804:	48 8d 1c c3          	lea    (%rbx,%rax,8),%rbx
    if (myring == IO_MODE_SEND) {
    3808:	40 f6 c5 01          	test   $0x1,%bpl
    380c:	0f 84 1e 01 00 00    	je     3930 <main+0x1230>
      thread_data[x].identity = recv_identity;
    3812:	48 8d 05 d4 5d 00 00 	lea    0x5dd4(%rip),%rax        # 95ed <_IO_stdin_used+0x5ed>
    thread_data[x].iomailboxes = iomailboxes; 
    3819:	4d 89 b7 10 01 00 00 	mov    %r14,0x110(%r15)
    3820:	89 ea                	mov    %ebp,%edx
    3822:	45 31 c0             	xor    %r8d,%r8d
    3825:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
    thread_data[x].other_io = otherring;
    382c:	31 c0                	xor    %eax,%eax
    382e:	b9 01 00 00 00       	mov    $0x1,%ecx
    3833:	48 8d 35 99 5d 00 00 	lea    0x5d99(%rip),%rsi        # 95d3 <_IO_stdin_used+0x5d3>
    383a:	41 89 87 18 01 00 00 	mov    %eax,0x118(%r15)
    3841:	bf 01 00 00 00       	mov    $0x1,%edi
    3846:	31 c0                	xor    %eax,%eax
    thread_data[x].io_mode = myring;
    3848:	41 c7 87 0c 01 00 00 01 00 00 00 	movl   $0x1,0x10c(%r15)
    thread_data[x].my_io = myring;
    3853:	41 c7 87 1c 01 00 00 01 00 00 00 	movl   $0x1,0x11c(%r15)
    385e:	e8 6d ec ff ff       	call   24d0 <__printf_chk@plt>
    thread_data[x].ring = rings[myring]; 
    3863:	48 8b 03             	mov    (%rbx),%rax
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3866:	be 00 08 00 00       	mov    $0x800,%esi
    386b:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = rings[myring]; 
    386d:	49 89 47 60          	mov    %rax,0x60(%r15)
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3871:	e8 da ec ff ff       	call   2550 <eventfd@plt>
    if (x % 2 == 0) {
      otherdataeventfd = dataeventfds[0];
      datafd = dataeventfds[1];
    } else {
      otherdataeventfd = dataeventfds[1];
      datafd = dataeventfds[0];
    3876:	8b 14 24             	mov    (%rsp),%edx
      otherdataeventfd = dataeventfds[1];
    3879:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    thread_data[x]._eventfd = myeventfd; 
    387d:	41 89 47 68          	mov    %eax,0x68(%r15)
    3881:	48 8d 35 a0 61 00 00 	lea    0x61a0(%rip),%rsi        # 9a28 <_IO_stdin_used+0xa28>
    3888:	bf 01 00 00 00       	mov    $0x1,%edi
    388d:	31 c0                	xor    %eax,%eax
    388f:	89 4c 24 70          	mov    %ecx,0x70(%rsp)
    3893:	89 54 24 68          	mov    %edx,0x68(%rsp)
    3897:	e8 34 ec ff ff       	call   24d0 <__printf_chk@plt>
    }
    printf("my data event fd is %d other is %d\n", datafd, otherdataeventfd);
    thread_data[x].dataeventfd = datafd; 
    thread_data[x].otherdataeventfd = otherdataeventfd; 
    389c:	8b 4c 24 70          	mov    0x70(%rsp),%ecx
    thread_data[x].dataeventfd = datafd; 
    38a0:	8b 54 24 68          	mov    0x68(%rsp),%edx
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    38a4:	be 08 00 00 00       	mov    $0x8,%esi
    38a9:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x].otherdataeventfd = otherdataeventfd; 
    38ae:	41 89 4f 70          	mov    %ecx,0x70(%r15)
    thread_data[x].dataeventfd = datafd; 
    38b2:	41 89 57 6c          	mov    %edx,0x6c(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    38b6:	e8 65 eb ff ff       	call   2420 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    38bb:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].thread_index = x;
    38c0:	41 89 6f 04          	mov    %ebp,0x4(%r15)
    38c4:	89 ea                	mov    %ebp,%edx
    thread_data[x].threads = my_thread_data;
    38c6:	49 89 47 18          	mov    %rax,0x18(%r15)
    38ca:	48 8d 35 d4 5b 00 00 	lea    0x5bd4(%rip),%rsi        # 94a5 <_IO_stdin_used+0x4a5>
    38d1:	bf 01 00 00 00       	mov    $0x1,%edi
      my_thread_data[n] = &thread_data[n]; 
    38d6:	48 89 18             	mov    %rbx,(%rax)
    38d9:	4c 89 68 08          	mov    %r13,0x8(%rax)
    38dd:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_count = thread_count;
    38df:	41 c7 47 28 02 00 00 00 	movl   $0x2,0x28(%r15)
    38e7:	e8 e4 eb ff ff       	call   24d0 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    38ec:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    38f1:	4c 89 f9             	mov    %r15,%rcx
    38f4:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    38f9:	48 8d 15 00 21 00 00 	lea    0x2100(%rip),%rdx        # 5a00 <io_thread>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    3900:	49 81 c7 30 01 00 00 	add    $0x130,%r15
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3907:	48 89 df             	mov    %rbx,%rdi
    390a:	e8 e1 eb ff ff       	call   24f0 <pthread_create@plt>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    390f:	48 89 d8             	mov    %rbx,%rax
    3912:	48 83 44 24 18 38    	addq   $0x38,0x18(%rsp)
    3918:	48 83 c0 08          	add    $0x8,%rax
    391c:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    3921:	83 fd 03             	cmp    $0x3,%ebp
    3924:	75 7c                	jne    39a2 <main+0x12a2>
    3926:	bd 04 00 00 00       	mov    $0x4,%ebp
    392b:	e9 b7 fe ff ff       	jmp    37e7 <main+0x10e7>
    3930:	48 8d 05 90 5c 00 00 	lea    0x5c90(%rip),%rax        # 95c7 <_IO_stdin_used+0x5c7>
    3937:	31 c9                	xor    %ecx,%ecx
    3939:	89 ea                	mov    %ebp,%edx
    393b:	bf 01 00 00 00       	mov    $0x1,%edi
    3940:	49 89 87 20 01 00 00 	mov    %rax,0x120(%r15)
    3947:	31 c0                	xor    %eax,%eax
    3949:	41 b8 01 00 00 00    	mov    $0x1,%r8d
    394f:	48 8d 35 7d 5c 00 00 	lea    0x5c7d(%rip),%rsi        # 95d3 <_IO_stdin_used+0x5d3>
    thread_data[x].io_mode = myring;
    3956:	41 c7 87 0c 01 00 00 00 00 00 00 	movl   $0x0,0x10c(%r15)
    thread_data[x].my_io = myring;
    3961:	41 c7 87 1c 01 00 00 00 00 00 00 	movl   $0x0,0x11c(%r15)
    thread_data[x].other_io = otherring;
    396c:	41 c7 87 18 01 00 00 01 00 00 00 	movl   $0x1,0x118(%r15)
    thread_data[x].iomailboxes = iomailboxes; 
    3977:	4d 89 b7 10 01 00 00 	mov    %r14,0x110(%r15)
    397e:	e8 4d eb ff ff       	call   24d0 <__printf_chk@plt>
    thread_data[x].ring = rings[myring]; 
    3983:	48 8b 03             	mov    (%rbx),%rax
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3986:	be 00 08 00 00       	mov    $0x800,%esi
    398b:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = rings[myring]; 
    398d:	49 89 47 60          	mov    %rax,0x60(%r15)
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3991:	e8 ba eb ff ff       	call   2550 <eventfd@plt>
      datafd = dataeventfds[1];
    3996:	8b 54 24 08          	mov    0x8(%rsp),%edx
      otherdataeventfd = dataeventfds[0];
    399a:	8b 0c 24             	mov    (%rsp),%ecx
    399d:	e9 db fe ff ff       	jmp    387d <main+0x117d>
    39a2:	ba 05 00 00 00       	mov    $0x5,%edx
    39a7:	48 8d 35 0e 5b 00 00 	lea    0x5b0e(%rip),%rsi        # 94bc <_IO_stdin_used+0x4bc>
    39ae:	bf 01 00 00 00       	mov    $0x1,%edi
    39b3:	31 c0                	xor    %eax,%eax
    39b5:	48 8b 5c 24 58       	mov    0x58(%rsp),%rbx
    39ba:	49 8d 6c 24 28       	lea    0x28(%r12),%rbp
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    39bf:	41 bf 05 00 00 00    	mov    $0x5,%r15d
    39c5:	e8 06 eb ff ff       	call   24d0 <__printf_chk@plt>
    39ca:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    39cf:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    39d4:	48 05 18 01 00 00    	add    $0x118,%rax
    39da:	48 89 04 24          	mov    %rax,(%rsp)
    39de:	44 89 fa             	mov    %r15d,%edx
    39e1:	48 8d 35 ea 5a 00 00 	lea    0x5aea(%rip),%rsi        # 94d2 <_IO_stdin_used+0x4d2>
    39e8:	bf 01 00 00 00       	mov    $0x1,%edi
    39ed:	31 c0                	xor    %eax,%eax
    39ef:	e8 dc ea ff ff       	call   24d0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    39f4:	be 08 00 00 00       	mov    $0x8,%esi
    39f9:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    39fe:	48 8b 05 2b 65 00 00 	mov    0x652b(%rip),%rax        # 9f30 <_IO_stdin_used+0xf30>
    thread_data[x].type = EXTERNAL;
    3a05:	41 c7 46 0c 03 00 00 00 	movl   $0x3,0xc(%r14)
    thread_data[x].task_count = 0;
    3a0d:	49 89 46 40          	mov    %rax,0x40(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3a11:	e8 0a ea ff ff       	call   2420 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3a16:	48 8b bc 24 80 00 00 00 	mov    0x80(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a1e:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3a23:	41 c7 86 cc 00 00 00 01 00 00 00 	movl   $0x1,0xcc(%r14)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3a2e:	49 89 46 50          	mov    %rax,0x50(%r14)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3a32:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a35:	bf 02 00 00 00       	mov    $0x2,%edi
    3a3a:	e8 e1 e9 ff ff       	call   2420 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3a3f:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a44:	4c 89 f1             	mov    %r14,%rcx
    3a47:	48 89 ef             	mov    %rbp,%rdi
    thread_data[x].threads = my_thread_data;
    3a4a:	49 89 46 18          	mov    %rax,0x18(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a4e:	48 8d 15 7b 09 00 00 	lea    0x97b(%rip),%rdx        # 43d0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a55:	48 83 c5 08          	add    $0x8,%rbp
    3a59:	49 81 c6 30 01 00 00 	add    $0x130,%r14
      my_thread_data[n] = &thread_data[n]; 
    3a60:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a63:	48 8b 34 24          	mov    (%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3a67:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3a6b:	48 8b 05 a6 64 00 00 	mov    0x64a6(%rip),%rax        # 9f18 <_IO_stdin_used+0xf18>
    thread_data[x].thread_index = x;
    3a72:	45 89 be d4 fe ff ff 	mov    %r15d,-0x12c(%r14)
    thread_data[x].thread_count = thread_count;
    3a79:	49 89 86 f8 fe ff ff 	mov    %rax,-0x108(%r14)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3a80:	e8 6b ea ff ff       	call   24f0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a85:	48 83 04 24 38       	addq   $0x38,(%rsp)
    3a8a:	48 83 84 24 80 00 00 00 10 	addq   $0x10,0x80(%rsp)
    3a93:	41 83 ff 05          	cmp    $0x5,%r15d
    3a97:	75 2b                	jne    3ac4 <main+0x13c4>
    3a99:	41 bf 06 00 00 00    	mov    $0x6,%r15d
    3a9f:	e9 3a ff ff ff       	jmp    39de <main+0x12de>
        my_thread_data[1] = &thread_data[other]; 
    3aa4:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3aa9:	4c 89 6c 24 50       	mov    %r13,0x50(%rsp)
    3aae:	48 89 da             	mov    %rbx,%rdx
    3ab1:	45 31 c0             	xor    %r8d,%r8d
        other = (x + 1) % total_threads;
    3ab4:	bd 01 00 00 00       	mov    $0x1,%ebp
        my_thread_data[1] = &thread_data[other]; 
    3ab9:	48 05 30 01 00 00    	add    $0x130,%rax
        thread_data[x].protected_state = &protected_state[k];
    3abf:	e9 4b f1 ff ff       	jmp    2c0f <main+0x50f>
    3ac4:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3ac9:	48 8d 2d 1f 5a 00 00 	lea    0x5a1f(%rip),%rbp        # 94ef <_IO_stdin_used+0x4ef>
    3ad0:	4c 8d 70 04          	lea    0x4(%rax),%r14
    3ad4:	4c 8d a8 54 08 00 00 	lea    0x854(%rax),%r13
    3adb:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3adf:	41 8b 16             	mov    (%r14),%edx
    3ae2:	48 89 ee             	mov    %rbp,%rsi
    3ae5:	bf 01 00 00 00       	mov    $0x1,%edi
    3aea:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3aec:	49 81 c6 30 01 00 00 	add    $0x130,%r14
    3af3:	e8 d8 e9 ff ff       	call   24d0 <__printf_chk@plt>
    3af8:	4d 39 ee             	cmp    %r13,%r14
    3afb:	75 de                	jne    3adb <main+0x13db>
    3afd:	48 8d 3d fe 59 00 00 	lea    0x59fe(%rip),%rdi        # 9502 <_IO_stdin_used+0x502>
    3b04:	45 31 f6             	xor    %r14d,%r14d
    3b07:	4c 8d ac 24 b0 00 00 00 	lea    0xb0(%rsp),%r13
    3b0f:	e8 3c e8 ff ff       	call   2350 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3b14:	48 8d 2d 05 5a 00 00 	lea    0x5a05(%rip),%rbp        # 9520 <_IO_stdin_used+0x520>
    void * result; 
    pthread_join(thread[x], &result);
    3b1b:	4b 8b 3c f4          	mov    (%r12,%r14,8),%rdi
    3b1f:	4c 89 ee             	mov    %r13,%rsi
    3b22:	e8 69 ea ff ff       	call   2590 <pthread_join@plt>
    3b27:	44 89 f2             	mov    %r14d,%edx
    3b2a:	48 89 ee             	mov    %rbp,%rsi
    3b2d:	bf 01 00 00 00       	mov    $0x1,%edi
    3b32:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3b34:	49 83 c6 01          	add    $0x1,%r14
    3b38:	e8 93 e9 ff ff       	call   24d0 <__printf_chk@plt>
    3b3d:	49 83 fe 07          	cmp    $0x7,%r14
    3b41:	75 d8                	jne    3b1b <main+0x141b>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3b43:	bf 00 04 00 00       	mov    $0x400,%edi
    3b48:	be 08 00 00 00       	mov    $0x8,%esi
    3b4d:	31 ed                	xor    %ebp,%ebp
    3b4f:	e8 cc e8 ff ff       	call   2420 <calloc@plt>
    3b54:	48 89 df             	mov    %rbx,%rdi
    3b57:	49 89 c6             	mov    %rax,%r14
  int datas2_size = 0; 
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3b5a:	44 8b 47 08          	mov    0x8(%rdi),%r8d
    3b5e:	45 85 c0             	test   %r8d,%r8d
    3b61:	7e 5b                	jle    3bbe <main+0x14be>
    3b63:	48 8b 17             	mov    (%rdi),%rdx
    3b66:	49 63 f0             	movslq %r8d,%rsi
    3b69:	48 63 c5             	movslq %ebp,%rax
    3b6c:	48 c1 e6 09          	shl    $0x9,%rsi
    3b70:	49 8d 0c c6          	lea    (%r14,%rax,8),%rcx
    3b74:	48 01 d6             	add    %rdx,%rsi
    3b77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b80:	48 8b 82 70 01 00 00 	mov    0x170(%rdx),%rax
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3b87:	48 81 c2 00 02 00 00 	add    $0x200,%rdx
    3b8e:	48 83 c1 20          	add    $0x20,%rcx
    3b92:	f3 0f 7e 80 00 01 00 00 	movq   0x100(%rax),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3b9a:	f3 0f 7e 08          	movq   (%rax),%xmm1
    3b9e:	0f 16 80 80 01 00 00 	movhps 0x180(%rax),%xmm0
    3ba5:	0f 16 88 80 00 00 00 	movhps 0x80(%rax),%xmm1
    3bac:	0f 11 49 e0          	movups %xmm1,-0x20(%rcx)
    3bb0:	0f 11 41 f0          	movups %xmm0,-0x10(%rcx)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3bb4:	48 39 f2             	cmp    %rsi,%rdx
    3bb7:	75 c7                	jne    3b80 <main+0x1480>
    3bb9:	42 8d 6c 85 00       	lea    0x0(%rbp,%r8,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3bbe:	48 81 c7 30 01 00 00 	add    $0x130,%rdi
    3bc5:	48 39 7c 24 10       	cmp    %rdi,0x10(%rsp)
    3bca:	75 8e                	jne    3b5a <main+0x145a>
    3bcc:	48 8d 3d 61 59 00 00 	lea    0x5961(%rip),%rdi        # 9534 <_IO_stdin_used+0x534>
    3bd3:	e8 78 e7 ff ff       	call   2350 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3bd8:	48 8d 35 25 58 00 00 	lea    0x5825(%rip),%rsi        # 9404 <_IO_stdin_used+0x404>
    3bdf:	48 8d 3d 66 59 00 00 	lea    0x5966(%rip),%rdi        # 954c <_IO_stdin_used+0x54c>
    3be6:	e8 35 e9 ff ff       	call   2520 <fopen@plt>
    3beb:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas2_size; x++) {
    3bee:	85 ed                	test   %ebp,%ebp
    3bf0:	0f 8e 80 00 00 00    	jle    3c76 <main+0x1576>
    3bf6:	48 8d 05 40 58 00 00 	lea    0x5840(%rip),%rax        # 943d <_IO_stdin_used+0x43d>
    3bfd:	48 63 ed             	movslq %ebp,%rbp
    3c00:	4c 8d 2d 2a 58 00 00 	lea    0x582a(%rip),%r13        # 9431 <_IO_stdin_used+0x431>
    3c07:	48 89 04 24          	mov    %rax,(%rsp)
    3c0b:	48 89 d8             	mov    %rbx,%rax
    3c0e:	4d 8d 24 ee          	lea    (%r14,%rbp,8),%r12
    3c12:	4c 89 f3             	mov    %r14,%rbx
    3c15:	49 89 c6             	mov    %rax,%r14
    char * c = calloc(250, sizeof(char));
    3c18:	be 01 00 00 00       	mov    $0x1,%esi
    3c1d:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3c22:	48 83 c3 08          	add    $0x8,%rbx
    char * c = calloc(250, sizeof(char));
    3c26:	e8 f5 e7 ff ff       	call   2420 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3c2b:	4c 89 e9             	mov    %r13,%rcx
    3c2e:	ba fa 00 00 00       	mov    $0xfa,%edx
    3c33:	be 01 00 00 00       	mov    $0x1,%esi
    3c38:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3c3b:	48 8b 43 f8          	mov    -0x8(%rbx),%rax
    3c3f:	48 89 ef             	mov    %rbp,%rdi
    3c42:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3c49:	31 c0                	xor    %eax,%eax
    3c4b:	e8 90 e9 ff ff       	call   25e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3c50:	48 8b 34 24          	mov    (%rsp),%rsi
    3c54:	48 89 ea             	mov    %rbp,%rdx
    3c57:	31 c0                	xor    %eax,%eax
    3c59:	bf 01 00 00 00       	mov    $0x1,%edi
    3c5e:	e8 6d e8 ff ff       	call   24d0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3c63:	4c 89 fe             	mov    %r15,%rsi
    3c66:	48 89 ef             	mov    %rbp,%rdi
    3c69:	e8 72 e7 ff ff       	call   23e0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3c6e:	4c 39 e3             	cmp    %r12,%rbx
    3c71:	75 a5                	jne    3c18 <main+0x1518>
    3c73:	4c 89 f3             	mov    %r14,%rbx
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    3c76:	4c 89 ff             	mov    %r15,%rdi
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c79:	45 31 ed             	xor    %r13d,%r13d
  fclose(m2);
    3c7c:	45 31 e4             	xor    %r12d,%r12d
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3c7f:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    3c89:	e8 f2 e6 ff ff       	call   2380 <fclose@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c8e:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
  fclose(m2);
    3c93:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
    3c9c:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
    3ca5:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3caa:	48 c7 44 24 10 00 00 00 00 	movq   $0x0,0x10(%rsp)
    3cb3:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3cbc:	bf 0a 00 00 00       	mov    $0xa,%edi
    3cc1:	45 89 ee             	mov    %r13d,%r14d
    3cc4:	e8 67 e6 ff ff       	call   2330 <putchar@plt>
    3cc9:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3cce:	48 8d 35 80 58 00 00 	lea    0x5880(%rip),%rsi        # 9555 <_IO_stdin_used+0x555>
    3cd5:	bf 01 00 00 00       	mov    $0x1,%edi
    3cda:	41 83 f6 01          	xor    $0x1,%r14d
    3cde:	48 8b 10             	mov    (%rax),%rdx
    3ce1:	31 c0                	xor    %eax,%eax
    3ce3:	e8 e8 e7 ff ff       	call   24d0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3ce8:	8b 53 08             	mov    0x8(%rbx),%edx
    3ceb:	85 d2                	test   %edx,%edx
    3ced:	0f 8e f6 04 00 00    	jle    41e9 <main+0x1ae9>
    3cf3:	48 63 ca             	movslq %edx,%rcx
    3cf6:	48 8b 03             	mov    (%rbx),%rax
      long v = 0;
    3cf9:	31 d2                	xor    %edx,%edx
    3cfb:	48 c1 e1 09          	shl    $0x9,%rcx
    3cff:	48 01 c1             	add    %rax,%rcx
    3d02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3d08:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3d0f:	48 05 00 02 00 00    	add    $0x200,%rax
    3d15:	48 39 c8             	cmp    %rcx,%rax
    3d18:	75 ee                	jne    3d08 <main+0x1608>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3d1a:	4c 89 f0             	mov    %r14,%rax
    3d1d:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    3d22:	48 f7 d8             	neg    %rax
    3d25:	25 30 01 00 00       	and    $0x130,%eax
    3d2a:	48 01 f8             	add    %rdi,%rax
    3d2d:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3d31:	85 c9                	test   %ecx,%ecx
    3d33:	7e 1d                	jle    3d52 <main+0x1652>
    3d35:	48 8b 40 38          	mov    0x38(%rax),%rax
    3d39:	48 c1 e1 09          	shl    $0x9,%rcx
    3d3d:	48 01 c1             	add    %rax,%rcx
        v += thread_data[other].tasks[n].v;
    3d40:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3d47:	48 05 00 02 00 00    	add    $0x200,%rax
    3d4d:	48 39 c8             	cmp    %rcx,%rax
    3d50:	75 ee                	jne    3d40 <main+0x1640>
    3d52:	48 8d 35 11 58 00 00 	lea    0x5811(%rip),%rsi        # 956a <_IO_stdin_used+0x56a>
    3d59:	bf 01 00 00 00       	mov    $0x1,%edi
    3d5e:	31 c0                	xor    %eax,%eax
    3d60:	e8 6b e7 ff ff       	call   24d0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3d65:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3d6a:	bf 01 00 00 00       	mov    $0x1,%edi
    3d6f:	48 8d 35 da 5c 00 00 	lea    0x5cda(%rip),%rsi        # 9a50 <_IO_stdin_used+0xa50>
    3d76:	48 8b 08             	mov    (%rax),%rcx
    3d79:	48 b8 4b 59 86 38 d6 c5 6d 34 	movabs $0x346dc5d63886594b,%rax
    3d83:	48 f7 e9             	imul   %rcx
    3d86:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3d8a:	31 c0                	xor    %eax,%eax
    3d8c:	48 c1 fa 0b          	sar    $0xb,%rdx
    3d90:	48 29 ca             	sub    %rcx,%rdx
    3d93:	e8 38 e7 ff ff       	call   24d0 <__printf_chk@plt>
    3d98:	bf 0a 00 00 00       	mov    $0xa,%edi
    3d9d:	e8 8e e5 ff ff       	call   2330 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3da2:	44 8b 73 08          	mov    0x8(%rbx),%r14d
    3da6:	45 85 f6             	test   %r14d,%r14d
    3da9:	0f 8e 3f 01 00 00    	jle    3eee <main+0x17ee>
    3daf:	4c 8b 54 24 28       	mov    0x28(%rsp),%r10
    3db4:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3db9:	44 89 2c 24          	mov    %r13d,(%rsp)
    3dbd:	31 d2                	xor    %edx,%edx
    3dbf:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    3dc4:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    3dc9:	49 89 dd             	mov    %rbx,%r13
    3dcc:	0f 1f 40 00          	nopl   0x0(%rax)
        total += thread_data[x].tasks[n].n;
    3dd0:	49 8b 45 00          	mov    0x0(%r13),%rax
    3dd4:	49 89 d1             	mov    %rdx,%r9
    3dd7:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    3ddc:	89 d3                	mov    %edx,%ebx
    3dde:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    3de2:	45 31 f6             	xor    %r14d,%r14d
        total += thread_data[x].tasks[n].n;
    3de5:	4c 01 c8             	add    %r9,%rax
    3de8:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    3ded:	4c 03 90 08 01 00 00 	add    0x108(%rax),%r10
        ingests += thread_data[x].tasks[n].ingest_count;
    3df4:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
        sends += thread_data[x].tasks[n].sends;
    3dfb:	48 03 b8 80 01 00 00 	add    0x180(%rax),%rdi
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3e02:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    3e07:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3e0c:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3e11:	8b 14 24             	mov    (%rsp),%edx
    3e14:	45 89 f0             	mov    %r14d,%r8d
    3e17:	89 d9                	mov    %ebx,%ecx
    3e19:	48 8d 35 57 57 00 00 	lea    0x5757(%rip),%rsi        # 9577 <_IO_stdin_used+0x577>
    3e20:	bf 01 00 00 00       	mov    $0x1,%edi
    3e25:	31 c0                	xor    %eax,%eax
    3e27:	e8 a4 e6 ff ff       	call   24d0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e2c:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3e31:	4c 89 f0             	mov    %r14,%rax
    3e34:	45 89 f0             	mov    %r14d,%r8d
    3e37:	49 8b 55 00          	mov    0x0(%r13),%rdx
    3e3b:	48 c1 e0 08          	shl    $0x8,%rax
    3e3f:	48 83 ec 08          	sub    $0x8,%rsp
    3e43:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    3e4b:	48 8b 38             	mov    (%rax),%rdi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3e4e:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3e55:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3e5c:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3e63:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e6a:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    3e71:	bf 01 00 00 00       	mov    $0x1,%edi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3e76:	49 01 c4             	add    %rax,%r12
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3e79:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3e7c:	49 01 cf             	add    %rcx,%r15
    3e7f:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3e83:	49 01 f4             	add    %rsi,%r12
    3e86:	50                   	push   %rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3e87:	49 01 d7             	add    %rdx,%r15
    3e8a:	8b 54 24 10          	mov    0x10(%rsp),%edx
    3e8e:	89 d9                	mov    %ebx,%ecx
    3e90:	48 8d 35 d9 5b 00 00 	lea    0x5bd9(%rip),%rsi        # 9a70 <_IO_stdin_used+0xa70>
    3e97:	31 c0                	xor    %eax,%eax
    3e99:	e8 32 e6 ff ff       	call   24d0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3e9e:	41 5a                	pop    %r10
    3ea0:	41 5b                	pop    %r11
    3ea2:	4d 85 f6             	test   %r14,%r14
    3ea5:	75 0a                	jne    3eb1 <main+0x17b1>
    3ea7:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3eac:	e9 60 ff ff ff       	jmp    3e11 <main+0x1711>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3eb1:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    3eb6:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    3ebb:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3ec0:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3ec5:	48 83 c2 01          	add    $0x1,%rdx
    3ec9:	41 39 55 08          	cmp    %edx,0x8(%r13)
    3ecd:	0f 8f fd fe ff ff    	jg     3dd0 <main+0x16d0>
    3ed3:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    3ed8:	4c 89 eb             	mov    %r13,%rbx
    3edb:	44 8b 2c 24          	mov    (%rsp),%r13d
    3edf:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    3ee4:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
    3ee9:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3eee:	45 31 ff             	xor    %r15d,%r15d
    3ef1:	48 83 7b 78 00       	cmpq   $0x0,0x78(%rbx)
    3ef6:	4c 8d 35 93 5b 00 00 	lea    0x5b93(%rip),%r14        # 9a90 <_IO_stdin_used+0xa90>
    3efd:	7e 53                	jle    3f52 <main+0x1852>
    3eff:	90                   	nop
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3f00:	48 8b 43 68          	mov    0x68(%rbx),%rax
    3f04:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    3f08:	48 83 ec 08          	sub    $0x8,%rsp
    3f0c:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3f11:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3f15:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3f19:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3f1d:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3f21:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3f24:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3f28:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3f2b:	48 f7 e5             	mul    %rbp
    3f2e:	8b 49 20             	mov    0x20(%rcx),%ecx
    3f31:	56                   	push   %rsi
    3f32:	31 c0                	xor    %eax,%eax
    3f34:	4c 89 f6             	mov    %r14,%rsi
    3f37:	48 c1 ea 12          	shr    $0x12,%rdx
    3f3b:	49 89 d1             	mov    %rdx,%r9
    3f3e:	ba 02 00 00 00       	mov    $0x2,%edx
    3f43:	e8 88 e5 ff ff       	call   24d0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3f48:	41 58                	pop    %r8
    3f4a:	41 59                	pop    %r9
    3f4c:	4c 39 7b 78          	cmp    %r15,0x78(%rbx)
    3f50:	7f ae                	jg     3f00 <main+0x1800>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    3f52:	8b 93 94 00 00 00    	mov    0x94(%rbx),%edx
    3f58:	85 d2                	test   %edx,%edx
    3f5a:	0f 8e 0a 01 00 00    	jle    406a <main+0x196a>
    3f60:	4c 89 64 24 50       	mov    %r12,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    3f65:	48 8b 7b 18          	mov    0x18(%rbx),%rdi
    3f69:	45 31 ff             	xor    %r15d,%r15d
    3f6c:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    3f71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    3f78:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    3f7c:	45 89 fd             	mov    %r15d,%r13d
    3f7f:	4e 8d 24 fd 00 00 00 00 	lea    0x0(,%r15,8),%r12
    3f87:	8b 30                	mov    (%rax),%esi
    3f89:	85 f6                	test   %esi,%esi
    3f8b:	0f 8e c2 00 00 00    	jle    4053 <main+0x1953>
    3f91:	4c 89 7c 24 08       	mov    %r15,0x8(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3f96:	31 d2                	xor    %edx,%edx
    3f98:	48 8b 48 08          	mov    0x8(%rax),%rcx
    3f9c:	49 89 f8             	mov    %rdi,%r8
    3f9f:	48 89 d7             	mov    %rdx,%rdi
    3fa2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    3fa8:	4c 8d 1c bf          	lea    (%rdi,%rdi,4),%r11
    3fac:	45 31 ff             	xor    %r15d,%r15d
    3faf:	4e 8d 34 dd 00 00 00 00 	lea    0x0(,%r11,8),%r14
    3fb7:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    3fbb:	8b 50 1c             	mov    0x1c(%rax),%edx
    3fbe:	85 d2                	test   %edx,%edx
    3fc0:	7e 77                	jle    4039 <main+0x1939>
    3fc2:	48 89 3c 24          	mov    %rdi,(%rsp)
    3fc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3fd0:	4c 89 f9             	mov    %r15,%rcx
    3fd3:	48 83 ec 08          	sub    $0x8,%rsp
    3fd7:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    3fdc:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    3fe0:	48 c1 e1 05          	shl    $0x5,%rcx
    3fe4:	48 03 48 10          	add    0x10(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3fe8:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3fec:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3ff0:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    3ff3:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    3ff7:	4c 2b 01             	sub    (%rcx),%r8
    3ffa:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    3ffb:	48 f7 e5             	mul    %rbp
    3ffe:	44 89 e9             	mov    %r13d,%ecx
    4001:	48 8d 35 d8 5a 00 00 	lea    0x5ad8(%rip),%rsi        # 9ae0 <_IO_stdin_used+0xae0>
    4008:	31 c0                	xor    %eax,%eax
    400a:	48 c1 ea 12          	shr    $0x12,%rdx
    400e:	49 89 d1             	mov    %rdx,%r9
    4011:	ba 02 00 00 00       	mov    $0x2,%edx
    4016:	e8 b5 e4 ff ff       	call   24d0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    401b:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    401f:	5e                   	pop    %rsi
    4020:	5f                   	pop    %rdi
    4021:	4b 8b 14 20          	mov    (%r8,%r12,1),%rdx
    4025:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    4029:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    402d:	44 39 78 1c          	cmp    %r15d,0x1c(%rax)
    4031:	7f 9d                	jg     3fd0 <main+0x18d0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4033:	48 8b 3c 24          	mov    (%rsp),%rdi
    4037:	8b 32                	mov    (%rdx),%esi
    4039:	48 83 c7 01          	add    $0x1,%rdi
    403d:	39 fe                	cmp    %edi,%esi
    403f:	0f 8f 63 ff ff ff    	jg     3fa8 <main+0x18a8>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4045:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    404a:	8b 93 94 00 00 00    	mov    0x94(%rbx),%edx
    4050:	4c 89 c7             	mov    %r8,%rdi
    4053:	49 83 c7 01          	add    $0x1,%r15
    4057:	44 39 fa             	cmp    %r15d,%edx
    405a:	0f 8f 18 ff ff ff    	jg     3f78 <main+0x1878>
    4060:	4c 8b 64 24 50       	mov    0x50(%rsp),%r12
    4065:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    406a:	48 83 44 24 48 18    	addq   $0x18,0x48(%rsp)
    4070:	48 81 c3 30 01 00 00 	add    $0x130,%rbx
    4077:	45 85 ed             	test   %r13d,%r13d
    407a:	75 0a                	jne    4086 <main+0x1986>
    407c:	44 8b 6c 24 40       	mov    0x40(%rsp),%r13d
    4081:	e9 36 fc ff ff       	jmp    3cbc <main+0x15bc>
    4086:	4c 8b 74 24 28       	mov    0x28(%rsp),%r14
    408b:	48 8d 35 f5 54 00 00 	lea    0x54f5(%rip),%rsi        # 9587 <_IO_stdin_used+0x587>
    4092:	bf 01 00 00 00       	mov    $0x1,%edi
    4097:	31 c0                	xor    %eax,%eax
    4099:	4c 89 f2             	mov    %r14,%rdx
    409c:	e8 2f e4 ff ff       	call   24d0 <__printf_chk@plt>
    40a1:	bf 0a 00 00 00       	mov    $0xa,%edi
    40a6:	e8 85 e2 ff ff       	call   2330 <putchar@plt>
    40ab:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
    40b0:	48 8d 35 81 5a 00 00 	lea    0x5a81(%rip),%rsi        # 9b38 <_IO_stdin_used+0xb38>
    40b7:	31 c0                	xor    %eax,%eax
    40b9:	bf 01 00 00 00       	mov    $0x1,%edi
    40be:	48 8b 53 08          	mov    0x8(%rbx),%rdx
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    40c2:	48 bb 4b 59 86 38 d6 c5 6d 34 	movabs $0x346dc5d63886594b,%rbx
    40cc:	e8 ff e3 ff ff       	call   24d0 <__printf_chk@plt>
    40d1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    40d6:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    40db:	48 8d 35 7e 5a 00 00 	lea    0x5a7e(%rip),%rsi        # 9b60 <_IO_stdin_used+0xb60>
    40e2:	48 f7 eb             	imul   %rbx
    40e5:	48 c1 ff 3f          	sar    $0x3f,%rdi
    40e9:	31 c0                	xor    %eax,%eax
    40eb:	48 c1 fa 0b          	sar    $0xb,%rdx
    40ef:	48 29 fa             	sub    %rdi,%rdx
    40f2:	bf 01 00 00 00       	mov    $0x1,%edi
    40f7:	e8 d4 e3 ff ff       	call   24d0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    40fc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    4101:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    4106:	48 8d 35 83 5a 00 00 	lea    0x5a83(%rip),%rsi        # 9b90 <_IO_stdin_used+0xb90>
    410d:	48 f7 eb             	imul   %rbx
    4110:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4114:	31 c0                	xor    %eax,%eax
    4116:	48 c1 fa 0b          	sar    $0xb,%rdx
    411a:	48 29 fa             	sub    %rdi,%rdx
    411d:	bf 01 00 00 00       	mov    $0x1,%edi
    4122:	e8 a9 e3 ff ff       	call   24d0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    4127:	4c 89 f0             	mov    %r14,%rax
    412a:	bf 01 00 00 00       	mov    $0x1,%edi
    412f:	48 8d 35 8a 5a 00 00 	lea    0x5a8a(%rip),%rsi        # 9bc0 <_IO_stdin_used+0xbc0>
    4136:	48 f7 eb             	imul   %rbx
    4139:	4c 89 f0             	mov    %r14,%rax
    413c:	48 c1 f8 3f          	sar    $0x3f,%rax
    4140:	48 c1 fa 0b          	sar    $0xb,%rdx
    4144:	48 29 c2             	sub    %rax,%rdx
    4147:	31 c0                	xor    %eax,%eax
    4149:	e8 82 e3 ff ff       	call   24d0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    414e:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4153:	bf 01 00 00 00       	mov    $0x1,%edi
    4158:	48 8d 35 3c 54 00 00 	lea    0x543c(%rip),%rsi        # 959b <_IO_stdin_used+0x59b>
    415f:	48 f7 eb             	imul   %rbx
    4162:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4167:	48 c1 f8 3f          	sar    $0x3f,%rax
    416b:	48 c1 fa 0b          	sar    $0xb,%rdx
    416f:	48 29 c2             	sub    %rax,%rdx
    4172:	31 c0                	xor    %eax,%eax
    4174:	48 89 d5             	mov    %rdx,%rbp
    4177:	e8 54 e3 ff ff       	call   24d0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
    417c:	4c 89 e0             	mov    %r12,%rax
    417f:	bf 01 00 00 00       	mov    $0x1,%edi
    4184:	48 8d 35 55 5a 00 00 	lea    0x5a55(%rip),%rsi        # 9be0 <_IO_stdin_used+0xbe0>
    418b:	48 f7 eb             	imul   %rbx
    418e:	4c 89 e0             	mov    %r12,%rax
    4191:	48 c1 f8 3f          	sar    $0x3f,%rax
    4195:	48 89 d3             	mov    %rdx,%rbx
    4198:	48 c1 fb 0b          	sar    $0xb,%rbx
    419c:	48 29 c3             	sub    %rax,%rbx
    419f:	31 c0                	xor    %eax,%eax
    41a1:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    41a4:	48 29 eb             	sub    %rbp,%rbx
    41a7:	e8 24 e3 ff ff       	call   24d0 <__printf_chk@plt>
    41ac:	31 c0                	xor    %eax,%eax
    41ae:	48 89 da             	mov    %rbx,%rdx
    41b1:	bf 01 00 00 00       	mov    $0x1,%edi
    41b6:	48 8d 35 fa 53 00 00 	lea    0x53fa(%rip),%rsi        # 95b7 <_IO_stdin_used+0x5b7>
    41bd:	e8 0e e3 ff ff       	call   24d0 <__printf_chk@plt>
  return 0;

}
    41c2:	48 8b 84 24 b8 00 00 00 	mov    0xb8(%rsp),%rax
    41ca:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    41d3:	75 25                	jne    41fa <main+0x1afa>
    41d5:	48 81 c4 c8 00 00 00 	add    $0xc8,%rsp
    41dc:	31 c0                	xor    %eax,%eax
    41de:	5b                   	pop    %rbx
    41df:	5d                   	pop    %rbp
    41e0:	41 5c                	pop    %r12
    41e2:	41 5d                	pop    %r13
    41e4:	41 5e                	pop    %r14
    41e6:	41 5f                	pop    %r15
    41e8:	c3                   	ret
      long v = 0;
    41e9:	31 d2                	xor    %edx,%edx
    41eb:	e9 2a fb ff ff       	jmp    3d1a <main+0x161a>
            exit(1);
    41f0:	bf 01 00 00 00       	mov    $0x1,%edi
    41f5:	e8 46 e3 ff ff       	call   2540 <exit@plt>
}
    41fa:	e8 a1 e1 ff ff       	call   23a0 <__stack_chk_fail@plt>
    41ff:	90                   	nop

0000000000004200 <_start>:
    4200:	f3 0f 1e fa          	endbr64
    4204:	31 ed                	xor    %ebp,%ebp
    4206:	49 89 d1             	mov    %rdx,%r9
    4209:	5e                   	pop    %rsi
    420a:	48 89 e2             	mov    %rsp,%rdx
    420d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4211:	50                   	push   %rax
    4212:	54                   	push   %rsp
    4213:	45 31 c0             	xor    %r8d,%r8d
    4216:	31 c9                	xor    %ecx,%ecx
    4218:	48 8d 3d e1 e4 ff ff 	lea    -0x1b1f(%rip),%rdi        # 2700 <main>
    421f:	ff 15 b3 7d 00 00    	call   *0x7db3(%rip)        # bfd8 <__libc_start_main@GLIBC_2.34>
    4225:	f4                   	hlt
    4226:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004230 <deregister_tm_clones>:
    4230:	48 8d 3d e9 7d 00 00 	lea    0x7de9(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4237:	48 8d 05 e2 7d 00 00 	lea    0x7de2(%rip),%rax        # c020 <stderr@GLIBC_2.2.5>
    423e:	48 39 f8             	cmp    %rdi,%rax
    4241:	74 15                	je     4258 <deregister_tm_clones+0x28>
    4243:	48 8b 05 96 7d 00 00 	mov    0x7d96(%rip),%rax        # bfe0 <_ITM_deregisterTMCloneTable@Base>
    424a:	48 85 c0             	test   %rax,%rax
    424d:	74 09                	je     4258 <deregister_tm_clones+0x28>
    424f:	ff e0                	jmp    *%rax
    4251:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4258:	c3                   	ret
    4259:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004260 <register_tm_clones>:
    4260:	48 8d 3d b9 7d 00 00 	lea    0x7db9(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4267:	48 8d 35 b2 7d 00 00 	lea    0x7db2(%rip),%rsi        # c020 <stderr@GLIBC_2.2.5>
    426e:	48 29 fe             	sub    %rdi,%rsi
    4271:	48 89 f0             	mov    %rsi,%rax
    4274:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4278:	48 c1 f8 03          	sar    $0x3,%rax
    427c:	48 01 c6             	add    %rax,%rsi
    427f:	48 d1 fe             	sar    %rsi
    4282:	74 14                	je     4298 <register_tm_clones+0x38>
    4284:	48 8b 05 65 7d 00 00 	mov    0x7d65(%rip),%rax        # bff0 <_ITM_registerTMCloneTable@Base>
    428b:	48 85 c0             	test   %rax,%rax
    428e:	74 08                	je     4298 <register_tm_clones+0x38>
    4290:	ff e0                	jmp    *%rax
    4292:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4298:	c3                   	ret
    4299:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000042a0 <__do_global_dtors_aux>:
    42a0:	f3 0f 1e fa          	endbr64
    42a4:	80 3d 7d 7d 00 00 00 	cmpb   $0x0,0x7d7d(%rip)        # c028 <completed.0>
    42ab:	75 2b                	jne    42d8 <__do_global_dtors_aux+0x38>
    42ad:	55                   	push   %rbp
    42ae:	48 83 3d 42 7d 00 00 00 	cmpq   $0x0,0x7d42(%rip)        # bff8 <__cxa_finalize@GLIBC_2.2.5>
    42b6:	48 89 e5             	mov    %rsp,%rbp
    42b9:	74 0c                	je     42c7 <__do_global_dtors_aux+0x27>
    42bb:	48 8b 3d 46 7d 00 00 	mov    0x7d46(%rip),%rdi        # c008 <__dso_handle>
    42c2:	e8 49 e0 ff ff       	call   2310 <__cxa_finalize@plt>
    42c7:	e8 64 ff ff ff       	call   4230 <deregister_tm_clones>
    42cc:	c6 05 55 7d 00 00 01 	movb   $0x1,0x7d55(%rip)        # c028 <completed.0>
    42d3:	5d                   	pop    %rbp
    42d4:	c3                   	ret
    42d5:	0f 1f 00             	nopl   (%rax)
    42d8:	c3                   	ret
    42d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000042e0 <frame_dummy>:
    42e0:	f3 0f 1e fa          	endbr64
    42e4:	e9 77 ff ff ff       	jmp    4260 <register_tm_clones>
    42e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000042f0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    42f0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    42f4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    42fb:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    42ff:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4307:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    430b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    430f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4316:	48 85 c9             	test   %rcx,%rcx
    4319:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4320:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4324:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4328:	31 c0                	xor    %eax,%eax
    432a:	c3                   	ret
    432b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004330 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4330:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4334:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    433b:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    for (int x = 0 ; x < data->task_count ; x++) {
    4342:	85 c9                	test   %ecx,%ecx
    4344:	7e 48                	jle    438e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4346:	48 63 97 30 01 00 00 	movslq 0x130(%rdi),%rdx
    434d:	49 8b 40 18          	mov    0x18(%r8),%rax
    4351:	48 c1 e1 09          	shl    $0x9,%rcx
      data->thread->tasks[x].available = 1; 
    4355:	49 8b 70 38          	mov    0x38(%r8),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4359:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    435d:	48 8b 50 38          	mov    0x38(%rax),%rdx
      data->thread->tasks[x].available = 1; 
    4361:	31 c0                	xor    %eax,%eax
    4363:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4368:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4370:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4378:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    4383:	48 05 00 02 00 00    	add    $0x200,%rax
    4389:	48 39 c1             	cmp    %rax,%rcx
    438c:	75 da                	jne    4368 <barriered_reset+0x38>
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    438e:	49 8b 88 00 01 00 00 	mov    0x100(%r8),%rcx
    4395:	8b 01                	mov    (%rcx),%eax
    4397:	83 f8 ff             	cmp    $0xffffffff,%eax
    439a:	74 0e                	je     43aa <barriered_reset+0x7a>
    439c:	41 8b b8 d0 00 00 00 	mov    0xd0(%r8),%edi
    43a3:	8d 57 ff             	lea    -0x1(%rdi),%edx
    43a6:	39 d0                	cmp    %edx,%eax
    43a8:	74 06                	je     43b0 <barriered_reset+0x80>
}
    43aa:	31 c0                	xor    %eax,%eax
    43ac:	c3                   	ret
    43ad:	0f 1f 00             	nopl   (%rax)
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    43b0:	41 83 78 04 01       	cmpl   $0x1,0x4(%r8)
    43b5:	75 f3                	jne    43aa <barriered_reset+0x7a>
    data->thread->group_data->arrived++;
    43b7:	49 8b 80 e8 00 00 00 	mov    0xe8(%r8),%rax
    43be:	83 00 01             	addl   $0x1,(%rax)
    data->thread->global->request_group_sync = -1;
    43c1:	c7 01 ff ff ff ff    	movl   $0xffffffff,(%rcx)
    43c7:	eb e1                	jmp    43aa <barriered_reset+0x7a>
    43c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000043d0 <external_thread>:
void * external_thread(void *arg) {
    43d0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    43d4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    43d8:	0f 85 ec 00 00 00    	jne    44ca <external_thread+0xfa>
void * external_thread(void *arg) {
    43de:	41 57                	push   %r15
    43e0:	4c 8d 3d 1d 4c 00 00 	lea    0x4c1d(%rip),%r15        # 9004 <_IO_stdin_used+0x4>
    43e7:	41 56                	push   %r14
    43e9:	49 89 fe             	mov    %rdi,%r14
    43ec:	41 55                	push   %r13
    43ee:	41 54                	push   %r12
    43f0:	55                   	push   %rbp
    43f1:	53                   	push   %rbx
    43f2:	48 83 ec 08          	sub    $0x8,%rsp
    43f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int b = 0; b < data->buffers_count; b++) {
    4400:	41 8b 8e cc 00 00 00 	mov    0xcc(%r14),%ecx
    4407:	85 c9                	test   %ecx,%ecx
    4409:	7e 55                	jle    4460 <external_thread+0x90>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    440b:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    440f:	45 31 ed             	xor    %r13d,%r13d
    4412:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4418:	4e 8d 24 ed 00 00 00 00 	lea    0x0(,%r13,8),%r12
    4420:	31 db                	xor    %ebx,%ebx
    4422:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    4426:	48 8b 06             	mov    (%rsi),%rax
    4429:	8b 10                	mov    (%rax),%edx
    442b:	85 d2                	test   %edx,%edx
    442d:	7e 28                	jle    4457 <external_thread+0x87>
    442f:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    4433:	48 8d 2c 9b          	lea    (%rbx,%rbx,4),%rbp
    4437:	48 c1 e5 03          	shl    $0x3,%rbp
    443b:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    443f:	44 8b 40 08          	mov    0x8(%rax),%r8d
    4443:	45 85 c0             	test   %r8d,%r8d
    4446:	74 38                	je     4480 <external_thread+0xb0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4448:	48 83 c3 01          	add    $0x1,%rbx
    444c:	39 da                	cmp    %ebx,%edx
    444e:	7f e3                	jg     4433 <external_thread+0x63>
    for (int b = 0; b < data->buffers_count; b++) {
    4450:	41 8b 8e cc 00 00 00 	mov    0xcc(%r14),%ecx
    4457:	49 83 c5 01          	add    $0x1,%r13
    445b:	44 39 e9             	cmp    %r13d,%ecx
    445e:	7f b8                	jg     4418 <external_thread+0x48>
  while (data->running == 1) {
    4460:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    4465:	74 99                	je     4400 <external_thread+0x30>
}
    4467:	48 83 c4 08          	add    $0x8,%rsp
    446b:	31 c0                	xor    %eax,%eax
    446d:	5b                   	pop    %rbx
    446e:	5d                   	pop    %rbp
    446f:	41 5c                	pop    %r12
    4471:	41 5d                	pop    %r13
    4473:	41 5e                	pop    %r14
    4475:	41 5f                	pop    %r15
    4477:	c3                   	ret
    4478:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    4480:	4c 89 38             	mov    %r15,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    4483:	48 8b 06             	mov    (%rsi),%rax
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4486:	48 83 c3 01          	add    $0x1,%rbx
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    448a:	48 8b 78 08          	mov    0x8(%rax),%rdi
    448e:	48 01 ef             	add    %rbp,%rdi
    4491:	48 63 77 1c          	movslq 0x1c(%rdi),%rsi
    4495:	48 c1 e6 05          	shl    $0x5,%rsi
    4499:	48 03 77 10          	add    0x10(%rdi),%rsi
    449d:	bf 04 00 00 00       	mov    $0x4,%edi
    44a2:	e8 c9 de ff ff       	call   2370 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    44a7:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    44ab:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    44af:	48 8b 06             	mov    (%rsi),%rax
    44b2:	48 8b 50 08          	mov    0x8(%rax),%rdx
    44b6:	c7 44 2a 08 01 00 00 00 	movl   $0x1,0x8(%rdx,%rbp,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
    44be:	8b 10                	mov    (%rax),%edx
    44c0:	39 da                	cmp    %ebx,%edx
    44c2:	0f 8f 67 ff ff ff    	jg     442f <external_thread+0x5f>
    44c8:	eb 86                	jmp    4450 <external_thread+0x80>
}
    44ca:	31 c0                	xor    %eax,%eax
    44cc:	c3                   	ret
    44cd:	0f 1f 00             	nopl   (%rax)

00000000000044d0 <timer_thread>:
void* timer_thread(void *arg) {
    44d0:	f3 0f 1e fa          	endbr64
    44d4:	41 57                	push   %r15
    44d6:	48 8d 35 33 4b 00 00 	lea    0x4b33(%rip),%rsi        # 9010 <_IO_stdin_used+0x10>
    44dd:	49 89 ff             	mov    %rdi,%r15
    44e0:	41 56                	push   %r14
    44e2:	41 55                	push   %r13
    44e4:	41 54                	push   %r12
    44e6:	55                   	push   %rbp
    44e7:	53                   	push   %rbx
    44e8:	48 83 ec 58          	sub    $0x58,%rsp
    44ec:	8b 57 04             	mov    0x4(%rdi),%edx
    44ef:	bf 01 00 00 00       	mov    $0x1,%edi
    44f4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    44fd:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    4502:	31 c0                	xor    %eax,%eax
    4504:	e8 c7 df ff ff       	call   24d0 <__printf_chk@plt>
  struct timespec preempt = {
    4509:	66 0f 6f 05 ef 58 00 00 	movdqa 0x58ef(%rip),%xmm0        # 9e00 <_IO_stdin_used+0xe00>
    4511:	ba 80 96 98 00       	mov    $0x989680,%edx
    4516:	31 c0                	xor    %eax,%eax
    4518:	48 8d 35 03 4b 00 00 	lea    0x4b03(%rip),%rsi        # 9022 <_IO_stdin_used+0x22>
    451f:	bf 01 00 00 00       	mov    $0x1,%edi
    4524:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4529:	e8 a2 df ff ff       	call   24d0 <__printf_chk@plt>
  while (data->running && n < times) {
    452e:	41 8b 47 44          	mov    0x44(%r15),%eax
    4532:	89 c3                	mov    %eax,%ebx
    4534:	85 c0                	test   %eax,%eax
    4536:	0f 84 97 00 00 00    	je     45d3 <timer_thread+0x103>
  int n = 0;
    453c:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    453f:	31 db                	xor    %ebx,%ebx
    4541:	49 89 e5             	mov    %rsp,%r13
    y++;
    4544:	31 ed                	xor    %ebp,%ebp
    4546:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    nanosleep(&preempt , &rem2);
    454b:	4c 89 e7             	mov    %r12,%rdi
    454e:	4c 89 ee             	mov    %r13,%rsi
    n++;
    4551:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    4555:	e8 66 de ff ff       	call   23c0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    455a:	49 63 47 30          	movslq 0x30(%r15),%rax
    y++;
    455e:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4561:	85 c0                	test   %eax,%eax
    4563:	7e 4a                	jle    45af <timer_thread+0xdf>
    4565:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4569:	4c 63 c3             	movslq %ebx,%r8
    456c:	49 c1 e0 09          	shl    $0x9,%r8
    4570:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4574:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4578:	48 8b 19             	mov    (%rcx),%rbx
    457b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    457d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4581:	99                   	cltd
    4582:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4585:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4589:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    458c:	48 63 d2             	movslq %edx,%rdx
    458f:	48 c1 e2 09          	shl    $0x9,%rdx
    4593:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    459e:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    45aa:	49 39 c9             	cmp    %rcx,%r9
    45ad:	75 c9                	jne    4578 <timer_thread+0xa8>
    if (y >= data->threads[0]->task_count) {
    45af:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
    45b3:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    y++;
    45b7:	89 fb                	mov    %edi,%ebx
    if (y >= data->threads[0]->task_count) {
    45b9:	48 8b 00             	mov    (%rax),%rax
    y++;
    45bc:	39 78 40             	cmp    %edi,0x40(%rax)
    45bf:	0f 4e dd             	cmovle %ebp,%ebx
  while (data->running && n < times) {
    45c2:	85 c9                	test   %ecx,%ecx
    45c4:	74 0d                	je     45d3 <timer_thread+0x103>
    45c6:	41 81 fe 80 96 98 00 	cmp    $0x989680,%r14d
    45cd:	0f 85 78 ff ff ff    	jne    454b <timer_thread+0x7b>
    45d3:	48 8d 3d 5e 4a 00 00 	lea    0x4a5e(%rip),%rdi        # 9038 <_IO_stdin_used+0x38>
    45da:	e8 71 dd ff ff       	call   2350 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    45df:	49 63 57 30          	movslq 0x30(%r15),%rdx
    45e3:	85 d2                	test   %edx,%edx
    45e5:	7e 6e                	jle    4655 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    45e7:	49 63 47 40          	movslq 0x40(%r15),%rax
    45eb:	85 c0                	test   %eax,%eax
    45ed:	7e 66                	jle    4655 <timer_thread+0x185>
    45ef:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    45f3:	4d 8b 47 18          	mov    0x18(%r15),%r8
    45f7:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    45ff:	31 c9                	xor    %ecx,%ecx
    4601:	48 89 c6             	mov    %rax,%rsi
    4604:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4608:	48 8b 40 38          	mov    0x38(%rax),%rax
    460c:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4610:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4616:	74 18                	je     4630 <timer_thread+0x160>
    4618:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4622:	48 05 00 02 00 00    	add    $0x200,%rax
    4628:	48 39 c2             	cmp    %rax,%rdx
    462b:	74 1f                	je     464c <timer_thread+0x17c>
    462d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->tasks[y].sending = 0;
    4630:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    463a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4640:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4647:	48 39 c2             	cmp    %rax,%rdx
    464a:	75 e4                	jne    4630 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    464c:	48 83 c1 08          	add    $0x8,%rcx
    4650:	48 39 cf             	cmp    %rcx,%rdi
    4653:	75 af                	jne    4604 <timer_thread+0x134>
  struct timespec drain = {
    4655:	66 0f 6f 05 b3 57 00 00 	movdqa 0x57b3(%rip),%xmm0        # 9e10 <_IO_stdin_used+0xe10>
    465d:	41 89 dc             	mov    %ebx,%r12d
    4660:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4665:	49 63 47 28          	movslq 0x28(%r15),%rax
    y++;
    4669:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    466e:	85 c0                	test   %eax,%eax
    4670:	7e 49                	jle    46bb <timer_thread+0x1eb>
    4672:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4676:	49 63 ec             	movslq %r12d,%rbp
    4679:	48 c1 e5 09          	shl    $0x9,%rbp
    467d:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4681:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4688:	48 8b 19             	mov    (%rcx),%rbx
    468b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    468d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4691:	99                   	cltd
    4692:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4695:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4699:	48 63 d2             	movslq %edx,%rdx
    469c:	48 c1 e2 09          	shl    $0x9,%rdx
    46a0:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    46ab:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    46b6:	49 39 c8             	cmp    %rcx,%r8
    46b9:	75 cd                	jne    4688 <timer_thread+0x1b8>
    if (y >= data->threads[0]->task_count) {
    46bb:	49 8b 77 18          	mov    0x18(%r15),%rsi
    y++;
    46bf:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    46c2:	48 8b 06             	mov    (%rsi),%rax
    y++;
    46c5:	39 78 40             	cmp    %edi,0x40(%rax)
    46c8:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46cc:	41 8b 7f 30          	mov    0x30(%r15),%edi
    46d0:	85 ff                	test   %edi,%edi
    46d2:	0f 8e ac 01 00 00    	jle    4884 <timer_thread+0x3b4>
    46d8:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    46db:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    46e1:	4c 89 f5             	mov    %r14,%rbp
    46e4:	0f 1f 40 00          	nopl   0x0(%rax)
    46e8:	89 eb                	mov    %ebp,%ebx
      for (int y = 0 ; y < 2 ; y++) {
    46ea:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    46f2:	45 31 f6             	xor    %r14d,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    46f5:	85 ff                	test   %edi,%edi
    46f7:	7e 7f                	jle    4778 <timer_thread+0x2a8>
    46f9:	4c 89 f6             	mov    %r14,%rsi
    46fc:	48 63 cf             	movslq %edi,%rcx
    46ff:	45 31 c0             	xor    %r8d,%r8d
    4702:	48 c1 e6 09          	shl    $0x9,%rsi
    4706:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (x == k) { continue; }
    4710:	41 39 e8             	cmp    %ebp,%r8d
    4713:	74 45                	je     475a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4715:	49 8b 47 18          	mov    0x18(%r15),%rax
    4719:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    471d:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4721:	4c 89 c0             	mov    %r8,%rax
    4724:	48 c1 e0 08          	shl    $0x8,%rax
    4728:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4730:	48 8b 10             	mov    (%rax),%rdx
    4733:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    473a:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4741:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4748:	4d 85 c9             	test   %r9,%r9
    474b:	0f 8f 97 00 00 00    	jg     47e8 <timer_thread+0x318>
    4751:	4d 85 db             	test   %r11,%r11
    4754:	0f 8f 8e 00 00 00    	jg     47e8 <timer_thread+0x318>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    475a:	49 83 c0 01          	add    $0x1,%r8
    475e:	4c 39 c1             	cmp    %r8,%rcx
    4761:	75 ad                	jne    4710 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    4763:	49 83 fe 01          	cmp    $0x1,%r14
    4767:	74 0f                	je     4778 <timer_thread+0x2a8>
    4769:	41 be 01 00 00 00    	mov    $0x1,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    476f:	85 ff                	test   %edi,%edi
    4771:	7f 86                	jg     46f9 <timer_thread+0x229>
    4773:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4778:	48 83 c5 01          	add    $0x1,%rbp
    477c:	39 ef                	cmp    %ebp,%edi
    477e:	0f 8f 64 ff ff ff    	jg     46e8 <timer_thread+0x218>
    4784:	44 89 d5             	mov    %r10d,%ebp
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4787:	85 ff                	test   %edi,%edi
    4789:	7e 3b                	jle    47c6 <timer_thread+0x2f6>
    478b:	31 db                	xor    %ebx,%ebx
    int all_waited = 1;
    478d:	bf 01 00 00 00       	mov    $0x1,%edi
    4792:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4796:	41 8b 57 40          	mov    0x40(%r15),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    479a:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    479e:	48 8b 40 38          	mov    0x38(%rax),%rax
    47a2:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    47a8:	39 d1                	cmp    %edx,%ecx
    47aa:	0f 8c a8 00 00 00    	jl     4858 <timer_thread+0x388>
    47b0:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    47b6:	39 d0                	cmp    %edx,%eax
    47b8:	7c 6e                	jl     4828 <timer_thread+0x358>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    47ba:	48 83 c3 01          	add    $0x1,%rbx
    47be:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    47c2:	7f d6                	jg     479a <timer_thread+0x2ca>
    47c4:	21 fd                	and    %edi,%ebp
    if (all_empty == 1 && all_waited == 1) {
    47c6:	85 ed                	test   %ebp,%ebp
    47c8:	0f 85 b6 00 00 00    	jne    4884 <timer_thread+0x3b4>
      nanosleep(&drain , &drainrem);
    47ce:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    47d3:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    47d8:	e8 e3 db ff ff       	call   23c0 <nanosleep@plt>
    47dd:	e9 83 fe ff ff       	jmp    4665 <timer_thread+0x195>
    47e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    47e8:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    47ee:	48 83 ec 08          	sub    $0x8,%rsp
    47f2:	bf 01 00 00 00       	mov    $0x1,%edi
    47f7:	44 89 f1             	mov    %r14d,%ecx
    47fa:	48 8d 35 5c 48 00 00 	lea    0x485c(%rip),%rsi        # 905d <_IO_stdin_used+0x5d>
    4801:	50                   	push   %rax
    4802:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    4808:	89 da                	mov    %ebx,%edx
    480a:	50                   	push   %rax
    480b:	31 c0                	xor    %eax,%eax
    480d:	41 53                	push   %r11
    480f:	e8 bc dc ff ff       	call   24d0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4814:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4818:	48 83 c4 20          	add    $0x20,%rsp
            all_empty = 0;
    481c:	45 31 d2             	xor    %r10d,%r10d
    481f:	e9 3f ff ff ff       	jmp    4763 <timer_thread+0x293>
    4824:	0f 1f 40 00          	nopl   0x0(%rax)
    4828:	89 c2                	mov    %eax,%edx
    482a:	bf 01 00 00 00       	mov    $0x1,%edi
    482f:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4831:	48 83 c3 01          	add    $0x1,%rbx
    4835:	48 8d 35 ec 4a 00 00 	lea    0x4aec(%rip),%rsi        # 9328 <_IO_stdin_used+0x328>
    483c:	e8 8f dc ff ff       	call   24d0 <__printf_chk@plt>
          all_waited = 0; 
    4841:	31 ff                	xor    %edi,%edi
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4843:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4847:	0f 8f 45 ff ff ff    	jg     4792 <timer_thread+0x2c2>
    484d:	e9 72 ff ff ff       	jmp    47c4 <timer_thread+0x2f4>
    4852:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4858:	89 ca                	mov    %ecx,%edx
    485a:	48 8d 35 c7 4a 00 00 	lea    0x4ac7(%rip),%rsi        # 9328 <_IO_stdin_used+0x328>
    4861:	bf 01 00 00 00       	mov    $0x1,%edi
    4866:	31 c0                	xor    %eax,%eax
    4868:	e8 63 dc ff ff       	call   24d0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    486d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4871:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    4875:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4877:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    487b:	48 8b 40 38          	mov    0x38(%rax),%rax
    487f:	e9 2c ff ff ff       	jmp    47b0 <timer_thread+0x2e0>
    4884:	48 8d 3d c9 47 00 00 	lea    0x47c9(%rip),%rdi        # 9054 <_IO_stdin_used+0x54>
    488b:	e8 c0 da ff ff       	call   2350 <puts@plt>
  while (data->running) {
    4890:	41 8b 57 44          	mov    0x44(%r15),%edx
    4894:	85 d2                	test   %edx,%edx
    4896:	0f 84 e8 00 00 00    	je     4984 <timer_thread+0x4b4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    489c:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    48a0:	31 db                	xor    %ebx,%ebx
    48a2:	48 8d 2d d1 47 00 00 	lea    0x47d1(%rip),%rbp        # 907a <_IO_stdin_used+0x7a>
    48a9:	4c 8d 25 e5 47 00 00 	lea    0x47e5(%rip),%r12        # 9095 <_IO_stdin_used+0x95>
    48b0:	85 c0                	test   %eax,%eax
    48b2:	7e 38                	jle    48ec <timer_thread+0x41c>
    48b4:	0f 1f 40 00          	nopl   0x0(%rax)
    48b8:	31 c0                	xor    %eax,%eax
    48ba:	89 da                	mov    %ebx,%edx
    48bc:	48 89 ee             	mov    %rbp,%rsi
    48bf:	bf 01 00 00 00       	mov    $0x1,%edi
    48c4:	e8 07 dc ff ff       	call   24d0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    48c9:	49 8b 47 18          	mov    0x18(%r15),%rax
    48cd:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    48d1:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    48d5:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    48dc:	0f 84 cf 00 00 00    	je     49b1 <timer_thread+0x4e1>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    48e2:	48 83 c3 01          	add    $0x1,%rbx
    48e6:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    48ea:	7f cc                	jg     48b8 <timer_thread+0x3e8>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48ec:	49 63 57 30          	movslq 0x30(%r15),%rdx
    48f0:	85 d2                	test   %edx,%edx
    48f2:	7e 7c                	jle    4970 <timer_thread+0x4a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    48f4:	41 8b 47 40          	mov    0x40(%r15),%eax
    48f8:	85 c0                	test   %eax,%eax
    48fa:	7e 74                	jle    4970 <timer_thread+0x4a0>
    48fc:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    48ff:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4903:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    490b:	31 c9                	xor    %ecx,%ecx
    490d:	48 c1 e6 09          	shl    $0x9,%rsi
    4911:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4918:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    491c:	48 8b 40 38          	mov    0x38(%rax),%rax
    4920:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4924:	f7 c6 00 02 00 00    	test   $0x200,%esi
    492a:	74 1c                	je     4948 <timer_thread+0x478>
    492c:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4936:	48 05 00 02 00 00    	add    $0x200,%rax
    493c:	48 39 d0             	cmp    %rdx,%rax
    493f:	74 26                	je     4967 <timer_thread+0x497>
    4941:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4948:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4952:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4958:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4962:	48 39 d0             	cmp    %rdx,%rax
    4965:	75 e1                	jne    4948 <timer_thread+0x478>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4967:	48 83 c1 08          	add    $0x8,%rcx
    496b:	48 39 cf             	cmp    %rcx,%rdi
    496e:	75 a8                	jne    4918 <timer_thread+0x448>
    4970:	48 8d 3d 30 47 00 00 	lea    0x4730(%rip),%rdi        # 90a7 <_IO_stdin_used+0xa7>
    4977:	e8 d4 d9 ff ff       	call   2350 <puts@plt>
    data->running = 0;
    497c:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4984:	48 8d 3d 23 47 00 00 	lea    0x4723(%rip),%rdi        # 90ae <_IO_stdin_used+0xae>
    498b:	e8 c0 d9 ff ff       	call   2350 <puts@plt>
}
    4990:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4995:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    499e:	75 41                	jne    49e1 <timer_thread+0x511>
    49a0:	48 83 c4 58          	add    $0x58,%rsp
    49a4:	31 c0                	xor    %eax,%eax
    49a6:	5b                   	pop    %rbx
    49a7:	5d                   	pop    %rbp
    49a8:	41 5c                	pop    %r12
    49aa:	41 5d                	pop    %r13
    49ac:	41 5e                	pop    %r14
    49ae:	41 5f                	pop    %r15
    49b0:	c3                   	ret
    49b1:	4c 89 e7             	mov    %r12,%rdi
    49b4:	e8 97 d9 ff ff       	call   2350 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    49b9:	49 8b 47 18          	mov    0x18(%r15),%rax
    49bd:	be 01 00 00 00       	mov    $0x1,%esi
    49c2:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    49c6:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    49ca:	8b 78 68             	mov    0x68(%rax),%edi
    49cd:	e8 ae da ff ff       	call   2480 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    49d2:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    49d6:	0f 8f dc fe ff ff    	jg     48b8 <timer_thread+0x3e8>
    49dc:	e9 0b ff ff ff       	jmp    48ec <timer_thread+0x41c>
}
    49e1:	e8 ba d9 ff ff       	call   23a0 <__stack_chk_fail@plt>
    49e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000049f0 <minf>:
int minf(int a, int b) {
    49f0:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    49f4:	39 f7                	cmp    %esi,%edi
    49f6:	89 f0                	mov    %esi,%eax
    49f8:	0f 4e c7             	cmovle %edi,%eax
}
    49fb:	c3                   	ret
    49fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a00 <maxf>:
int maxf(int a, int b) {
    4a00:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    4a04:	39 f7                	cmp    %esi,%edi
    4a06:	89 f0                	mov    %esi,%eax
    4a08:	0f 4d c7             	cmovge %edi,%eax
}
    4a0b:	c3                   	ret
    4a0c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a10 <strtolower>:
void strtolower(char *str) {
    4a10:	f3 0f 1e fa          	endbr64
    4a14:	55                   	push   %rbp
    4a15:	53                   	push   %rbx
    4a16:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    4a1a:	48 0f be 1f          	movsbq (%rdi),%rbx
    4a1e:	84 db                	test   %bl,%bl
    4a20:	74 24                	je     4a46 <strtolower+0x36>
    4a22:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4a25:	e8 a6 db ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    4a2a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a30:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4a33:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4a37:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4a3a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    4a3d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4a42:	84 db                	test   %bl,%bl
    4a44:	75 ea                	jne    4a30 <strtolower+0x20>
}
    4a46:	48 83 c4 08          	add    $0x8,%rsp
    4a4a:	5b                   	pop    %rbx
    4a4b:	5d                   	pop    %rbp
    4a4c:	c3                   	ret
    4a4d:	0f 1f 00             	nopl   (%rax)

0000000000004a50 <zh_malloc>:
void *zh_malloc(size_t size) {
    4a50:	f3 0f 1e fa          	endbr64
    4a54:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4a58:	e8 33 da ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    4a5d:	48 85 c0             	test   %rax,%rax
    4a60:	74 05                	je     4a67 <zh_malloc+0x17>
}
    4a62:	48 83 c4 08          	add    $0x8,%rsp
    4a66:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4a67:	48 8b 0d b2 75 00 00 	mov    0x75b2(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    4a6e:	ba 28 00 00 00       	mov    $0x28,%edx
    4a73:	be 01 00 00 00       	mov    $0x1,%esi
    4a78:	48 8d 3d 81 4b 00 00 	lea    0x4b81(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    4a7f:	e8 dc da ff ff       	call   2560 <fwrite@plt>
        exit(1);
    4a84:	bf 01 00 00 00       	mov    $0x1,%edi
    4a89:	e8 b2 da ff ff       	call   2540 <exit@plt>
    4a8e:	66 90                	xchg   %ax,%ax

0000000000004a90 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4a90:	f3 0f 1e fa          	endbr64
    4a94:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4a95:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4a9a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4a9d:	e8 2e d9 ff ff       	call   23d0 <strrchr@plt>
    if (!dot || dot == filename)
    4aa2:	48 85 c0             	test   %rax,%rax
    4aa5:	74 11                	je     4ab8 <get_filename_ext+0x28>
    4aa7:	48 39 c3             	cmp    %rax,%rbx
    4aaa:	74 0c                	je     4ab8 <get_filename_ext+0x28>
    return dot + 1;
    4aac:	48 83 c0 01          	add    $0x1,%rax
}
    4ab0:	5b                   	pop    %rbx
    4ab1:	c3                   	ret
    4ab2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4ab8:	48 8d 05 37 46 00 00 	lea    0x4637(%rip),%rax        # 90f6 <_IO_stdin_used+0xf6>
}
    4abf:	5b                   	pop    %rbx
    4ac0:	c3                   	ret
    4ac1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4acc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004ad0 <send_headers>:
void send_headers(struct KernelThread *data, struct Buffers *buffers, const char *path, off_t len, struct iovec *iov) {
    4ad0:	f3 0f 1e fa          	endbr64
    4ad4:	41 55                	push   %r13
    4ad6:	48 89 d6             	mov    %rdx,%rsi
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ad9:	ba 00 04 00 00       	mov    $0x400,%edx
    4ade:	49 89 cd             	mov    %rcx,%r13
    4ae1:	41 54                	push   %r12
    4ae3:	55                   	push   %rbp
    4ae4:	4c 89 c5             	mov    %r8,%rbp
    4ae7:	53                   	push   %rbx
    4ae8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4aef:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4af8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4b00:	31 c0                	xor    %eax,%eax
    4b02:	49 89 e4             	mov    %rsp,%r12
    4b05:	4c 89 e7             	mov    %r12,%rdi
    4b08:	e8 a3 d9 ff ff       	call   24b0 <__strcpy_chk@plt>
    for (; *str; ++str)
    4b0d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4b12:	84 db                	test   %bl,%bl
    4b14:	74 24                	je     4b3a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4b16:	e8 b5 da ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    4b1b:	48 8b 08             	mov    (%rax),%rcx
    4b1e:	4c 89 e0             	mov    %r12,%rax
    4b21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4b28:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4b2b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4b2f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4b32:	48 0f be 18          	movsbq (%rax),%rbx
    4b36:	84 db                	test   %bl,%bl
    4b38:	75 ee                	jne    4b28 <send_headers+0x58>
    void *buf = malloc(size);
    4b3a:	bf 11 00 00 00       	mov    $0x11,%edi
    4b3f:	e8 4c d9 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    4b44:	48 85 c0             	test   %rax,%rax
    4b47:	0f 84 7e 04 00 00    	je     4fcb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4b4d:	66 0f 6f 05 cb 52 00 00 	movdqa 0x52cb(%rip),%xmm0        # 9e20 <_IO_stdin_used+0xe20>
    iov[0].iov_base = zh_malloc(slen);
    4b55:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4b59:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4b5e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4b66:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4b6a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4b6d:	e8 1e d9 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    4b72:	48 85 c0             	test   %rax,%rax
    4b75:	0f 84 50 04 00 00    	je     4fcb <send_headers+0x4fb>
    4b7b:	66 0f 6f 05 ad 52 00 00 	movdqa 0x52ad(%rip),%xmm0        # 9e30 <_IO_stdin_used+0xe30>
    iov[1].iov_base = zh_malloc(slen);
    4b83:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4b87:	4c 89 e7             	mov    %r12,%rdi
    4b8a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4b94:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4b9c:	0f 11 00             	movups %xmm0,(%rax)
    4b9f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4ba3:	be 2e 00 00 00       	mov    $0x2e,%esi
    4ba8:	e8 23 d8 ff ff       	call   23d0 <strrchr@plt>
    if (!dot || dot == filename)
    4bad:	48 85 c0             	test   %rax,%rax
    4bb0:	0f 84 ea 02 00 00    	je     4ea0 <send_headers+0x3d0>
    4bb6:	4c 39 e0             	cmp    %r12,%rax
    4bb9:	0f 84 e1 02 00 00    	je     4ea0 <send_headers+0x3d0>
    return dot + 1;
    4bbf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4bc3:	48 8d 3d fa 44 00 00 	lea    0x44fa(%rip),%rdi        # 90c4 <_IO_stdin_used+0xc4>
    4bca:	48 89 de             	mov    %rbx,%rsi
    4bcd:	e8 5e d8 ff ff       	call   2430 <strcmp@plt>
    4bd2:	85 c0                	test   %eax,%eax
    4bd4:	75 20                	jne    4bf6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4bd6:	66 0f 6f 05 62 52 00 00 	movdqa 0x5262(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4bde:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4be6:	66 0f 6f 05 62 52 00 00 	movdqa 0x5262(%rip),%xmm0        # 9e50 <_IO_stdin_used+0xe50>
    4bee:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4bf6:	48 89 de             	mov    %rbx,%rsi
    4bf9:	48 8d 3d c8 44 00 00 	lea    0x44c8(%rip),%rdi        # 90c8 <_IO_stdin_used+0xc8>
    4c00:	e8 2b d8 ff ff       	call   2430 <strcmp@plt>
    4c05:	85 c0                	test   %eax,%eax
    4c07:	75 20                	jne    4c29 <send_headers+0x159>
    4c09:	66 0f 6f 05 2f 52 00 00 	movdqa 0x522f(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4c11:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4c19:	66 0f 6f 05 2f 52 00 00 	movdqa 0x522f(%rip),%xmm0        # 9e50 <_IO_stdin_used+0xe50>
    4c21:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4c29:	48 89 de             	mov    %rbx,%rsi
    4c2c:	48 8d 3d 9a 44 00 00 	lea    0x449a(%rip),%rdi        # 90cd <_IO_stdin_used+0xcd>
    4c33:	e8 f8 d7 ff ff       	call   2430 <strcmp@plt>
    4c38:	85 c0                	test   %eax,%eax
    4c3a:	0f 84 10 02 00 00    	je     4e50 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4c40:	48 89 de             	mov    %rbx,%rsi
    4c43:	48 8d 3d 87 44 00 00 	lea    0x4487(%rip),%rdi        # 90d1 <_IO_stdin_used+0xd1>
    4c4a:	e8 e1 d7 ff ff       	call   2430 <strcmp@plt>
    4c4f:	85 c0                	test   %eax,%eax
    4c51:	0f 84 a9 02 00 00    	je     4f00 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4c57:	48 89 de             	mov    %rbx,%rsi
    4c5a:	48 8d 3d 74 44 00 00 	lea    0x4474(%rip),%rdi        # 90d5 <_IO_stdin_used+0xd5>
    4c61:	e8 ca d7 ff ff       	call   2430 <strcmp@plt>
    4c66:	85 c0                	test   %eax,%eax
    4c68:	0f 84 6a 02 00 00    	je     4ed8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4c6e:	48 89 de             	mov    %rbx,%rsi
    4c71:	48 8d 3d bd 44 00 00 	lea    0x44bd(%rip),%rdi        # 9135 <_IO_stdin_used+0x135>
    4c78:	e8 b3 d7 ff ff       	call   2430 <strcmp@plt>
    4c7d:	85 c0                	test   %eax,%eax
    4c7f:	0f 84 2b 02 00 00    	je     4eb0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4c85:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4c88:	0f 84 52 01 00 00    	je     4de0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4c8e:	48 89 de             	mov    %rbx,%rsi
    4c91:	48 8d 3d 41 44 00 00 	lea    0x4441(%rip),%rdi        # 90d9 <_IO_stdin_used+0xd9>
    4c98:	e8 93 d7 ff ff       	call   2430 <strcmp@plt>
    4c9d:	85 c0                	test   %eax,%eax
    4c9f:	0f 84 ab 02 00 00    	je     4f50 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4ca5:	48 89 de             	mov    %rbx,%rsi
    4ca8:	48 8d 3d 2e 44 00 00 	lea    0x442e(%rip),%rdi        # 90dd <_IO_stdin_used+0xdd>
    4caf:	e8 7c d7 ff ff       	call   2430 <strcmp@plt>
    4cb4:	85 c0                	test   %eax,%eax
    4cb6:	0f 84 6c 02 00 00    	je     4f28 <send_headers+0x458>
    slen = strlen(send_buffer);
    4cbc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4cc4:	4c 89 e7             	mov    %r12,%rdi
    4cc7:	e8 c4 d6 ff ff       	call   2390 <strlen@plt>
    void *buf = malloc(size);
    4ccc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4ccf:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4cd2:	e8 b9 d7 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    4cd7:	48 85 c0             	test   %rax,%rax
    4cda:	0f 84 eb 02 00 00    	je     4fcb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4ce0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4ce4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ce8:	83 fb 08             	cmp    $0x8,%ebx
    4ceb:	0f 83 3f 01 00 00    	jae    4e30 <send_headers+0x360>
    4cf1:	f6 c3 04             	test   $0x4,%bl
    4cf4:	0f 85 7b 02 00 00    	jne    4f75 <send_headers+0x4a5>
    4cfa:	85 db                	test   %ebx,%ebx
    4cfc:	74 13                	je     4d11 <send_headers+0x241>
    4cfe:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4d06:	88 10                	mov    %dl,(%rax)
    4d08:	f6 c3 02             	test   $0x2,%bl
    4d0b:	0f 85 96 02 00 00    	jne    4fa7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4d11:	4d 89 e8             	mov    %r13,%r8
    4d14:	48 8d 0d c6 43 00 00 	lea    0x43c6(%rip),%rcx        # 90e1 <_IO_stdin_used+0xe1>
    4d1b:	4c 89 e7             	mov    %r12,%rdi
    4d1e:	31 c0                	xor    %eax,%eax
    4d20:	ba 00 04 00 00       	mov    $0x400,%edx
    4d25:	be 01 00 00 00       	mov    $0x1,%esi
    4d2a:	e8 b1 d8 ff ff       	call   25e0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4d2f:	4c 89 e7             	mov    %r12,%rdi
    4d32:	e8 59 d6 ff ff       	call   2390 <strlen@plt>
    void *buf = malloc(size);
    4d37:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4d3a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4d3d:	e8 4e d7 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    4d42:	48 85 c0             	test   %rax,%rax
    4d45:	0f 84 80 02 00 00    	je     4fcb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4d4b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4d4f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4d53:	83 fb 08             	cmp    $0x8,%ebx
    4d56:	0f 83 1c 01 00 00    	jae    4e78 <send_headers+0x3a8>
    4d5c:	f6 c3 04             	test   $0x4,%bl
    4d5f:	0f 85 29 02 00 00    	jne    4f8e <send_headers+0x4be>
    4d65:	85 db                	test   %ebx,%ebx
    4d67:	74 13                	je     4d7c <send_headers+0x2ac>
    4d69:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4d71:	88 10                	mov    %dl,(%rax)
    4d73:	f6 c3 02             	test   $0x2,%bl
    4d76:	0f 85 3d 02 00 00    	jne    4fb9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4d7c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4d81:	bf 02 00 00 00       	mov    $0x2,%edi
    4d86:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4d8e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4d96:	e8 f5 d6 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    4d9b:	48 85 c0             	test   %rax,%rax
    4d9e:	0f 84 27 02 00 00    	je     4fcb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4da4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4dac:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4db0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4db8:	66 89 10             	mov    %dx,(%rax)
}
    4dbb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4dc3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4dcc:	0f 85 20 02 00 00    	jne    4ff2 <send_headers+0x522>
    4dd2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4dd9:	5b                   	pop    %rbx
    4dda:	5d                   	pop    %rbp
    4ddb:	41 5c                	pop    %r12
    4ddd:	41 5d                	pop    %r13
    4ddf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4de0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4de4:	0f 85 a4 fe ff ff    	jne    4c8e <send_headers+0x1be>
    4dea:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4dee:	0f 85 9a fe ff ff    	jne    4c8e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4df4:	66 0f 6f 05 a4 50 00 00 	movdqa 0x50a4(%rip),%xmm0        # 9ea0 <_IO_stdin_used+0xea0>
    4dfc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4e06:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e0e:	66 0f 6f 05 9a 50 00 00 	movdqa 0x509a(%rip),%xmm0        # 9eb0 <_IO_stdin_used+0xeb0>
    4e16:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4e1e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4e26:	e9 63 fe ff ff       	jmp    4c8e <send_headers+0x1be>
    4e2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4e30:	89 da                	mov    %ebx,%edx
    4e32:	48 89 c7             	mov    %rax,%rdi
    4e35:	4c 89 e6             	mov    %r12,%rsi
    4e38:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4e3d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4e42:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4e45:	c1 e9 03             	shr    $0x3,%ecx
    4e48:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4e4b:	e9 c1 fe ff ff       	jmp    4d11 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4e50:	66 0f 6f 05 e8 4f 00 00 	movdqa 0x4fe8(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4e58:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e60:	66 0f 6f 05 f8 4f 00 00 	movdqa 0x4ff8(%rip),%xmm0        # 9e60 <_IO_stdin_used+0xe60>
    4e68:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4e70:	e9 cb fd ff ff       	jmp    4c40 <send_headers+0x170>
    4e75:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4e78:	89 da                	mov    %ebx,%edx
    4e7a:	48 89 c7             	mov    %rax,%rdi
    4e7d:	4c 89 e6             	mov    %r12,%rsi
    4e80:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4e85:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4e8a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4e8d:	c1 e9 03             	shr    $0x3,%ecx
    4e90:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4e93:	e9 e4 fe ff ff       	jmp    4d7c <send_headers+0x2ac>
    4e98:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4ea0:	48 8d 1d 4f 42 00 00 	lea    0x424f(%rip),%rbx        # 90f6 <_IO_stdin_used+0xf6>
    4ea7:	e9 94 fd ff ff       	jmp    4c40 <send_headers+0x170>
    4eac:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4eb0:	66 0f 6f 05 c8 4f 00 00 	movdqa 0x4fc8(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4eb8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ec0:	66 0f 6f 05 c8 4f 00 00 	movdqa 0x4fc8(%rip),%xmm0        # 9e90 <_IO_stdin_used+0xe90>
    4ec8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ed0:	e9 b0 fd ff ff       	jmp    4c85 <send_headers+0x1b5>
    4ed5:	0f 1f 00             	nopl   (%rax)
    4ed8:	66 0f 6f 05 a0 4f 00 00 	movdqa 0x4fa0(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4ee0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ee8:	66 0f 6f 05 a0 4f 00 00 	movdqa 0x4fa0(%rip),%xmm0        # 9e90 <_IO_stdin_used+0xe90>
    4ef0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ef8:	e9 71 fd ff ff       	jmp    4c6e <send_headers+0x19e>
    4efd:	0f 1f 00             	nopl   (%rax)
    4f00:	66 0f 6f 05 38 4f 00 00 	movdqa 0x4f38(%rip),%xmm0        # 9e40 <_IO_stdin_used+0xe40>
    4f08:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f10:	66 0f 6f 05 58 4f 00 00 	movdqa 0x4f58(%rip),%xmm0        # 9e70 <_IO_stdin_used+0xe70>
    4f18:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4f20:	e9 32 fd ff ff       	jmp    4c57 <send_headers+0x187>
    4f25:	0f 1f 00             	nopl   (%rax)
    4f28:	66 0f 6f 05 50 4f 00 00 	movdqa 0x4f50(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4f30:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f38:	66 0f 6f 05 90 4f 00 00 	movdqa 0x4f90(%rip),%xmm0        # 9ed0 <_IO_stdin_used+0xed0>
    4f40:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4f48:	e9 6f fd ff ff       	jmp    4cbc <send_headers+0x1ec>
    4f4d:	0f 1f 00             	nopl   (%rax)
    4f50:	66 0f 6f 05 28 4f 00 00 	movdqa 0x4f28(%rip),%xmm0        # 9e80 <_IO_stdin_used+0xe80>
    4f58:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f60:	66 0f 6f 05 58 4f 00 00 	movdqa 0x4f58(%rip),%xmm0        # 9ec0 <_IO_stdin_used+0xec0>
    4f68:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4f70:	e9 30 fd ff ff       	jmp    4ca5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f75:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4f7c:	89 db                	mov    %ebx,%ebx
    4f7e:	89 10                	mov    %edx,(%rax)
    4f80:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4f85:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4f89:	e9 83 fd ff ff       	jmp    4d11 <send_headers+0x241>
    4f8e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4f95:	89 db                	mov    %ebx,%ebx
    4f97:	89 10                	mov    %edx,(%rax)
    4f99:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4f9e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4fa2:	e9 d5 fd ff ff       	jmp    4d7c <send_headers+0x2ac>
    4fa7:	89 db                	mov    %ebx,%ebx
    4fa9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4faf:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4fb4:	e9 58 fd ff ff       	jmp    4d11 <send_headers+0x241>
    4fb9:	89 db                	mov    %ebx,%ebx
    4fbb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    4fc1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    4fc6:	e9 b1 fd ff ff       	jmp    4d7c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4fcb:	48 8b 0d 4e 70 00 00 	mov    0x704e(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    4fd2:	ba 28 00 00 00       	mov    $0x28,%edx
    4fd7:	be 01 00 00 00       	mov    $0x1,%esi
    4fdc:	48 8d 3d 1d 46 00 00 	lea    0x461d(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    4fe3:	e8 78 d5 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    4fe8:	bf 01 00 00 00       	mov    $0x1,%edi
    4fed:	e8 4e d5 ff ff       	call   2540 <exit@plt>
}
    4ff2:	e8 a9 d3 ff ff       	call   23a0 <__stack_chk_fail@plt>
    4ff7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005000 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5000:	f3 0f 1e fa          	endbr64
    5004:	41 55                	push   %r13
    5006:	49 89 d5             	mov    %rdx,%r13
    5009:	41 54                	push   %r12
    500b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    500e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5011:	55                   	push   %rbp
    5012:	53                   	push   %rbx
    5013:	48 89 f3             	mov    %rsi,%rbx
    5016:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    501a:	e8 71 d4 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    501f:	48 85 c0             	test   %rax,%rax
    5022:	74 6b                	je     508f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    5024:	4c 89 e7             	mov    %r12,%rdi
    5027:	48 89 c5             	mov    %rax,%rbp
    502a:	31 f6                	xor    %esi,%esi
    502c:	31 c0                	xor    %eax,%eax
    502e:	e8 dd d4 ff ff       	call   2510 <open@plt>
    5033:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    5036:	85 c0                	test   %eax,%eax
    5038:	0f 88 d8 d5 ff ff    	js     2616 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    503e:	48 89 da             	mov    %rbx,%rdx
    5041:	48 89 ee             	mov    %rbp,%rsi
    5044:	89 c7                	mov    %eax,%edi
    5046:	e8 c5 d3 ff ff       	call   2410 <read@plt>
    if (ret < file_size) {
    504b:	48 98                	cltq
    504d:	48 39 d8             	cmp    %rbx,%rax
    5050:	7c 1e                	jl     5070 <copy_file_contents+0x70>
    close(fd);
    5052:	44 89 e7             	mov    %r12d,%edi
    5055:	e8 96 d3 ff ff       	call   23f0 <close@plt>
    iov->iov_base = buf;
    505a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    505e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    5062:	48 83 c4 08          	add    $0x8,%rsp
    5066:	5b                   	pop    %rbx
    5067:	5d                   	pop    %rbp
    5068:	41 5c                	pop    %r12
    506a:	41 5d                	pop    %r13
    506c:	c3                   	ret
    506d:	0f 1f 00             	nopl   (%rax)
    5070:	48 8b 0d a9 6f 00 00 	mov    0x6fa9(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5077:	ba 1a 00 00 00       	mov    $0x1a,%edx
    507c:	be 01 00 00 00       	mov    $0x1,%esi
    5081:	48 8d 3d 6f 40 00 00 	lea    0x406f(%rip),%rdi        # 90f7 <_IO_stdin_used+0xf7>
    5088:	e8 d3 d4 ff ff       	call   2560 <fwrite@plt>
    508d:	eb c3                	jmp    5052 <copy_file_contents+0x52>
    508f:	48 8b 0d 8a 6f 00 00 	mov    0x6f8a(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5096:	ba 28 00 00 00       	mov    $0x28,%edx
    509b:	be 01 00 00 00       	mov    $0x1,%esi
    50a0:	48 8d 3d 59 45 00 00 	lea    0x4559(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    50a7:	e8 b4 d4 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    50ac:	bf 01 00 00 00       	mov    $0x1,%edi
    50b1:	e8 8a d4 ff ff       	call   2540 <exit@plt>
    50b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000050c0 <add_write_request>:
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    50c0:	f3 0f 1e fa          	endbr64
    50c4:	55                   	push   %rbp
    struct Write *write = calloc(1, sizeof(struct Write));
    50c5:	be 10 00 00 00       	mov    $0x10,%esi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    50ca:	48 89 d5             	mov    %rdx,%rbp
    50cd:	53                   	push   %rbx
    50ce:	48 89 fb             	mov    %rdi,%rbx
    struct Write *write = calloc(1, sizeof(struct Write));
    50d1:	bf 01 00 00 00       	mov    $0x1,%edi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    50d6:	48 83 ec 08          	sub    $0x8,%rsp
    struct Write *write = calloc(1, sizeof(struct Write));
    50da:	e8 41 d3 ff ff       	call   2420 <calloc@plt>
    write->client_socket = req->client_socket;
    50df:	f3 0f 7e 45 08       	movq   0x8(%rbp),%xmm0
    req->event_type = EVENT_TYPE_WRITE;
    50e4:	c7 45 00 02 00 00 00 	movl   $0x2,0x0(%rbp)
    if (write->client_socket == -1) {
    50eb:	66 0f 7e c2          	movd   %xmm0,%edx
    write->client_socket = req->client_socket;
    50ef:	66 0f d6 40 08       	movq   %xmm0,0x8(%rax)
    50f4:	66 0f 70 c8 e5       	pshufd $0xe5,%xmm0,%xmm1
    if (write->client_socket == -1) {
    50f9:	83 fa ff             	cmp    $0xffffffff,%edx
    50fc:	74 69                	je     5167 <add_write_request+0xa7>
    buffersend_filter(data, &data->iomailboxes[data->other_io], IO_WRITE, write, write->sockettoken);
    50fe:	48 63 b3 18 01 00 00 	movslq 0x118(%rbx),%rsi
    write->request = req;
    5105:	48 89 28             	mov    %rbp,(%rax)
    5108:	66 0f 7e cf          	movd   %xmm1,%edi
    buffersend_filter(data, &data->iomailboxes[data->other_io], IO_WRITE, write, write->sockettoken);
    510c:	48 c1 e6 04          	shl    $0x4,%rsi
    5110:	48 03 b3 10 01 00 00 	add    0x110(%rbx),%rsi
  while (data->running == 1) {
    5117:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    511b:	75 41                	jne    515e <add_write_request+0x9e>
      for (int x = 0 ; x < buffers->count ; x++) {
    511d:	48 63 0e             	movslq (%rsi),%rcx
    5120:	85 c9                	test   %ecx,%ecx
    5122:	7e f3                	jle    5117 <add_write_request+0x57>
    5124:	48 8b 56 08          	mov    0x8(%rsi),%rdx
    5128:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    512c:	48 8d 0c ca          	lea    (%rdx,%rcx,8),%rcx
    5130:	eb 0f                	jmp    5141 <add_write_request+0x81>
    5132:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5138:	48 83 c2 28          	add    $0x28,%rdx
    513c:	48 39 ca             	cmp    %rcx,%rdx
    513f:	74 d6                	je     5117 <add_write_request+0x57>
        if (buffers->buffer[x].available == 0) {
    5141:	44 8b 42 08          	mov    0x8(%rdx),%r8d
    5145:	45 85 c0             	test   %r8d,%r8d
    5148:	75 ee                	jne    5138 <add_write_request+0x78>
          buffers->buffer[x].data = send;
    514a:	48 89 02             	mov    %rax,(%rdx)
          buffers->buffer[x].kind = kind;
    514d:	c7 42 20 03 00 00 00 	movl   $0x3,0x20(%rdx)
          buffers->buffer[x].filter = filter;
    5154:	89 7a 24             	mov    %edi,0x24(%rdx)
          buffers->buffer[x].available = 1;
    5157:	c7 42 08 01 00 00 00 	movl   $0x1,0x8(%rdx)
}
    515e:	48 83 c4 08          	add    $0x8,%rsp
    5162:	31 c0                	xor    %eax,%eax
    5164:	5b                   	pop    %rbx
    5165:	5d                   	pop    %rbp
    5166:	c3                   	ret
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5167:	bf 01 00 00 00       	mov    $0x1,%edi
    516c:	48 8d 35 bd 44 00 00 	lea    0x44bd(%rip),%rsi        # 9630 <_IO_stdin_used+0x630>
    5173:	31 c0                	xor    %eax,%eax
    5175:	e8 56 d3 ff ff       	call   24d0 <__printf_chk@plt>
      exit(1);
    517a:	bf 01 00 00 00       	mov    $0x1,%edi
    517f:	e8 bc d3 ff ff       	call   2540 <exit@plt>
    5184:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    518f:	90                   	nop

0000000000005190 <add_read_request>:
int add_read_request(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5190:	f3 0f 1e fa          	endbr64
    5194:	41 56                	push   %r14
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    5196:	41 8b 40 44          	mov    0x44(%r8),%eax
    519a:	41 89 ce             	mov    %ecx,%r14d
    519d:	41 55                	push   %r13
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    519f:	41 8b 88 c0 00 00 00 	mov    0xc0(%r8),%ecx
    51a6:	41 89 d5             	mov    %edx,%r13d
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    51a9:	49 8b 10             	mov    (%r8),%rdx
    51ac:	41 54                	push   %r12
	unsigned int head, next = sq->sqe_tail + 1;
    51ae:	83 c0 01             	add    $0x1,%eax
    51b1:	55                   	push   %rbp
    51b2:	53                   	push   %rbx
    51b3:	4c 89 c3             	mov    %r8,%rbx
		head = IO_URING_READ_ONCE(*sq->khead);
    51b6:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    51b8:	f6 c1 02             	test   $0x2,%cl
    51bb:	74 00                	je     51bd <add_read_request+0x2d>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    51bd:	89 c2                	mov    %eax,%edx
    51bf:	29 f2                	sub    %esi,%edx
    51c1:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    51c4:	0f 82 58 d4 ff ff    	jb     2622 <add_read_request.cold>
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    51ca:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    51cd:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    51d0:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    51d3:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    51d8:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    51db:	23 6b 58             	and    0x58(%rbx),%ebp
    51de:	d3 e5                	shl    %cl,%ebp
    51e0:	48 c1 e5 06          	shl    $0x6,%rbp
    51e4:	48 03 6b 38          	add    0x38(%rbx),%rbp
    51e8:	e8 a3 d2 ff ff       	call   2490 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    51ed:	be 01 00 00 00       	mov    $0x1,%esi
    51f2:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    51f7:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    51fa:	e8 21 d2 ff ff       	call   2420 <calloc@plt>
    req->client_socket = client_socket;
    51ff:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5204:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5208:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    520b:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    5210:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->sockettoken = sockettoken;
    5215:	45 89 74 24 0c       	mov    %r14d,0xc(%r12)
    req->iov[0].iov_len = READ_SZ;
    521a:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    5223:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    522b:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    522f:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    5233:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    523a:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    5242:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    5246:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    524e:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    5256:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    525a:	e8 51 d1 ff ff       	call   23b0 <io_uring_submit@plt>
}
    525f:	5b                   	pop    %rbx
    5260:	31 c0                	xor    %eax,%eax
    5262:	5d                   	pop    %rbp
    5263:	41 5c                	pop    %r12
    5265:	41 5d                	pop    %r13
    5267:	41 5e                	pop    %r14
    5269:	c3                   	ret
    526a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005270 <_send_static_string_content>:
void _send_static_string_content(struct KernelThread *data, struct Buffers *buffers, const char *str, int client_socket, int sockettoken, struct io_uring *ring) {
    5270:	f3 0f 1e fa          	endbr64
    5274:	41 57                	push   %r15
    5276:	4d 89 cf             	mov    %r9,%r15
    5279:	41 56                	push   %r14
    527b:	49 89 f6             	mov    %rsi,%r14
    527e:	41 55                	push   %r13
    5280:	41 54                	push   %r12
    5282:	45 89 c4             	mov    %r8d,%r12d
    5285:	55                   	push   %rbp
    5286:	48 89 d5             	mov    %rdx,%rbp
    5289:	53                   	push   %rbx
    528a:	89 cb                	mov    %ecx,%ebx
    528c:	48 83 ec 18          	sub    $0x18,%rsp
    5290:	48 89 3c 24          	mov    %rdi,(%rsp)
    void *buf = malloc(size);
    5294:	bf 20 00 00 00       	mov    $0x20,%edi
    5299:	e8 f2 d1 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    529e:	48 85 c0             	test   %rax,%rax
    52a1:	74 6a                	je     530d <_send_static_string_content+0x9d>
    52a3:	49 89 c5             	mov    %rax,%r13
    unsigned long slen = strlen(str);
    52a6:	48 89 ef             	mov    %rbp,%rdi
    52a9:	e8 e2 d0 ff ff       	call   2390 <strlen@plt>
    req->iovec_count = 1;
    52ae:	41 c7 45 04 01 00 00 00 	movl   $0x1,0x4(%r13)
    req->client_socket = client_socket;
    52b6:	41 89 5d 08          	mov    %ebx,0x8(%r13)
    req->sockettoken = sockettoken;
    52ba:	45 89 65 0c          	mov    %r12d,0xc(%r13)
    if (req->client_socket == -1) {
    52be:	83 fb ff             	cmp    $0xffffffff,%ebx
    52c1:	74 71                	je     5334 <_send_static_string_content+0xc4>
    void *buf = malloc(size);
    52c3:	48 89 c7             	mov    %rax,%rdi
    52c6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    52cb:	e8 c0 d1 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    52d0:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    52d5:	48 85 c0             	test   %rax,%rax
    void *buf = malloc(size);
    52d8:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    52db:	74 30                	je     530d <_send_static_string_content+0x9d>
    req->iov[0].iov_len = slen;
    52dd:	49 89 55 18          	mov    %rdx,0x18(%r13)
    52e1:	48 89 ee             	mov    %rbp,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    52e4:	49 89 45 10          	mov    %rax,0x10(%r13)
    52e8:	e8 73 d1 ff ff       	call   2460 <memcpy@plt>
    add_write_request(data, buffers, req, ring);
    52ed:	48 8b 3c 24          	mov    (%rsp),%rdi
}
    52f1:	48 83 c4 18          	add    $0x18,%rsp
    add_write_request(data, buffers, req, ring);
    52f5:	4c 89 f9             	mov    %r15,%rcx
}
    52f8:	5b                   	pop    %rbx
    add_write_request(data, buffers, req, ring);
    52f9:	4c 89 ea             	mov    %r13,%rdx
}
    52fc:	5d                   	pop    %rbp
    add_write_request(data, buffers, req, ring);
    52fd:	4c 89 f6             	mov    %r14,%rsi
}
    5300:	41 5c                	pop    %r12
    5302:	41 5d                	pop    %r13
    5304:	41 5e                	pop    %r14
    5306:	41 5f                	pop    %r15
    add_write_request(data, buffers, req, ring);
    5308:	e9 b3 fd ff ff       	jmp    50c0 <add_write_request>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    530d:	48 8b 0d 0c 6d 00 00 	mov    0x6d0c(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5314:	ba 28 00 00 00       	mov    $0x28,%edx
    5319:	be 01 00 00 00       	mov    $0x1,%esi
    531e:	48 8d 3d db 42 00 00 	lea    0x42db(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    5325:	e8 36 d2 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    532a:	bf 01 00 00 00       	mov    $0x1,%edi
    532f:	e8 0c d2 ff ff       	call   2540 <exit@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5334:	48 8d 3d d7 3d 00 00 	lea    0x3dd7(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    533b:	e8 10 d0 ff ff       	call   2350 <puts@plt>
      exit(1);
    5340:	bf 01 00 00 00       	mov    $0x1,%edi
    5345:	e8 f6 d1 ff ff       	call   2540 <exit@plt>
    534a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005350 <handle_unimplemented_method>:
void handle_unimplemented_method(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5350:	f3 0f 1e fa          	endbr64
    5354:	41 57                	push   %r15
    5356:	41 56                	push   %r14
    5358:	4d 89 c6             	mov    %r8,%r14
    535b:	41 55                	push   %r13
    535d:	49 89 f5             	mov    %rsi,%r13
    5360:	41 54                	push   %r12
    5362:	55                   	push   %rbp
    5363:	89 cd                	mov    %ecx,%ebp
    5365:	53                   	push   %rbx
    5366:	89 d3                	mov    %edx,%ebx
    5368:	48 83 ec 18          	sub    $0x18,%rsp
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, sockettoken, ring);
    536c:	4c 8b 3d a5 6c 00 00 	mov    0x6ca5(%rip),%r15        # c018 <unimplemented_content>
void handle_unimplemented_method(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5373:	48 89 3c 24          	mov    %rdi,(%rsp)
    void *buf = malloc(size);
    5377:	bf 20 00 00 00       	mov    $0x20,%edi
    537c:	e8 0f d1 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    5381:	48 85 c0             	test   %rax,%rax
    5384:	74 6f                	je     53f5 <handle_unimplemented_method+0xa5>
    5386:	49 89 c4             	mov    %rax,%r12
    unsigned long slen = strlen(str);
    5389:	4c 89 ff             	mov    %r15,%rdi
    538c:	e8 ff cf ff ff       	call   2390 <strlen@plt>
    req->client_socket = client_socket;
    5391:	41 89 5c 24 08       	mov    %ebx,0x8(%r12)
    req->iovec_count = 1;
    5396:	41 c7 44 24 04 01 00 00 00 	movl   $0x1,0x4(%r12)
    req->sockettoken = sockettoken;
    539f:	41 89 6c 24 0c       	mov    %ebp,0xc(%r12)
    if (req->client_socket == -1) {
    53a4:	83 fb ff             	cmp    $0xffffffff,%ebx
    53a7:	74 73                	je     541c <handle_unimplemented_method+0xcc>
    void *buf = malloc(size);
    53a9:	48 89 c7             	mov    %rax,%rdi
    53ac:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    53b1:	e8 da d0 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    53b6:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    53bb:	48 85 c0             	test   %rax,%rax
    void *buf = malloc(size);
    53be:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    53c1:	74 32                	je     53f5 <handle_unimplemented_method+0xa5>
    req->iov[0].iov_len = slen;
    53c3:	49 89 54 24 18       	mov    %rdx,0x18(%r12)
    53c8:	4c 89 fe             	mov    %r15,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    53cb:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    53d0:	e8 8b d0 ff ff       	call   2460 <memcpy@plt>
    add_write_request(data, buffers, req, ring);
    53d5:	48 8b 3c 24          	mov    (%rsp),%rdi
}
    53d9:	48 83 c4 18          	add    $0x18,%rsp
    add_write_request(data, buffers, req, ring);
    53dd:	4c 89 f1             	mov    %r14,%rcx
}
    53e0:	5b                   	pop    %rbx
    add_write_request(data, buffers, req, ring);
    53e1:	4c 89 e2             	mov    %r12,%rdx
}
    53e4:	5d                   	pop    %rbp
    add_write_request(data, buffers, req, ring);
    53e5:	4c 89 ee             	mov    %r13,%rsi
}
    53e8:	41 5c                	pop    %r12
    53ea:	41 5d                	pop    %r13
    53ec:	41 5e                	pop    %r14
    53ee:	41 5f                	pop    %r15
    add_write_request(data, buffers, req, ring);
    53f0:	e9 cb fc ff ff       	jmp    50c0 <add_write_request>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    53f5:	48 8b 0d 24 6c 00 00 	mov    0x6c24(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    53fc:	ba 28 00 00 00       	mov    $0x28,%edx
    5401:	be 01 00 00 00       	mov    $0x1,%esi
    5406:	48 8d 3d f3 41 00 00 	lea    0x41f3(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    540d:	e8 4e d1 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    5412:	bf 01 00 00 00       	mov    $0x1,%edi
    5417:	e8 24 d1 ff ff       	call   2540 <exit@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    541c:	48 8d 3d ef 3c 00 00 	lea    0x3cef(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    5423:	e8 28 cf ff ff       	call   2350 <puts@plt>
      exit(1);
    5428:	bf 01 00 00 00       	mov    $0x1,%edi
    542d:	e8 0e d1 ff ff       	call   2540 <exit@plt>
    5432:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    543d:	0f 1f 00             	nopl   (%rax)

0000000000005440 <handle_http_404>:
void handle_http_404(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5440:	f3 0f 1e fa          	endbr64
    5444:	41 57                	push   %r15
    5446:	41 56                	push   %r14
    5448:	4d 89 c6             	mov    %r8,%r14
    544b:	41 55                	push   %r13
    544d:	49 89 f5             	mov    %rsi,%r13
    5450:	41 54                	push   %r12
    5452:	55                   	push   %rbp
    5453:	89 cd                	mov    %ecx,%ebp
    5455:	53                   	push   %rbx
    5456:	89 d3                	mov    %edx,%ebx
    5458:	48 83 ec 18          	sub    $0x18,%rsp
    _send_static_string_content(data, buffers, http_404_content, client_socket, sockettoken, ring);
    545c:	4c 8b 3d ad 6b 00 00 	mov    0x6bad(%rip),%r15        # c010 <http_404_content>
void handle_http_404(struct KernelThread *data, struct Buffers *buffers, int client_socket, int sockettoken, struct io_uring *ring) {
    5463:	48 89 3c 24          	mov    %rdi,(%rsp)
    void *buf = malloc(size);
    5467:	bf 20 00 00 00       	mov    $0x20,%edi
    546c:	e8 1f d0 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    5471:	48 85 c0             	test   %rax,%rax
    5474:	74 6f                	je     54e5 <handle_http_404+0xa5>
    5476:	49 89 c4             	mov    %rax,%r12
    unsigned long slen = strlen(str);
    5479:	4c 89 ff             	mov    %r15,%rdi
    547c:	e8 0f cf ff ff       	call   2390 <strlen@plt>
    req->client_socket = client_socket;
    5481:	41 89 5c 24 08       	mov    %ebx,0x8(%r12)
    req->iovec_count = 1;
    5486:	41 c7 44 24 04 01 00 00 00 	movl   $0x1,0x4(%r12)
    req->sockettoken = sockettoken;
    548f:	41 89 6c 24 0c       	mov    %ebp,0xc(%r12)
    if (req->client_socket == -1) {
    5494:	83 fb ff             	cmp    $0xffffffff,%ebx
    5497:	74 73                	je     550c <handle_http_404+0xcc>
    void *buf = malloc(size);
    5499:	48 89 c7             	mov    %rax,%rdi
    549c:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    54a1:	e8 ea cf ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    54a6:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    54ab:	48 85 c0             	test   %rax,%rax
    void *buf = malloc(size);
    54ae:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    54b1:	74 32                	je     54e5 <handle_http_404+0xa5>
    req->iov[0].iov_len = slen;
    54b3:	49 89 54 24 18       	mov    %rdx,0x18(%r12)
    54b8:	4c 89 fe             	mov    %r15,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    54bb:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    54c0:	e8 9b cf ff ff       	call   2460 <memcpy@plt>
    add_write_request(data, buffers, req, ring);
    54c5:	48 8b 3c 24          	mov    (%rsp),%rdi
}
    54c9:	48 83 c4 18          	add    $0x18,%rsp
    add_write_request(data, buffers, req, ring);
    54cd:	4c 89 f1             	mov    %r14,%rcx
}
    54d0:	5b                   	pop    %rbx
    add_write_request(data, buffers, req, ring);
    54d1:	4c 89 e2             	mov    %r12,%rdx
}
    54d4:	5d                   	pop    %rbp
    add_write_request(data, buffers, req, ring);
    54d5:	4c 89 ee             	mov    %r13,%rsi
}
    54d8:	41 5c                	pop    %r12
    54da:	41 5d                	pop    %r13
    54dc:	41 5e                	pop    %r14
    54de:	41 5f                	pop    %r15
    add_write_request(data, buffers, req, ring);
    54e0:	e9 db fb ff ff       	jmp    50c0 <add_write_request>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    54e5:	48 8b 0d 34 6b 00 00 	mov    0x6b34(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    54ec:	ba 28 00 00 00       	mov    $0x28,%edx
    54f1:	be 01 00 00 00       	mov    $0x1,%esi
    54f6:	48 8d 3d 03 41 00 00 	lea    0x4103(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    54fd:	e8 5e d0 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    5502:	bf 01 00 00 00       	mov    $0x1,%edi
    5507:	e8 34 d0 ff ff       	call   2540 <exit@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    550c:	48 8d 3d ff 3b 00 00 	lea    0x3bff(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    5513:	e8 38 ce ff ff       	call   2350 <puts@plt>
      exit(1);
    5518:	bf 01 00 00 00       	mov    $0x1,%edi
    551d:	e8 1e d0 ff ff       	call   2540 <exit@plt>
    5522:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    552d:	0f 1f 00             	nopl   (%rax)

0000000000005530 <handle_get_method>:
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, int sockettoken, struct io_uring *ring) {
    5530:	f3 0f 1e fa          	endbr64
    5534:	41 57                	push   %r15
    5536:	41 56                	push   %r14
    5538:	41 89 ce             	mov    %ecx,%r14d
    553b:	41 55                	push   %r13
    553d:	45 89 c5             	mov    %r8d,%r13d
    5540:	41 54                	push   %r12
    5542:	4d 89 cc             	mov    %r9,%r12
    5545:	55                   	push   %rbp
    5546:	48 89 f5             	mov    %rsi,%rbp
    5549:	53                   	push   %rbx
    554a:	48 89 fb             	mov    %rdi,%rbx
    if (path[strlen(path) - 1] == '/') {
    554d:	48 89 d7             	mov    %rdx,%rdi
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, int sockettoken, struct io_uring *ring) {
    5550:	48 81 ec b8 04 00 00 	sub    $0x4b8,%rsp
    5557:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5560:	48 89 84 24 a8 04 00 00 	mov    %rax,0x4a8(%rsp)
    5568:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    556a:	48 89 54 24 08       	mov    %rdx,0x8(%rsp)
    556f:	e8 1c ce ff ff       	call   2390 <strlen@plt>
    5574:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    5579:	48 89 c2             	mov    %rax,%rdx
    557c:	80 7c 06 ff 2f       	cmpb   $0x2f,-0x1(%rsi,%rax,1)
    5581:	0f 84 a9 00 00 00    	je     5630 <handle_get_method+0x100>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5587:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    558c:	48 83 c2 01          	add    $0x1,%rdx
    5590:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
    5598:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    559d:	66 89 84 24 a4 00 00 00 	mov    %ax,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55a5:	4c 8d bc 24 a0 00 00 00 	lea    0xa0(%rsp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55ad:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55b8:	e8 83 ce ff ff       	call   2440 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    55bd:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
    55c2:	4c 89 ff             	mov    %r15,%rdi
    55c5:	e8 86 ce ff ff       	call   2450 <stat@plt>
    55ca:	83 f8 ff             	cmp    $0xffffffff,%eax
    55cd:	74 14                	je     55e3 <handle_get_method+0xb3>
        if (S_ISREG(path_stat.st_mode)) {
    55cf:	8b 44 24 28          	mov    0x28(%rsp),%eax
    55d3:	25 00 f0 00 00       	and    $0xf000,%eax
    55d8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    55dd:	0f 84 ad 00 00 00    	je     5690 <handle_get_method+0x160>
    _send_static_string_content(data, buffers, http_404_content, client_socket, sockettoken, ring);
    55e3:	48 8b 15 26 6a 00 00 	mov    0x6a26(%rip),%rdx        # c010 <http_404_content>
    55ea:	4d 89 e1             	mov    %r12,%r9
    55ed:	45 89 e8             	mov    %r13d,%r8d
    55f0:	44 89 f1             	mov    %r14d,%ecx
    55f3:	48 89 ee             	mov    %rbp,%rsi
    55f6:	48 89 df             	mov    %rbx,%rdi
    55f9:	e8 72 fc ff ff       	call   5270 <_send_static_string_content>
}
    55fe:	48 8b 84 24 a8 04 00 00 	mov    0x4a8(%rsp),%rax
    5606:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    560f:	0f 85 e3 00 00 00    	jne    56f8 <handle_get_method+0x1c8>
    5615:	48 81 c4 b8 04 00 00 	add    $0x4b8,%rsp
    561c:	5b                   	pop    %rbx
    561d:	5d                   	pop    %rbp
    561e:	41 5c                	pop    %r12
    5620:	41 5d                	pop    %r13
    5622:	41 5e                	pop    %r14
    5624:	41 5f                	pop    %r15
    5626:	c3                   	ret
    5627:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5630:	b9 69 63 00 00       	mov    $0x6369,%ecx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5635:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    563d:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
    5648:	4c 8d bc 24 a0 00 00 00 	lea    0xa0(%rsp),%r15
    5650:	66 89 8c 24 a4 00 00 00 	mov    %cx,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5658:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    565d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5662:	e8 d9 cd ff ff       	call   2440 <__memcpy_chk@plt>
    5667:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    566c:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5671:	48 8d 35 b7 3a 00 00 	lea    0x3ab7(%rip),%rsi        # 912f <_IO_stdin_used+0x12f>
    5678:	48 29 d1             	sub    %rdx,%rcx
    567b:	49 8d 7c 17 06       	lea    0x6(%r15,%rdx,1),%rdi
    5680:	ba 0b 00 00 00       	mov    $0xb,%edx
    5685:	e8 b6 cd ff ff       	call   2440 <__memcpy_chk@plt>
    568a:	e9 2e ff ff ff       	jmp    55bd <handle_get_method+0x8d>
    568f:	90                   	nop
    void *buf = malloc(size);
    5690:	bf 70 00 00 00       	mov    $0x70,%edi
    5695:	e8 f6 cd ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    569a:	48 85 c0             	test   %rax,%rax
    569d:	74 5e                	je     56fd <handle_get_method+0x1cd>
            req->client_socket = client_socket;
    569f:	44 89 70 08          	mov    %r14d,0x8(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    56a3:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    56a8:	4c 8d 40 10          	lea    0x10(%rax),%r8
    56ac:	4c 89 fa             	mov    %r15,%rdx
            req->sockettoken = sockettoken;
    56af:	44 89 68 0c          	mov    %r13d,0xc(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    56b3:	48 89 ee             	mov    %rbp,%rsi
    56b6:	48 89 df             	mov    %rbx,%rdi
            req->iovec_count = 6;
    56b9:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    56c0:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    56c5:	e8 06 f4 ff ff       	call   4ad0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    56ca:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    56cf:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    56d4:	4c 89 ff             	mov    %r15,%rdi
    56d7:	48 8d 50 60          	lea    0x60(%rax),%rdx
    56db:	e8 20 f9 ff ff       	call   5000 <copy_file_contents>
            add_write_request(data, buffers, req, ring);
    56e0:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    56e5:	4c 89 e1             	mov    %r12,%rcx
    56e8:	48 89 ee             	mov    %rbp,%rsi
    56eb:	48 89 df             	mov    %rbx,%rdi
    56ee:	e8 cd f9 ff ff       	call   50c0 <add_write_request>
}
    56f3:	e9 06 ff ff ff       	jmp    55fe <handle_get_method+0xce>
    56f8:	e8 a3 cc ff ff       	call   23a0 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    56fd:	48 8b 0d 1c 69 00 00 	mov    0x691c(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5704:	ba 28 00 00 00       	mov    $0x28,%edx
    5709:	be 01 00 00 00       	mov    $0x1,%esi
    570e:	48 8d 3d eb 3e 00 00 	lea    0x3eeb(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    5715:	e8 46 ce ff ff       	call   2560 <fwrite@plt>
        exit(1);
    571a:	bf 01 00 00 00       	mov    $0x1,%edi
    571f:	e8 1c ce ff ff       	call   2540 <exit@plt>
    5724:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    572f:	90                   	nop

0000000000005730 <handle_http_method>:
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    5730:	f3 0f 1e fa          	endbr64
    5734:	41 57                	push   %r15
    5736:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5738:	4c 8d 35 6d 39 00 00 	lea    0x396d(%rip),%r14        # 90ac <_IO_stdin_used+0xac>
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    573f:	41 55                	push   %r13
    5741:	4d 89 cd             	mov    %r9,%r13
    5744:	41 54                	push   %r12
    5746:	45 89 c4             	mov    %r8d,%r12d
    5749:	55                   	push   %rbp
    574a:	89 cd                	mov    %ecx,%ebp
    574c:	53                   	push   %rbx
    574d:	48 83 ec 38          	sub    $0x38,%rsp
    5751:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    method = strtok_r(method_buffer, " ", &saveptr);
    5756:	4c 8d 7c 24 20       	lea    0x20(%rsp),%r15
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    575b:	48 89 d7             	mov    %rdx,%rdi
    575e:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    method = strtok_r(method_buffer, " ", &saveptr);
    5763:	4c 89 fa             	mov    %r15,%rdx
    5766:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, int sockettoken, struct io_uring *ring) {
    5769:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5772:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    5777:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5779:	e8 82 cc ff ff       	call   2400 <strtok_r@plt>
    for (; *str; ++str)
    577e:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    5781:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    5784:	84 d2                	test   %dl,%dl
    5786:	88 54 24 1f          	mov    %dl,0x1f(%rsp)
    578a:	74 29                	je     57b5 <handle_http_method+0x85>
        *str = (char)tolower(*str);
    578c:	e8 3f ce ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    5791:	48 0f be 54 24 1f    	movsbq 0x1f(%rsp),%rdx
    5797:	48 89 d9             	mov    %rbx,%rcx
    579a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    57a0:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    57a3:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    57a7:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    57aa:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    57ad:	48 0f be 11          	movsbq (%rcx),%rdx
    57b1:	84 d2                	test   %dl,%dl
    57b3:	75 eb                	jne    57a0 <handle_http_method+0x70>
    path = strtok_r(NULL, " ", &saveptr);
    57b5:	4c 89 f6             	mov    %r14,%rsi
    57b8:	4c 89 fa             	mov    %r15,%rdx
    57bb:	31 ff                	xor    %edi,%edi
    57bd:	e8 3e cc ff ff       	call   2400 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    57c2:	48 8d 35 71 39 00 00 	lea    0x3971(%rip),%rsi        # 913a <_IO_stdin_used+0x13a>
    57c9:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    57cc:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    57cf:	e8 5c cc ff ff       	call   2430 <strcmp@plt>
        handle_get_method(data, buffers, path, client_socket, sockettoken, ring);
    57d4:	4d 89 e9             	mov    %r13,%r9
    57d7:	45 89 e0             	mov    %r12d,%r8d
    57da:	89 e9                	mov    %ebp,%ecx
    if (strcmp(method, "get") == 0) {
    57dc:	85 c0                	test   %eax,%eax
    57de:	75 38                	jne    5818 <handle_http_method+0xe8>
        handle_get_method(data, buffers, path, client_socket, sockettoken, ring);
    57e0:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    57e5:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    57ea:	4c 89 f2             	mov    %r14,%rdx
    57ed:	e8 3e fd ff ff       	call   5530 <handle_get_method>
}
    57f2:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    57f7:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5800:	75 2e                	jne    5830 <handle_http_method+0x100>
    5802:	48 83 c4 38          	add    $0x38,%rsp
    5806:	5b                   	pop    %rbx
    5807:	5d                   	pop    %rbp
    5808:	41 5c                	pop    %r12
    580a:	41 5d                	pop    %r13
    580c:	41 5e                	pop    %r14
    580e:	41 5f                	pop    %r15
    5810:	c3                   	ret
    5811:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, sockettoken, ring);
    5818:	48 8b 15 f9 67 00 00 	mov    0x67f9(%rip),%rdx        # c018 <unimplemented_content>
    581f:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5824:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    5829:	e8 42 fa ff ff       	call   5270 <_send_static_string_content>
}
    582e:	eb c2                	jmp    57f2 <handle_http_method+0xc2>
    5830:	e8 6b cb ff ff       	call   23a0 <__stack_chk_fail@plt>
    5835:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005840 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5840:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5844:	85 d2                	test   %edx,%edx
    5846:	7e 38                	jle    5880 <get_line+0x40>
    5848:	48 63 d2             	movslq %edx,%rdx
    584b:	48 83 c7 01          	add    $0x1,%rdi
    584f:	48 01 f2             	add    %rsi,%rdx
    5852:	eb 11                	jmp    5865 <get_line+0x25>
    5854:	0f 1f 40 00          	nopl   0x0(%rax)
    5858:	48 83 c6 01          	add    $0x1,%rsi
    585c:	48 83 c7 01          	add    $0x1,%rdi
    5860:	48 39 d6             	cmp    %rdx,%rsi
    5863:	74 1b                	je     5880 <get_line+0x40>
        dest[i] = src[i];
    5865:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5869:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    586b:	3c 0d                	cmp    $0xd,%al
    586d:	75 e9                	jne    5858 <get_line+0x18>
    586f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5872:	75 e4                	jne    5858 <get_line+0x18>
            dest[i] = '\0';
    5874:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5877:	31 c0                	xor    %eax,%eax
    5879:	c3                   	ret
    587a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5880:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5885:	c3                   	ret
    5886:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005890 <handle_client_request>:
int handle_client_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    5890:	f3 0f 1e fa          	endbr64
    5894:	53                   	push   %rbx
    5895:	49 89 fa             	mov    %rdi,%r10
    5898:	48 89 f3             	mov    %rsi,%rbx
    589b:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    58a2:	48 8b 72 10          	mov    0x10(%rdx),%rsi
    58a6:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    58af:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    58b7:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    58b9:	49 89 e3             	mov    %rsp,%r11
    58bc:	4c 8d 84 24 00 04 00 00 	lea    0x400(%rsp),%r8
    58c4:	4c 89 d8             	mov    %r11,%rax
    58c7:	eb 14                	jmp    58dd <handle_client_request+0x4d>
    58c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    58d0:	48 83 c0 01          	add    $0x1,%rax
    58d4:	48 83 c6 01          	add    $0x1,%rsi
    58d8:	4c 39 c0             	cmp    %r8,%rax
    58db:	74 53                	je     5930 <handle_client_request+0xa0>
        dest[i] = src[i];
    58dd:	0f b6 3e             	movzbl (%rsi),%edi
    58e0:	40 88 38             	mov    %dil,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    58e3:	40 80 ff 0d          	cmp    $0xd,%dil
    58e7:	75 e7                	jne    58d0 <handle_client_request+0x40>
    58e9:	80 7e 01 0a          	cmpb   $0xa,0x1(%rsi)
    58ed:	75 e1                	jne    58d0 <handle_client_request+0x40>
            dest[i] = '\0';
    58ef:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    58f2:	8b 42 08             	mov    0x8(%rdx),%eax
    58f5:	49 89 c9             	mov    %rcx,%r9
    58f8:	48 89 de             	mov    %rbx,%rsi
    58fb:	44 8b 42 0c          	mov    0xc(%rdx),%r8d
    58ff:	4c 89 d7             	mov    %r10,%rdi
    5902:	4c 89 da             	mov    %r11,%rdx
    5905:	89 c1                	mov    %eax,%ecx
    5907:	e8 24 fe ff ff       	call   5730 <handle_http_method>
}
    590c:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5914:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    591d:	75 38                	jne    5957 <handle_client_request+0xc7>
    591f:	48 81 c4 10 04 00 00 	add    $0x410,%rsp
    5926:	31 c0                	xor    %eax,%eax
    5928:	5b                   	pop    %rbx
    5929:	c3                   	ret
    592a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5930:	48 8b 0d e9 66 00 00 	mov    0x66e9(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5937:	ba 12 00 00 00       	mov    $0x12,%edx
    593c:	be 01 00 00 00       	mov    $0x1,%esi
    5941:	48 8d 3d f6 37 00 00 	lea    0x37f6(%rip),%rdi        # 913e <_IO_stdin_used+0x13e>
    5948:	e8 13 cc ff ff       	call   2560 <fwrite@plt>
        exit(1);
    594d:	bf 01 00 00 00       	mov    $0x1,%edi
    5952:	e8 e9 cb ff ff       	call   2540 <exit@plt>
}
    5957:	e8 44 ca ff ff       	call   23a0 <__stack_chk_fail@plt>
    595c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005960 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5960:	f3 0f 1e fa          	endbr64
    5964:	55                   	push   %rbp
    5965:	53                   	push   %rbx
    5966:	48 89 cb             	mov    %rcx,%rbx
    5969:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    596d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5970:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5973:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5979:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    597c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    597f:	f6 c1 02             	test   $0x2,%cl
    5982:	74 00                	je     5984 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5984:	41 89 c0             	mov    %eax,%r8d
    5987:	45 29 c8             	sub    %r9d,%r8d
    598a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    598e:	0f 82 98 cc ff ff    	jb     262c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5994:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5997:	8b 6b 44             	mov    0x44(%rbx),%ebp
    599a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    599d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    59a0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    59a3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    59a7:	d3 e5                	shl    %cl,%ebp
    59a9:	48 c1 e5 06          	shl    $0x6,%rbp
    59ad:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    59b1:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    59b4:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    59b9:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    59c0:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    59c4:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    59c8:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    59d0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    59d8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    59dc:	e8 af ca ff ff       	call   2490 <malloc@plt>
  io_uring_submit(ring);
    59e1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    59e4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    59ea:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    59ee:	48 83 c4 08          	add    $0x8,%rsp
    59f2:	5b                   	pop    %rbx
    59f3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    59f4:	e9 b7 c9 ff ff       	jmp    23b0 <io_uring_submit@plt>
    59f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005a00 <io_thread>:
void* io_thread(void *arg) {
    5a00:	f3 0f 1e fa          	endbr64
    5a04:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a06:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5a08:	41 56                	push   %r14
    5a0a:	41 55                	push   %r13
    5a0c:	41 54                	push   %r12
    5a0e:	49 89 fc             	mov    %rdi,%r12
    5a11:	55                   	push   %rbp
    5a12:	53                   	push   %rbx
    5a13:	48 81 ec 68 05 00 00 	sub    $0x568,%rsp
  struct io_uring ring = *data->ring;
    5a1a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5a23:	48 89 84 24 58 05 00 00 	mov    %rax,0x558(%rsp)
    5a2b:	48 8b 47 60          	mov    0x60(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a2f:	4c 8d 6c 24 70       	lea    0x70(%rsp),%r13
    5a34:	bf 00 01 00 00       	mov    $0x100,%edi
    5a39:	4c 89 ee             	mov    %r13,%rsi
  struct io_uring ring = *data->ring;
    5a3c:	f3 0f 6f 18          	movdqu (%rax),%xmm3
    5a40:	0f 29 5c 24 70       	movaps %xmm3,0x70(%rsp)
    5a45:	f3 0f 6f 60 10       	movdqu 0x10(%rax),%xmm4
    5a4a:	0f 29 a4 24 80 00 00 00 	movaps %xmm4,0x80(%rsp)
    5a52:	f3 0f 6f 68 20       	movdqu 0x20(%rax),%xmm5
    5a57:	0f 29 ac 24 90 00 00 00 	movaps %xmm5,0x90(%rsp)
    5a5f:	f3 0f 6f 70 30       	movdqu 0x30(%rax),%xmm6
    5a64:	0f 29 b4 24 a0 00 00 00 	movaps %xmm6,0xa0(%rsp)
    5a6c:	f3 0f 6f 78 40       	movdqu 0x40(%rax),%xmm7
    5a71:	0f 29 bc 24 b0 00 00 00 	movaps %xmm7,0xb0(%rsp)
    5a79:	f3 0f 6f 48 50       	movdqu 0x50(%rax),%xmm1
    5a7e:	0f 29 8c 24 c0 00 00 00 	movaps %xmm1,0xc0(%rsp)
    5a86:	f3 0f 6f 58 60       	movdqu 0x60(%rax),%xmm3
    5a8b:	0f 29 9c 24 d0 00 00 00 	movaps %xmm3,0xd0(%rsp)
    5a93:	f3 0f 6f 60 70       	movdqu 0x70(%rax),%xmm4
    5a98:	0f 29 a4 24 e0 00 00 00 	movaps %xmm4,0xe0(%rsp)
    5aa0:	f3 0f 6f a8 80 00 00 00 	movdqu 0x80(%rax),%xmm5
    5aa8:	0f 29 ac 24 f0 00 00 00 	movaps %xmm5,0xf0(%rsp)
    5ab0:	f3 0f 6f b0 90 00 00 00 	movdqu 0x90(%rax),%xmm6
    5ab8:	0f 29 b4 24 00 01 00 00 	movaps %xmm6,0x100(%rsp)
    5ac0:	f3 0f 6f b8 a0 00 00 00 	movdqu 0xa0(%rax),%xmm7
    5ac8:	0f 29 bc 24 10 01 00 00 	movaps %xmm7,0x110(%rsp)
    5ad0:	f3 0f 6f 88 b0 00 00 00 	movdqu 0xb0(%rax),%xmm1
    5ad8:	0f 29 8c 24 20 01 00 00 	movaps %xmm1,0x120(%rsp)
    5ae0:	f3 0f 6f 98 c0 00 00 00 	movdqu 0xc0(%rax),%xmm3
    5ae8:	0f 29 9c 24 30 01 00 00 	movaps %xmm3,0x130(%rsp)
    5af0:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5af7:	48 89 84 24 40 01 00 00 	mov    %rax,0x140(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5aff:	e8 6c c9 ff ff       	call   2470 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, data->_eventfd);
    5b04:	41 8b 74 24 68       	mov    0x68(%r12),%esi
    5b09:	49 8b 7c 24 60       	mov    0x60(%r12),%rdi
    5b0e:	e8 6d ca ff ff       	call   2580 <io_uring_register_eventfd@plt>
  if (data->io_mode == IO_MODE_RECV) {
    5b13:	41 8b 84 24 0c 01 00 00 	mov    0x10c(%r12),%eax
    5b1b:	83 f8 01             	cmp    $0x1,%eax
    5b1e:	0f 84 fb 0b 00 00    	je     671f <io_thread+0xd1f>
  if (data->io_mode == IO_MODE_SEND) {
    5b24:	85 c0                	test   %eax,%eax
    5b26:	0f 85 9c 06 00 00    	jne    61c8 <io_thread+0x7c8>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5b2c:	48 8d 3d bd 3b 00 00 	lea    0x3bbd(%rip),%rdi        # 96f0 <_IO_stdin_used+0x6f0>
    5b33:	e8 18 c8 ff ff       	call   2350 <puts@plt>
    int epollfd = epoll_create1(0);
    5b38:	31 ff                	xor    %edi,%edi
    5b3a:	e8 81 ca ff ff       	call   25c0 <epoll_create1@plt>
    5b3f:	89 04 24             	mov    %eax,(%rsp)
				if (epollfd == -1) {
    5b42:	83 f8 ff             	cmp    $0xffffffff,%eax
    5b45:	0f 84 69 cb ff ff    	je     26b4 <io_thread.cold+0x7e>
    5b4b:	89 c2                	mov    %eax,%edx
    5b4d:	48 8d 35 7e 36 00 00 	lea    0x367e(%rip),%rsi        # 91d2 <_IO_stdin_used+0x1d2>
    5b54:	bf 01 00 00 00       	mov    $0x1,%edi
    5b59:	31 c0                	xor    %eax,%eax
    5b5b:	e8 70 c9 ff ff       	call   24d0 <__printf_chk@plt>
    5b60:	48 8d 3d c1 3b 00 00 	lea    0x3bc1(%rip),%rdi        # 9728 <_IO_stdin_used+0x728>
    5b67:	e8 e4 c7 ff ff       	call   2350 <puts@plt>
    5b6c:	41 8b 8c 24 1c 01 00 00 	mov    0x11c(%r12),%ecx
    5b74:	31 c0                	xor    %eax,%eax
    5b76:	48 8d 35 e3 3b 00 00 	lea    0x3be3(%rip),%rsi        # 9760 <_IO_stdin_used+0x760>
    5b7d:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    5b85:	45 8b 84 24 18 01 00 00 	mov    0x118(%r12),%r8d
    5b8d:	bf 01 00 00 00       	mov    $0x1,%edi
    5b92:	e8 39 c9 ff ff       	call   24d0 <__printf_chk@plt>
    void * _reply = bufferrecv("waitsocketreply", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET, &reply, 0); 
    5b97:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    5b9f:	48 c1 e0 04          	shl    $0x4,%rax
    5ba3:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
  while (data->running == 1) {
    5bab:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5bb1:	0f 85 13 cb ff ff    	jne    26ca <io_thread.cold+0x94>
      for (int x = 0 ; x < buffers->count ; x++) {
    5bb7:	8b 08                	mov    (%rax),%ecx
    5bb9:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5bbd:	48 63 c1             	movslq %ecx,%rax
    5bc0:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    5bc4:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    5bc8:	85 c9                	test   %ecx,%ecx
    5bca:	0f 8e a9 11 00 00    	jle    6d79 <io_thread+0x1379>
void* io_thread(void *arg) {
    5bd0:	48 89 d3             	mov    %rdx,%rbx
    5bd3:	eb 0c                	jmp    5be1 <io_thread+0x1e1>
    5bd5:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    5bd8:	48 83 c3 28          	add    $0x28,%rbx
    5bdc:	48 39 c3             	cmp    %rax,%rbx
    5bdf:	74 ef                	je     5bd0 <io_thread+0x1d0>
        if (buffers->buffer[x].available == 1) {
    5be1:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    5be5:	75 f1                	jne    5bd8 <io_thread+0x1d8>
          if (buffers->buffer[x].kind == kind) {
    5be7:	44 8b 43 20          	mov    0x20(%rbx),%r8d
    5beb:	45 85 c0             	test   %r8d,%r8d
    5bee:	75 e8                	jne    5bd8 <io_thread+0x1d8>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    5bf0:	be 28 00 00 00       	mov    $0x28,%esi
    5bf5:	bf 01 00 00 00       	mov    $0x1,%edi
    5bfa:	e8 21 c8 ff ff       	call   2420 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    5bff:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    5c02:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            reply->kind = buffers->buffer[x].kind;
    5c09:	c7 40 20 00 00 00 00 	movl   $0x0,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    5c10:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    5c13:	0f ae f8             	sfence
    struct NewSocketMessage *msg = bufferreply->data;
    5c16:	48 8b 18             	mov    (%rax),%rbx
    5c19:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    5c21:	48 8d 35 78 3b 00 00 	lea    0x3b78(%rip),%rsi        # 97a0 <_IO_stdin_used+0x7a0>
    5c28:	31 c0                	xor    %eax,%eax
    5c2a:	bf 01 00 00 00       	mov    $0x1,%edi
    5c2f:	8b 0b                	mov    (%rbx),%ecx
    5c31:	e8 9a c8 ff ff       	call   24d0 <__printf_chk@plt>
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    5c36:	be 04 00 00 00       	mov    $0x4,%esi
    5c3b:	bf 01 00 00 00       	mov    $0x1,%edi
    5c40:	e8 db c7 ff ff       	call   2420 <calloc@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    5c45:	49 63 8c 24 18 01 00 00 	movslq 0x118(%r12),%rcx
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    5c4d:	48 89 c6             	mov    %rax,%rsi
    ourreply->nothing = msg->socket;
    5c50:	8b 03                	mov    (%rbx),%eax
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    5c52:	48 c1 e1 04          	shl    $0x4,%rcx
    5c56:	49 03 8c 24 10 01 00 00 	add    0x110(%r12),%rcx
  while (data->running == 1) {
    5c5e:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    ourreply->nothing = msg->socket;
    5c64:	89 06                	mov    %eax,(%rsi)
  while (data->running == 1) {
    5c66:	75 3e                	jne    5ca6 <io_thread+0x2a6>
      for (int x = 0 ; x < buffers->count ; x++) {
    5c68:	48 63 11             	movslq (%rcx),%rdx
    5c6b:	85 d2                	test   %edx,%edx
    5c6d:	0f 8e 68 0a 00 00    	jle    66db <io_thread+0xcdb>
    5c73:	48 8b 41 08          	mov    0x8(%rcx),%rax
    5c77:	48 8d 14 92          	lea    (%rdx,%rdx,4),%rdx
    5c7b:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    5c7f:	eb 0d                	jmp    5c8e <io_thread+0x28e>
    5c81:	48 83 c0 28          	add    $0x28,%rax
    5c85:	48 39 d0             	cmp    %rdx,%rax
    5c88:	0f 84 4d 0a 00 00    	je     66db <io_thread+0xcdb>
        if (buffers->buffer[x].available == 0) {
    5c8e:	8b 78 08             	mov    0x8(%rax),%edi
    5c91:	85 ff                	test   %edi,%edi
    5c93:	75 ec                	jne    5c81 <io_thread+0x281>
          buffers->buffer[x].data = send;
    5c95:	48 89 30             	mov    %rsi,(%rax)
          buffers->buffer[x].kind = kind;
    5c98:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
          buffers->buffer[x].available = 1;
    5c9f:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    5ca6:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    5cae:	31 c0                	xor    %eax,%eax
    5cb0:	bf 01 00 00 00       	mov    $0x1,%edi
    5cb5:	48 8d 35 1c 3b 00 00 	lea    0x3b1c(%rip),%rsi        # 97d8 <_IO_stdin_used+0x7d8>
    5cbc:	e8 0f c8 ff ff       	call   24d0 <__printf_chk@plt>
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    5cc1:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    5cc9:	48 c1 e0 04          	shl    $0x4,%rax
    5ccd:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
  while (data->running == 1) {
    5cd5:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5cdb:	0f 85 b6 c9 ff ff    	jne    2697 <io_thread.cold+0x61>
      for (int x = 0 ; x < buffers->count ; x++) {
    5ce1:	8b 08                	mov    (%rax),%ecx
    5ce3:	48 8b 50 08          	mov    0x8(%rax),%rdx
    5ce7:	48 63 c1             	movslq %ecx,%rax
    5cea:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    5cee:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    5cf2:	85 c9                	test   %ecx,%ecx
    5cf4:	0f 8e 7d 10 00 00    	jle    6d77 <io_thread+0x1377>
void* io_thread(void *arg) {
    5cfa:	48 89 d3             	mov    %rdx,%rbx
    5cfd:	eb 0a                	jmp    5d09 <io_thread+0x309>
    5cff:	90                   	nop
      for (int x = 0 ; x < buffers->count ; x++) {
    5d00:	48 83 c3 28          	add    $0x28,%rbx
    5d04:	48 39 c3             	cmp    %rax,%rbx
    5d07:	74 f1                	je     5cfa <io_thread+0x2fa>
        if (buffers->buffer[x].available == 1) {
    5d09:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    5d0d:	75 f1                	jne    5d00 <io_thread+0x300>
          if (buffers->buffer[x].kind == kind) {
    5d0f:	83 7b 20 02          	cmpl   $0x2,0x20(%rbx)
    5d13:	75 eb                	jne    5d00 <io_thread+0x300>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    5d15:	be 28 00 00 00       	mov    $0x28,%esi
    5d1a:	bf 01 00 00 00       	mov    $0x1,%edi
    5d1f:	e8 fc c6 ff ff       	call   2420 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    5d24:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    5d27:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            reply->kind = buffers->buffer[x].kind;
    5d2e:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    5d35:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    5d38:	0f ae f8             	sfence
  struct NewClientMessage *newclientmsg = newclient->data;
    5d3b:	48 8b 00             	mov    (%rax),%rax
    int new_client_socket = newclient_message->socket;
    5d3e:	44 8b 30             	mov    (%rax),%r14d
  struct NewClientMessage *newclientmsg = newclient->data;
    5d41:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    if (new_client_socket == -1) {
    5d46:	41 83 fe ff          	cmp    $0xffffffff,%r14d
    5d4a:	0f 84 4a 11 00 00    	je     6e9a <io_thread+0x149a>
    5d50:	44 89 f2             	mov    %r14d,%edx
    5d53:	48 8d 35 8d 34 00 00 	lea    0x348d(%rip),%rsi        # 91e7 <_IO_stdin_used+0x1e7>
    5d5a:	bf 01 00 00 00       	mov    $0x1,%edi
    5d5f:	31 c0                	xor    %eax,%eax
    5d61:	e8 6a c7 ff ff       	call   24d0 <__printf_chk@plt>
    struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    5d66:	be 0c 00 00 00       	mov    $0xc,%esi
    5d6b:	bf 01 00 00 00       	mov    $0x1,%edi
    5d70:	e8 ab c6 ff ff       	call   2420 <calloc@plt>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    5d75:	bf 01 00 00 00       	mov    $0x1,%edi
    5d7a:	be 10 00 00 00       	mov    $0x10,%esi
    ev->events = EPOLLOUT;
    5d7f:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
    struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    5d85:	49 89 c7             	mov    %rax,%r15
    ev->data.fd = new_client_socket;
    5d88:	44 89 70 04          	mov    %r14d,0x4(%rax)
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    5d8c:	e8 8f c6 ff ff       	call   2420 <calloc@plt>
    void *buf = malloc(size);
    5d91:	bf 0a 00 00 00       	mov    $0xa,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    5d96:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    5d99:	e8 f2 c6 ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    5d9e:	48 85 c0             	test   %rax,%rax
    5da1:	0f 84 cc 10 00 00    	je     6e73 <io_thread+0x1473>
    iov->iov_base = zh_malloc(10);
    5da7:	48 89 03             	mov    %rax,(%rbx)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    5daa:	be 20 00 00 00       	mov    $0x20,%esi
    5daf:	bf 01 00 00 00       	mov    $0x1,%edi
    iov->iov_len = 10;
    5db4:	48 c7 43 08 0a 00 00 00 	movq   $0xa,0x8(%rbx)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    5dbc:	e8 5f c6 ff ff       	call   2420 <calloc@plt>
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    5dc1:	be 20 00 00 00       	mov    $0x20,%esi
    5dc6:	bf 01 00 00 00       	mov    $0x1,%edi
    eventfdstop->kind = 3; 
    5dcb:	c7 00 03 00 00 00    	movl   $0x3,(%rax)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    5dd1:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    5dd6:	e8 45 c6 ff ff       	call   2420 <calloc@plt>
    io_uring_register_eventfd(data->ring, data->dataeventfd);
    5ddb:	41 8b 74 24 6c       	mov    0x6c(%r12),%esi
    5de0:	49 8b 7c 24 60       	mov    0x60(%r12),%rdi
    removed->kind = 7; 
    5de5:	c7 00 07 00 00 00    	movl   $0x7,(%rax)
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    5deb:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    io_uring_register_eventfd(data->ring, data->dataeventfd);
    5df0:	e8 8b c7 ff ff       	call   2580 <io_uring_register_eventfd@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5df5:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5dfc:	8b 94 24 30 01 00 00 	mov    0x130(%rsp),%edx
	unsigned int head, next = sq->sqe_tail + 1;
    5e03:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    5e06:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    5e0b:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5e0d:	f6 c2 02             	test   $0x2,%dl
    5e10:	74 00                	je     5e12 <io_thread+0x412>
	if (next - head <= sq->ring_entries) {
    5e12:	89 f1                	mov    %esi,%ecx
    5e14:	29 c1                	sub    %eax,%ecx
    5e16:	39 8c 24 cc 00 00 00 	cmp    %ecx,0xcc(%rsp)
    5e1d:	0f 82 c5 c8 ff ff    	jb     26e8 <io_thread.cold+0xb2>
	if (ring->flags & IORING_SETUP_SQE128)
    5e23:	c1 ea 0a             	shr    $0xa,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e26:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	sqe->addr3 = 0;
    5e2d:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e31:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5e38:	89 d1                	mov    %edx,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e3a:	41 89 c1             	mov    %eax,%r9d
	sqe->fd = fd;
    5e3d:	8b 04 24             	mov    (%rsp),%eax
		sq->sqe_tail = next;
    5e40:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
    5e47:	83 e1 01             	and    $0x1,%ecx
          struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    5e4a:	be 20 00 00 00       	mov    $0x20,%esi
    5e4f:	bf 01 00 00 00       	mov    $0x1,%edi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e54:	41 d3 e1             	shl    %cl,%r9d
    5e57:	49 c1 e1 06          	shl    $0x6,%r9
    5e5b:	4c 03 8c 24 a8 00 00 00 	add    0xa8(%rsp),%r9
	sqe->fd = fd;
    5e63:	41 89 41 04          	mov    %eax,0x4(%r9)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    5e67:	44 89 f0             	mov    %r14d,%eax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5e6a:	4c 89 cd             	mov    %r9,%rbp
	sqe->opcode = (__u8) op;
    5e6d:	41 c7 01 1d 00 00 00 	movl   $0x1d,(%r9)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    5e74:	49 89 41 08          	mov    %rax,0x8(%r9)
	sqe->addr = (unsigned long) addr;
    5e78:	4d 89 79 10          	mov    %r15,0x10(%r9)
	sqe->len = len;
    5e7c:	49 c7 41 18 01 00 00 00 	movq   $0x1,0x18(%r9)
	sqe->buf_index = 0;
    5e84:	49 c7 41 28 00 00 00 00 	movq   $0x0,0x28(%r9)
	sqe->addr3 = 0;
    5e8c:	41 0f 11 41 30       	movups %xmm0,0x30(%r9)
    5e91:	e8 8a c5 ff ff       	call   2420 <calloc@plt>
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    5e96:	be 18 00 00 00       	mov    $0x18,%esi
    5e9b:	bf 01 00 00 00       	mov    $0x1,%edi
          readywriting->kind = 4; 
    5ea0:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
    5ea6:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    5eab:	e8 70 c5 ff ff       	call   2420 <calloc@plt>
          rr->sockettoken = newclient_message->sockettoken; 
    5eb0:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
          readywriting->data = rr; 
    5eb5:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
          io_uring_submit(&ring);
    5eba:	4c 89 ef             	mov    %r13,%rdi
          rr->client_socket = new_client_socket; 
    5ebd:	44 89 30             	mov    %r14d,(%rax)
          rr->sockettoken = newclient_message->sockettoken; 
    5ec0:	8b 49 04             	mov    0x4(%rcx),%ecx
          readywriting->data = rr; 
    5ec3:	48 89 42 08          	mov    %rax,0x8(%rdx)
          readywriting->event = ev; 
    5ec7:	4c 89 7a 10          	mov    %r15,0x10(%rdx)
          rr->sockettoken = newclient_message->sockettoken; 
    5ecb:	89 48 10             	mov    %ecx,0x10(%rax)
	sqe->user_data = (unsigned long) data;
    5ece:	48 89 55 20          	mov    %rdx,0x20(%rbp)
          io_uring_submit(&ring);
    5ed2:	e8 d9 c4 ff ff       	call   23b0 <io_uring_submit@plt>
    struct SendUserData *dataavailable = calloc(1, sizeof(struct SendUserData));
    5ed7:	be 20 00 00 00       	mov    $0x20,%esi
    5edc:	bf 01 00 00 00       	mov    $0x1,%edi
    5ee1:	e8 3a c5 ff ff       	call   2420 <calloc@plt>
    5ee6:	41 8b 54 24 6c       	mov    0x6c(%r12),%edx
    5eeb:	bf 01 00 00 00       	mov    $0x1,%edi
    5ef0:	48 8d 35 03 33 00 00 	lea    0x3303(%rip),%rsi        # 91fa <_IO_stdin_used+0x1fa>
    dataavailable->kind = 8; 
    5ef7:	c7 00 08 00 00 00    	movl   $0x8,(%rax)
    struct SendUserData *dataavailable = calloc(1, sizeof(struct SendUserData));
    5efd:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5f02:	31 c0                	xor    %eax,%eax
    5f04:	e8 c7 c5 ff ff       	call   24d0 <__printf_chk@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5f09:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    5f10:	8d 50 01             	lea    0x1(%rax),%edx
	if (ring->flags & IORING_SETUP_SQE128)
    5f13:	8b 84 24 30 01 00 00 	mov    0x130(%rsp),%eax
    5f1a:	89 c1                	mov    %eax,%ecx
    5f1c:	c1 e9 0a             	shr    $0xa,%ecx
    5f1f:	83 e1 01             	and    $0x1,%ecx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5f22:	a8 02                	test   $0x2,%al
		head = IO_URING_READ_ONCE(*sq->khead);
    5f24:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    5f29:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5f2b:	0f 85 ce 02 00 00    	jne    61ff <io_thread+0x7ff>
	if (next - head <= sq->ring_entries) {
    5f31:	89 d6                	mov    %edx,%esi
    5f33:	29 c6                	sub    %eax,%esi
    5f35:	39 b4 24 cc 00 00 00 	cmp    %esi,0xcc(%rsp)
    5f3c:	0f 82 4b c7 ff ff    	jb     268d <io_thread.cold+0x57>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f42:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	sqe->addr3 = 0;
    5f49:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(&ring);
    5f4d:	4c 89 ef             	mov    %r13,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f50:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
		sq->sqe_tail = next;
    5f57:	89 94 24 b4 00 00 00 	mov    %edx,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f5e:	d3 e0                	shl    %cl,%eax
    io_uring_prep_readv(sqe, data->dataeventfd, iov, 1, 0);
    5f60:	41 8b 54 24 6c       	mov    0x6c(%r12),%edx
	sqe->user_data = (unsigned long) data;
    5f65:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f6a:	48 c1 e0 06          	shl    $0x6,%rax
    5f6e:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->opcode = (__u8) op;
    5f76:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5f7c:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5f7f:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5f87:	48 89 58 10          	mov    %rbx,0x10(%rax)
	sqe->len = len;
    5f8b:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5f93:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5f9b:	48 89 48 20          	mov    %rcx,0x20(%rax)
	sqe->addr3 = 0;
    5f9f:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(&ring);
    5fa3:	e8 08 c4 ff ff       	call   23b0 <io_uring_submit@plt>
    while (data->running == 1) {
    5fa8:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    5fae:	0f 85 08 02 00 00    	jne    61bc <io_thread+0x7bc>
void* io_thread(void *arg) {
    5fb4:	b8 01 00 00 00       	mov    $0x1,%eax
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
    5fb9:	83 f8 01             	cmp    $0x1,%eax
    5fbc:	0f 85 9e 00 00 00    	jne    6060 <io_thread+0x660>
    5fc2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    5fc8:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    5fd0:	48 c1 e0 04          	shl    $0x4,%rax
    5fd4:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
      for (int x = 0 ; x < buffers->count ; x++) {
    5fdc:	48 63 10             	movslq (%rax),%rdx
    5fdf:	85 d2                	test   %edx,%edx
    5fe1:	7e 7d                	jle    6060 <io_thread+0x660>
    5fe3:	4c 8b 70 08          	mov    0x8(%rax),%r14
    5fe7:	48 8d 04 92          	lea    (%rdx,%rdx,4),%rax
    5feb:	49 8d 04 c6          	lea    (%r14,%rax,8),%rax
    5fef:	eb 10                	jmp    6001 <io_thread+0x601>
    5ff1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5ff8:	49 83 c6 28          	add    $0x28,%r14
    5ffc:	49 39 c6             	cmp    %rax,%r14
    5fff:	74 5f                	je     6060 <io_thread+0x660>
        if (buffers->buffer[x].available == 1) {
    6001:	41 83 7e 08 01       	cmpl   $0x1,0x8(%r14)
    6006:	75 f0                	jne    5ff8 <io_thread+0x5f8>
          if (buffers->buffer[x].kind == kind) {
    6008:	41 83 7e 20 02       	cmpl   $0x2,0x20(%r14)
    600d:	75 e9                	jne    5ff8 <io_thread+0x5f8>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    600f:	be 28 00 00 00       	mov    $0x28,%esi
    6014:	bf 01 00 00 00       	mov    $0x1,%edi
    6019:	e8 02 c4 ff ff       	call   2420 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    601e:	49 8b 16             	mov    (%r14),%rdx
            buffers->buffer[x].available = 0;
    6021:	41 c7 46 08 00 00 00 00 	movl   $0x0,0x8(%r14)
            reply->kind = buffers->buffer[x].kind;
    6029:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    6030:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    6033:	0f ae f8             	sfence
  struct NewClientMessage *newclientmsg = newclient->data;
    6036:	4c 8b 38             	mov    (%rax),%r15
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
    6039:	4d 85 ff             	test   %r15,%r15
    603c:	74 22                	je     6060 <io_thread+0x660>
    603e:	45 8b 37             	mov    (%r15),%r14d
    6041:	45 85 f6             	test   %r14d,%r14d
    6044:	74 1a                	je     6060 <io_thread+0x660>
          if (new_client_socket != -1) {
    6046:	41 83 fe ff          	cmp    $0xffffffff,%r14d
    604a:	0f 85 b4 01 00 00    	jne    6204 <io_thread+0x804>
        while (data->running == 1 && ((ncm = wait_for_new_client(data, 1)) != NULL) && (new_client_socket = ncm->socket)) {
    6050:	41 8b 44 24 44       	mov    0x44(%r12),%eax
    6055:	83 f8 01             	cmp    $0x1,%eax
    6058:	0f 84 6a ff ff ff    	je     5fc8 <io_thread+0x5c8>
    605e:	66 90                	xchg   %ax,%ax
        struct __kernel_timespec delay = {
    6060:	66 0f 6f 15 a8 3d 00 00 	movdqa 0x3da8(%rip),%xmm2        # 9e10 <_IO_stdin_used+0xe10>
        int ret = io_uring_wait_cqe_timeout(&ring, &cqe, &delay);
    6068:	48 8d 54 24 40       	lea    0x40(%rsp),%rdx
    606d:	48 8d 74 24 38       	lea    0x38(%rsp),%rsi
    6072:	4c 89 ef             	mov    %r13,%rdi
        struct __kernel_timespec delay = {
    6075:	0f 29 54 24 40       	movaps %xmm2,0x40(%rsp)
        int ret = io_uring_wait_cqe_timeout(&ring, &cqe, &delay);
    607a:	e8 81 c4 ff ff       	call   2500 <io_uring_wait_cqe_timeout@plt>
        if (ret < 0) { continue; }
    607f:	85 c0                	test   %eax,%eax
    6081:	0f 88 29 01 00 00    	js     61b0 <io_thread+0x7b0>
        if (((struct SendUserData*) cqe->user_data)->kind == 3) {
    6087:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    608c:	4c 8b 3a             	mov    (%rdx),%r15
    608f:	41 8b 07             	mov    (%r15),%eax
    6092:	4c 89 f9             	mov    %r15,%rcx
    6095:	83 f8 03             	cmp    $0x3,%eax
    6098:	0f 84 e7 0c 00 00    	je     6d85 <io_thread+0x1385>
        if (((struct SendUserData*) cqe->user_data)->kind == 8) {
    609e:	83 f8 08             	cmp    $0x8,%eax
    60a1:	0f 84 67 03 00 00    	je     640e <io_thread+0xa0e>
        if (((struct SendUserData*) cqe->user_data)->kind == 4) {
    60a7:	83 f8 04             	cmp    $0x4,%eax
    60aa:	0f 84 84 03 00 00    	je     6434 <io_thread+0xa34>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
    60b0:	83 f8 05             	cmp    $0x5,%eax
    60b3:	0f 84 53 02 00 00    	je     630c <io_thread+0x90c>
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    60b9:	83 f8 07             	cmp    $0x7,%eax
    60bc:	0f 84 19 03 00 00    	je     63db <io_thread+0x9db>
	unsigned int head, next = sq->sqe_tail + 1;
    60c2:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    60c9:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    60d0:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    60d3:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    60d8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    60da:	f6 c1 02             	test   $0x2,%cl
    60dd:	74 00                	je     60df <io_thread+0x6df>
	if (next - head <= sq->ring_entries) {
    60df:	89 d0                	mov    %edx,%eax
    60e1:	29 f0                	sub    %esi,%eax
    60e3:	39 84 24 cc 00 00 00 	cmp    %eax,0xcc(%rsp)
    60ea:	0f 82 ba c5 ff ff    	jb     26aa <io_thread.cold+0x74>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    60f0:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    60f7:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    60fa:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
          io_uring_submit(&ring);
    6101:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    6104:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6107:	41 89 c7             	mov    %eax,%r15d
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    610a:	41 8b 44 24 68       	mov    0x68(%r12),%eax
	sqe->addr3 = 0;
    610f:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6113:	41 d3 e7             	shl    %cl,%r15d
		sq->sqe_tail = next;
    6116:	89 94 24 b4 00 00 00 	mov    %edx,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    611d:	49 c1 e7 06          	shl    $0x6,%r15
    6121:	4c 03 bc 24 a8 00 00 00 	add    0xa8(%rsp),%r15
	sqe->fd = fd;
    6129:	41 89 47 04          	mov    %eax,0x4(%r15)
	sqe->user_data = (unsigned long) data;
    612d:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
	sqe->opcode = (__u8) op;
    6132:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
	sqe->off = offset;
    6139:	49 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%r15)
	sqe->addr = (unsigned long) addr;
    6141:	49 89 5f 10          	mov    %rbx,0x10(%r15)
	sqe->len = len;
    6145:	49 c7 47 18 01 00 00 00 	movq   $0x1,0x18(%r15)
	sqe->buf_index = 0;
    614d:	49 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%r15)
	sqe->user_data = (unsigned long) data;
    6155:	49 89 47 20          	mov    %rax,0x20(%r15)
	sqe->addr3 = 0;
    6159:	41 0f 11 47 30       	movups %xmm0,0x30(%r15)
          io_uring_submit(&ring);
    615e:	e8 4d c2 ff ff       	call   23b0 <io_uring_submit@plt>
          io_uring_prep_readv(sqe, data->dataeventfd, iov, 1, 0);
    6163:	41 8b 44 24 6c       	mov    0x6c(%r12),%eax
	sqe->addr = (unsigned long) addr;
    6168:	49 89 5f 10          	mov    %rbx,0x10(%r15)
	sqe->addr3 = 0;
    616c:	66 0f ef c0          	pxor   %xmm0,%xmm0
	sqe->opcode = (__u8) op;
    6170:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
          io_uring_submit(&ring);
    6177:	4c 89 ef             	mov    %r13,%rdi
	sqe->fd = fd;
    617a:	41 89 47 04          	mov    %eax,0x4(%r15)
	sqe->user_data = (unsigned long) data;
    617e:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
	sqe->off = offset;
    6183:	49 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%r15)
	sqe->len = len;
    618b:	49 c7 47 18 01 00 00 00 	movq   $0x1,0x18(%r15)
	sqe->buf_index = 0;
    6193:	49 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%r15)
	sqe->user_data = (unsigned long) data;
    619b:	49 89 47 20          	mov    %rax,0x20(%r15)
	sqe->addr3 = 0;
    619f:	41 0f 11 47 30       	movups %xmm0,0x30(%r15)
    61a4:	e8 07 c2 ff ff       	call   23b0 <io_uring_submit@plt>
    61a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    while (data->running == 1) {
    61b0:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    61b6:	0f 84 f8 fd ff ff    	je     5fb4 <io_thread+0x5b4>
    61bc:	48 8d 3d 4c 30 00 00 	lea    0x304c(%rip),%rdi        # 920f <_IO_stdin_used+0x20f>
    61c3:	e8 88 c1 ff ff       	call   2350 <puts@plt>
    61c8:	48 8d 3d 4f 30 00 00 	lea    0x304f(%rip),%rdi        # 921e <_IO_stdin_used+0x21e>
    61cf:	e8 7c c1 ff ff       	call   2350 <puts@plt>
}
    61d4:	48 8b 84 24 58 05 00 00 	mov    0x558(%rsp),%rax
    61dc:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    61e5:	0f 85 b9 0c 00 00    	jne    6ea4 <io_thread+0x14a4>
    61eb:	48 81 c4 68 05 00 00 	add    $0x568,%rsp
    61f2:	31 c0                	xor    %eax,%eax
    61f4:	5b                   	pop    %rbx
    61f5:	5d                   	pop    %rbp
    61f6:	41 5c                	pop    %r12
    61f8:	41 5d                	pop    %r13
    61fa:	41 5e                	pop    %r14
    61fc:	41 5f                	pop    %r15
    61fe:	c3                   	ret
		head = io_uring_smp_load_acquire(sq->khead);
    61ff:	e9 2d fd ff ff       	jmp    5f31 <io_thread+0x531>
            struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    6204:	be 0c 00 00 00       	mov    $0xc,%esi
    6209:	bf 01 00 00 00       	mov    $0x1,%edi
    620e:	e8 0d c2 ff ff       	call   2420 <calloc@plt>
            struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    6213:	be 20 00 00 00       	mov    $0x20,%esi
    6218:	bf 01 00 00 00       	mov    $0x1,%edi
            ev->events = EPOLLOUT;
    621d:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
            ev->data.fd = new_client_socket;
    6223:	44 89 70 04          	mov    %r14d,0x4(%rax)
    6227:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
            struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    622c:	e8 ef c1 ff ff       	call   2420 <calloc@plt>
            readywriting->event = ev;
    6231:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
            readywriting->sockettoken = ncm->sockettoken;
    6236:	45 8b 7f 04          	mov    0x4(%r15),%r15d
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    623a:	be 18 00 00 00       	mov    $0x18,%esi
            readywriting->kind = 4; 
    623f:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    6245:	bf 01 00 00 00       	mov    $0x1,%edi
            readywriting->event = ev;
    624a:	4c 89 40 10          	mov    %r8,0x10(%rax)
            readywriting->sockettoken = ncm->sockettoken;
    624e:	44 89 78 18          	mov    %r15d,0x18(%rax)
            readywriting->event = ev;
    6252:	4c 89 44 24 20       	mov    %r8,0x20(%rsp)
            readywriting->sockettoken = ncm->sockettoken;
    6257:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
            struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    625c:	e8 bf c1 ff ff       	call   2420 <calloc@plt>
            readywriting->data = rr; 
    6261:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
		head = IO_URING_READ_ONCE(*sq->khead);
    6266:	48 8b 7c 24 70       	mov    0x70(%rsp),%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    626b:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6272:	4c 8b 44 24 20       	mov    0x20(%rsp),%r8
            rr->client_socket = new_client_socket; 
    6277:	44 89 30             	mov    %r14d,(%rax)
            rr->sockettoken = ncm->sockettoken; 
    627a:	44 89 78 10          	mov    %r15d,0x10(%rax)
            readywriting->data = rr; 
    627e:	48 89 42 08          	mov    %rax,0x8(%rdx)
	unsigned int head, next = sq->sqe_tail + 1;
    6282:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6289:	f6 c1 02             	test   $0x2,%cl
	unsigned int head, next = sq->sqe_tail + 1;
    628c:	8d 70 01             	lea    0x1(%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    628f:	0f 85 5a 01 00 00    	jne    63ef <io_thread+0x9ef>
		head = IO_URING_READ_ONCE(*sq->khead);
    6295:	44 8b 0f             	mov    (%rdi),%r9d
	if (next - head <= sq->ring_entries) {
    6298:	89 f7                	mov    %esi,%edi
    629a:	44 29 cf             	sub    %r9d,%edi
    629d:	39 bc 24 cc 00 00 00 	cmp    %edi,0xcc(%rsp)
    62a4:	0f 82 30 0c 00 00    	jb     6eda <io_thread+0x14da>
	if (ring->flags & IORING_SETUP_SQE128)
    62aa:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    62ad:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
	sqe->addr3 = 0;
    62b4:	66 0f ef c0          	pxor   %xmm0,%xmm0
            io_uring_submit(&ring);
    62b8:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    62bb:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    62be:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    62c5:	d3 e0                	shl    %cl,%eax
	sqe->fd = fd;
    62c7:	8b 0c 24             	mov    (%rsp),%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    62ca:	48 c1 e0 06          	shl    $0x6,%rax
    62ce:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->fd = fd;
    62d6:	89 48 04             	mov    %ecx,0x4(%rax)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    62d9:	44 89 f1             	mov    %r14d,%ecx
    62dc:	48 89 48 08          	mov    %rcx,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    62e0:	4c 89 40 10          	mov    %r8,0x10(%rax)
	sqe->user_data = (unsigned long) data;
    62e4:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->opcode = (__u8) op;
    62e8:	c7 00 1d 00 00 00    	movl   $0x1d,(%rax)
	sqe->len = len;
    62ee:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    62f6:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    62fe:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    6302:	e8 a9 c0 ff ff       	call   23b0 <io_uring_submit@plt>
    6307:	e9 44 fd ff ff       	jmp    6050 <io_thread+0x650>
          struct Request *req = ((struct SendUserData *) cqe->user_data)->data;
    630c:	4c 8b 79 08          	mov    0x8(%rcx),%r15
          if (cqe->res < 0) {
    6310:	8b 42 08             	mov    0x8(%rdx),%eax
              fprintf(stderr, "Async request failed: %s for event: %d\n",
    6313:	45 8b 37             	mov    (%r15),%r14d
          if (cqe->res < 0) {
    6316:	85 c0                	test   %eax,%eax
    6318:	0f 88 e3 0a 00 00    	js     6e01 <io_thread+0x1401>
          switch (req->event_type) {
    631e:	41 83 fe 01          	cmp    $0x1,%r14d
    6322:	0f 84 c8 03 00 00    	je     66f0 <io_thread+0xcf0>
    6328:	41 83 fe 02          	cmp    $0x2,%r14d
    632c:	0f 85 8b 03 00 00    	jne    66bd <io_thread+0xcbd>
                  for (int i = 0; i < req->iovec_count; i++) {
    6332:	41 8b 47 04          	mov    0x4(%r15),%eax
    6336:	45 31 f6             	xor    %r14d,%r14d
    6339:	85 c0                	test   %eax,%eax
    633b:	7e 23                	jle    6360 <io_thread+0x960>
                      free(req->iov[i].iov_base);
    633d:	4c 89 f0             	mov    %r14,%rax
                  for (int i = 0; i < req->iovec_count; i++) {
    6340:	49 83 c6 01          	add    $0x1,%r14
                      free(req->iov[i].iov_base);
    6344:	48 c1 e0 04          	shl    $0x4,%rax
    6348:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    634d:	e8 ce bf ff ff       	call   2320 <free@plt>
                  for (int i = 0; i < req->iovec_count; i++) {
    6352:	45 39 77 04          	cmp    %r14d,0x4(%r15)
    6356:	7f e5                	jg     633d <io_thread+0x93d>
                  io_uring_prep_epoll_ctl(sqe, epollfd, req->client_socket, EPOLL_CTL_DEL, ((struct SendUserData *) cqe->user_data)->event);
    6358:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    635d:	48 8b 08             	mov    (%rax),%rcx
	sqe->fd = fd;
    6360:	8b 04 24             	mov    (%rsp),%eax
    6363:	f3 0f 7e 49 10       	movq   0x10(%rcx),%xmm1
                  io_uring_submit(&ring);
    6368:	4c 89 ef             	mov    %r13,%rdi
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    636b:	66 41 0f 6e 47 08    	movd   0x8(%r15),%xmm0
	sqe->opcode = (__u8) op;
    6371:	c7 45 00 1d 00 00 00 	movl   $0x1d,0x0(%rbp)
	sqe->fd = fd;
    6378:	89 45 04             	mov    %eax,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    637b:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
	sqe->off = offset;
    6380:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
	sqe->len = len;
    6384:	48 c7 45 18 02 00 00 00 	movq   $0x2,0x18(%rbp)
	sqe->buf_index = 0;
    638c:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->user_data = (unsigned long) data;
    6394:	48 89 45 20          	mov    %rax,0x20(%rbp)
	sqe->off = offset;
    6398:	0f 11 45 08          	movups %xmm0,0x8(%rbp)
	sqe->addr3 = 0;
    639c:	66 0f ef c0          	pxor   %xmm0,%xmm0
    63a0:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    63a4:	e8 07 c0 ff ff       	call   23b0 <io_uring_submit@plt>
                  close(req->client_socket);
    63a9:	41 8b 7f 08          	mov    0x8(%r15),%edi
    63ad:	e8 3e c0 ff ff       	call   23f0 <close@plt>
                  free(req);
    63b2:	4c 89 ff             	mov    %r15,%rdi
    63b5:	e8 66 bf ff ff       	call   2320 <free@plt>
            io_uring_cqe_seen(&ring, cqe);
    63ba:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    63bf:	48 85 c0             	test   %rax,%rax
    63c2:	0f 85 f5 02 00 00    	jne    66bd <io_thread+0xcbd>
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    63c8:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    63d0:	8b 00                	mov    (%rax),%eax
    63d2:	83 f8 07             	cmp    $0x7,%eax
    63d5:	0f 85 e7 fc ff ff    	jne    60c2 <io_thread+0x6c2>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    63db:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    63e3:	8b 02                	mov    (%rdx),%eax
    63e5:	83 c0 01             	add    $0x1,%eax
    63e8:	89 02                	mov    %eax,(%rdx)
}
    63ea:	e9 d3 fc ff ff       	jmp    60c2 <io_thread+0x6c2>
		head = io_uring_smp_load_acquire(sq->khead);
    63ef:	8b 3f                	mov    (%rdi),%edi
	if (next - head <= sq->ring_entries) {
    63f1:	89 f0                	mov    %esi,%eax
    63f3:	29 f8                	sub    %edi,%eax
    63f5:	39 84 24 cc 00 00 00 	cmp    %eax,0xcc(%rsp)
    63fc:	0f 82 d2 c2 ff ff    	jb     26d4 <io_thread.cold+0x9e>
    6402:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    6409:	e9 9c fe ff ff       	jmp    62aa <io_thread+0x8aa>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    640e:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6416:	8b 02                	mov    (%rdx),%eax
    6418:	83 c0 01             	add    $0x1,%eax
    641b:	89 02                	mov    %eax,(%rdx)
        if (((struct SendUserData*) cqe->user_data)->kind == 4) {
    641d:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    6422:	4c 8b 3a             	mov    (%rdx),%r15
    6425:	41 8b 07             	mov    (%r15),%eax
    6428:	4c 89 f9             	mov    %r15,%rcx
    642b:	83 f8 04             	cmp    $0x4,%eax
    642e:	0f 85 7c fc ff ff    	jne    60b0 <io_thread+0x6b0>
          struct ReadyWriting *rr = readywriting->data; 
    6434:	49 8b 47 08          	mov    0x8(%r15),%rax
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
    6438:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
          struct ReadyWriting *rr = readywriting->data; 
    643e:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
    6443:	0f 85 79 fc ff ff    	jne    60c2 <io_thread+0x6c2>
    6449:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    644e:	48 89 dd             	mov    %rbx,%rbp
    6451:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    6456:	8b 70 10             	mov    0x10(%rax),%esi
    6459:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    6461:	48 c1 e0 04          	shl    $0x4,%rax
    6465:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
      for (int x = 0 ; x < buffers->count ; x++) {
    646d:	8b 08                	mov    (%rax),%ecx
    646f:	85 c9                	test   %ecx,%ecx
    6471:	0f 8e 2f 02 00 00    	jle    66a6 <io_thread+0xca6>
    6477:	4c 8b 70 08          	mov    0x8(%rax),%r14
    647b:	48 63 c1             	movslq %ecx,%rax
    647e:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6482:	49 8d 04 c6          	lea    (%r14,%rax,8),%rax
    6486:	eb 15                	jmp    649d <io_thread+0xa9d>
    6488:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6490:	49 83 c6 28          	add    $0x28,%r14
    6494:	49 39 c6             	cmp    %rax,%r14
    6497:	0f 84 09 02 00 00    	je     66a6 <io_thread+0xca6>
        if (buffers->buffer[x].available == 1) {
    649d:	41 83 7e 08 01       	cmpl   $0x1,0x8(%r14)
    64a2:	75 ec                	jne    6490 <io_thread+0xa90>
          if (buffers->buffer[x].kind == kind && buffers->buffer[x].filter == filter) {
    64a4:	41 83 7e 20 03       	cmpl   $0x3,0x20(%r14)
    64a9:	75 e5                	jne    6490 <io_thread+0xa90>
    64ab:	41 3b 76 24          	cmp    0x24(%r14),%esi
    64af:	75 df                	jne    6490 <io_thread+0xa90>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    64b1:	be 28 00 00 00       	mov    $0x28,%esi
    64b6:	bf 01 00 00 00       	mov    $0x1,%edi
    64bb:	e8 60 bf ff ff       	call   2420 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    64c0:	49 8b 0e             	mov    (%r14),%rcx
            buffers->buffer[x].available = 0;
    64c3:	41 c7 46 08 00 00 00 00 	movl   $0x0,0x8(%r14)
            reply->kind = buffers->buffer[x].kind;
    64cb:	c7 40 20 03 00 00 00 	movl   $0x3,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    64d2:	48 89 08             	mov    %rcx,(%rax)
            asm volatile ("mfence" ::: "memory");
    64d5:	0f ae f0             	mfence
	unsigned int head, next = sq->sqe_tail + 1;
    64d8:	8b 8c 24 b4 00 00 00 	mov    0xb4(%rsp),%ecx
            struct Write *write = send->data;
    64df:	48 8b 00             	mov    (%rax),%rax
    64e2:	8d 71 01             	lea    0x1(%rcx),%esi
	if (ring->flags & IORING_SETUP_SQE128)
    64e5:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
            int client_socket = write->client_socket; 
    64ec:	8b 78 08             	mov    0x8(%rax),%edi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    64ef:	f6 c1 02             	test   $0x2,%cl
    64f2:	0f 84 4b 08 00 00    	je     6d43 <io_thread+0x1343>
		head = io_uring_smp_load_acquire(sq->khead);
    64f8:	4c 8b 44 24 70       	mov    0x70(%rsp),%r8
    64fd:	45 8b 00             	mov    (%r8),%r8d
            struct Request *req = write->request;
    6500:	4c 8b 30             	mov    (%rax),%r14
	if (next - head <= sq->ring_entries) {
    6503:	89 f0                	mov    %esi,%eax
    6505:	44 29 c0             	sub    %r8d,%eax
    6508:	39 84 24 cc 00 00 00 	cmp    %eax,0xcc(%rsp)
    650f:	0f 82 4f c1 ff ff    	jb     2664 <io_thread.cold+0x2e>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6515:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    651c:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr3 = 0;
    651f:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6523:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    652a:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    652d:	89 c3                	mov    %eax,%ebx
            io_uring_prep_writev(sqe, client_socket, req->iov, req->iovec_count, 0);
    652f:	41 8b 46 04          	mov    0x4(%r14),%eax
		sq->sqe_tail = next;
    6533:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    653a:	d3 e3                	shl    %cl,%ebx
    653c:	49 8d 4e 10          	lea    0x10(%r14),%rcx
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    6540:	be 20 00 00 00       	mov    $0x20,%esi
    6545:	48 c1 e3 06          	shl    $0x6,%rbx
    6549:	48 03 9c 24 a8 00 00 00 	add    0xa8(%rsp),%rbx
            req->event_type = EVENT_TYPE_WRITE;
    6551:	41 c7 06 02 00 00 00 	movl   $0x2,(%r14)
	sqe->fd = fd;
    6558:	89 7b 04             	mov    %edi,0x4(%rbx)
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    655b:	bf 01 00 00 00       	mov    $0x1,%edi
            io_uring_prep_writev(sqe, client_socket, req->iov, req->iovec_count, 0);
    6560:	48 89 4b 10          	mov    %rcx,0x10(%rbx)
	sqe->opcode = (__u8) op;
    6564:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->off = offset;
    656a:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
	sqe->len = len;
    6572:	89 43 18             	mov    %eax,0x18(%rbx)
	sqe->rw_flags = 0;
    6575:	c7 43 1c 00 00 00 00 	movl   $0x0,0x1c(%rbx)
	sqe->buf_index = 0;
    657c:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->addr3 = 0;
    6584:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    6588:	e8 93 be ff ff       	call   2420 <calloc@plt>
            finishedwrite->data = req;
    658d:	66 49 0f 6e c6       	movq   %r14,%xmm0
            io_uring_submit(&ring);
    6592:	4c 89 ef             	mov    %r13,%rdi
            finishedwrite->data = req;
    6595:	41 0f 16 47 10       	movhps 0x10(%r15),%xmm0
            finishedwrite->kind = 5; 
    659a:	c7 00 05 00 00 00    	movl   $0x5,(%rax)
            finishedwrite->data = req;
    65a0:	0f 11 40 08          	movups %xmm0,0x8(%rax)
	sqe->user_data = (unsigned long) data;
    65a4:	48 89 43 20          	mov    %rax,0x20(%rbx)
            io_uring_submit(&ring);
    65a8:	e8 03 be ff ff       	call   23b0 <io_uring_submit@plt>
	if (cqe)
    65ad:	48 83 7c 24 38 00    	cmpq   $0x0,0x38(%rsp)
    65b3:	74 0f                	je     65c4 <io_thread+0xbc4>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    65b5:	48 8b 8c 24 d8 00 00 00 	mov    0xd8(%rsp),%rcx
    65bd:	8b 01                	mov    (%rcx),%eax
    65bf:	83 c0 01             	add    $0x1,%eax
    65c2:	89 01                	mov    %eax,(%rcx)
	unsigned int head, next = sq->sqe_tail + 1;
    65c4:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    65cb:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    65d2:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    65d5:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    65da:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    65dc:	f6 c1 02             	test   $0x2,%cl
    65df:	74 00                	je     65e1 <io_thread+0xbe1>
	if (next - head <= sq->ring_entries) {
    65e1:	89 f7                	mov    %esi,%edi
    65e3:	29 c7                	sub    %eax,%edi
    65e5:	39 bc 24 cc 00 00 00 	cmp    %edi,0xcc(%rsp)
    65ec:	0f 82 68 c0 ff ff    	jb     265a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    65f2:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    65f5:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    65fc:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
              io_uring_submit(&ring);
    6603:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    6606:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    6609:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	sqe->addr3 = 0;
    6610:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6614:	d3 e0                	shl    %cl,%eax
              io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6616:	41 8b 4c 24 68       	mov    0x68(%r12),%ecx
    661b:	48 c1 e0 06          	shl    $0x6,%rax
    661f:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->fd = fd;
    6627:	89 48 04             	mov    %ecx,0x4(%rax)
	sqe->user_data = (unsigned long) data;
    662a:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
	sqe->opcode = (__u8) op;
    662f:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->user_data = (unsigned long) data;
    6635:	48 89 48 20          	mov    %rcx,0x20(%rax)
	sqe->off = offset;
    6639:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    6641:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->len = len;
    6645:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    664d:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    6655:	0f 11 40 30          	movups %xmm0,0x30(%rax)
              io_uring_submit(&ring);
    6659:	e8 52 bd ff ff       	call   23b0 <io_uring_submit@plt>
	sqe->fd = fd;
    665e:	8b 04 24             	mov    (%rsp),%eax
	sqe->addr = (unsigned long) addr;
    6661:	48 89 6b 10          	mov    %rbp,0x10(%rbx)
	sqe->addr3 = 0;
    6665:	66 0f ef c0          	pxor   %xmm0,%xmm0
	sqe->opcode = (__u8) op;
    6669:	c7 03 01 00 00 00    	movl   $0x1,(%rbx)
          io_uring_submit(&ring);
    666f:	4c 89 ef             	mov    %r13,%rdi
	sqe->fd = fd;
    6672:	89 43 04             	mov    %eax,0x4(%rbx)
	sqe->off = offset;
    6675:	48 c7 43 08 00 00 00 00 	movq   $0x0,0x8(%rbx)
	sqe->len = len;
    667d:	48 c7 43 18 01 00 00 00 	movq   $0x1,0x18(%rbx)
	sqe->buf_index = 0;
    6685:	48 c7 43 28 00 00 00 00 	movq   $0x0,0x28(%rbx)
	sqe->user_data = (unsigned long) data;
    668d:	4c 89 7b 20          	mov    %r15,0x20(%rbx)
	sqe->addr3 = 0;
    6691:	0f 11 43 30          	movups %xmm0,0x30(%rbx)
    6695:	e8 16 bd ff ff       	call   23b0 <io_uring_submit@plt>
          while (data->running == 1 && (send = bufferrecv_filter("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1, rr->sockettoken)) != NULL) {
    669a:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    66a0:	0f 84 ab fd ff ff    	je     6451 <io_thread+0xa51>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
    66a6:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    66ab:	48 89 eb             	mov    %rbp,%rbx
    66ae:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
    66b3:	48 8b 0a             	mov    (%rdx),%rcx
    66b6:	8b 01                	mov    (%rcx),%eax
    66b8:	e9 f3 f9 ff ff       	jmp    60b0 <io_thread+0x6b0>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    66bd:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    66c5:	8b 02                	mov    (%rdx),%eax
    66c7:	83 c0 01             	add    $0x1,%eax
    66ca:	89 02                	mov    %eax,(%rdx)
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    66cc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    66d1:	48 8b 00             	mov    (%rax),%rax
    66d4:	8b 00                	mov    (%rax),%eax
}
    66d6:	e9 de f9 ff ff       	jmp    60b9 <io_thread+0x6b9>
  while (data->running == 1) {
    66db:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    66e1:	0f 84 81 f5 ff ff    	je     5c68 <io_thread+0x268>
    66e7:	e9 ba f5 ff ff       	jmp    5ca6 <io_thread+0x2a6>
    66ec:	0f 1f 40 00          	nopl   0x0(%rax)
                  if (!cqe->res) {
    66f0:	85 c0                	test   %eax,%eax
    66f2:	0f 85 38 06 00 00    	jne    6d30 <io_thread+0x1330>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    66f8:	48 8b 0d 21 59 00 00 	mov    0x5921(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    66ff:	ba 0f 00 00 00       	mov    $0xf,%edx
    6704:	be 01 00 00 00       	mov    $0x1,%esi
    6709:	48 8d 3d 99 2a 00 00 	lea    0x2a99(%rip),%rdi        # 91a9 <_IO_stdin_used+0x1a9>
    6710:	e8 4b be ff ff       	call   2560 <fwrite@plt>
            io_uring_cqe_seen(&ring, cqe);
    6715:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    671a:	e9 a0 fc ff ff       	jmp    63bf <io_thread+0x9bf>
    sock = socket(PF_INET, SOCK_STREAM, 0);
    671f:	31 d2                	xor    %edx,%edx
    6721:	be 01 00 00 00       	mov    $0x1,%esi
    6726:	bf 02 00 00 00       	mov    $0x2,%edi
    672b:	e8 c0 be ff ff       	call   25f0 <socket@plt>
    6730:	89 c3                	mov    %eax,%ebx
    if (sock == -1)
    6732:	83 f8 ff             	cmp    $0xffffffff,%eax
    6735:	0f 84 fb be ff ff    	je     2636 <io_thread.cold>
    if (setsockopt(sock,
    673b:	48 8d 4c 24 34       	lea    0x34(%rsp),%rcx
    6740:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    6746:	ba 02 00 00 00       	mov    $0x2,%edx
    674b:	89 c7                	mov    %eax,%edi
    674d:	be 01 00 00 00       	mov    $0x1,%esi
    int enable = 1;
    6752:	c7 44 24 34 01 00 00 00 	movl   $0x1,0x34(%rsp)
    if (setsockopt(sock,
    675a:	e8 01 bc ff ff       	call   2360 <setsockopt@plt>
    675f:	85 c0                	test   %eax,%eax
    6761:	0f 88 db be ff ff    	js     2642 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    6767:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
    if (bind(sock,
    676c:	ba 10 00 00 00       	mov    $0x10,%edx
    6771:	89 df                	mov    %ebx,%edi
    6773:	48 c7 44 24 54 00 00 00 00 	movq   $0x0,0x54(%rsp)
    677c:	c7 44 24 5c 00 00 00 00 	movl   $0x0,0x5c(%rsp)
    srv_addr.sin_family = AF_INET;
    6784:	c7 44 24 50 02 00 18 db 	movl   $0xdb180002,0x50(%rsp)
    if (bind(sock,
    678c:	e8 4f bd ff ff       	call   24e0 <bind@plt>
    6791:	85 c0                	test   %eax,%eax
    6793:	0f 88 b5 be ff ff    	js     264e <io_thread.cold+0x18>
    if (listen(sock, 10) < 0) {
    6799:	be 0a 00 00 00       	mov    $0xa,%esi
    679e:	89 df                	mov    %ebx,%edi
    67a0:	e8 fb bc ff ff       	call   24a0 <listen@plt>
    67a5:	85 c0                	test   %eax,%eax
    67a7:	0f 88 c8 be ff ff    	js     2675 <io_thread.cold+0x3f>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    67ad:	89 d9                	mov    %ebx,%ecx
    67af:	ba db 18 00 00       	mov    $0x18db,%edx
    67b4:	48 8d 35 9d 2e 00 00 	lea    0x2e9d(%rip),%rsi        # 9658 <_IO_stdin_used+0x658>
    67bb:	31 c0                	xor    %eax,%eax
    67bd:	bf 01 00 00 00       	mov    $0x1,%edi
    67c2:	e8 09 bd ff ff       	call   24d0 <__printf_chk@plt>
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    67c7:	be 04 00 00 00       	mov    $0x4,%esi
    67cc:	bf 01 00 00 00       	mov    $0x1,%edi
    67d1:	e8 4a bc ff ff       	call   2420 <calloc@plt>
    67d6:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    67de:	bf 01 00 00 00       	mov    $0x1,%edi
    67e3:	48 8d 35 8e 2e 00 00 	lea    0x2e8e(%rip),%rsi        # 9678 <_IO_stdin_used+0x678>
    msg->socket = sock;
    67ea:	89 18                	mov    %ebx,(%rax)
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    67ec:	48 89 c5             	mov    %rax,%rbp
    67ef:	31 c0                	xor    %eax,%eax
    67f1:	e8 da bc ff ff       	call   24d0 <__printf_chk@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET, msg);
    67f6:	49 63 94 24 18 01 00 00 	movslq 0x118(%r12),%rdx
    67fe:	48 c1 e2 04          	shl    $0x4,%rdx
    6802:	49 03 94 24 10 01 00 00 	add    0x110(%r12),%rdx
  while (data->running == 1) {
    680a:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6810:	0f 85 b6 00 00 00    	jne    68cc <io_thread+0xecc>
      for (int x = 0 ; x < buffers->count ; x++) {
    6816:	48 63 0a             	movslq (%rdx),%rcx
    6819:	85 c9                	test   %ecx,%ecx
    681b:	7e ed                	jle    680a <io_thread+0xe0a>
    681d:	48 8b 42 08          	mov    0x8(%rdx),%rax
    6821:	48 8d 0c 89          	lea    (%rcx,%rcx,4),%rcx
    6825:	48 8d 0c c8          	lea    (%rax,%rcx,8),%rcx
    6829:	eb 09                	jmp    6834 <io_thread+0xe34>
    682b:	48 83 c0 28          	add    $0x28,%rax
    682f:	48 39 c1             	cmp    %rax,%rcx
    6832:	74 d6                	je     680a <io_thread+0xe0a>
        if (buffers->buffer[x].available == 0) {
    6834:	44 8b 50 08          	mov    0x8(%rax),%r10d
    6838:	45 85 d2             	test   %r10d,%r10d
    683b:	75 ee                	jne    682b <io_thread+0xe2b>
          buffers->buffer[x].data = send;
    683d:	48 89 28             	mov    %rbp,(%rax)
          buffers->buffer[x].kind = kind;
    6840:	c7 40 20 00 00 00 00 	movl   $0x0,0x20(%rax)
          buffers->buffer[x].available = 1;
    6847:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
    684e:	49 63 84 24 1c 01 00 00 	movslq 0x11c(%r12),%rax
    6856:	48 c1 e0 04          	shl    $0x4,%rax
    685a:	49 03 84 24 10 01 00 00 	add    0x110(%r12),%rax
  while (data->running == 1) {
    6862:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6868:	75 62                	jne    68cc <io_thread+0xecc>
      for (int x = 0 ; x < buffers->count ; x++) {
    686a:	8b 10                	mov    (%rax),%edx
    686c:	48 8b 48 08          	mov    0x8(%rax),%rcx
    6870:	48 63 c2             	movslq %edx,%rax
    6873:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6877:	48 8d 04 c1          	lea    (%rcx,%rax,8),%rax
    687b:	85 d2                	test   %edx,%edx
    687d:	0f 8e ee 05 00 00    	jle    6e71 <io_thread+0x1471>
void* io_thread(void *arg) {
    6883:	48 89 cd             	mov    %rcx,%rbp
    6886:	eb 11                	jmp    6899 <io_thread+0xe99>
    6888:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    6890:	48 83 c5 28          	add    $0x28,%rbp
    6894:	48 39 e8             	cmp    %rbp,%rax
    6897:	74 ea                	je     6883 <io_thread+0xe83>
        if (buffers->buffer[x].available == 1) {
    6899:	83 7d 08 01          	cmpl   $0x1,0x8(%rbp)
    689d:	75 f1                	jne    6890 <io_thread+0xe90>
          if (buffers->buffer[x].kind == kind) {
    689f:	83 7d 20 01          	cmpl   $0x1,0x20(%rbp)
    68a3:	75 eb                	jne    6890 <io_thread+0xe90>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    68a5:	be 28 00 00 00       	mov    $0x28,%esi
    68aa:	bf 01 00 00 00       	mov    $0x1,%edi
    68af:	e8 6c bb ff ff       	call   2420 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    68b4:	48 8b 55 00          	mov    0x0(%rbp),%rdx
            buffers->buffer[x].available = 0;
    68b8:	c7 45 08 00 00 00 00 	movl   $0x0,0x8(%rbp)
            reply->kind = buffers->buffer[x].kind;
    68bf:	c7 40 20 01 00 00 00 	movl   $0x1,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    68c6:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    68c9:	0f ae f8             	sfence
    68cc:	49 8b 94 24 20 01 00 00 	mov    0x120(%r12),%rdx
    68d4:	48 8d 35 c5 2d 00 00 	lea    0x2dc5(%rip),%rsi        # 96a0 <_IO_stdin_used+0x6a0>
    68db:	bf 01 00 00 00       	mov    $0x1,%edi
    68e0:	31 c0                	xor    %eax,%eax
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    68e2:	4c 8d 74 24 38       	lea    0x38(%rsp),%r14
    68e7:	e8 e4 bb ff ff       	call   24d0 <__printf_chk@plt>
    68ec:	48 8d 44 24 60       	lea    0x60(%rsp),%rax
    68f1:	4c 89 e9             	mov    %r13,%rcx
    68f4:	4c 89 f2             	mov    %r14,%rdx
    68f7:	48 89 c6             	mov    %rax,%rsi
    68fa:	89 df                	mov    %ebx,%edi
    socklen_t client_addr_len = sizeof(client_addr);
    68fc:	c7 44 24 38 10 00 00 00 	movl   $0x10,0x38(%rsp)
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6904:	48 89 04 24          	mov    %rax,(%rsp)
    6908:	e8 53 f0 ff ff       	call   5960 <add_accept_request>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    690d:	bf 01 00 00 00       	mov    $0x1,%edi
    6912:	be 10 00 00 00       	mov    $0x10,%esi
    6917:	e8 04 bb ff ff       	call   2420 <calloc@plt>
    void *buf = malloc(size);
    691c:	bf e8 03 00 00       	mov    $0x3e8,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    6921:	48 89 c5             	mov    %rax,%rbp
    void *buf = malloc(size);
    6924:	e8 67 bb ff ff       	call   2490 <malloc@plt>
    if (!buf) {
    6929:	48 85 c0             	test   %rax,%rax
    692c:	0f 84 77 05 00 00    	je     6ea9 <io_thread+0x14a9>
    iov->iov_base = zh_malloc(1000);
    6932:	48 89 45 00          	mov    %rax,0x0(%rbp)
	unsigned int head, next = sq->sqe_tail + 1;
    6936:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    693d:	8b 94 24 30 01 00 00 	mov    0x130(%rsp),%edx
    iov->iov_len = 1000;
    6944:	48 c7 45 08 e8 03 00 00 	movq   $0x3e8,0x8(%rbp)
	unsigned int head, next = sq->sqe_tail + 1;
    694c:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    694f:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    6954:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6956:	f6 c2 02             	test   $0x2,%dl
    6959:	0f 85 21 04 00 00    	jne    6d80 <io_thread+0x1380>
	if (next - head <= sq->ring_entries) {
    695f:	89 f1                	mov    %esi,%ecx
    6961:	29 c1                	sub    %eax,%ecx
    6963:	39 8c 24 cc 00 00 00 	cmp    %ecx,0xcc(%rsp)
    696a:	0f 82 30 bd ff ff    	jb     26a0 <io_thread.cold+0x6a>
	if (ring->flags & IORING_SETUP_SQE128)
    6970:	c1 ea 0a             	shr    $0xa,%edx
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
    6973:	4d 8d 7c 24 68       	lea    0x68(%r12),%r15
	sqe->addr3 = 0;
    6978:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(&ring);
    697c:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    697f:	89 d1                	mov    %edx,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6981:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    6988:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
		sq->sqe_tail = next;
    698f:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
    6996:	83 e1 01             	and    $0x1,%ecx
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6999:	41 8b 54 24 68       	mov    0x68(%r12),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    699e:	d3 e0                	shl    %cl,%eax
    69a0:	48 c1 e0 06          	shl    $0x6,%rax
    69a4:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->opcode = (__u8) op;
    69ac:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    69b2:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    69b5:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    69bd:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->len = len;
    69c1:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    69c9:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    69d1:	4c 89 78 20          	mov    %r15,0x20(%rax)
	sqe->addr3 = 0;
    69d5:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(&ring);
    69d9:	e8 d2 b9 ff ff       	call   23b0 <io_uring_submit@plt>
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    69de:	48 8d 44 24 40       	lea    0x40(%rsp),%rax
    69e3:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    while (data->running == 1) {
    69e8:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    69ee:	0f 85 17 03 00 00    	jne    6d0b <io_thread+0x130b>
	if (ring->flags & IORING_SETUP_CQE32)
    69f4:	8b 8c 24 30 01 00 00 	mov    0x130(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    69fb:	8b 94 24 20 01 00 00 	mov    0x120(%rsp),%edx
	if (ring->flags & IORING_SETUP_CQE32)
    6a02:	c1 e9 0b             	shr    $0xb,%ecx
    6a05:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    6a08:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
    6a10:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    6a12:	48 8b bc 24 d8 00 00 00 	mov    0xd8(%rsp),%rdi
    6a1a:	8b 37                	mov    (%rdi),%esi
		if (!available)
    6a1c:	39 f0                	cmp    %esi,%eax
    6a1e:	74 36                	je     6a56 <io_thread+0x1056>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    6a20:	89 d0                	mov    %edx,%eax
    6a22:	21 f0                	and    %esi,%eax
    6a24:	d3 e0                	shl    %cl,%eax
    6a26:	48 c1 e0 04          	shl    $0x4,%rax
    6a2a:	48 03 84 24 08 01 00 00 	add    0x108(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    6a32:	f6 84 24 39 01 00 00 01 	testb  $0x1,0x139(%rsp)
    6a3a:	0f 85 95 02 00 00    	jne    6cd5 <io_thread+0x12d5>
    6a40:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    6a44:	0f 85 86 04 00 00    	jne    6ed0 <io_thread+0x14d0>
			if (cqe->res < 0)
    6a4a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6a4d:	83 c6 01             	add    $0x1,%esi
    6a50:	89 37                	mov    %esi,(%rdi)
			if (!err)
    6a52:	85 c0                	test   %eax,%eax
    6a54:	79 b2                	jns    6a08 <io_thread+0x1008>
	*cqe_ptr = cqe;
    6a56:	48 c7 44 24 40 00 00 00 00 	movq   $0x0,0x40(%rsp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    6a5f:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    6a64:	b9 01 00 00 00       	mov    $0x1,%ecx
    6a69:	31 d2                	xor    %edx,%edx
    6a6b:	45 31 c0             	xor    %r8d,%r8d
    6a6e:	4c 89 ef             	mov    %r13,%rdi
    6a71:	e8 4a ba ff ff       	call   24c0 <__io_uring_get_cqe@plt>
    6a76:	89 c1                	mov    %eax,%ecx
        if (cqe->user_data == 1) {
    6a78:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6a7d:	48 8b 10             	mov    (%rax),%rdx
    6a80:	48 83 fa 01          	cmp    $0x1,%rdx
    6a84:	0f 84 66 02 00 00    	je     6cf0 <io_thread+0x12f0>
        if (ret < 0)
    6a8a:	85 c9                	test   %ecx,%ecx
    6a8c:	0f 88 ef bb ff ff    	js     2681 <io_thread.cold+0x4b>
        if (cqe->res < 0) {
    6a92:	8b 40 08             	mov    0x8(%rax),%eax
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    6a95:	44 8b 02             	mov    (%rdx),%r8d
        if (cqe->res < 0) {
    6a98:	85 c0                	test   %eax,%eax
    6a9a:	0f 88 11 03 00 00    	js     6db1 <io_thread+0x13b1>
        switch (req->event_type) {
    6aa0:	45 85 c0             	test   %r8d,%r8d
    6aa3:	0f 84 9e 00 00 00    	je     6b47 <io_thread+0x1147>
    6aa9:	41 83 f8 01          	cmp    $0x1,%r8d
    6aad:	0f 85 77 01 00 00    	jne    6c2a <io_thread+0x122a>
                if (!cqe->res) {
    6ab3:	85 c0                	test   %eax,%eax
    6ab5:	0f 84 95 02 00 00    	je     6d50 <io_thread+0x1350>
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    6abb:	48 8d b4 24 50 01 00 00 	lea    0x150(%rsp),%rsi
    6ac3:	4d 8b 8c 24 10 01 00 00 	mov    0x110(%r12),%r9
    6acb:	48 8b 4a 10          	mov    0x10(%rdx),%rcx
    6acf:	4c 8d 94 24 50 05 00 00 	lea    0x550(%rsp),%r10
    6ad7:	41 8b bc 24 18 01 00 00 	mov    0x118(%r12),%edi
    for (int i = 0; i < dest_sz; i++) {
    6adf:	48 89 f0             	mov    %rsi,%rax
    6ae2:	eb 15                	jmp    6af9 <io_thread+0x10f9>
    6ae4:	0f 1f 40 00          	nopl   0x0(%rax)
    6ae8:	48 83 c0 01          	add    $0x1,%rax
    6aec:	48 83 c1 01          	add    $0x1,%rcx
    6af0:	4c 39 d0             	cmp    %r10,%rax
    6af3:	0f 84 51 03 00 00    	je     6e4a <io_thread+0x144a>
        dest[i] = src[i];
    6af9:	44 0f b6 01          	movzbl (%rcx),%r8d
    6afd:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    6b00:	41 80 f8 0d          	cmp    $0xd,%r8b
    6b04:	75 e2                	jne    6ae8 <io_thread+0x10e8>
    6b06:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    6b0a:	75 dc                	jne    6ae8 <io_thread+0x10e8>
            dest[i] = '\0';
    6b0c:	c6 00 00             	movb   $0x0,(%rax)
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    6b0f:	48 63 c7             	movslq %edi,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    6b12:	8b 4a 08             	mov    0x8(%rdx),%ecx
    6b15:	4c 89 e7             	mov    %r12,%rdi
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    6b18:	48 c1 e0 04          	shl    $0x4,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    6b1c:	44 8b 42 0c          	mov    0xc(%rdx),%r8d
    6b20:	48 89 f2             	mov    %rsi,%rdx
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    6b23:	4c 01 c8             	add    %r9,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, req->sockettoken, ring);
    6b26:	4d 89 e9             	mov    %r13,%r9
    6b29:	48 89 c6             	mov    %rax,%rsi
    6b2c:	e8 ff eb ff ff       	call   5730 <handle_http_method>
                eventfd_write(data->otherdataeventfd, 0);
    6b31:	41 8b 7c 24 70       	mov    0x70(%r12),%edi
    6b36:	31 f6                	xor    %esi,%esi
    6b38:	e8 43 b9 ff ff       	call   2480 <eventfd_write@plt>
          io_uring_cqe_seen(&ring, cqe);
    6b3d:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
                break;
    6b42:	e9 de 00 00 00       	jmp    6c25 <io_thread+0x1225>
                add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6b47:	48 8b 34 24          	mov    (%rsp),%rsi
    6b4b:	4c 89 e9             	mov    %r13,%rcx
    6b4e:	4c 89 f2             	mov    %r14,%rdx
    6b51:	89 df                	mov    %ebx,%edi
    6b53:	e8 08 ee ff ff       	call   5960 <add_accept_request>
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
    6b58:	be 08 00 00 00       	mov    $0x8,%esi
    6b5d:	bf 01 00 00 00       	mov    $0x1,%edi
    6b62:	e8 b9 b8 ff ff       	call   2420 <calloc@plt>
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
    6b67:	49 63 b4 24 18 01 00 00 	movslq 0x118(%r12),%rsi
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
    6b6f:	48 89 c7             	mov    %rax,%rdi
                newclientmsg->socket = cqe->res;
    6b72:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
    6b77:	48 c1 e6 04          	shl    $0x4,%rsi
    6b7b:	49 03 b4 24 10 01 00 00 	add    0x110(%r12),%rsi
  while (data->running == 1) {
    6b83:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
                newclientmsg->socket = cqe->res;
    6b89:	8b 50 08             	mov    0x8(%rax),%edx
                data->sockettoken++;
    6b8c:	41 8b 84 24 28 01 00 00 	mov    0x128(%r12),%eax
    6b94:	8d 48 01             	lea    0x1(%rax),%ecx
                newclientmsg->socket = cqe->res;
    6b97:	66 0f 6e c2          	movd   %edx,%xmm0
    6b9b:	66 0f 6e e1          	movd   %ecx,%xmm4
                data->sockettoken++;
    6b9f:	41 89 8c 24 28 01 00 00 	mov    %ecx,0x128(%r12)
                newclientmsg->socket = cqe->res;
    6ba7:	66 0f 62 c4          	punpckldq %xmm4,%xmm0
    6bab:	66 0f d6 07          	movq   %xmm0,(%rdi)
  while (data->running == 1) {
    6baf:	75 64                	jne    6c15 <io_thread+0x1215>
      for (int x = 0 ; x < buffers->count ; x++) {
    6bb1:	48 63 16             	movslq (%rsi),%rdx
    6bb4:	85 d2                	test   %edx,%edx
    6bb6:	0f 8e 5c 01 00 00    	jle    6d18 <io_thread+0x1318>
    6bbc:	48 8b 46 08          	mov    0x8(%rsi),%rax
    6bc0:	48 8d 14 92          	lea    (%rdx,%rdx,4),%rdx
    6bc4:	48 8d 14 d0          	lea    (%rax,%rdx,8),%rdx
    6bc8:	eb 0d                	jmp    6bd7 <io_thread+0x11d7>
    6bca:	48 83 c0 28          	add    $0x28,%rax
    6bce:	48 39 c2             	cmp    %rax,%rdx
    6bd1:	0f 84 41 01 00 00    	je     6d18 <io_thread+0x1318>
        if (buffers->buffer[x].available == 0) {
    6bd7:	44 8b 48 08          	mov    0x8(%rax),%r9d
    6bdb:	45 85 c9             	test   %r9d,%r9d
    6bde:	75 ea                	jne    6bca <io_thread+0x11ca>
          buffers->buffer[x].data = send;
    6be0:	48 89 38             	mov    %rdi,(%rax)
          buffers->buffer[x].kind = kind;
    6be3:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
          buffers->buffer[x].available = 1;
    6bea:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
                add_read_request(data, &data->iomailboxes[data->other_io], cqe->res, data->sockettoken, &ring);
    6bf1:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6bf6:	49 63 b4 24 18 01 00 00 	movslq 0x118(%r12),%rsi
    6bfe:	41 8b 8c 24 28 01 00 00 	mov    0x128(%r12),%ecx
    6c06:	8b 50 08             	mov    0x8(%rax),%edx
    6c09:	48 c1 e6 04          	shl    $0x4,%rsi
    6c0d:	49 03 b4 24 10 01 00 00 	add    0x110(%r12),%rsi
    6c15:	4d 89 e8             	mov    %r13,%r8
    6c18:	4c 89 e7             	mov    %r12,%rdi
    6c1b:	e8 70 e5 ff ff       	call   5190 <add_read_request>
          io_uring_cqe_seen(&ring, cqe);
    6c20:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
	if (cqe)
    6c25:	48 85 c0             	test   %rax,%rax
    6c28:	74 0f                	je     6c39 <io_thread+0x1239>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6c2a:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6c32:	8b 02                	mov    (%rdx),%eax
    6c34:	83 c0 01             	add    $0x1,%eax
    6c37:	89 02                	mov    %eax,(%rdx)
	unsigned int head, next = sq->sqe_tail + 1;
    6c39:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6c40:	8b 94 24 30 01 00 00 	mov    0x130(%rsp),%edx
	unsigned int head, next = sq->sqe_tail + 1;
    6c47:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    6c4a:	48 8b 44 24 70       	mov    0x70(%rsp),%rax
    6c4f:	8b 00                	mov    (%rax),%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6c51:	f6 c2 02             	test   $0x2,%dl
    6c54:	74 00                	je     6c56 <io_thread+0x1256>
	if (next - head <= sq->ring_entries) {
    6c56:	89 f1                	mov    %esi,%ecx
    6c58:	29 c1                	sub    %eax,%ecx
    6c5a:	39 8c 24 cc 00 00 00 	cmp    %ecx,0xcc(%rsp)
    6c61:	0f 82 77 ba ff ff    	jb     26de <io_thread.cold+0xa8>
	if (ring->flags & IORING_SETUP_SQE128)
    6c67:	c1 ea 0a             	shr    $0xa,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6c6a:	8b 84 24 b4 00 00 00 	mov    0xb4(%rsp),%eax
    6c71:	23 84 24 c8 00 00 00 	and    0xc8(%rsp),%eax
        io_uring_submit(&ring);
    6c78:	4c 89 ef             	mov    %r13,%rdi
	if (ring->flags & IORING_SETUP_SQE128)
    6c7b:	89 d1                	mov    %edx,%ecx
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6c7d:	41 8b 54 24 68       	mov    0x68(%r12),%edx
		sq->sqe_tail = next;
    6c82:	89 b4 24 b4 00 00 00 	mov    %esi,0xb4(%rsp)
	sqe->addr3 = 0;
    6c89:	66 0f ef ed          	pxor   %xmm5,%xmm5
	if (ring->flags & IORING_SETUP_SQE128)
    6c8d:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6c90:	d3 e0                	shl    %cl,%eax
    6c92:	48 c1 e0 06          	shl    $0x6,%rax
    6c96:	48 03 84 24 a8 00 00 00 	add    0xa8(%rsp),%rax
	sqe->fd = fd;
    6c9e:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->addr = (unsigned long) addr;
    6ca1:	48 89 68 10          	mov    %rbp,0x10(%rax)
	sqe->user_data = (unsigned long) data;
    6ca5:	4c 89 78 20          	mov    %r15,0x20(%rax)
	sqe->opcode = (__u8) op;
    6ca9:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->off = offset;
    6caf:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->len = len;
    6cb7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    6cbf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    6cc7:	0f 11 68 30          	movups %xmm5,0x30(%rax)
        io_uring_submit(&ring);
    6ccb:	e8 e0 b6 ff ff       	call   23b0 <io_uring_submit@plt>
    while (data->running == 1) {
    6cd0:	e9 13 fd ff ff       	jmp    69e8 <io_thread+0xfe8>
	*cqe_ptr = cqe;
    6cd5:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    6cda:	48 85 c0             	test   %rax,%rax
    6cdd:	0f 84 7c fd ff ff    	je     6a5f <io_thread+0x105f>
        if (cqe->user_data == 1) {
    6ce3:	48 8b 10             	mov    (%rax),%rdx
    6ce6:	48 83 fa 01          	cmp    $0x1,%rdx
    6cea:	0f 85 a2 fd ff ff    	jne    6a92 <io_thread+0x1092>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6cf0:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6cf8:	48 8d 3d 84 24 00 00 	lea    0x2484(%rip),%rdi        # 9183 <_IO_stdin_used+0x183>
    6cff:	8b 02                	mov    (%rdx),%eax
    6d01:	83 c0 01             	add    $0x1,%eax
    6d04:	89 02                	mov    %eax,(%rdx)
    6d06:	e8 45 b6 ff ff       	call   2350 <puts@plt>
  if (data->io_mode == IO_MODE_SEND) {
    6d0b:	41 8b 84 24 0c 01 00 00 	mov    0x10c(%r12),%eax
    6d13:	e9 0c ee ff ff       	jmp    5b24 <io_thread+0x124>
  while (data->running == 1) {
    6d18:	41 83 7c 24 44 01    	cmpl   $0x1,0x44(%r12)
    6d1e:	0f 84 8d fe ff ff    	je     6bb1 <io_thread+0x11b1>
    6d24:	e9 c8 fe ff ff       	jmp    6bf1 <io_thread+0x11f1>
    6d29:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                  free(req->iov[0].iov_base);
    6d30:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    6d34:	e8 e7 b5 ff ff       	call   2320 <free@plt>
            io_uring_cqe_seen(&ring, cqe);
    6d39:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
                  break;
    6d3e:	e9 7c f6 ff ff       	jmp    63bf <io_thread+0x9bf>
		head = IO_URING_READ_ONCE(*sq->khead);
    6d43:	4c 8b 44 24 70       	mov    0x70(%rsp),%r8
    6d48:	45 8b 00             	mov    (%r8),%r8d
    6d4b:	e9 b0 f7 ff ff       	jmp    6500 <io_thread+0xb00>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6d50:	48 8b 0d c9 52 00 00 	mov    0x52c9(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6d57:	ba 0f 00 00 00       	mov    $0xf,%edx
    6d5c:	be 01 00 00 00       	mov    $0x1,%esi
    6d61:	48 8d 3d 41 24 00 00 	lea    0x2441(%rip),%rdi        # 91a9 <_IO_stdin_used+0x1a9>
    6d68:	e8 f3 b7 ff ff       	call   2560 <fwrite@plt>
          io_uring_cqe_seen(&ring, cqe);
    6d6d:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    6d72:	e9 ae fe ff ff       	jmp    6c25 <io_thread+0x1225>
      for (int x = 0 ; x < buffers->count ; x++) {
    6d77:	eb fe                	jmp    6d77 <io_thread+0x1377>
    6d79:	eb fe                	jmp    6d79 <io_thread+0x1379>
    6d7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    6d80:	e9 da fb ff ff       	jmp    695f <io_thread+0xf5f>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6d85:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6d8d:	48 8d 3d ef 23 00 00 	lea    0x23ef(%rip),%rdi        # 9183 <_IO_stdin_used+0x183>
    6d94:	8b 02                	mov    (%rdx),%eax
    6d96:	83 c0 01             	add    $0x1,%eax
    6d99:	89 02                	mov    %eax,(%rdx)
    6d9b:	e8 b0 b5 ff ff       	call   2350 <puts@plt>
    6da0:	48 8d 3d 68 24 00 00 	lea    0x2468(%rip),%rdi        # 920f <_IO_stdin_used+0x20f>
    6da7:	e8 a4 b5 ff ff       	call   2350 <puts@plt>
    6dac:	e9 17 f4 ff ff       	jmp    61c8 <io_thread+0x7c8>
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    6db1:	f7 d8                	neg    %eax
    6db3:	44 89 44 24 10       	mov    %r8d,0x10(%rsp)
    6db8:	89 c7                	mov    %eax,%edi
    6dba:	e8 e1 b7 ff ff       	call   25a0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6dbf:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
    6dc4:	be 01 00 00 00       	mov    $0x1,%esi
    6dc9:	48 8b 3d 50 52 00 00 	mov    0x5250(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    6dd0:	48 89 c1             	mov    %rax,%rcx
    6dd3:	48 8d 15 ee 28 00 00 	lea    0x28ee(%rip),%rdx        # 96c8 <_IO_stdin_used+0x6c8>
    6dda:	31 c0                	xor    %eax,%eax
    6ddc:	e8 8f b7 ff ff       	call   2570 <__fprintf_chk@plt>
	if (cqe)
    6de1:	48 83 7c 24 40 00    	cmpq   $0x0,0x40(%rsp)
    6de7:	0f 84 fb fb ff ff    	je     69e8 <io_thread+0xfe8>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6ded:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6df5:	8b 02                	mov    (%rdx),%eax
    6df7:	83 c0 01             	add    $0x1,%eax
    6dfa:	89 02                	mov    %eax,(%rdx)
}
    6dfc:	e9 e7 fb ff ff       	jmp    69e8 <io_thread+0xfe8>
              fprintf(stderr, "Async request failed: %s for event: %d\n",
    6e01:	f7 d8                	neg    %eax
    6e03:	89 c7                	mov    %eax,%edi
    6e05:	e8 96 b7 ff ff       	call   25a0 <strerror@plt>
    6e0a:	48 8b 3d 0f 52 00 00 	mov    0x520f(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    6e11:	45 89 f0             	mov    %r14d,%r8d
    6e14:	48 8d 15 ad 28 00 00 	lea    0x28ad(%rip),%rdx        # 96c8 <_IO_stdin_used+0x6c8>
    6e1b:	48 89 c1             	mov    %rax,%rcx
    6e1e:	be 01 00 00 00       	mov    $0x1,%esi
    6e23:	31 c0                	xor    %eax,%eax
    6e25:	e8 46 b7 ff ff       	call   2570 <__fprintf_chk@plt>
	if (cqe)
    6e2a:	48 83 7c 24 38 00    	cmpq   $0x0,0x38(%rsp)
    6e30:	0f 84 7a f3 ff ff    	je     61b0 <io_thread+0x7b0>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6e36:	48 8b 94 24 d8 00 00 00 	mov    0xd8(%rsp),%rdx
    6e3e:	8b 02                	mov    (%rdx),%eax
    6e40:	83 c0 01             	add    $0x1,%eax
    6e43:	89 02                	mov    %eax,(%rdx)
}
    6e45:	e9 66 f3 ff ff       	jmp    61b0 <io_thread+0x7b0>
    6e4a:	48 8b 0d cf 51 00 00 	mov    0x51cf(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6e51:	ba 12 00 00 00       	mov    $0x12,%edx
    6e56:	be 01 00 00 00       	mov    $0x1,%esi
    6e5b:	48 8d 3d dc 22 00 00 	lea    0x22dc(%rip),%rdi        # 913e <_IO_stdin_used+0x13e>
    6e62:	e8 f9 b6 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    6e67:	bf 01 00 00 00       	mov    $0x1,%edi
    6e6c:	e8 cf b6 ff ff       	call   2540 <exit@plt>
      for (int x = 0 ; x < buffers->count ; x++) {
    6e71:	eb fe                	jmp    6e71 <io_thread+0x1471>
    6e73:	48 8b 0d a6 51 00 00 	mov    0x51a6(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6e7a:	ba 28 00 00 00       	mov    $0x28,%edx
    6e7f:	be 01 00 00 00       	mov    $0x1,%esi
    6e84:	48 8d 3d 75 27 00 00 	lea    0x2775(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    6e8b:	e8 d0 b6 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    6e90:	bf 01 00 00 00       	mov    $0x1,%edi
    6e95:	e8 a6 b6 ff ff       	call   2540 <exit@plt>
      exit(1); 
    6e9a:	bf 01 00 00 00       	mov    $0x1,%edi
    6e9f:	e8 9c b6 ff ff       	call   2540 <exit@plt>
}
    6ea4:	e8 f7 b4 ff ff       	call   23a0 <__stack_chk_fail@plt>
    6ea9:	48 8b 0d 70 51 00 00 	mov    0x5170(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6eb0:	ba 28 00 00 00       	mov    $0x28,%edx
    6eb5:	be 01 00 00 00       	mov    $0x1,%esi
    6eba:	48 8d 3d 3f 27 00 00 	lea    0x273f(%rip),%rdi        # 9600 <_IO_stdin_used+0x600>
    6ec1:	e8 9a b6 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    6ec6:	bf 01 00 00 00       	mov    $0x1,%edi
    6ecb:	e8 70 b6 ff ff       	call   2540 <exit@plt>
	*cqe_ptr = cqe;
    6ed0:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
	return err;
    6ed5:	e9 09 fe ff ff       	jmp    6ce3 <io_thread+0x12e3>
    6eda:	e9 f5 b7 ff ff       	jmp    26d4 <io_thread.cold+0x9e>
    6edf:	90                   	nop

0000000000006ee0 <buffersend>:
int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send) {
    6ee0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    6ee4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    6ee8:	75 35                	jne    6f1f <buffersend+0x3f>
      for (int x = 0 ; x < buffers->count ; x++) {
    6eea:	4c 63 06             	movslq (%rsi),%r8
    6eed:	45 85 c0             	test   %r8d,%r8d
    6ef0:	7e f2                	jle    6ee4 <buffersend+0x4>
    6ef2:	48 8b 46 08          	mov    0x8(%rsi),%rax
    6ef6:	4f 8d 04 80          	lea    (%r8,%r8,4),%r8
    6efa:	4e 8d 04 c0          	lea    (%rax,%r8,8),%r8
    6efe:	eb 09                	jmp    6f09 <buffersend+0x29>
    6f00:	48 83 c0 28          	add    $0x28,%rax
    6f04:	4c 39 c0             	cmp    %r8,%rax
    6f07:	74 db                	je     6ee4 <buffersend+0x4>
        if (buffers->buffer[x].available == 0) {
    6f09:	44 8b 48 08          	mov    0x8(%rax),%r9d
    6f0d:	45 85 c9             	test   %r9d,%r9d
    6f10:	75 ee                	jne    6f00 <buffersend+0x20>
          buffers->buffer[x].data = send;
    6f12:	48 89 08             	mov    %rcx,(%rax)
          buffers->buffer[x].kind = kind;
    6f15:	89 50 20             	mov    %edx,0x20(%rax)
          buffers->buffer[x].available = 1;
    6f18:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
}
    6f1f:	31 c0                	xor    %eax,%eax
    6f21:	c3                   	ret
    6f22:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6f2d:	0f 1f 00             	nopl   (%rax)

0000000000006f30 <buffersend_filter>:
int buffersend_filter(struct KernelThread *data, struct Buffers *buffers, int kind, void * send, int filter) {
    6f30:	f3 0f 1e fa          	endbr64
    6f34:	49 89 f9             	mov    %rdi,%r9
    6f37:	48 89 f7             	mov    %rsi,%rdi
  while (data->running == 1) {
    6f3a:	41 83 79 44 01       	cmpl   $0x1,0x44(%r9)
    6f3f:	75 42                	jne    6f83 <buffersend_filter+0x53>
      for (int x = 0 ; x < buffers->count ; x++) {
    6f41:	48 63 37             	movslq (%rdi),%rsi
    6f44:	85 f6                	test   %esi,%esi
    6f46:	7e f2                	jle    6f3a <buffersend_filter+0xa>
    6f48:	48 8b 47 08          	mov    0x8(%rdi),%rax
    6f4c:	48 8d 34 b6          	lea    (%rsi,%rsi,4),%rsi
    6f50:	48 8d 34 f0          	lea    (%rax,%rsi,8),%rsi
    6f54:	eb 13                	jmp    6f69 <buffersend_filter+0x39>
    6f56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6f60:	48 83 c0 28          	add    $0x28,%rax
    6f64:	48 39 f0             	cmp    %rsi,%rax
    6f67:	74 d1                	je     6f3a <buffersend_filter+0xa>
        if (buffers->buffer[x].available == 0) {
    6f69:	44 8b 50 08          	mov    0x8(%rax),%r10d
    6f6d:	45 85 d2             	test   %r10d,%r10d
    6f70:	75 ee                	jne    6f60 <buffersend_filter+0x30>
          buffers->buffer[x].data = send;
    6f72:	48 89 08             	mov    %rcx,(%rax)
          buffers->buffer[x].kind = kind;
    6f75:	89 50 20             	mov    %edx,0x20(%rax)
          buffers->buffer[x].filter = filter;
    6f78:	44 89 40 24          	mov    %r8d,0x24(%rax)
          buffers->buffer[x].available = 1;
    6f7c:	c7 40 08 01 00 00 00 	movl   $0x1,0x8(%rax)
}
    6f83:	31 c0                	xor    %eax,%eax
    6f85:	c3                   	ret
    6f86:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006f90 <bufferrecv_filter>:
void * bufferrecv_filter(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking, int filter) {
    6f90:	f3 0f 1e fa          	endbr64
    6f94:	55                   	push   %rbp
    6f95:	48 89 f0             	mov    %rsi,%rax
    6f98:	53                   	push   %rbx
    6f99:	48 83 ec 08          	sub    $0x8,%rsp
  while (data->running == 1) {
    6f9d:	83 78 44 01          	cmpl   $0x1,0x44(%rax)
void * bufferrecv_filter(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking, int filter) {
    6fa1:	8b 74 24 20          	mov    0x20(%rsp),%esi
  while (data->running == 1) {
    6fa5:	75 75                	jne    701c <bufferrecv_filter+0x8c>
    6fa7:	89 cd                	mov    %ecx,%ebp
      for (int x = 0 ; x < buffers->count ; x++) {
    6fa9:	8b 0a                	mov    (%rdx),%ecx
    6fab:	85 c9                	test   %ecx,%ecx
    6fad:	7e 61                	jle    7010 <bufferrecv_filter+0x80>
    6faf:	90                   	nop
    6fb0:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    6fb4:	48 63 c1             	movslq %ecx,%rax
    6fb7:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6fbb:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    6fbf:	eb 10                	jmp    6fd1 <bufferrecv_filter+0x41>
    6fc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6fc8:	48 83 c3 28          	add    $0x28,%rbx
    6fcc:	48 39 c3             	cmp    %rax,%rbx
    6fcf:	74 3f                	je     7010 <bufferrecv_filter+0x80>
        if (buffers->buffer[x].available == 1) {
    6fd1:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    6fd5:	75 f1                	jne    6fc8 <bufferrecv_filter+0x38>
          if (buffers->buffer[x].kind == kind && buffers->buffer[x].filter == filter) {
    6fd7:	39 6b 20             	cmp    %ebp,0x20(%rbx)
    6fda:	75 ec                	jne    6fc8 <bufferrecv_filter+0x38>
    6fdc:	39 73 24             	cmp    %esi,0x24(%rbx)
    6fdf:	75 e7                	jne    6fc8 <bufferrecv_filter+0x38>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6fe1:	be 28 00 00 00       	mov    $0x28,%esi
    6fe6:	bf 01 00 00 00       	mov    $0x1,%edi
    6feb:	e8 30 b4 ff ff       	call   2420 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    6ff0:	48 8b 13             	mov    (%rbx),%rdx
            reply->kind = buffers->buffer[x].kind;
    6ff3:	89 68 20             	mov    %ebp,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    6ff6:	48 89 10             	mov    %rdx,(%rax)
            buffers->buffer[x].available = 0;
    6ff9:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            asm volatile ("mfence" ::: "memory");
    7000:	0f ae f0             	mfence
}
    7003:	48 83 c4 08          	add    $0x8,%rsp
    7007:	5b                   	pop    %rbx
    7008:	5d                   	pop    %rbp
    7009:	c3                   	ret
    700a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
     if (nonblocking == 1) { return NULL; }
    7010:	41 83 f9 01          	cmp    $0x1,%r9d
    7014:	74 06                	je     701c <bufferrecv_filter+0x8c>
      for (int x = 0 ; x < buffers->count ; x++) {
    7016:	85 c9                	test   %ecx,%ecx
    7018:	7f 96                	jg     6fb0 <bufferrecv_filter+0x20>
    701a:	eb fa                	jmp    7016 <bufferrecv_filter+0x86>
}
    701c:	48 83 c4 08          	add    $0x8,%rsp
     if (nonblocking == 1) { return NULL; }
    7020:	31 c0                	xor    %eax,%eax
}
    7022:	5b                   	pop    %rbx
    7023:	5d                   	pop    %rbp
    7024:	c3                   	ret
    7025:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000007030 <bufferrecv>:
void * bufferrecv(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking) {
    7030:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    7034:	83 7e 44 01          	cmpl   $0x1,0x44(%rsi)
    7038:	75 76                	jne    70b0 <bufferrecv+0x80>
void * bufferrecv(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking) {
    703a:	55                   	push   %rbp
    703b:	89 cd                	mov    %ecx,%ebp
    703d:	53                   	push   %rbx
    703e:	48 83 ec 08          	sub    $0x8,%rsp
      for (int x = 0 ; x < buffers->count ; x++) {
    7042:	8b 0a                	mov    (%rdx),%ecx
    7044:	85 c9                	test   %ecx,%ecx
    7046:	7e 58                	jle    70a0 <bufferrecv+0x70>
    7048:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    704c:	48 63 c1             	movslq %ecx,%rax
    704f:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    7053:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    7057:	eb 10                	jmp    7069 <bufferrecv+0x39>
    7059:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7060:	48 83 c3 28          	add    $0x28,%rbx
    7064:	48 39 c3             	cmp    %rax,%rbx
    7067:	74 37                	je     70a0 <bufferrecv+0x70>
        if (buffers->buffer[x].available == 1) {
    7069:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    706d:	75 f1                	jne    7060 <bufferrecv+0x30>
          if (buffers->buffer[x].kind == kind) {
    706f:	39 6b 20             	cmp    %ebp,0x20(%rbx)
    7072:	75 ec                	jne    7060 <bufferrecv+0x30>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    7074:	be 28 00 00 00       	mov    $0x28,%esi
    7079:	bf 01 00 00 00       	mov    $0x1,%edi
    707e:	e8 9d b3 ff ff       	call   2420 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    7083:	48 8b 13             	mov    (%rbx),%rdx
            reply->kind = buffers->buffer[x].kind;
    7086:	89 68 20             	mov    %ebp,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    7089:	48 89 10             	mov    %rdx,(%rax)
            buffers->buffer[x].available = 0;
    708c:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            asm volatile ("sfence" ::: "memory");
    7093:	0f ae f8             	sfence
}
    7096:	48 83 c4 08          	add    $0x8,%rsp
    709a:	5b                   	pop    %rbx
    709b:	5d                   	pop    %rbp
    709c:	c3                   	ret
    709d:	0f 1f 00             	nopl   (%rax)
     if (nonblocking == 1) { return NULL; }
    70a0:	41 83 f9 01          	cmp    $0x1,%r9d
    70a4:	74 06                	je     70ac <bufferrecv+0x7c>
      for (int x = 0 ; x < buffers->count ; x++) {
    70a6:	85 c9                	test   %ecx,%ecx
    70a8:	7f 9e                	jg     7048 <bufferrecv+0x18>
    70aa:	eb fa                	jmp    70a6 <bufferrecv+0x76>
     if (nonblocking == 1) { return NULL; }
    70ac:	31 c0                	xor    %eax,%eax
    70ae:	eb e6                	jmp    7096 <bufferrecv+0x66>
    70b0:	31 c0                	xor    %eax,%eax
}
    70b2:	c3                   	ret
    70b3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    70be:	66 90                	xchg   %ax,%ax

00000000000070c0 <wait_for_new_client>:
struct NewClientMessage * wait_for_new_client(struct KernelThread *data, int nonblocking) {
    70c0:	f3 0f 1e fa          	endbr64
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    70c4:	48 63 97 1c 01 00 00 	movslq 0x11c(%rdi),%rdx
    70cb:	48 c1 e2 04          	shl    $0x4,%rdx
    70cf:	48 03 97 10 01 00 00 	add    0x110(%rdi),%rdx
  while (data->running == 1) {
    70d6:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    70da:	0f 85 84 00 00 00    	jne    7164 <wait_for_new_client+0xa4>
      for (int x = 0 ; x < buffers->count ; x++) {
    70e0:	8b 0a                	mov    (%rdx),%ecx
    70e2:	85 c9                	test   %ecx,%ecx
    70e4:	7e 65                	jle    714b <wait_for_new_client+0x8b>
struct NewClientMessage * wait_for_new_client(struct KernelThread *data, int nonblocking) {
    70e6:	53                   	push   %rbx
    70e7:	48 8b 5a 08          	mov    0x8(%rdx),%rbx
    70eb:	48 63 c1             	movslq %ecx,%rax
    70ee:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    70f2:	48 8d 04 c3          	lea    (%rbx,%rax,8),%rax
    70f6:	eb 11                	jmp    7109 <wait_for_new_client+0x49>
    70f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    7100:	48 83 c3 28          	add    $0x28,%rbx
    7104:	48 39 c3             	cmp    %rax,%rbx
    7107:	74 37                	je     7140 <wait_for_new_client+0x80>
        if (buffers->buffer[x].available == 1) {
    7109:	83 7b 08 01          	cmpl   $0x1,0x8(%rbx)
    710d:	75 f1                	jne    7100 <wait_for_new_client+0x40>
          if (buffers->buffer[x].kind == kind) {
    710f:	83 7b 20 02          	cmpl   $0x2,0x20(%rbx)
    7113:	75 eb                	jne    7100 <wait_for_new_client+0x40>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    7115:	be 28 00 00 00       	mov    $0x28,%esi
    711a:	bf 01 00 00 00       	mov    $0x1,%edi
    711f:	e8 fc b2 ff ff       	call   2420 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    7124:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    7127:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
            reply->kind = buffers->buffer[x].kind;
    712e:	c7 40 20 02 00 00 00 	movl   $0x2,0x20(%rax)
            reply->data = buffers->buffer[x].data;
    7135:	48 89 10             	mov    %rdx,(%rax)
            asm volatile ("sfence" ::: "memory");
    7138:	0f ae f8             	sfence
  struct NewClientMessage *newclientmsg = newclient->data;
    713b:	48 8b 00             	mov    (%rax),%rax
}
    713e:	5b                   	pop    %rbx
    713f:	c3                   	ret
     if (nonblocking == 1) { return NULL; }
    7140:	83 fe 01             	cmp    $0x1,%esi
    7143:	74 1b                	je     7160 <wait_for_new_client+0xa0>
      for (int x = 0 ; x < buffers->count ; x++) {
    7145:	85 c9                	test   %ecx,%ecx
    7147:	7f 9e                	jg     70e7 <wait_for_new_client+0x27>
    7149:	eb fa                	jmp    7145 <wait_for_new_client+0x85>
     if (nonblocking == 1) { return NULL; }
    714b:	83 fe 01             	cmp    $0x1,%esi
    714e:	74 14                	je     7164 <wait_for_new_client+0xa4>
      for (int x = 0 ; x < buffers->count ; x++) {
    7150:	85 c9                	test   %ecx,%ecx
    7152:	7f 92                	jg     70e6 <wait_for_new_client+0x26>
    7154:	eb fa                	jmp    7150 <wait_for_new_client+0x90>
    7156:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    return NULL;
    7160:	31 c0                	xor    %eax,%eax
}
    7162:	5b                   	pop    %rbx
    7163:	c3                   	ret
    return NULL;
    7164:	31 c0                	xor    %eax,%eax
}
    7166:	c3                   	ret
    7167:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007170 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    7170:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    7174:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    717b:	8b 8e cc 00 00 00    	mov    0xcc(%rsi),%ecx
    7181:	85 c9                	test   %ecx,%ecx
    7183:	0f 8e d5 00 00 00    	jle    725e <barriered_work_ingest+0xee>
int barriered_work_ingest(struct BarrierTask *data) {
    7189:	41 56                	push   %r14
    718b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    718d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    7190:	41 54                	push   %r12
    7192:	49 89 fc             	mov    %rdi,%r12
    7195:	55                   	push   %rbp
    7196:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    7197:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    719b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    71a0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    71a4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    71ac:	31 ed                	xor    %ebp,%ebp
    71ae:	8b 10                	mov    (%rax),%edx
    71b0:	85 d2                	test   %edx,%edx
    71b2:	7e 25                	jle    71d9 <barriered_work_ingest+0x69>
    71b4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    71b8:	48 8d 5c ad 00       	lea    0x0(%rbp,%rbp,4),%rbx
    71bd:	48 c1 e3 03          	shl    $0x3,%rbx
    71c1:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    71c5:	83 78 08 01          	cmpl   $0x1,0x8(%rax)
    71c9:	74 25                	je     71f0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    71cb:	48 83 c5 01          	add    $0x1,%rbp
    71cf:	39 ea                	cmp    %ebp,%edx
    71d1:	7f e5                	jg     71b8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    71d3:	8b 8e cc 00 00 00    	mov    0xcc(%rsi),%ecx
    71d9:	49 83 c5 01          	add    $0x1,%r13
    71dd:	44 39 e9             	cmp    %r13d,%ecx
    71e0:	7f be                	jg     71a0 <barriered_work_ingest+0x30>
}
    71e2:	5b                   	pop    %rbx
    71e3:	31 c0                	xor    %eax,%eax
    71e5:	5d                   	pop    %rbp
    71e6:	41 5c                	pop    %r12
    71e8:	41 5d                	pop    %r13
    71ea:	41 5e                	pop    %r14
    71ec:	c3                   	ret
    71ed:	0f 1f 00             	nopl   (%rax)
        data->ingest_count++;
    71f0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    71f9:	48 63 70 1c          	movslq 0x1c(%rax),%rsi
    71fd:	bf 04 00 00 00       	mov    $0x4,%edi
    7202:	48 c1 e6 05          	shl    $0x5,%rsi
    7206:	48 03 70 10          	add    0x10(%rax),%rsi
    720a:	48 83 c6 10          	add    $0x10,%rsi
    720e:	e8 5d b1 ff ff       	call   2370 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    7213:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    721b:	48 8b 40 50          	mov    0x50(%rax),%rax
    721f:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    7223:	48 03 58 08          	add    0x8(%rax),%rbx
    7227:	8b 43 1c             	mov    0x1c(%rbx),%eax
        data->thread->buffers[b]->buffer[x].available = 0;
    722a:	c7 43 08 00 00 00 00 	movl   $0x0,0x8(%rbx)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    7231:	83 c0 01             	add    $0x1,%eax
    7234:	99                   	cltd
    7235:	f7 7b 18             	idivl  0x18(%rbx)
    7238:	89 53 1c             	mov    %edx,0x1c(%rbx)
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    723b:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    7243:	48 83 c5 01          	add    $0x1,%rbp
    7247:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    724b:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    724f:	8b 10                	mov    (%rax),%edx
    7251:	39 ea                	cmp    %ebp,%edx
    7253:	0f 8f 5b ff ff ff    	jg     71b4 <barriered_work_ingest+0x44>
    7259:	e9 75 ff ff ff       	jmp    71d3 <barriered_work_ingest+0x63>
}
    725e:	31 c0                	xor    %eax,%eax
    7260:	c3                   	ret
    7261:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    726c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000007270 <barriered_thread>:
void* barriered_thread(void *arg) {
    7270:	f3 0f 1e fa          	endbr64
    7274:	41 56                	push   %r14
    7276:	41 55                	push   %r13
    7278:	41 54                	push   %r12
  int t = 0;
    727a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    727d:	55                   	push   %rbp
  int waiting = 0;
    727e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    7280:	53                   	push   %rbx
    7281:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    7284:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7288:	0f 85 7c 02 00 00    	jne    750a <barriered_thread+0x29a>
    if (t >= data->task_count) {
    728e:	8b 43 40             	mov    0x40(%rbx),%eax
    7291:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7298:	41 39 c4             	cmp    %eax,%r12d
    729b:	0f 8d 6f 01 00 00    	jge    7410 <barriered_thread+0x1a0>
    72a1:	49 63 fc             	movslq %r12d,%rdi
    72a4:	48 c1 e7 09          	shl    $0x9,%rdi
    72a8:	49 89 fd             	mov    %rdi,%r13
    72ab:	eb 32                	jmp    72df <barriered_thread+0x6f>
    72ad:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    72b0:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    72b4:	48 8b 43 18          	mov    0x18(%rbx),%rax
    72b8:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    72bc:	48 8b 78 38          	mov    0x38(%rax),%rdi
    72c0:	4c 01 ef             	add    %r13,%rdi
    72c3:	e8 a8 fe ff ff       	call   7170 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    72c8:	8b 43 40             	mov    0x40(%rbx),%eax
    72cb:	41 83 c4 01          	add    $0x1,%r12d
    72cf:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    72d6:	44 39 e0             	cmp    %r12d,%eax
    72d9:	0f 8e 21 02 00 00    	jle    7500 <barriered_thread+0x290>
      if (data->tasks[t].available == 1) {
    72df:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    72e3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    72e7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    72ee:	75 c0                	jne    72b0 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    72f0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    72f4:	83 e8 01             	sub    $0x1,%eax
    72f7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    72fc:	45 85 e4             	test   %r12d,%r12d
    72ff:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    7302:	45 85 c0             	test   %r8d,%r8d
    7305:	0f 8e 2d 01 00 00    	jle    7438 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    730b:	48 63 c8             	movslq %eax,%rcx
    730e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    7312:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    7315:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    731b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    7322:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    7326:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    7329:	45 31 f6             	xor    %r14d,%r14d
    732c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    7330:	48 8b 10             	mov    (%rax),%rdx
    7333:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    7337:	49 01 cb             	add    %rcx,%r11
    733a:	4c 89 da             	mov    %r11,%rdx
    733d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    7344:	75 04                	jne    734a <barriered_thread+0xda>
            arrived++;
    7346:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    734a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    7350:	75 04                	jne    7356 <barriered_thread+0xe6>
            prearrive++;
    7352:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    7356:	48 83 c0 08          	add    $0x8,%rax
    735a:	48 39 c6             	cmp    %rax,%rsi
    735d:	75 d1                	jne    7330 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    735f:	45 85 d2             	test   %r10d,%r10d
    7362:	0f 84 c0 00 00 00    	je     7428 <barriered_thread+0x1b8>
    7368:	45 39 d0             	cmp    %r10d,%r8d
    736b:	0f 84 b7 00 00 00    	je     7428 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    7371:	45 85 f6             	test   %r14d,%r14d
    7374:	74 0a                	je     7380 <barriered_thread+0x110>
    7376:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    737a:	0f 85 b6 01 00 00    	jne    7536 <barriered_thread+0x2c6>
    7380:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    7384:	4c 01 ea             	add    %r13,%rdx
    7387:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    738e:	45 85 e4             	test   %r12d,%r12d
    7391:	75 14                	jne    73a7 <barriered_thread+0x137>
    7393:	48 8b b3 90 00 00 00 	mov    0x90(%rbx),%rsi
    739a:	48 3b b3 98 00 00 00 	cmp    0x98(%rbx),%rsi
    73a1:	0f 8c 71 01 00 00    	jl     7518 <barriered_thread+0x2a8>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    73a7:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    73ab:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    73af:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    73b9:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    73bd:	48 8b 78 38          	mov    0x38(%rax),%rdi
    73c1:	4c 01 ef             	add    %r13,%rdi
    73c4:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    73ca:	48 8b 43 38          	mov    0x38(%rbx),%rax
    73ce:	4c 01 e8             	add    %r13,%rax
    73d1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    73d8:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    73db:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    73e3:	83 e8 01             	sub    $0x1,%eax
    73e6:	44 39 e0             	cmp    %r12d,%eax
    73e9:	0f 84 a1 00 00 00    	je     7490 <barriered_thread+0x220>
          if (waiting == 0) {
    73ef:	85 ed                	test   %ebp,%ebp
    73f1:	0f 84 d9 00 00 00    	je     74d0 <barriered_thread+0x260>
        int arrived = 0; 
    73f7:	bd 01 00 00 00       	mov    $0x1,%ebp
    73fc:	e9 c7 fe ff ff       	jmp    72c8 <barriered_thread+0x58>
  while (data->running == 1) {
    7401:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7405:	0f 85 ff 00 00 00    	jne    750a <barriered_thread+0x29a>
    740b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    7410:	48 83 83 b8 00 00 00 01 	addq   $0x1,0xb8(%rbx)
    for (; t < data->task_count; t++) {
    7418:	85 c0                	test   %eax,%eax
    741a:	7e e5                	jle    7401 <barriered_thread+0x191>
    741c:	45 31 e4             	xor    %r12d,%r12d
    741f:	e9 7d fe ff ff       	jmp    72a1 <barriered_thread+0x31>
    7424:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    7428:	83 fd 01             	cmp    $0x1,%ebp
    742b:	74 1b                	je     7448 <barriered_thread+0x1d8>
        int arrived = 0; 
    742d:	31 ed                	xor    %ebp,%ebp
    742f:	e9 3d ff ff ff       	jmp    7371 <barriered_thread+0x101>
    7434:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    7438:	83 fd 01             	cmp    $0x1,%ebp
    743b:	0f 85 43 ff ff ff    	jne    7384 <barriered_thread+0x114>
        int arrived = 0; 
    7441:	45 31 f6             	xor    %r14d,%r14d
    7444:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    7448:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    744f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    7454:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    7456:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    745a:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    7461:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    7466:	e8 05 af ff ff       	call   2370 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    746b:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
    7472:	48 83 c0 01          	add    $0x1,%rax
    7476:	48 99                	cqto
    7478:	48 f7 bb b0 00 00 00 	idivq  0xb0(%rbx)
    747f:	48 89 93 a8 00 00 00 	mov    %rdx,0xa8(%rbx)
            waiting = 0; 
    7486:	e9 e6 fe ff ff       	jmp    7371 <barriered_thread+0x101>
    748b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7490:	48 8b b3 90 00 00 00 	mov    0x90(%rbx),%rsi
    7497:	48 3b b3 98 00 00 00 	cmp    0x98(%rbx),%rsi
    749e:	0f 8d 4b ff ff ff    	jge    73ef <barriered_thread+0x17f>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    74a4:	48 c1 e6 04          	shl    $0x4,%rsi
    74a8:	bf 04 00 00 00       	mov    $0x4,%edi
    74ad:	48 03 b3 80 00 00 00 	add    0x80(%rbx),%rsi
    74b4:	e8 b7 ae ff ff       	call   2370 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    74b9:	48 83 83 90 00 00 00 01 	addq   $0x1,0x90(%rbx)
          if (waiting == 0) {
    74c1:	85 ed                	test   %ebp,%ebp
    74c3:	0f 85 2e ff ff ff    	jne    73f7 <barriered_thread+0x187>
    74c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            data->task_snapshot[data->task_timestamp_count].task = t;
    74d0:	48 8b 83 a8 00 00 00 	mov    0xa8(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    74d7:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    74dc:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    74e0:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    74e7:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    74eb:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    74ef:	e8 7c ae ff ff       	call   2370 <clock_gettime@plt>
            waiting = 1;
    74f4:	e9 fe fe ff ff       	jmp    73f7 <barriered_thread+0x187>
    74f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    7500:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7504:	0f 84 8e fd ff ff    	je     7298 <barriered_thread+0x28>
}
    750a:	5b                   	pop    %rbx
    750b:	31 c0                	xor    %eax,%eax
    750d:	5d                   	pop    %rbp
    750e:	41 5c                	pop    %r12
    7510:	41 5d                	pop    %r13
    7512:	41 5e                	pop    %r14
    7514:	c3                   	ret
    7515:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    7518:	48 c1 e6 04          	shl    $0x4,%rsi
    751c:	bf 04 00 00 00       	mov    $0x4,%edi
    7521:	48 03 73 78          	add    0x78(%rbx),%rsi
    7525:	e8 46 ae ff ff       	call   2370 <clock_gettime@plt>
          data->tasks[t].available = 0;
    752a:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    752e:	4c 01 ea             	add    %r13,%rdx
    7531:	e9 71 fe ff ff       	jmp    73a7 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    7536:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    753a:	48 8b 43 18          	mov    0x18(%rbx),%rax
    753e:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7542:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7546:	4c 01 ef             	add    %r13,%rdi
    7549:	e8 22 fc ff ff       	call   7170 <barriered_work_ingest>
          break;
    754e:	e9 31 fd ff ff       	jmp    7284 <barriered_thread+0x14>
    7553:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    755e:	66 90                	xchg   %ax,%ax

0000000000007560 <receive>:
int receive(struct BarrierTask *data) {
    7560:	f3 0f 1e fa          	endbr64
    7564:	41 56                	push   %r14
    7566:	41 55                	push   %r13
    7568:	41 54                	push   %r12
    756a:	55                   	push   %rbp
    756b:	53                   	push   %rbx
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    756c:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    7573:	45 85 e4             	test   %r12d,%r12d
    7576:	0f 8e 27 01 00 00    	jle    76a3 <receive+0x143>
    if (n == data->thread->real_thread_index) { continue; }
    757c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    7583:	48 89 fe             	mov    %rdi,%rsi
    7586:	31 db                	xor    %ebx,%ebx
    7588:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    758c:	49 89 ed             	mov    %rbp,%r13
    758f:	90                   	nop
    7590:	41 39 dd             	cmp    %ebx,%r13d
    7593:	0f 84 fd 00 00 00    	je     7696 <receive+0x136>
    struct Data *me = data->mailboxes[n].lower;
    7599:	48 89 d8             	mov    %rbx,%rax
    759c:	48 c1 e0 08          	shl    $0x8,%rax
    75a0:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    75a7:	48 8b 10             	mov    (%rax),%rdx
    if (me->available_reading == 1) {
    75aa:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    75b0:	83 f8 01             	cmp    $0x1,%eax
    75b3:	74 11                	je     75c6 <receive+0x66>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    75b5:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    75bc:	75 08                	jne    75c6 <receive+0x66>
    75be:	85 c0                	test   %eax,%eax
    75c0:	0f 84 d0 00 00 00    	je     7696 <receive+0x136>
    for (; me->messages_count > 0 ; ) {
    75c6:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    75cd:	48 85 ff             	test   %rdi,%rdi
    75d0:	0f 8e a2 00 00 00    	jle    7678 <receive+0x118>
    75d6:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    75dd:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    75e4:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
    75e8:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    75eb:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    75ef:	49 01 f9             	add    %rdi,%r9
    75f2:	49 01 f8             	add    %rdi,%r8
    75f5:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    75fc:	eb 08                	jmp    7606 <receive+0xa6>
    75fe:	66 90                	xchg   %ax,%ax
    for (; me->messages_count > 0 ; ) {
    7600:	48 83 e8 01          	sub    $0x1,%rax
    7604:	72 72                	jb     7678 <receive+0x118>
      data->sends++;
    7606:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
    7609:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
    7610:	48 29 c1             	sub    %rax,%rcx
    7613:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      data->n++;
    761a:	4c 89 c1             	mov    %r8,%rcx
    761d:	48 29 c1             	sub    %rax,%rcx
    7620:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
    7627:	48 89 f9             	mov    %rdi,%rcx
    762a:	48 29 c1             	sub    %rax,%rcx
    762d:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
      if (me->messages[x]->group == data->group) {
    7634:	48 63 c8             	movslq %eax,%rcx
    7637:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    763b:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    763f:	75 bf                	jne    7600 <receive+0xa0>
    7641:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    7645:	75 b9                	jne    7600 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    7647:	49 63 46 04          	movslq 0x4(%r14),%rax
    764b:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    764d:	bf 01 00 00 00       	mov    $0x1,%edi
    7652:	ba 01 00 00 00       	mov    $0x1,%edx
    7657:	48 8d 35 b2 21 00 00 	lea    0x21b2(%rip),%rsi        # 9810 <_IO_stdin_used+0x810>
    765e:	48 39 e8             	cmp    %rbp,%rax
    7661:	0f 94 c1             	sete   %cl
    7664:	31 c0                	xor    %eax,%eax
    7666:	e8 65 ae ff ff       	call   24d0 <__printf_chk@plt>
        exit(1);
    766b:	bf 01 00 00 00       	mov    $0x1,%edi
    7670:	e8 cb ae ff ff       	call   2540 <exit@plt>
    7675:	0f 1f 00             	nopl   (%rax)
      me->available_reading = 0;
    7678:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    7682:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
    768c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7696:	48 83 c3 01          	add    $0x1,%rbx
    769a:	49 39 dc             	cmp    %rbx,%r12
    769d:	0f 85 ed fe ff ff    	jne    7590 <receive+0x30>
}
    76a3:	31 c0                	xor    %eax,%eax
    76a5:	5b                   	pop    %rbx
    76a6:	5d                   	pop    %rbp
    76a7:	41 5c                	pop    %r12
    76a9:	41 5d                	pop    %r13
    76ab:	41 5e                	pop    %r14
    76ad:	c3                   	ret
    76ae:	66 90                	xchg   %ax,%ax

00000000000076b0 <sendm>:
int sendm(struct BarrierTask *data) {
    76b0:	f3 0f 1e fa          	endbr64
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    76b4:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    76ba:	85 c0                	test   %eax,%eax
    76bc:	0f 8e 96 02 00 00    	jle    7958 <sendm+0x2a8>
int sendm(struct BarrierTask *data) {
    76c2:	41 57                	push   %r15
    76c4:	41 56                	push   %r14
    76c6:	41 55                	push   %r13
        if (n == data->thread->real_thread_index) { continue; }
    76c8:	45 31 ed             	xor    %r13d,%r13d
int sendm(struct BarrierTask *data) {
    76cb:	41 54                	push   %r12
    76cd:	4c 63 e0             	movslq %eax,%r12
    76d0:	55                   	push   %rbp
    76d1:	48 89 fd             	mov    %rdi,%rbp
    76d4:	53                   	push   %rbx
        if (n == data->thread->real_thread_index) { continue; }
    76d5:	48 8b 9f 28 01 00 00 	mov    0x128(%rdi),%rbx
    76dc:	44 8b 7b 08          	mov    0x8(%rbx),%r15d
    76e0:	48 89 5c 24 c8       	mov    %rbx,-0x38(%rsp)
    76e5:	0f 1f 00             	nopl   (%rax)
    76e8:	45 39 ef             	cmp    %r13d,%r15d
    76eb:	0f 84 97 00 00 00    	je     7788 <sendm+0xd8>
        struct Data *them = data->mailboxes[n].higher;
    76f1:	4c 89 e8             	mov    %r13,%rax
    76f4:	48 c1 e0 08          	shl    $0x8,%rax
    76f8:	48 03 85 70 01 00 00 	add    0x170(%rbp),%rax
        data->mailboxes[n].counter++;
    76ff:	48 8b 98 b8 00 00 00 	mov    0xb8(%rax),%rbx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7706:	83 b8 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax)
        struct Data *them = data->mailboxes[n].higher;
    770d:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7714:	40 0f 94 c7          	sete   %dil
        data->mailboxes[n].counter++;
    7718:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    771c:	48 89 90 b8 00 00 00 	mov    %rdx,0xb8(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7723:	48 85 d2             	test   %rdx,%rdx
    7726:	7f 05                	jg     772d <sendm+0x7d>
    7728:	40 84 ff             	test   %dil,%dil
    772b:	75 5b                	jne    7788 <sendm+0xd8>
        if (them->messages_count > 0) {
    772d:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    7734:	48 85 f6             	test   %rsi,%rsi
    7737:	7f 4f                	jg     7788 <sendm+0xd8>
        if (them->available_sending == 1) {
    7739:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    7740:	41 83 f8 01          	cmp    $0x1,%r8d
    7744:	74 0e                	je     7754 <sendm+0xa4>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    7746:	83 b9 08 04 00 00 02 	cmpl   $0x2,0x408(%rcx)
    774d:	75 05                	jne    7754 <sendm+0xa4>
    774f:	45 85 c0             	test   %r8d,%r8d
    7752:	74 34                	je     7788 <sendm+0xd8>
        if (data->sending == 1) {
    7754:	83 bd 88 01 00 00 01 	cmpl   $0x1,0x188(%rbp)
    775b:	74 4b                	je     77a8 <sendm+0xf8>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter >= limit) {
    775d:	48 85 d2             	test   %rdx,%rdx
    7760:	7e 26                	jle    7788 <sendm+0xd8>
    7762:	40 84 ff             	test   %dil,%dil
    7765:	74 21                	je     7788 <sendm+0xd8>
          data->mailboxes[n].counter = 0;
    7767:	48 c7 80 b8 00 00 00 00 00 00 00 	movq   $0x0,0xb8(%rax)
          data->thread->have_foreign = 1;
    7772:	48 8b 44 24 c8       	mov    -0x38(%rsp),%rax
    7777:	c7 80 08 01 00 00 01 00 00 00 	movl   $0x1,0x108(%rax)
    7781:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7788:	49 83 c5 01          	add    $0x1,%r13
    778c:	4d 39 ec             	cmp    %r13,%r12
    778f:	0f 85 53 ff ff ff    	jne    76e8 <sendm+0x38>
}
    7795:	31 c0                	xor    %eax,%eax
    7797:	5b                   	pop    %rbx
    7798:	5d                   	pop    %rbp
    7799:	41 5c                	pop    %r12
    779b:	41 5d                	pop    %r13
    779d:	41 5e                	pop    %r14
    779f:	41 5f                	pop    %r15
    77a1:	c3                   	ret
    77a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (; them->messages_count < min;) {
    77a8:	4c 63 99 88 00 00 00 	movslq 0x88(%rcx),%r11
    77af:	4c 39 de             	cmp    %r11,%rsi
    77b2:	0f 8d c2 00 00 00    	jge    787a <sendm+0x1ca>
    77b8:	48 8b 9d 08 01 00 00 	mov    0x108(%rbp),%rbx
    77bf:	4d 89 de             	mov    %r11,%r14
            them->messages[them->messages_count++] = data->message; 
    77c2:	4c 8b 11             	mov    (%rcx),%r10
    77c5:	49 29 f6             	sub    %rsi,%r14
    77c8:	48 89 5c 24 d8       	mov    %rbx,-0x28(%rsp)
    77cd:	48 8b 99 80 03 00 00 	mov    0x380(%rcx),%rbx
    77d4:	4d 8d 46 ff          	lea    -0x1(%r14),%r8
    77d8:	48 89 5c 24 e0       	mov    %rbx,-0x20(%rsp)
    77dd:	49 83 f8 02          	cmp    $0x2,%r8
    77e1:	0f 86 51 01 00 00    	jbe    7938 <sendm+0x288>
    77e7:	48 8d 1c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rbx
    77ef:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    77f7:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    77fc:	4c 01 d3             	add    %r10,%rbx
    77ff:	4c 8d 85 90 01 00 00 	lea    0x190(%rbp),%r8
    7806:	48 89 5c 24 d0       	mov    %rbx,-0x30(%rsp)
    780b:	4b 8d 1c 0a          	lea    (%r10,%r9,1),%rbx
    780f:	49 39 d8             	cmp    %rbx,%r8
    7812:	0f 83 88 00 00 00    	jae    78a0 <sendm+0x1f0>
    7818:	48 8d 9d 98 01 00 00 	lea    0x198(%rbp),%rbx
    781f:	48 39 5c 24 d0       	cmp    %rbx,-0x30(%rsp)
    7824:	73 7a                	jae    78a0 <sendm+0x1f0>
    7826:	4c 8b 44 24 e8       	mov    -0x18(%rsp),%r8
    782b:	4b 8d 34 0a          	lea    (%r10,%r9,1),%rsi
    782f:	4d 01 d0             	add    %r10,%r8
    7832:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    7838:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
          for (; them->messages_count < min;) {
    783f:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    7843:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    7847:	4c 39 c6             	cmp    %r8,%rsi
    784a:	75 ec                	jne    7838 <sendm+0x188>
    784c:	0f 1f 40 00          	nopl   0x0(%rax)
    7850:	48 8b 74 24 d8       	mov    -0x28(%rsp),%rsi
    7855:	4c 01 f6             	add    %r14,%rsi
    7858:	48 89 b5 08 01 00 00 	mov    %rsi,0x108(%rbp)
    785f:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    7864:	4c 89 99 80 00 00 00 	mov    %r11,0x80(%rcx)
    786b:	4c 01 f6             	add    %r14,%rsi
    786e:	48 89 b1 80 03 00 00 	mov    %rsi,0x380(%rcx)
    7875:	4f 89 4c da f8       	mov    %r9,-0x8(%r10,%r11,8)
          them->available_sending = 0;
    787a:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_reading = 1;
    7884:	c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rcx)
          them->available_receiving = 1;
    788e:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    7898:	e9 c0 fe ff ff       	jmp    775d <sendm+0xad>
    789d:	0f 1f 00             	nopl   (%rax)
    78a0:	4c 89 f3             	mov    %r14,%rbx
    78a3:	4c 8b 44 24 d0       	mov    -0x30(%rsp),%r8
    78a8:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    78af:	48 d1 eb             	shr    %rbx
    78b2:	48 c1 e3 04          	shl    $0x4,%rbx
    78b6:	66 49 0f 6e c1       	movq   %r9,%xmm0
    78bb:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    78c0:	4c 01 c3             	add    %r8,%rbx
    78c3:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    78c7:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    78cc:	48 8b 5c 24 e8       	mov    -0x18(%rsp),%rbx
    78d1:	83 e3 10             	and    $0x10,%ebx
    78d4:	75 4a                	jne    7920 <sendm+0x270>
    78d6:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    78db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    78e0:	41 0f 11 00          	movups %xmm0,(%r8)
    78e4:	49 83 c0 20          	add    $0x20,%r8
    78e8:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    78ed:	49 39 d8             	cmp    %rbx,%r8
    78f0:	75 ee                	jne    78e0 <sendm+0x230>
    78f2:	4d 89 f0             	mov    %r14,%r8
    78f5:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    78f9:	49 01 f0             	add    %rsi,%r8
    78fc:	41 f6 c6 01          	test   $0x1,%r14b
    7900:	0f 84 4a ff ff ff    	je     7850 <sendm+0x1a0>
            them->messages[them->messages_count++] = data->message; 
    7906:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    790d:	4f 89 0c c2          	mov    %r9,(%r10,%r8,8)
          for (; them->messages_count < min;) {
    7911:	e9 3a ff ff ff       	jmp    7850 <sendm+0x1a0>
    7916:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    7920:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    7925:	41 0f 11 00          	movups %xmm0,(%r8)
          for (; them->messages_count < min;) {
    7929:	49 83 c0 10          	add    $0x10,%r8
    792d:	49 39 d8             	cmp    %rbx,%r8
    7930:	75 ae                	jne    78e0 <sendm+0x230>
    7932:	eb be                	jmp    78f2 <sendm+0x242>
    7934:	0f 1f 40 00          	nopl   0x0(%rax)
    7938:	48 8d 34 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rsi
    7940:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    7948:	48 89 74 24 e8       	mov    %rsi,-0x18(%rsp)
    794d:	e9 d4 fe ff ff       	jmp    7826 <sendm+0x176>
    7952:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
}
    7958:	31 c0                	xor    %eax,%eax
    795a:	c3                   	ret
    795b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000007960 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    7960:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    7964:	85 f6                	test   %esi,%esi
    7966:	74 18                	je     7980 <mailboxkind+0x20>
  return NULL;
    7968:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    796a:	83 fe 01             	cmp    $0x1,%esi
    796d:	74 01                	je     7970 <mailboxkind+0x10>
}
    796f:	c3                   	ret
    return mailbox->higher;
    7970:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
}
    7977:	c3                   	ret
    7978:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    return mailbox->lower;
    7980:	48 8b 07             	mov    (%rdi),%rax
    7983:	c3                   	ret
    7984:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    798f:	90                   	nop

0000000000007990 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    7990:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    7994:	85 d2                	test   %edx,%edx
    7996:	75 08                	jne    79a0 <setmailboxkind+0x10>
    mailbox->lower = data;
    7998:	48 89 37             	mov    %rsi,(%rdi)
}
    799b:	31 c0                	xor    %eax,%eax
    799d:	c3                   	ret
    799e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    79a0:	83 fa 01             	cmp    $0x1,%edx
    79a3:	74 13                	je     79b8 <setmailboxkind+0x28>
  if (kind == 2) {
    79a5:	83 fa 02             	cmp    $0x2,%edx
    79a8:	75 1e                	jne    79c8 <setmailboxkind+0x38>
    mailbox->pending_lower = data;
    79aa:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
}
    79b1:	31 c0                	xor    %eax,%eax
    79b3:	c3                   	ret
    79b4:	0f 1f 40 00          	nopl   0x0(%rax)
    mailbox->higher = data;
    79b8:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
}
    79bf:	31 c0                	xor    %eax,%eax
    79c1:	c3                   	ret
    79c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (kind == 3) {
    79c8:	83 fa 03             	cmp    $0x3,%edx
    79cb:	75 ce                	jne    799b <setmailboxkind+0xb>
    mailbox->pending_higher = data;
    79cd:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
}
    79d4:	31 c0                	xor    %eax,%eax
    79d6:	c3                   	ret
    79d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000079e0 <fswap>:
int fswap(struct BarrierTask *data) {
    79e0:	f3 0f 1e fa          	endbr64
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    79e4:	48 8b 8f 28 01 00 00 	mov    0x128(%rdi),%rcx
    79eb:	8b 87 9c 01 00 00    	mov    0x19c(%rdi),%eax
    79f1:	44 8b 97 30 01 00 00 	mov    0x130(%rdi),%r10d
  int t = data->task_index;
    79f8:	48 63 57 04          	movslq 0x4(%rdi),%rdx
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    79fc:	4c 63 99 d4 00 00 00 	movslq 0xd4(%rcx),%r11
    7a03:	41 0f af c3          	imul   %r11d,%eax
    7a07:	41 01 c2             	add    %eax,%r10d
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    7a0a:	45 85 db             	test   %r11d,%r11d
    7a0d:	0f 8e 18 01 00 00    	jle    7b2b <fswap+0x14b>
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7a13:	4d 63 d2             	movslq %r10d,%r10
int fswap(struct BarrierTask *data) {
    7a16:	41 56                	push   %r14
    7a18:	48 98                	cltq
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7a1a:	48 c1 e2 09          	shl    $0x9,%rdx
int fswap(struct BarrierTask *data) {
    7a1e:	41 55                	push   %r13
    7a20:	48 89 c6             	mov    %rax,%rsi
    7a23:	49 01 c3             	add    %rax,%r11
    7a26:	41 54                	push   %r12
    7a28:	48 c1 e6 08          	shl    $0x8,%rsi
    7a2c:	49 c1 e3 08          	shl    $0x8,%r11
    7a30:	55                   	push   %rbp
    7a31:	53                   	push   %rbx
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7a32:	4c 8b 49 20          	mov    0x20(%rcx),%r9
    7a36:	4b 8d 0c d2          	lea    (%r10,%r10,8),%rcx
    7a3a:	49 8d 0c 4a          	lea    (%r10,%rcx,2),%rcx
        int next_task = abs((t + 1) % (data->thread_count));
    7a3e:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    7a45:	49 c1 e2 08          	shl    $0x8,%r10
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7a49:	48 c1 e1 04          	shl    $0x4,%rcx
    7a4d:	49 8b 5c 09 38       	mov    0x38(%r9,%rcx,1),%rbx
    7a52:	48 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%rbp
    7a5a:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
    7a5e:	48 8d 14 50          	lea    (%rax,%rdx,2),%rdx
    7a62:	48 c1 e2 04          	shl    $0x4,%rdx
    7a66:	49 01 d1             	add    %rdx,%r9
    7a69:	eb 1c                	jmp    7a87 <fswap+0xa7>
    7a6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    7a70:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    7a77:	49 81 c1 30 01 00 00 	add    $0x130,%r9
    7a7e:	49 39 f3             	cmp    %rsi,%r11
    7a81:	0f 84 99 00 00 00    	je     7b20 <fswap+0x140>
        if (kind == MAILBOX_FRIEND) {
    7a87:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    7a8f:	75 df                	jne    7a70 <fswap+0x90>
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    7a91:	49 8b 79 38          	mov    0x38(%r9),%rdi
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    7a95:	45 85 c0             	test   %r8d,%r8d
    7a98:	7e d6                	jle    7a70 <fswap+0x90>
    7a9a:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    7aa1:	31 c9                	xor    %ecx,%ecx
    7aa3:	eb 58                	jmp    7afd <fswap+0x11d>
    7aa5:	0f 1f 00             	nopl   (%rax)
              struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    7aa8:	48 63 d2             	movslq %edx,%rdx
    7aab:	48 c1 e2 09          	shl    $0x9,%rdx
    7aaf:	4c 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%r13
    7ab7:	49 01 f5             	add    %rsi,%r13
    7aba:	4c 89 ea             	mov    %r13,%rdx
    return mailbox->lower;
    7abd:	4d 8b 6d 00          	mov    0x0(%r13),%r13
                if (dest->messages_count != 0) { 
    7ac1:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    7ac9:	75 22                	jne    7aed <fswap+0x10d>
    mailbox->lower = data;
    7acb:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    7ad2:	4c 89 32             	mov    %r14,(%rdx)
    7ad5:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    mailbox->higher = data;
    7adc:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    mailbox->lower = data;
    7ae3:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    7ae6:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    7aed:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    7af4:	41 39 c8             	cmp    %ecx,%r8d
    7af7:	0f 84 73 ff ff ff    	je     7a70 <fswap+0x90>
              int next_task = abs((nn + 1) % (data->thread_count));
    7afd:	83 c1 01             	add    $0x1,%ecx
    7b00:	89 c8                	mov    %ecx,%eax
    7b02:	99                   	cltd
    7b03:	41 f7 f8             	idiv   %r8d
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7b06:	48 8b 07             	mov    (%rdi),%rax
    7b09:	4c 01 d0             	add    %r10,%rax
    return mailbox->lower;
    7b0c:	4c 8b 20             	mov    (%rax),%r12
                if (source2->messages_count != 0) { 
    7b0f:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    7b18:	74 8e                	je     7aa8 <fswap+0xc8>
    7b1a:	e9 51 ff ff ff       	jmp    7a70 <fswap+0x90>
    7b1f:	90                   	nop
}
    7b20:	5b                   	pop    %rbx
    7b21:	31 c0                	xor    %eax,%eax
    7b23:	5d                   	pop    %rbp
    7b24:	41 5c                	pop    %r12
    7b26:	41 5d                	pop    %r13
    7b28:	41 5e                	pop    %r14
    7b2a:	c3                   	ret
    7b2b:	31 c0                	xor    %eax,%eax
    7b2d:	c3                   	ret
    7b2e:	66 90                	xchg   %ax,%ax

0000000000007b30 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    7b30:	f3 0f 1e fa          	endbr64
    7b34:	41 57                	push   %r15
    7b36:	41 56                	push   %r14
    7b38:	41 55                	push   %r13
    7b3a:	41 54                	push   %r12
    7b3c:	55                   	push   %rbp
    7b3d:	53                   	push   %rbx
    7b3e:	48 89 fb             	mov    %rdi,%rbx
    7b41:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
  struct timespec preempt = {
    7b48:	66 0f 6f 05 b0 22 00 00 	movdqa 0x22b0(%rip),%xmm0        # 9e00 <_IO_stdin_used+0xe00>
int barriered_work(struct BarrierTask *data) {
    7b50:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    7b59:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    7b5e:	31 c0                	xor    %eax,%eax
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    7b60:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  struct timespec preempt = {
    7b67:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    7b6c:	48 8b 88 00 01 00 00 	mov    0x100(%rax),%rcx
  struct timespec rem = {
    7b73:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    7b78:	8b 11                	mov    (%rcx),%edx
    7b7a:	83 fa ff             	cmp    $0xffffffff,%edx
    7b7d:	0f 84 ed 02 00 00    	je     7e70 <barriered_work+0x340>
    7b83:	3b 90 f8 00 00 00    	cmp    0xf8(%rax),%edx
    7b89:	74 2d                	je     7bb8 <barriered_work+0x88>
}
    7b8b:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    7b90:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    7b99:	0f 85 50 05 00 00    	jne    80ef <barriered_work+0x5bf>
    7b9f:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    7ba6:	31 c0                	xor    %eax,%eax
    7ba8:	5b                   	pop    %rbx
    7ba9:	5d                   	pop    %rbp
    7baa:	41 5c                	pop    %r12
    7bac:	41 5d                	pop    %r13
    7bae:	41 5e                	pop    %r14
    7bb0:	41 5f                	pop    %r15
    7bb2:	c3                   	ret
    7bb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    7bb8:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    7bbf:	8b 41 04             	mov    0x4(%rcx),%eax
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    7bc2:	85 ed                	test   %ebp,%ebp
    7bc4:	0f 85 a6 04 00 00    	jne    8070 <barriered_work+0x540>
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    7bca:	85 c0                	test   %eax,%eax
    7bcc:	0f 84 a6 04 00 00    	je     8078 <barriered_work+0x548>
    7bd2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          int t = data->task_index;
    7bd8:	44 8b 63 04          	mov    0x4(%rbx),%r12d
      receive(data);
    7bdc:	48 89 df             	mov    %rbx,%rdi
    if (data->thread_index == data->task_index) {
    7bdf:	41 39 ec             	cmp    %ebp,%r12d
    7be2:	0f 85 d0 03 00 00    	jne    7fb8 <barriered_work+0x488>
      receive(data);
    7be8:	e8 73 f9 ff ff       	call   7560 <receive>
        if (data->thread->have_foreign == 1) {
    7bed:	4c 8b bb 28 01 00 00 	mov    0x128(%rbx),%r15
    7bf4:	41 83 bf 08 01 00 00 01 	cmpl   $0x1,0x108(%r15)
    7bfc:	0f 85 c6 02 00 00    	jne    7ec8 <barriered_work+0x398>
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7c02:	44 8b b3 40 01 00 00 	mov    0x140(%rbx),%r14d
    7c09:	45 85 f6             	test   %r14d,%r14d
    7c0c:	0f 8e b6 02 00 00    	jle    7ec8 <barriered_work+0x398>
                int next_task = abs((t + 1) % (data->thread_count));
    7c12:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7c18:	48 c1 e5 09          	shl    $0x9,%rbp
    7c1c:	45 31 c0             	xor    %r8d,%r8d
    7c1f:	31 f6                	xor    %esi,%esi
    7c21:	49 89 ed             	mov    %rbp,%r13
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7c24:	c7 44 24 0c 00 00 00 00 	movl   $0x0,0xc(%rsp)
                int next_task = abs((t + 1) % (data->thread_count));
    7c2c:	89 44 24 24          	mov    %eax,0x24(%rsp)
          int b = data->thread->real_thread_index;
    7c30:	49 63 47 08          	movslq 0x8(%r15),%rax
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7c34:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7c39:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
          int b = data->thread->real_thread_index;
    7c3d:	48 89 c2             	mov    %rax,%rdx
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7c40:	48 8d 0c 48          	lea    (%rax,%rcx,2),%rcx
    7c44:	48 c1 e0 08          	shl    $0x8,%rax
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7c48:	41 89 d3             	mov    %edx,%r11d
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7c4b:	48 c1 e1 04          	shl    $0x4,%rcx
    7c4f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    7c54:	48 89 cd             	mov    %rcx,%rbp
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    7c57:	48 89 d9             	mov    %rbx,%rcx
    7c5a:	eb 24                	jmp    7c80 <barriered_work+0x150>
    7c5c:	0f 1f 40 00          	nopl   0x0(%rax)
    7c60:	83 44 24 0c 01       	addl   $0x1,0xc(%rsp)
    7c65:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    7c69:	48 81 c6 30 01 00 00 	add    $0x130,%rsi
    7c70:	49 81 c0 00 01 00 00 	add    $0x100,%r8
    7c77:	44 39 f0             	cmp    %r14d,%eax
    7c7a:	0f 84 40 02 00 00    	je     7ec0 <barriered_work+0x390>
                if (y == b) { continue; }
    7c80:	8b 44 24 0c          	mov    0xc(%rsp),%eax
    7c84:	41 39 c3             	cmp    %eax,%r11d
    7c87:	74 d7                	je     7c60 <barriered_work+0x130>
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    7c89:	49 8b 57 20          	mov    0x20(%r15),%rdx
    7c8d:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    7c92:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    7c96:	44 8b 88 a0 01 00 00 	mov    0x1a0(%rax),%r9d
    7c9d:	45 85 c9             	test   %r9d,%r9d
    7ca0:	75 be                	jne    7c60 <barriered_work+0x130>
    7ca2:	4c 8b 4c 2a 38       	mov    0x38(%rdx,%rbp,1),%r9
    7ca7:	4b 8d 14 29          	lea    (%r9,%r13,1),%rdx
    7cab:	44 8b 92 a0 01 00 00 	mov    0x1a0(%rdx),%r10d
    7cb2:	45 85 d2             	test   %r10d,%r10d
    7cb5:	75 a9                	jne    7c60 <barriered_work+0x130>
    7cb7:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    7cbe:	42 83 bc 02 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r8,1)
    7cc7:	75 97                	jne    7c60 <barriered_work+0x130>
    7cc9:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    7cd0:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    7cd5:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    7cdd:	75 81                	jne    7c60 <barriered_work+0x130>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    7cdf:	48 63 44 24 24       	movslq 0x24(%rsp),%rax
    7ce4:	85 c0                	test   %eax,%eax
    7ce6:	0f 8e 74 ff ff ff    	jle    7c60 <barriered_work+0x130>
    7cec:	48 89 c2             	mov    %rax,%rdx
    7cef:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
    7cf4:	41 bc 70 01 00 00    	mov    $0x170,%r12d
    7cfa:	48 c1 e2 09          	shl    $0x9,%rdx
    7cfe:	44 89 74 24 3c       	mov    %r14d,0x3c(%rsp)
    7d03:	48 89 54 24 40       	mov    %rdx,0x40(%rsp)
    7d08:	48 8d 9a a0 01 00 00 	lea    0x1a0(%rdx),%rbx
    7d0f:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    7d14:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    7d19:	4c 8b 6c 24 18       	mov    0x18(%rsp),%r13
    7d1e:	44 89 5c 24 38       	mov    %r11d,0x38(%rsp)
    7d23:	44 8b 5c 24 24       	mov    0x24(%rsp),%r11d
    7d28:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                        int next_task = abs((nn + 1) % data->thread_count);
    7d30:	41 83 c2 01          	add    $0x1,%r10d
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7d34:	4b 8b 34 21          	mov    (%r9,%r12,1),%rsi
                        int next_task = abs((nn + 1) % data->thread_count);
    7d38:	44 89 d0             	mov    %r10d,%eax
    7d3b:	99                   	cltd
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7d3c:	4c 01 c6             	add    %r8,%rsi
                        int next_task = abs((nn + 1) % data->thread_count);
    7d3f:	41 f7 fb             	idiv   %r11d
    return mailbox->lower;
    7d42:	4c 8b 36             	mov    (%rsi),%r14
    7d45:	4c 89 74 24 10       	mov    %r14,0x10(%rsp)
    mailbox->lower = data;
    7d4a:	4c 8b b6 80 00 00 00 	mov    0x80(%rsi),%r14
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    7d51:	48 63 d2             	movslq %edx,%rdx
    7d54:	48 c1 e2 09          	shl    $0x9,%rdx
    7d58:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    7d60:	4c 01 e8             	add    %r13,%rax
    return mailbox->lower;
    7d63:	4c 8b 38             	mov    (%rax),%r15
    return mailbox->higher;
    7d66:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    mailbox->lower = data;
    7d6d:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    7d70:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    7d75:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    mailbox->lower = data;
    7d7c:	48 89 16             	mov    %rdx,(%rsi)
    mailbox->higher = data;
    7d7f:	4c 89 be 80 00 00 00 	mov    %r15,0x80(%rsi)
    7d86:	be a0 01 00 00       	mov    $0x1a0,%esi
    7d8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
    7d90:	41 c7 04 31 01 00 00 00 	movl   $0x1,(%r9,%rsi,1)
                          data->thread->all_threads[t2].tasks[jj].swap = 1;
    7d98:	c7 04 37 01 00 00 00 	movl   $0x1,(%rdi,%rsi,1)
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
    7d9f:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
    7da6:	48 39 de             	cmp    %rbx,%rsi
    7da9:	75 e5                	jne    7d90 <barriered_work+0x260>
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    7dab:	4a 8b 34 27          	mov    (%rdi,%r12,1),%rsi
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    7daf:	48 8b 00             	mov    (%rax),%rax
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    7db2:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    7dbd:	49 81 c4 00 02 00 00 	add    $0x200,%r12
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    7dc4:	4a 8b b4 2e 80 00 00 00 	mov    0x80(%rsi,%r13,1),%rsi
    7dcc:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
                            ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    7dd6:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    7de0:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    7dea:	45 39 d3             	cmp    %r10d,%r11d
    7ded:	0f 85 3d ff ff ff    	jne    7d30 <barriered_work+0x200>
    7df3:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
    7df8:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    7dfd:	b8 70 01 00 00       	mov    $0x170,%eax
    7e02:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    7e07:	44 8b 5c 24 38       	mov    0x38(%rsp),%r11d
    7e0c:	44 8b 74 24 3c       	mov    0x3c(%rsp),%r14d
    7e11:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    7e16:	48 8d 9a 70 01 00 00 	lea    0x170(%rdx),%rbx
    7e1d:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    7e22:	eb 13                	jmp    7e37 <barriered_work+0x307>
    7e24:	0f 1f 40 00          	nopl   0x0(%rax)
                        for (int nn = 0; nn < data->thread_count; nn++) {
    7e28:	48 05 00 02 00 00    	add    $0x200,%rax
    7e2e:	48 39 d8             	cmp    %rbx,%rax
    7e31:	0f 84 29 fe ff ff    	je     7c60 <barriered_work+0x130>
                          if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    7e37:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    7e3b:	4d 8b 14 01          	mov    (%r9,%rax,1),%r10
    7e3f:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    7e43:	4b 39 14 02          	cmp    %rdx,(%r10,%r8,1)
    7e47:	75 df                	jne    7e28 <barriered_work+0x2f8>
    7e49:	bf 01 00 00 00       	mov    $0x1,%edi
    7e4e:	48 8d 35 f9 13 00 00 	lea    0x13f9(%rip),%rsi        # 924e <_IO_stdin_used+0x24e>
    7e55:	31 c0                	xor    %eax,%eax
    7e57:	e8 74 a6 ff ff       	call   24d0 <__printf_chk@plt>
                            exit(1);
    7e5c:	bf 01 00 00 00       	mov    $0x1,%edi
    7e61:	e8 da a6 ff ff       	call   2540 <exit@plt>
    7e66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    7e70:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    7e77:	85 ed                	test   %ebp,%ebp
    7e79:	0f 85 59 fd ff ff    	jne    7bd8 <barriered_work+0xa8>
    7e7f:	44 8b 90 f8 00 00 00 	mov    0xf8(%rax),%r10d
    7e86:	45 85 d2             	test   %r10d,%r10d
    7e89:	0f 85 49 fd ff ff    	jne    7bd8 <barriered_work+0xa8>
    7e8f:	69 87 80 00 00 00 1d e6 cb 0b 	imul   $0xbcbe61d,0x80(%rdi),%eax
    7e99:	05 40 7c 0a 00       	add    $0xa7c40,%eax
    7e9e:	c1 c8 05             	ror    $0x5,%eax
    7ea1:	3d c4 a7 00 00       	cmp    $0xa7c4,%eax
    7ea6:	0f 87 2c fd ff ff    	ja     7bd8 <barriered_work+0xa8>
      data->thread->global->request_group_sync = 0;
    7eac:	48 c7 01 00 00 00 00 	movq   $0x0,(%rcx)
    7eb3:	e9 20 fd ff ff       	jmp    7bd8 <barriered_work+0xa8>
    7eb8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    7ec0:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    7ec5:	48 89 cb             	mov    %rcx,%rbx
        fswap(data); 
    7ec8:	48 89 df             	mov    %rbx,%rdi
    7ecb:	e8 10 fb ff ff       	call   79e0 <fswap>
        receive(data);
    7ed0:	48 89 df             	mov    %rbx,%rdi
    7ed3:	e8 88 f6 ff ff       	call   7560 <receive>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    7ed8:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    7edf:	31 ff                	xor    %edi,%edi
    7ee1:	48 c1 e6 05          	shl    $0x5,%rsi
    7ee5:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    7eec:	e8 7f a4 ff ff       	call   2370 <clock_gettime@plt>
      int modcount = ++data->thread->protected_state->modcount;
    7ef1:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    7ef8:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      int modcount = ++data->thread->protected_state->modcount;
    7eff:	48 8b 50 48          	mov    0x48(%rax),%rdx
    7f03:	8b 4a 10             	mov    0x10(%rdx),%ecx
    7f06:	8d 69 01             	lea    0x1(%rcx),%ebp
    7f09:	89 6a 10             	mov    %ebp,0x10(%rdx)
      while (data->scheduled == 1) {
    7f0c:	75 50                	jne    7f5e <barriered_work+0x42e>
    7f0e:	66 90                	xchg   %ax,%ax
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    7f10:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    7f17:	48 8b 40 18          	mov    0x18(%rax),%rax
    7f1b:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
        data->n++;
    7f1f:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    7f27:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7f2b:	48 c1 e7 09          	shl    $0x9,%rdi
    7f2f:	48 03 78 38          	add    0x38(%rax),%rdi
    7f33:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      while (data->scheduled == 1) {
    7f39:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      if (modcount != data->thread->protected_state->modcount) {
    7f40:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    7f47:	74 c7                	je     7f10 <barriered_work+0x3e0>
      if (modcount != data->thread->protected_state->modcount) {
    7f49:	48 8b 40 48          	mov    0x48(%rax),%rax
    7f4d:	3b 68 10             	cmp    0x10(%rax),%ebp
    7f50:	74 0c                	je     7f5e <barriered_work+0x42e>
    7f52:	48 8d 3d 10 13 00 00 	lea    0x1310(%rip),%rdi        # 9269 <_IO_stdin_used+0x269>
    7f59:	e8 f2 a3 ff ff       	call   2350 <puts@plt>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    7f5e:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    7f65:	31 ff                	xor    %edi,%edi
    7f67:	48 c1 e6 05          	shl    $0x5,%rsi
    7f6b:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    7f72:	48 83 c6 10          	add    $0x10,%rsi
    7f76:	e8 f5 a3 ff ff       	call   2370 <clock_gettime@plt>
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    7f7b:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    7f82:	48 83 c0 01          	add    $0x1,%rax
    7f86:	48 99                	cqto
    7f88:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    if (t == data->thread_count - 1) {
    7f8f:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    7f95:	83 e8 01             	sub    $0x1,%eax
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    7f98:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    if (t == data->thread_count - 1) {
    7f9f:	44 39 e0             	cmp    %r12d,%eax
    7fa2:	74 53                	je     7ff7 <barriered_work+0x4c7>
    data->swap = 0;
    7fa4:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    return 0;
    7fae:	e9 d8 fb ff ff       	jmp    7b8b <barriered_work+0x5b>
    7fb3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      receive(data);
    7fb8:	e8 a3 f5 ff ff       	call   7560 <receive>
      while (data->scheduled == 1) {
    7fbd:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    7fc4:	75 1b                	jne    7fe1 <barriered_work+0x4b1>
    7fc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        data->n++;
    7fd0:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      while (data->scheduled == 1) {
    7fd8:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    7fdf:	74 ef                	je     7fd0 <barriered_work+0x4a0>
      sendm(data);
    7fe1:	48 89 df             	mov    %rbx,%rdi
    7fe4:	e8 c7 f6 ff ff       	call   76b0 <sendm>
    if (t == data->thread_count - 1) {
    7fe9:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    7fef:	83 e8 01             	sub    $0x1,%eax
    7ff2:	44 39 e0             	cmp    %r12d,%eax
    7ff5:	75 ad                	jne    7fa4 <barriered_work+0x474>
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    7ff7:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    7ffe:	85 d2                	test   %edx,%edx
    8000:	7e a2                	jle    7fa4 <barriered_work+0x474>
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    8002:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    8009:	48 c1 e2 09          	shl    $0x9,%rdx
    800d:	48 63 41 08          	movslq 0x8(%rcx),%rax
    8011:	48 8d 34 c0          	lea    (%rax,%rax,8),%rsi
    8015:	48 8d 04 70          	lea    (%rax,%rsi,2),%rax
    8019:	48 c1 e0 04          	shl    $0x4,%rax
    801d:	48 03 41 20          	add    0x20(%rcx),%rax
    8021:	48 8b 40 38          	mov    0x38(%rax),%rax
    8025:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    8029:	80 e6 02             	and    $0x2,%dh
    802c:	74 1a                	je     8048 <barriered_work+0x518>
    802e:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    8035:	48 05 00 02 00 00    	add    $0x200,%rax
    803b:	48 39 c8             	cmp    %rcx,%rax
    803e:	0f 84 60 ff ff ff    	je     7fa4 <barriered_work+0x474>
    8044:	0f 1f 40 00          	nopl   0x0(%rax)
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    8048:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    804f:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    8056:	48 05 00 04 00 00    	add    $0x400,%rax
    805c:	48 39 c8             	cmp    %rcx,%rax
    805f:	75 e7                	jne    8048 <barriered_work+0x518>
    8061:	e9 3e ff ff ff       	jmp    7fa4 <barriered_work+0x474>
    8066:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    8070:	39 c5                	cmp    %eax,%ebp
    8072:	0f 85 60 fb ff ff    	jne    7bd8 <barriered_work+0xa8>
      struct ProtectedState *protected = data->thread->global->protected_state;
    8078:	48 8b 69 08          	mov    0x8(%rcx),%rbp
      nanosleep(&preempt , &rem);
    807c:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
    8081:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
      int modcount = ++protected->modcount;
    8086:	8b 45 10             	mov    0x10(%rbp),%eax
      protected->protected++;
    8089:	48 83 45 00 01       	addq   $0x1,0x0(%rbp)
      int modcount = ++protected->modcount;
    808e:	44 8d 60 01          	lea    0x1(%rax),%r12d
    8092:	44 89 65 10          	mov    %r12d,0x10(%rbp)
      nanosleep(&preempt , &rem);
    8096:	e8 25 a3 ff ff       	call   23c0 <nanosleep@plt>
      if (protected->modcount != modcount) {
    809b:	44 3b 65 10          	cmp    0x10(%rbp),%r12d
    809f:	74 0c                	je     80ad <barriered_work+0x57d>
    80a1:	48 8d 3d 89 11 00 00 	lea    0x1189(%rip),%rdi        # 9231 <_IO_stdin_used+0x231>
    80a8:	e8 a3 a2 ff ff       	call   2350 <puts@plt>
      data->thread->global->request_thread_sync = (data->thread_index + 1) % data->thread_count;
    80ad:	48 63 ab 30 01 00 00 	movslq 0x130(%rbx),%rbp
    80b4:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    80bb:	8d 45 01             	lea    0x1(%rbp),%eax
    80be:	48 8b b1 00 01 00 00 	mov    0x100(%rcx),%rsi
    80c5:	99                   	cltd
    80c6:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    80cc:	89 56 04             	mov    %edx,0x4(%rsi)
      if (data->thread_index == 1) {
    80cf:	83 fd 01             	cmp    $0x1,%ebp
    80d2:	0f 85 00 fb ff ff    	jne    7bd8 <barriered_work+0xa8>
        data->thread->global->request_group_sync = (data->thread->group + 1) % data->thread->group_count;
    80d8:	8b 81 f8 00 00 00    	mov    0xf8(%rcx),%eax
    80de:	83 c0 01             	add    $0x1,%eax
    80e1:	99                   	cltd
    80e2:	f7 b9 d0 00 00 00    	idivl  0xd0(%rcx)
    80e8:	89 16                	mov    %edx,(%rsi)
    80ea:	e9 e9 fa ff ff       	jmp    7bd8 <barriered_work+0xa8>
}
    80ef:	e8 ac a2 ff ff       	call   23a0 <__stack_chk_fail@plt>
    80f4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    80ff:	90                   	nop

0000000000008100 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    8100:	f3 0f 1e fa          	endbr64
    8104:	53                   	push   %rbx
    8105:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    8108:	e8 63 f0 ff ff       	call   7170 <barriered_work_ingest>
  barriered_work(data);
    810d:	48 89 df             	mov    %rbx,%rdi
}
    8110:	5b                   	pop    %rbx
  barriered_work(data);
    8111:	e9 1a fa ff ff       	jmp    7b30 <barriered_work>
    8116:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000008120 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    8120:	f3 0f 1e fa          	endbr64
}
    8124:	31 c0                	xor    %eax,%eax
    8126:	c3                   	ret
    8127:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000008130 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    8130:	f3 0f 1e fa          	endbr64
    8134:	31 c0                	xor    %eax,%eax
    8136:	c3                   	ret
    8137:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000008140 <after>:
int after(struct timespec left, struct timespec right) {
    8140:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    8144:	31 c0                	xor    %eax,%eax
    8146:	48 39 d7             	cmp    %rdx,%rdi
    8149:	7e 08                	jle    8153 <after+0x13>
    814b:	31 c0                	xor    %eax,%eax
    814d:	48 39 ce             	cmp    %rcx,%rsi
    8150:	0f 9f c0             	setg   %al
}
    8153:	c3                   	ret
    8154:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    815f:	90                   	nop

0000000000008160 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    8160:	f3 0f 1e fa          	endbr64
    8164:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    8169:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    816e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8170:	48 39 d7             	cmp    %rdx,%rdi
    8173:	7f 18                	jg     818d <within+0x2d>
    8175:	4d 39 d8             	cmp    %r11,%r8
    8178:	0f 9e c2             	setle  %dl
    817b:	48 39 ce             	cmp    %rcx,%rsi
    817e:	0f 9e c0             	setle  %al
    8181:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8183:	31 c0                	xor    %eax,%eax
    8185:	4d 39 d1             	cmp    %r10,%r9
    8188:	0f 9e c0             	setle  %al
    818b:	21 d0                	and    %edx,%eax
}
    818d:	c3                   	ret
    818e:	66 90                	xchg   %ax,%ax

0000000000008190 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    8190:	f3 0f 1e fa          	endbr64
    8194:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    8199:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    819e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    81a3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    81a8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    81ad:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    81b2:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    81b7:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    81bc:	48 39 fe             	cmp    %rdi,%rsi
    81bf:	7d 2f                	jge    81f0 <overlap+0x60>
    81c1:	48 39 ca             	cmp    %rcx,%rdx
    81c4:	7d 62                	jge    8228 <overlap+0x98>
    81c6:	4d 39 da             	cmp    %r11,%r10
    81c9:	7d 0e                	jge    81d9 <overlap+0x49>
    return 1;
    81cb:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    81d0:	4d 39 c1             	cmp    %r8,%r9
    81d3:	0f 8c 7f 00 00 00    	jl     8258 <overlap+0xc8>
  return 0;
    81d9:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    81db:	4d 39 c1             	cmp    %r8,%r9
    81de:	7f 4c                	jg     822c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    81e0:	31 c0                	xor    %eax,%eax
    81e2:	4d 39 da             	cmp    %r11,%r10
    81e5:	0f 9e c0             	setle  %al
    81e8:	c3                   	ret
    81e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    81f0:	7e 4e                	jle    8240 <overlap+0xb0>
    81f2:	48 39 ca             	cmp    %rcx,%rdx
    81f5:	7f 39                	jg     8230 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    81f7:	75 31                	jne    822a <overlap+0x9a>
    81f9:	4d 39 c1             	cmp    %r8,%r9
    81fc:	7c 2c                	jl     822a <overlap+0x9a>
    return 1;
    81fe:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8203:	4d 39 da             	cmp    %r11,%r10
    8206:	7d 24                	jge    822c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8208:	48 39 ca             	cmp    %rcx,%rdx
    820b:	0f 94 c2             	sete   %dl
    820e:	48 39 fe             	cmp    %rdi,%rsi
    8211:	0f 94 c0             	sete   %al
    8214:	21 c2                	and    %eax,%edx
    8216:	31 c0                	xor    %eax,%eax
    8218:	4d 39 c1             	cmp    %r8,%r9
    821b:	0f 94 c0             	sete   %al
    821e:	21 d0                	and    %edx,%eax
    8220:	c3                   	ret
    8221:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    8228:	74 af                	je     81d9 <overlap+0x49>
  return 0;
    822a:	31 c0                	xor    %eax,%eax
}
    822c:	c3                   	ret
    822d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    8230:	4d 39 da             	cmp    %r11,%r10
    8233:	7e c4                	jle    81f9 <overlap+0x69>
    return 1;
    8235:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    823a:	4d 39 c1             	cmp    %r8,%r9
    823d:	7e ba                	jle    81f9 <overlap+0x69>
    823f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8240:	48 39 ca             	cmp    %rcx,%rdx
    8243:	7c 94                	jl     81d9 <overlap+0x49>
    8245:	4d 39 c1             	cmp    %r8,%r9
    8248:	7d b4                	jge    81fe <overlap+0x6e>
    824a:	48 39 ca             	cmp    %rcx,%rdx
    824d:	74 91                	je     81e0 <overlap+0x50>
    824f:	eb d9                	jmp    822a <overlap+0x9a>
    8251:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    8258:	c3                   	ret
    8259:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000008260 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    8260:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    8264:	85 f6                	test   %esi,%esi
    8266:	0f 8e 44 03 00 00    	jle    85b0 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    826c:	41 57                	push   %r15
    826e:	41 89 f7             	mov    %esi,%r15d
    8271:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    8273:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    8276:	41 55                	push   %r13
    8278:	41 54                	push   %r12
    827a:	55                   	push   %rbp
    827b:	53                   	push   %rbx
    827c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    8280:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    8284:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    8289:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    828e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    8291:	45 39 e6             	cmp    %r12d,%r14d
    8294:	0f 84 4e 02 00 00    	je     84e8 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    829a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    829f:	8b 50 08             	mov    0x8(%rax),%edx
    82a2:	85 d2                	test   %edx,%edx
    82a4:	0f 8e 3e 02 00 00    	jle    84e8 <verify+0x288>
    82aa:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    82af:	31 c9                	xor    %ecx,%ecx
    82b1:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    82b6:	31 c0                	xor    %eax,%eax
    82b8:	44 89 f2             	mov    %r14d,%edx
    82bb:	bf 01 00 00 00       	mov    $0x1,%edi
    82c0:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    82c5:	48 8d 35 ad 0f 00 00 	lea    0xfad(%rip),%rsi        # 9279 <_IO_stdin_used+0x279>
    82cc:	e8 ff a1 ff ff       	call   24d0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    82d1:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    82d6:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    82db:	8b 40 08             	mov    0x8(%rax),%eax
    82de:	85 c0                	test   %eax,%eax
    82e0:	0f 8e e6 01 00 00    	jle    84cc <verify+0x26c>
    82e6:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    82e9:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    82ee:	31 db                	xor    %ebx,%ebx
    82f0:	48 c1 e0 09          	shl    $0x9,%rax
    82f4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    82f9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    82fe:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8303:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    8308:	4c 8b 20             	mov    (%rax),%r12
    830b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    8310:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    8315:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    831a:	49 89 de             	mov    %rbx,%r14
    831d:	48 8d 35 6a 0f 00 00 	lea    0xf6a(%rip),%rsi        # 928e <_IO_stdin_used+0x28e>
    8324:	49 c1 e6 09          	shl    $0x9,%r14
    8328:	bf 01 00 00 00       	mov    $0x1,%edi
    832d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    8331:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    8339:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    833e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    8346:	31 c0                	xor    %eax,%eax
    8348:	e8 83 a1 ff ff       	call   24d0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    834d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8352:	4c 8b 20             	mov    (%rax),%r12
    8355:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    835e:	0f 8e 47 01 00 00    	jle    84ab <verify+0x24b>
    8364:	4c 03 75 00          	add    0x0(%rbp),%r14
    8368:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    836d:	ba 01 00 00 00       	mov    $0x1,%edx
    8372:	4d 89 f5             	mov    %r14,%r13
    8375:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    837c:	4d 85 f6             	test   %r14,%r14
    837f:	0f 8e 21 01 00 00    	jle    84a6 <verify+0x246>
    8385:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    8388:	48 89 d5             	mov    %rdx,%rbp
    838b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8390:	31 db                	xor    %ebx,%ebx
    8392:	4d 89 f2             	mov    %r14,%r10
    8395:	48 c1 e5 05          	shl    $0x5,%rbp
    8399:	48 83 ed 20          	sub    $0x20,%rbp
    839d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    83a1:	49 89 ee             	mov    %rbp,%r14
    83a4:	48 89 dd             	mov    %rbx,%rbp
    83a7:	48 89 d3             	mov    %rdx,%rbx
    83aa:	eb 31                	jmp    83dd <verify+0x17d>
    83ac:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    83b0:	4c 39 c2             	cmp    %r8,%rdx
    83b3:	0f 8d 57 01 00 00    	jge    8510 <verify+0x2b0>
    83b9:	4c 39 df             	cmp    %r11,%rdi
    83bc:	7e 05                	jle    83c3 <verify+0x163>
    83be:	49 39 c1             	cmp    %rax,%r9
    83c1:	7c 75                	jl     8438 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    83c3:	4c 39 df             	cmp    %r11,%rdi
    83c6:	0f 8d ab 01 00 00    	jge    8577 <verify+0x317>
    83cc:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    83d0:	48 83 c5 01          	add    $0x1,%rbp
    83d4:	49 39 ea             	cmp    %rbp,%r10
    83d7:	0f 8e a9 00 00 00    	jle    8486 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    83dd:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    83e4:	48 89 e8             	mov    %rbp,%rax
    83e7:	48 c1 e0 05          	shl    $0x5,%rax
    83eb:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    83f2:	4c 01 f2             	add    %r14,%rdx
    83f5:	48 8b 08             	mov    (%rax),%rcx
    83f8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    83fc:	48 8b 32             	mov    (%rdx),%rsi
    83ff:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    8403:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    8407:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    840b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    840f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    8413:	48 39 f1             	cmp    %rsi,%rcx
    8416:	7c 98                	jl     83b0 <verify+0x150>
    8418:	0f 8e 42 01 00 00    	jle    8560 <verify+0x300>
    841e:	4c 39 c2             	cmp    %r8,%rdx
    8421:	0f 8f f9 00 00 00    	jg     8520 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8427:	75 a7                	jne    83d0 <verify+0x170>
    8429:	4c 39 df             	cmp    %r11,%rdi
    842c:	7f a2                	jg     83d0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    842e:	49 39 c1             	cmp    %rax,%r9
    8431:	7c 9d                	jl     83d0 <verify+0x170>
    8433:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    8438:	49 89 c1             	mov    %rax,%r9
    843b:	48 89 f9             	mov    %rdi,%rcx
    843e:	48 89 f2             	mov    %rsi,%rdx
    8441:	bf 01 00 00 00       	mov    $0x1,%edi
    8446:	48 8d 35 eb 13 00 00 	lea    0x13eb(%rip),%rsi        # 9838 <_IO_stdin_used+0x838>
    844d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    844f:	48 83 c5 01          	add    $0x1,%rbp
    8453:	e8 78 a0 ff ff       	call   24d0 <__printf_chk@plt>
    8458:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    845d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    8462:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8465:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    846a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8471:	4c 8b 20             	mov    (%rax),%r12
    8474:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8479:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    847d:	49 39 ea             	cmp    %rbp,%r10
    8480:	0f 8f 57 ff ff ff    	jg     83dd <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8486:	48 89 da             	mov    %rbx,%rdx
    8489:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    8490:	7d 14                	jge    84a6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8492:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    8499:	48 83 c2 01          	add    $0x1,%rdx
    849d:	4d 85 f6             	test   %r14,%r14
    84a0:	0f 8f e2 fe ff ff    	jg     8388 <verify+0x128>
    84a6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    84ab:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    84b0:	48 83 c3 01          	add    $0x1,%rbx
    84b4:	39 58 08             	cmp    %ebx,0x8(%rax)
    84b7:	0f 8f 53 fe ff ff    	jg     8310 <verify+0xb0>
    84bd:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    84c2:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    84c7:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    84cc:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    84d1:	48 83 c1 01          	add    $0x1,%rcx
    84d5:	39 48 08             	cmp    %ecx,0x8(%rax)
    84d8:	0f 8f d8 fd ff ff    	jg     82b6 <verify+0x56>
    84de:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    84e3:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    84e8:	48 81 44 24 10 30 01 00 00 	addq   $0x130,0x10(%rsp)
    84f1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    84f6:	41 39 c7             	cmp    %eax,%r15d
    84f9:	0f 84 86 00 00 00    	je     8585 <verify+0x325>
    84ff:	41 89 c4             	mov    %eax,%r12d
    8502:	e9 8a fd ff ff       	jmp    8291 <verify+0x31>
    8507:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8510:	0f 85 ba fe ff ff    	jne    83d0 <verify+0x170>
    8516:	e9 a8 fe ff ff       	jmp    83c3 <verify+0x163>
    851b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    8520:	49 39 c1             	cmp    %rax,%r9
    8523:	7e 09                	jle    852e <verify+0x2ce>
    8525:	4c 39 df             	cmp    %r11,%rdi
    8528:	0f 8c 0a ff ff ff    	jl     8438 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    852e:	4c 39 df             	cmp    %r11,%rdi
    8531:	0f 8f 99 fe ff ff    	jg     83d0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8537:	49 39 c1             	cmp    %rax,%r9
    853a:	0f 8d f8 fe ff ff    	jge    8438 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8540:	48 39 f1             	cmp    %rsi,%rcx
    8543:	0f 85 87 fe ff ff    	jne    83d0 <verify+0x170>
    8549:	4c 39 c2             	cmp    %r8,%rdx
    854c:	0f 85 7e fe ff ff    	jne    83d0 <verify+0x170>
    8552:	4c 39 df             	cmp    %r11,%rdi
    8555:	0f 84 dd fe ff ff    	je     8438 <verify+0x1d8>
    855b:	e9 70 fe ff ff       	jmp    83d0 <verify+0x170>
    8560:	4c 39 c2             	cmp    %r8,%rdx
    8563:	0f 8c 5a fe ff ff    	jl     83c3 <verify+0x163>
    8569:	4c 39 df             	cmp    %r11,%rdi
    856c:	7e c9                	jle    8537 <verify+0x2d7>
    856e:	4c 39 c2             	cmp    %r8,%rdx
    8571:	0f 85 59 fe ff ff    	jne    83d0 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8577:	49 39 c1             	cmp    %rax,%r9
    857a:	0f 8f 50 fe ff ff    	jg     83d0 <verify+0x170>
    8580:	e9 b3 fe ff ff       	jmp    8438 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    8585:	48 81 44 24 18 30 01 00 00 	addq   $0x130,0x18(%rsp)
    858e:	41 8d 46 01          	lea    0x1(%r14),%eax
    8592:	45 39 e6             	cmp    %r12d,%r14d
    8595:	74 08                	je     859f <verify+0x33f>
    8597:	41 89 c6             	mov    %eax,%r14d
    859a:	e9 ea fc ff ff       	jmp    8289 <verify+0x29>
}
    859f:	48 83 c4 58          	add    $0x58,%rsp
    85a3:	31 c0                	xor    %eax,%eax
    85a5:	5b                   	pop    %rbx
    85a6:	5d                   	pop    %rbp
    85a7:	41 5c                	pop    %r12
    85a9:	41 5d                	pop    %r13
    85ab:	41 5e                	pop    %r14
    85ad:	41 5f                	pop    %r15
    85af:	c3                   	ret
    85b0:	31 c0                	xor    %eax,%eax
    85b2:	c3                   	ret

Disassembly of section .fini:

00000000000085b4 <_fini>:
    85b4:	f3 0f 1e fa          	endbr64
    85b8:	48 83 ec 08          	sub    $0x8,%rsp
    85bc:	48 83 c4 08          	add    $0x8,%rsp
    85c0:	c3                   	ret
