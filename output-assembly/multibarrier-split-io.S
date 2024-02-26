
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

0000000000002310 <free@plt>:
    2310:	f3 0f 1e fa          	endbr64
    2314:	ff 25 56 9b 00 00    	jmp    *0x9b56(%rip)        # be70 <free@GLIBC_2.2.5>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002320 <putchar@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 4e 9b 00 00    	jmp    *0x9b4e(%rip)        # be78 <putchar@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <pthread_setaffinity_np@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 46 9b 00 00    	jmp    *0x9b46(%rip)        # be80 <pthread_setaffinity_np@GLIBC_2.34>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <puts@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 3e 9b 00 00    	jmp    *0x9b3e(%rip)        # be88 <puts@GLIBC_2.2.5>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <setsockopt@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 36 9b 00 00    	jmp    *0x9b36(%rip)        # be90 <setsockopt@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <clock_gettime@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 2e 9b 00 00    	jmp    *0x9b2e(%rip)        # be98 <clock_gettime@GLIBC_2.17>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <fclose@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 26 9b 00 00    	jmp    *0x9b26(%rip)        # bea0 <fclose@GLIBC_2.2.5>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <strlen@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 1e 9b 00 00    	jmp    *0x9b1e(%rip)        # bea8 <strlen@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <__stack_chk_fail@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 16 9b 00 00    	jmp    *0x9b16(%rip)        # beb0 <__stack_chk_fail@GLIBC_2.4>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <io_uring_submit@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 0e 9b 00 00    	jmp    *0x9b0e(%rip)        # beb8 <io_uring_submit@LIBURING_2.0>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <nanosleep@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 06 9b 00 00    	jmp    *0x9b06(%rip)        # bec0 <nanosleep@GLIBC_2.2.5>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <strrchr@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 fe 9a 00 00    	jmp    *0x9afe(%rip)        # bec8 <strrchr@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <fputs@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 f6 9a 00 00    	jmp    *0x9af6(%rip)        # bed0 <fputs@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <close@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 ee 9a 00 00    	jmp    *0x9aee(%rip)        # bed8 <close@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <strtok_r@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 e6 9a 00 00    	jmp    *0x9ae6(%rip)        # bee0 <strtok_r@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <read@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 de 9a 00 00    	jmp    *0x9ade(%rip)        # bee8 <read@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <calloc@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 d6 9a 00 00    	jmp    *0x9ad6(%rip)        # bef0 <calloc@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <strcmp@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 ce 9a 00 00    	jmp    *0x9ace(%rip)        # bef8 <strcmp@GLIBC_2.2.5>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <__memcpy_chk@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 c6 9a 00 00    	jmp    *0x9ac6(%rip)        # bf00 <__memcpy_chk@GLIBC_2.3.4>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <stat@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 be 9a 00 00    	jmp    *0x9abe(%rip)        # bf08 <stat@GLIBC_2.33>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <memcpy@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 b6 9a 00 00    	jmp    *0x9ab6(%rip)        # bf10 <memcpy@GLIBC_2.14>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <io_uring_queue_init@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 ae 9a 00 00    	jmp    *0x9aae(%rip)        # bf18 <io_uring_queue_init@LIBURING_2.0>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <eventfd_write@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 a6 9a 00 00    	jmp    *0x9aa6(%rip)        # bf20 <eventfd_write@GLIBC_2.7>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <malloc@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 9e 9a 00 00    	jmp    *0x9a9e(%rip)        # bf28 <malloc@GLIBC_2.2.5>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <listen@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 96 9a 00 00    	jmp    *0x9a96(%rip)        # bf30 <listen@GLIBC_2.2.5>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <__strcpy_chk@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 8e 9a 00 00    	jmp    *0x9a8e(%rip)        # bf38 <__strcpy_chk@GLIBC_2.3.4>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <__io_uring_get_cqe@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 86 9a 00 00    	jmp    *0x9a86(%rip)        # bf40 <__io_uring_get_cqe@LIBURING_2.0>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <__printf_chk@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 7e 9a 00 00    	jmp    *0x9a7e(%rip)        # bf48 <__printf_chk@GLIBC_2.3.4>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <bind@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 76 9a 00 00    	jmp    *0x9a76(%rip)        # bf50 <bind@GLIBC_2.2.5>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <pthread_create@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 6e 9a 00 00    	jmp    *0x9a6e(%rip)        # bf58 <pthread_create@GLIBC_2.34>
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
  if (b > a) { return b; }
  return a;
}

int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send);
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
    25f6:	48 8d 3d 4a 6d 00 00 	lea    0x6d4a(%rip),%rdi        # 9347 <_IO_stdin_used+0x347>
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
    2620:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2628:	0f 0b                	ud2

    sock = socket(PF_INET, SOCK_STREAM, 0);


    if (sock == -1)
        fatal_error("socket()");
    262a:	48 8d 3d 75 6b 00 00 	lea    0x6b75(%rip),%rdi        # 91a6 <_IO_stdin_used+0x1a6>
    2631:	e8 aa ff ff ff       	call   25e0 <fatal_error>
    printf("in send io read my identity %s my ring is %d other io is %d\n", data->identity, data->my_io, data->other_io);
    void * reply;
    
    void * _reply = bufferrecv("waitsocketreply", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET, &reply, 0); 
    struct Buffer *bufferreply = _reply;
    struct NewSocketMessage *msg = bufferreply->data;
    2636:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    263e:	0f 0b                	ud2
        fatal_error("setsockopt(SO_REUSEADDR)");
    2640:	48 8d 3d 68 6b 00 00 	lea    0x6b68(%rip),%rdi        # 91af <_IO_stdin_used+0x1af>
    2647:	e8 94 ff ff ff       	call   25e0 <fatal_error>
        fatal_error("bind()");
    264c:	48 8d 3d 75 6b 00 00 	lea    0x6b75(%rip),%rdi        # 91c8 <_IO_stdin_used+0x1c8>
    2653:	e8 88 ff ff ff       	call   25e0 <fatal_error>
				   perror("new client epoll_create1");
    2658:	48 8d 3d ee 6b 00 00 	lea    0x6bee(%rip),%rdi        # 924d <_IO_stdin_used+0x24d>
    265f:	e8 ac fe ff ff       	call   2510 <perror@plt>
				   exit(EXIT_FAILURE);
    2664:	bf 01 00 00 00       	mov    $0x1,%edi
    2669:	e8 b2 fe ff ff       	call   2520 <exit@plt>
      fatal_error("listen()");
    266e:	48 8d 3d 5a 6b 00 00 	lea    0x6b5a(%rip),%rdi        # 91cf <_IO_stdin_used+0x1cf>
    2675:	e8 66 ff ff ff       	call   25e0 <fatal_error>
    267a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2682:	0f 0b                	ud2
            fatal_error("io_uring_wait_cqe");
    2684:	48 8d 3d 82 6b 00 00 	lea    0x6b82(%rip),%rdi        # 920d <_IO_stdin_used+0x20d>
    268b:	e8 50 ff ff ff       	call   25e0 <fatal_error>
    2690:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2698:	0f 0b                	ud2
    269a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26a2:	0f 0b                	ud2
    26a4:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26ac:	0f 0b                	ud2
          if (send != NULL) {
            printf("data is to write\n");
            struct Write *write = send->data;
            struct io_uring_sqe *sqe = io_uring_get_sqe(&ring);
            struct Request *req = write->request;
            req->event_type = EVENT_TYPE_WRITE;
    26ae:	41 c7 07 02 00 00 00 	movl   $0x2,(%r15)
    26b5:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26bd:	0f 0b                	ud2
    26bf:	90                   	nop

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
    26c6:	48 8d 3d b3 72 00 00 	lea    0x72b3(%rip),%rdi        # 9980 <_IO_stdin_used+0x980>
    26cd:	41 56                	push   %r14
    26cf:	41 55                	push   %r13
    26d1:	41 54                	push   %r12
    26d3:	4c 8d 25 f8 6d 00 00 	lea    0x6df8(%rip),%r12        # 94d2 <_IO_stdin_used+0x4d2>
    26da:	55                   	push   %rbp
    26db:	53                   	push   %rbx
    26dc:	48 81 ec 38 01 00 00 	sub    $0x138,%rsp
    26e3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    26ec:	48 89 84 24 28 01 00 00 	mov    %rax,0x128(%rsp)
    26f4:	48 8d 05 55 22 00 00 	lea    0x2255(%rip),%rax        # 4950 <barriered_reset>
    26fb:	66 48 0f 6e f0       	movq   %rax,%xmm6
    2700:	0f 16 35 49 95 00 00 	movhps 0x9549(%rip),%xmm6        # bc50 <__do_global_dtors_aux_fini_array_entry+0x8>
    2707:	0f 29 b4 24 c0 00 00 00 	movaps %xmm6,0xc0(%rsp)
    270f:	e8 2c fc ff ff       	call   2340 <puts@plt>
    2714:	bf 0a 00 00 00       	mov    $0xa,%edi
    2719:	e8 02 fc ff ff       	call   2320 <putchar@plt>
    271e:	ba 01 00 00 00       	mov    $0x1,%edx
    2723:	48 8d 35 a0 6c 00 00 	lea    0x6ca0(%rip),%rsi        # 93ca <_IO_stdin_used+0x3ca>
    272a:	31 c0                	xor    %eax,%eax
    272c:	bf 01 00 00 00       	mov    $0x1,%edi
    2731:	e8 8a fd ff ff       	call   24c0 <__printf_chk@plt>
    2736:	ba 06 00 00 00       	mov    $0x6,%edx
    273b:	48 8d 35 98 6c 00 00 	lea    0x6c98(%rip),%rsi        # 93da <_IO_stdin_used+0x3da>
    2742:	31 c0                	xor    %eax,%eax
    2744:	bf 01 00 00 00       	mov    $0x1,%edi
    2749:	e8 72 fd ff ff       	call   24c0 <__printf_chk@plt>
    274e:	ba 03 00 00 00       	mov    $0x3,%edx
    2753:	48 8d 35 95 6c 00 00 	lea    0x6c95(%rip),%rsi        # 93ef <_IO_stdin_used+0x3ef>
    275a:	31 c0                	xor    %eax,%eax
    275c:	bf 01 00 00 00       	mov    $0x1,%edi
    2761:	e8 5a fd ff ff       	call   24c0 <__printf_chk@plt>
    2766:	ba 02 00 00 00       	mov    $0x2,%edx
    276b:	48 8d 35 8d 6c 00 00 	lea    0x6c8d(%rip),%rsi        # 93ff <_IO_stdin_used+0x3ff>
    2772:	31 c0                	xor    %eax,%eax
    2774:	bf 01 00 00 00       	mov    $0x1,%edi
    2779:	e8 42 fd ff ff       	call   24c0 <__printf_chk@plt>
    277e:	48 8d 3d 90 6c 00 00 	lea    0x6c90(%rip),%rdi        # 9415 <_IO_stdin_used+0x415>
    2785:	e8 b6 fb ff ff       	call   2340 <puts@plt>
    278a:	ba 02 00 00 00       	mov    $0x2,%edx
    278f:	48 8d 35 9b 6c 00 00 	lea    0x6c9b(%rip),%rsi        # 9431 <_IO_stdin_used+0x431>
    2796:	31 c0                	xor    %eax,%eax
    2798:	bf 01 00 00 00       	mov    $0x1,%edi
    279d:	e8 1e fd ff ff       	call   24c0 <__printf_chk@plt>
    27a2:	ba 0b 00 00 00       	mov    $0xb,%edx
    27a7:	48 8d 35 9d 6c 00 00 	lea    0x6c9d(%rip),%rsi        # 944b <_IO_stdin_used+0x44b>
    27ae:	31 c0                	xor    %eax,%eax
    27b0:	bf 01 00 00 00       	mov    $0x1,%edi
    27b5:	e8 06 fd ff ff       	call   24c0 <__printf_chk@plt>
    27ba:	ba 02 00 00 00       	mov    $0x2,%edx
    27bf:	48 8d 35 99 6c 00 00 	lea    0x6c99(%rip),%rsi        # 945f <_IO_stdin_used+0x45f>
    27c6:	31 c0                	xor    %eax,%eax
    27c8:	bf 01 00 00 00       	mov    $0x1,%edi
    27cd:	e8 ee fc ff ff       	call   24c0 <__printf_chk@plt>
    27d2:	ba 01 00 00 00       	mov    $0x1,%edx
    27d7:	48 8d 35 92 6c 00 00 	lea    0x6c92(%rip),%rsi        # 9470 <_IO_stdin_used+0x470>
    27de:	31 c0                	xor    %eax,%eax
    27e0:	bf 01 00 00 00       	mov    $0x1,%edi
    27e5:	e8 d6 fc ff ff       	call   24c0 <__printf_chk@plt>
    27ea:	ba 02 00 00 00       	mov    $0x2,%edx
    27ef:	48 8d 35 92 6c 00 00 	lea    0x6c92(%rip),%rsi        # 9488 <_IO_stdin_used+0x488>
    27f6:	31 c0                	xor    %eax,%eax
    27f8:	bf 01 00 00 00       	mov    $0x1,%edi
    27fd:	e8 be fc ff ff       	call   24c0 <__printf_chk@plt>
    2802:	ba 01 00 00 00       	mov    $0x1,%edx
    2807:	48 8d 35 da 71 00 00 	lea    0x71da(%rip),%rsi        # 99e8 <_IO_stdin_used+0x9e8>
    280e:	31 c0                	xor    %eax,%eax
    2810:	bf 01 00 00 00       	mov    $0x1,%edi
    2815:	e8 a6 fc ff ff       	call   24c0 <__printf_chk@plt>
    281a:	ba 01 00 00 00       	mov    $0x1,%edx
    281f:	48 8d 35 f2 71 00 00 	lea    0x71f2(%rip),%rsi        # 9a18 <_IO_stdin_used+0xa18>
    2826:	31 c0                	xor    %eax,%eax
    2828:	bf 01 00 00 00       	mov    $0x1,%edi
    282d:	e8 8e fc ff ff       	call   24c0 <__printf_chk@plt>
    2832:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2837:	48 8d 35 66 6c 00 00 	lea    0x6c66(%rip),%rsi        # 94a4 <_IO_stdin_used+0x4a4>
    283e:	31 c0                	xor    %eax,%eax
    2840:	bf 01 00 00 00       	mov    $0x1,%edi
    2845:	e8 76 fc ff ff       	call   24c0 <__printf_chk@plt>
    284a:	ba 19 00 00 00       	mov    $0x19,%edx
    284f:	48 8d 35 68 6c 00 00 	lea    0x6c68(%rip),%rsi        # 94be <_IO_stdin_used+0x4be>
    2856:	31 c0                	xor    %eax,%eax
    2858:	bf 01 00 00 00       	mov    $0x1,%edi
    285d:	e8 5e fc ff ff       	call   24c0 <__printf_chk@plt>
    2862:	48 8d 3d 8c 68 00 00 	lea    0x688c(%rip),%rdi        # 90f5 <_IO_stdin_used+0xf5>
    2869:	e8 d2 fa ff ff       	call   2340 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
    286e:	be 18 00 00 00       	mov    $0x18,%esi
    2873:	bf 01 00 00 00       	mov    $0x1,%edi
    2878:	e8 93 fb ff ff       	call   2410 <calloc@plt>
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    287d:	be 18 00 00 00       	mov    $0x18,%esi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
    2882:	45 31 ff             	xor    %r15d,%r15d
  int cc = 0; 
    2885:	45 31 f6             	xor    %r14d,%r14d
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2888:	bf 03 00 00 00       	mov    $0x3,%edi
  struct ProtectedState *global_protected_state = calloc(1, sizeof(struct ProtectedState));
    288d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2892:	e8 79 fb ff ff       	call   2410 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2897:	be 20 01 00 00       	mov    $0x120,%esi
    289c:	bf 0b 00 00 00       	mov    $0xb,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    28a1:	48 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28a9:	e8 62 fb ff ff       	call   2410 <calloc@plt>
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28ae:	be 28 00 00 00       	mov    $0x28,%esi
    28b3:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    28b8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28bd:	e8 4e fb ff ff       	call   2410 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28c2:	be 28 00 00 00       	mov    $0x28,%esi
    28c7:	bf 79 00 00 00       	mov    $0x79,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28cc:	48 89 84 24 e8 00 00 00 	mov    %rax,0xe8(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28d4:	e8 37 fb ff ff       	call   2410 <calloc@plt>
    28d9:	48 89 84 24 f0 00 00 00 	mov    %rax,0xf0(%rsp)
  for (int x = 0 ; x < total_threads; x++) {
    28e1:	48 89 c3             	mov    %rax,%rbx
int main() {
    28e4:	49 89 dd             	mov    %rbx,%r13
    for (int y = 0 ; y < total_threads; y++) {
    28e7:	31 ed                	xor    %ebp,%ebp
    28e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    28f0:	42 8d 54 35 00       	lea    0x0(%rbp,%r14,1),%edx
    28f5:	41 89 e8             	mov    %ebp,%r8d
    28f8:	44 89 f9             	mov    %r15d,%ecx
    28fb:	4c 89 e6             	mov    %r12,%rsi
    28fe:	bf 01 00 00 00       	mov    $0x1,%edi
    2903:	31 c0                	xor    %eax,%eax
    2905:	83 c5 01             	add    $0x1,%ebp
    2908:	e8 b3 fb ff ff       	call   24c0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    290d:	4c 89 ef             	mov    %r13,%rdi
    2910:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    2912:	49 83 c5 28          	add    $0x28,%r13
      pthread_mutex_init(&swapmutex[cc++], NULL);
    2916:	e8 75 fc ff ff       	call   2590 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    291b:	83 fd 0b             	cmp    $0xb,%ebp
    291e:	75 d0                	jne    28f0 <main+0x230>
    2920:	41 83 c6 0b          	add    $0xb,%r14d
  for (int x = 0 ; x < total_threads; x++) {
    2924:	41 83 c7 01          	add    $0x1,%r15d
    2928:	48 81 c3 b8 01 00 00 	add    $0x1b8,%rbx
    292f:	41 83 fe 79          	cmp    $0x79,%r14d
    2933:	75 af                	jne    28e4 <main+0x224>
    2935:	ba 06 00 00 00       	mov    $0x6,%edx
    293a:	48 8d 35 a1 6b 00 00 	lea    0x6ba1(%rip),%rsi        # 94e2 <_IO_stdin_used+0x4e2>
    2941:	bf 01 00 00 00       	mov    $0x1,%edi
    2946:	31 c0                	xor    %eax,%eax
    2948:	e8 73 fb ff ff       	call   24c0 <__printf_chk@plt>
    294d:	ba 0c 00 00 00       	mov    $0xc,%edx
    2952:	48 8d 35 9f 6b 00 00 	lea    0x6b9f(%rip),%rsi        # 94f8 <_IO_stdin_used+0x4f8>
    2959:	31 c0                	xor    %eax,%eax
    295b:	bf 01 00 00 00       	mov    $0x1,%edi
    2960:	e8 5b fb ff ff       	call   24c0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2965:	be 10 00 00 00       	mov    $0x10,%esi
    296a:	bf 0c 00 00 00       	mov    $0xc,%edi
    296f:	e8 9c fa ff ff       	call   2410 <calloc@plt>
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2974:	be 10 00 00 00       	mov    $0x10,%esi
    2979:	bf 02 00 00 00       	mov    $0x2,%edi
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    297e:	48 89 c5             	mov    %rax,%rbp
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2981:	e8 8a fa ff ff       	call   2410 <calloc@plt>


  int snapshot_limit = 100;
  for (int x = 0 ; x < io_threads; x++) {
    iobuffers[x].count = buffer_size;
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2986:	be 00 01 00 00       	mov    $0x100,%esi
    298b:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int y = 0 ; y < buffer_size; y++) {
      iobuffers[x].buffer[y].available = 0;
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2990:	49 89 ee             	mov    %rbp,%r14
    iobuffers[x].count = buffer_size;
    2993:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2999:	49 89 c4             	mov    %rax,%r12
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    299c:	e8 6f fa ff ff       	call   2410 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29a1:	be 20 00 00 00       	mov    $0x20,%esi
    29a6:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29ab:	49 89 44 24 08       	mov    %rax,0x8(%r12)
    29b0:	49 89 c5             	mov    %rax,%r13
      iobuffers[x].buffer[y].available = 0;
    29b3:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    29bd:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29c7:	e8 44 fa ff ff       	call   2410 <calloc@plt>
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29cc:	be 00 01 00 00       	mov    $0x100,%esi
    29d1:	bf 01 00 00 00       	mov    $0x1,%edi
    iobuffers[x].count = buffer_size;
    29d6:	41 c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%r12)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29df:	49 89 85 88 00 00 00 	mov    %rax,0x88(%r13)
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29e6:	e8 25 fa ff ff       	call   2410 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29eb:	be 20 00 00 00       	mov    $0x20,%esi
    29f0:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29f5:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    29fa:	49 89 c5             	mov    %rax,%r13
    29fd:	4c 8d a5 c0 00 00 00 	lea    0xc0(%rbp),%r12
      iobuffers[x].buffer[y].available = 0;
    2a04:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2a0e:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a18:	e8 f3 f9 ff ff       	call   2410 <calloc@plt>
    2a1d:	48 89 ac 24 d8 00 00 00 	mov    %rbp,0xd8(%rsp)
    2a25:	49 89 85 88 00 00 00 	mov    %rax,0x88(%r13)
    }
  }
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    2a2c:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a33:	be 00 01 00 00       	mov    $0x100,%esi
    2a38:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2a3d:	49 83 c6 10          	add    $0x10,%r14
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a41:	e8 ca f9 ff ff       	call   2410 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a46:	be 20 00 00 00       	mov    $0x20,%esi
    2a4b:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a50:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    2a54:	48 89 c3             	mov    %rax,%rbx
      buffers[x].buffer[y].available = 0;
    2a57:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2a61:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a6b:	e8 a0 f9 ff ff       	call   2410 <calloc@plt>
    2a70:	48 89 83 88 00 00 00 	mov    %rax,0x88(%rbx)
  for (int x = 0 ; x < buffers_required; x++) {
    2a77:	4d 39 f4             	cmp    %r14,%r12
    2a7a:	75 b0                	jne    2a2c <main+0x36c>
  int iocur_buffer = 0;
  int swap = 0;
  int groupcount = 0;
  int seq = 0;
  int seqs[] = {1, 3, 6};
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a7c:	be 08 00 00 00       	mov    $0x8,%esi
    2a81:	bf 64 00 00 00       	mov    $0x64,%edi
  struct Global *global = calloc(1, sizeof(struct Global));
  global->request_group_sync = -1;
  global->protected_state = global_protected_state;
    2a86:	45 31 ff             	xor    %r15d,%r15d
  int dataid = 0;
    2a89:	31 db                	xor    %ebx,%ebx
  int seqs[] = {1, 3, 6};
    2a8b:	48 8b 05 6e 75 00 00 	mov    0x756e(%rip),%rax        # a000 <_IO_stdin_used+0x1000>
              }
              printf("Creating friend mailbox %d other is %d\n", b, mailboxes[b].other);
              data[0].messages = messages;
              data[1].messages = messages2;
              data[0].messages_limit = messages_limit;
              data[0].messages_count = 0;
    2a92:	4d 89 fd             	mov    %r15,%r13
  int seqs[] = {1, 3, 6};
    2a95:	c7 84 24 20 01 00 00 06 00 00 00 	movl   $0x6,0x120(%rsp)
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2aa0:	4c 8d b4 24 18 01 00 00 	lea    0x118(%rsp),%r14
              data[0].messages_count = 0;
    2aa8:	41 89 df             	mov    %ebx,%r15d
  int seqs[] = {1, 3, 6};
    2aab:	48 89 84 24 18 01 00 00 	mov    %rax,0x118(%rsp)
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2ab3:	e8 58 f9 ff ff       	call   2410 <calloc@plt>
  struct Global *global = calloc(1, sizeof(struct Global));
    2ab8:	be 10 00 00 00       	mov    $0x10,%esi
    2abd:	bf 01 00 00 00       	mov    $0x1,%edi
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2ac2:	48 89 84 24 d0 00 00 00 	mov    %rax,0xd0(%rsp)
  struct Global *global = calloc(1, sizeof(struct Global));
    2aca:	e8 41 f9 ff ff       	call   2410 <calloc@plt>
  int swap = 0;
    2acf:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
  struct Global *global = calloc(1, sizeof(struct Global));
    2ad7:	49 89 c3             	mov    %rax,%r11
  global->request_group_sync = -1;
    2ada:	c7 00 ff ff ff ff    	movl   $0xffffffff,(%rax)
  global->protected_state = global_protected_state;
    2ae0:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  int iocur_buffer = 0;
    2ae5:	c7 84 24 84 00 00 00 00 00 00 00 	movl   $0x0,0x84(%rsp)
  global->protected_state = global_protected_state;
    2af0:	49 89 43 08          	mov    %rax,0x8(%r11)
  for (int k = 0 ; k < group_count ; k++) {
    2af4:	48 8b 84 24 b8 00 00 00 	mov    0xb8(%rsp),%rax
  int cur_buffer = 0;
    2afc:	c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rsp)
    2b07:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
  global->protected_state = global_protected_state;
    2b0f:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  int curcpu = 0;
    2b17:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
              data[0].messages_count = 0;
    2b1f:	4c 89 9c 24 e0 00 00 00 	mov    %r11,0xe0(%rsp)
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2b27:	be 00 01 00 00       	mov    $0x100,%esi
    2b2c:	bf 01 00 00 00       	mov    $0x1,%edi
    2b31:	44 89 6c 24 50       	mov    %r13d,0x50(%rsp)
    2b36:	e8 d5 f8 ff ff       	call   2410 <calloc@plt>
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2b3b:	be 08 00 00 00       	mov    $0x8,%esi
    2b40:	bf 64 00 00 00       	mov    $0x64,%edi
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2b45:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2b4a:	e8 c1 f8 ff ff       	call   2410 <calloc@plt>
    all_groups[groupcount++] = group_data;
    2b4f:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2b54:	48 8b 9c 24 d0 00 00 00 	mov    0xd0(%rsp),%rbx
        thread_data[x].protected_state = &protected_state[k];
    2b5c:	48 c7 44 24 68 00 00 00 00 	movq   $0x0,0x68(%rsp)
    2b65:	48 89 ac 24 f8 00 00 00 	mov    %rbp,0xf8(%rsp)
    group_data->threads = group_threads;
    2b6d:	48 89 82 88 00 00 00 	mov    %rax,0x88(%rdx)
    group_data->global = global;
    2b74:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
    all_groups[groupcount++] = group_data;
    2b7c:	4a 89 14 eb          	mov    %rdx,(%rbx,%r13,8)
    group_data->thread_count = threads_per_group * group_count;
    2b80:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    group_data->global = global;
    2b85:	48 89 82 98 00 00 00 	mov    %rax,0x98(%rdx)
    group_data->seq = seqs[seq++ % 3];
    2b8c:	43 8b 04 ae          	mov    (%r14,%r13,4),%eax
    group_data->thread_count = threads_per_group * group_count;
    2b90:	c7 82 90 00 00 00 06 00 00 00 	movl   $0x6,0x90(%rdx)
    group_data->seq = seqs[seq++ % 3];
    2b9a:	89 82 a0 00 00 00    	mov    %eax,0xa0(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2ba0:	4b 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%rax
    2ba5:	48 c1 e0 06          	shl    $0x6,%rax
    2ba9:	48 89 94 24 00 01 00 00 	mov    %rdx,0x100(%rsp)
    2bb1:	4c 8d 0c 18          	lea    (%rax,%rbx,1),%r9
    2bb5:	48 63 84 24 84 00 00 00 	movslq 0x84(%rsp),%rax
    2bbd:	48 89 9c 24 a0 00 00 00 	mov    %rbx,0xa0(%rsp)
    2bc5:	43 8d 5c 2d 00       	lea    0x0(%r13,%r13,1),%ebx
    2bca:	4c 89 b4 24 08 01 00 00 	mov    %r14,0x108(%rsp)
    2bd2:	41 89 de             	mov    %ebx,%r14d
    2bd5:	48 c1 e0 04          	shl    $0x4,%rax
    2bd9:	48 01 e8             	add    %rbp,%rax
    2bdc:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2be1:	48 63 84 24 80 00 00 00 	movslq 0x80(%rsp),%rax
    2be9:	48 c1 e0 04          	shl    $0x4,%rax
    2bed:	48 01 e8             	add    %rbp,%rax
    2bf0:	48 89 84 24 b0 00 00 00 	mov    %rax,0xb0(%rsp)
      thread_data[x].all_groups = all_groups;
    2bf8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
      thread_data[x].group = k;
    2c00:	8b 54 24 50          	mov    0x50(%rsp),%edx
    2c04:	44 89 f1             	mov    %r14d,%ecx
    2c07:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].group_data = group_data;
    2c0c:	48 8b 9c 24 00 01 00 00 	mov    0x100(%rsp),%rbx
    2c14:	48 8d 35 25 6e 00 00 	lea    0x6e25(%rip),%rsi        # 9a40 <_IO_stdin_used+0xa40>
      thread_data[x].global = global;
    2c1b:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].all_groups = all_groups;
    2c20:	49 89 81 e8 00 00 00 	mov    %rax,0xe8(%r9)
      thread_data[x].global = global;
    2c27:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
      thread_data[x].group_data = group_data;
    2c2f:	49 89 99 e0 00 00 00 	mov    %rbx,0xe0(%r9)
      thread_data[x].group = k;
    2c36:	41 89 91 f0 00 00 00 	mov    %edx,0xf0(%r9)
      thread_data[x].global = global;
    2c3d:	49 89 81 f8 00 00 00 	mov    %rax,0xf8(%r9)
    2c44:	31 c0                	xor    %eax,%eax
    2c46:	e8 75 f8 ff ff       	call   24c0 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c4b:	be 08 00 00 00       	mov    $0x8,%esi
    2c50:	bf 02 00 00 00       	mov    $0x2,%edi
    2c55:	e8 b6 f7 ff ff       	call   2410 <calloc@plt>
      group_data->threads[group_thread_count++] = &thread_data[x];  
    2c5a:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2c5f:	be 80 00 00 00       	mov    $0x80,%esi
    2c64:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c69:	48 89 c5             	mov    %rax,%rbp
      group_data->threads[group_thread_count++] = &thread_data[x];  
    2c6c:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    2c73:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    2c78:	4c 89 0c 18          	mov    %r9,(%rax,%rbx,1)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2c7c:	e8 8f f7 ff ff       	call   2410 <calloc@plt>
      if (x % 2 == 1) {
    2c81:	45 89 f0             	mov    %r14d,%r8d
    2c84:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2c89:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2c8d:	48 89 c3             	mov    %rax,%rbx
      if (x % 2 == 1) {
    2c90:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2c95:	0f 84 cb 0a 00 00    	je     3766 <main+0x10a6>
        other = abs(x - 1) % total_threads;
    2c9b:	41 8d 46 ff          	lea    -0x1(%r14),%eax
    2c9f:	41 8d 7e 01          	lea    0x1(%r14),%edi
        my_thread_data[0] = &thread_data[other]; 
    2ca3:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
        other = abs(x - 1) % total_threads;
    2ca7:	48 89 c1             	mov    %rax,%rcx
        my_thread_data[0] = &thread_data[other]; 
    2caa:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2caf:	89 bc 24 88 00 00 00 	mov    %edi,0x88(%rsp)
    2cb6:	48 c1 e2 05          	shl    $0x5,%rdx
    2cba:	48 01 c2             	add    %rax,%rdx
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2cbd:	48 8d 45 08          	lea    0x8(%rbp),%rax
    2cc1:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2cc6:	4c 89 c8             	mov    %r9,%rax
        my_thread_data[1] = &thread_data[x]; 
    2cc9:	48 89 45 08          	mov    %rax,0x8(%rbp)
        thread_data[x].protected_state = &protected_state[k];
    2ccd:	48 8b 84 24 98 00 00 00 	mov    0x98(%rsp),%rax
    2cd5:	48 8d 35 94 6d 00 00 	lea    0x6d94(%rip),%rsi        # 9a70 <_IO_stdin_used+0xa70>
    2cdc:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].thread_index = 1;
    2ce1:	45 89 41 04          	mov    %r8d,0x4(%r9)
        thread_data[x].protected_state = &protected_state[k];
    2ce5:	49 89 41 48          	mov    %rax,0x48(%r9)
    2ce9:	31 c0                	xor    %eax,%eax
        my_thread_data[0] = &thread_data[other]; 
    2ceb:	48 89 55 00          	mov    %rdx,0x0(%rbp)
    2cef:	44 89 f2             	mov    %r14d,%edx
        thread_data[x].protected_state = &protected_state[k];
    2cf2:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2cf7:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2cfb:	e8 c0 f7 ff ff       	call   24c0 <__printf_chk@plt>
      thread_data[x].other = other;
    2d00:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2d04:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2d09:	31 c0                	xor    %eax,%eax
    2d0b:	44 89 f2             	mov    %r14d,%edx
    2d0e:	48 8d 35 8b 6d 00 00 	lea    0x6d8b(%rip),%rsi        # 9aa0 <_IO_stdin_used+0xaa0>
    2d15:	bf 01 00 00 00       	mov    $0x1,%edi
    2d1a:	41 89 89 c0 00 00 00 	mov    %ecx,0xc0(%r9)
    2d21:	8b 4c 24 7c          	mov    0x7c(%rsp),%ecx
    2d25:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2d2a:	e8 91 f7 ff ff       	call   24c0 <__printf_chk@plt>
        if (x < thread_count) {
    2d2f:	41 83 fe 01          	cmp    $0x1,%r14d
    2d33:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2d38:	0f 8f b5 11 00 00    	jg     3ef3 <main+0x1833>
          CPU_SET(curcpu, sendercpu);
    2d3e:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2d43:	48 89 c7             	mov    %rax,%rdi
    2d46:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2d4c:	77 12                	ja     2d60 <main+0x6a0>
    2d4e:	48 c1 e8 06          	shr    $0x6,%rax
    2d52:	ba 01 00 00 00       	mov    $0x1,%edx
    2d57:	89 f9                	mov    %edi,%ecx
    2d59:	48 d3 e2             	shl    %cl,%rdx
    2d5c:	48 09 14 c3          	or     %rdx,(%rbx,%rax,8)
          curcpu += 2;
    2d60:	83 44 24 7c 02       	addl   $0x2,0x7c(%rsp)
      thread_data[x].real_thread_index = x;
    2d65:	45 89 71 08          	mov    %r14d,0x8(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2d69:	be 10 00 00 00       	mov    $0x10,%esi
    2d6e:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].swapmutex = swapmutex;
    2d73:	48 8b 84 24 f0 00 00 00 	mov    0xf0(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    2d7b:	49 89 99 b8 00 00 00 	mov    %rbx,0xb8(%r9)
      thread_data[x].swapmutex = swapmutex;
    2d82:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2d89:	48 8b 84 24 e8 00 00 00 	mov    0xe8(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2d91:	49 89 69 18          	mov    %rbp,0x18(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2d95:	31 ed                	xor    %ebp,%ebp
      thread_data[x].mswapmutex = mswapmutex;
    2d97:	49 89 81 d8 00 00 00 	mov    %rax,0xd8(%r9)
      thread_data[x].all_threads = thread_data;
    2d9e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].kind = KERNEL_THREAD;
    2da3:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].all_threads = thread_data;
    2daa:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2dae:	48 8b 05 53 72 00 00 	mov    0x7253(%rip),%rax        # a008 <_IO_stdin_used+0x1008>
      thread_data[x].task_count = total_barrier_count;
    2db5:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].group_count = group_count;
    2dbd:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].thread_count = 2;
    2dc4:	48 8b 05 45 72 00 00 	mov    0x7245(%rip),%rax        # a010 <_IO_stdin_used+0x1010>
      thread_data[x].task_count = total_barrier_count;
    2dcb:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].thread_count = 2;
    2dd0:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2dd4:	e8 37 f6 ff ff       	call   2410 <calloc@plt>
    2dd9:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2dde:	be 10 00 00 00       	mov    $0x10,%esi
    2de3:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2de8:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2dec:	e8 1f f6 ff ff       	call   2410 <calloc@plt>
    2df1:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2df6:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2dfb:	66 0f 6f 3d cd 71 00 00 	movdqa 0x71cd(%rip),%xmm7        # 9fd0 <_IO_stdin_used+0xfd0>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2e03:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2e08:	49 89 41 78          	mov    %rax,0x78(%r9)
      thread_data[x].timestamp_count = 0;
    2e0c:	41 0f 11 b9 88 00 00 00 	movups %xmm7,0x88(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2e14:	e8 f7 f5 ff ff       	call   2410 <calloc@plt>
    2e19:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e1e:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2e23:	66 0f 6f 35 a5 71 00 00 	movdqa 0x71a5(%rip),%xmm6        # 9fd0 <_IO_stdin_used+0xfd0>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e2b:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2e30:	49 89 81 98 00 00 00 	mov    %rax,0x98(%r9)
      thread_data[x].task_timestamp_count = 0;
    2e37:	41 0f 11 b1 a0 00 00 00 	movups %xmm6,0xa0(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e3f:	e8 cc f5 ff ff       	call   2410 <calloc@plt>
        thread_data[x].tasks = barriers;
    2e44:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
            data[0].messages_count = 0;
    2e49:	44 89 74 24 18       	mov    %r14d,0x18(%rsp)
    2e4e:	45 89 fe             	mov    %r15d,%r14d
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2e51:	48 63 bc 24 88 00 00 00 	movslq 0x88(%rsp),%rdi
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e59:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2e5c:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2e60:	48 89 fb             	mov    %rdi,%rbx
    2e63:	48 69 ff ab aa aa 2a 	imul   $0x2aaaaaab,%rdi,%rdi
            data[0].messages_count = 0;
    2e6a:	4c 89 4c 24 48       	mov    %r9,0x48(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2e6f:	89 d8                	mov    %ebx,%eax
    2e71:	c1 f8 1f             	sar    $0x1f,%eax
    2e74:	48 c1 ef 20          	shr    $0x20,%rdi
    2e78:	29 c7                	sub    %eax,%edi
    2e7a:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2e7d:	01 c0                	add    %eax,%eax
    2e7f:	29 c3                	sub    %eax,%ebx
            data[0].messages_count = 0;
    2e81:	89 9c 24 8c 00 00 00 	mov    %ebx,0x8c(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2e88:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2e8b:	be 00 01 00 00       	mov    $0x100,%esi
    2e90:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e95:	45 31 ff             	xor    %r15d,%r15d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2e98:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2e9d:	48 c1 e0 09          	shl    $0x9,%rax
    2ea1:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
    2ea5:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2eaa:	48 8d 05 5f 1a 00 00 	lea    0x1a5f(%rip),%rax        # 4910 <do_protected_write>
    2eb1:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2eb8:	e8 53 f5 ff ff       	call   2410 <calloc@plt>
    2ebd:	8b 74 24 58          	mov    0x58(%rsp),%esi
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2ec1:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ec8:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ecb:	49 89 c4             	mov    %rax,%r12
    2ece:	85 f6                	test   %esi,%esi
    2ed0:	0f 84 86 01 00 00    	je     305c <main+0x99c>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2ed6:	8b 44 24 18          	mov    0x18(%rsp),%eax
    2eda:	48 89 8c 24 90 00 00 00 	mov    %rcx,0x90(%rsp)
    2ee2:	48 89 cb             	mov    %rcx,%rbx
    2ee5:	45 89 fc             	mov    %r15d,%r12d
    2ee8:	83 e8 01             	sub    $0x1,%eax
    2eeb:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2eef:	eb 1c                	jmp    2f0d <main+0x84d>
    2ef1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ef8:	41 83 c4 01          	add    $0x1,%r12d
    2efc:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    2f03:	41 83 fc 06          	cmp    $0x6,%r12d
    2f07:	0f 84 d7 02 00 00    	je     31e4 <main+0xb24>
            int group_of = b / threads_per_group;
    2f0d:	45 89 e7             	mov    %r12d,%r15d
    2f10:	31 c0                	xor    %eax,%eax
    2f12:	44 89 e2             	mov    %r12d,%edx
    2f15:	bf 01 00 00 00       	mov    $0x1,%edi
    2f1a:	41 d1 ff             	sar    %r15d
    2f1d:	48 8d 35 ee 65 00 00 	lea    0x65ee(%rip),%rsi        # 9512 <_IO_stdin_used+0x512>
    2f24:	44 89 f9             	mov    %r15d,%ecx
    2f27:	e8 94 f5 ff ff       	call   24c0 <__printf_chk@plt>
            if (k == group_of) {
    2f2c:	45 39 ef             	cmp    %r13d,%r15d
    2f2f:	75 c7                	jne    2ef8 <main+0x838>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f31:	be 08 00 00 00       	mov    $0x8,%esi
    2f36:	bf 01 00 00 00       	mov    $0x1,%edi
    2f3b:	e8 d0 f4 ff ff       	call   2410 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f40:	be 08 00 00 00       	mov    $0x8,%esi
    2f45:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2f4a:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f4f:	e8 bc f4 ff ff       	call   2410 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2f54:	be 80 04 00 00       	mov    $0x480,%esi
    2f59:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2f5e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2f63:	e8 a8 f4 ff ff       	call   2410 <calloc@plt>
              data[0].a = x;
    2f68:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    2f6c:	44 89 e2             	mov    %r12d,%edx
              mailboxes[b].pending_lower = NULL;
    2f6f:	48 c7 83 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%rbx)
              struct Data *data = calloc(3, sizeof(struct Data));
    2f7a:	49 89 c7             	mov    %rax,%r15
              data[0].b = y;
    2f7d:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    2f83:	48 8d 35 36 6b 00 00 	lea    0x6b36(%rip),%rsi        # 9ac0 <_IO_stdin_used+0xac0>
              data[0].a = x;
    2f8a:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
              data[0].kind = MAILBOX_LOWER;
    2f90:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
              data[0].c = b;
    2f9a:	44 89 a0 14 04 00 00 	mov    %r12d,0x414(%rax)
              data[0].id = dataid++;
    2fa1:	41 8d 46 01          	lea    0x1(%r14),%eax
              data[1].id = dataid++;
    2fa5:	41 89 87 98 08 00 00 	mov    %eax,0x898(%r15)
              mailboxes[b].higher = &data[1];
    2fac:	49 8d 87 80 04 00 00 	lea    0x480(%r15),%rax
    2fb3:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
    2fba:	8b 44 24 70          	mov    0x70(%rsp),%eax
              data[0].id = dataid++;
    2fbe:	45 89 b7 18 04 00 00 	mov    %r14d,0x418(%r15)
              data[1].id = dataid++;
    2fc5:	41 83 c6 02          	add    $0x2,%r14d
              data[1].a = x;
    2fc9:	41 89 bf 8c 08 00 00 	mov    %edi,0x88c(%r15)
    2fd0:	89 c1                	mov    %eax,%ecx
    2fd2:	bf 01 00 00 00       	mov    $0x1,%edi
    2fd7:	89 83 b4 00 00 00    	mov    %eax,0xb4(%rbx)
    2fdd:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    2fdf:	41 c7 87 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r15)
              data[1].b = y;
    2fea:	41 89 af 90 08 00 00 	mov    %ebp,0x890(%r15)
              data[1].c = b;
    2ff1:	45 89 a7 94 08 00 00 	mov    %r12d,0x894(%r15)
              mailboxes[b].lower = &data[0];
    2ff8:	4c 89 3b             	mov    %r15,(%rbx)
              mailboxes[b].pending_higher = NULL;
    2ffb:	48 c7 83 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%rbx)
              data[0].finished_reading = 1;
    3006:	41 c7 87 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r15)
              data[1].finished_reading = 1;
    3011:	41 c7 87 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r15)
              mailboxes[b].kind = MAILBOX_FRIEND;
    301c:	c7 83 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%rbx)
    3026:	e8 95 f4 ff ff       	call   24c0 <__printf_chk@plt>
              data[0].messages = messages;
    302b:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
              data[1].messages = messages2;
    3030:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
              data[0].messages_count = 0;
    3035:	66 0f 6f 35 a3 6f 00 00 	movdqa 0x6fa3(%rip),%xmm6        # 9fe0 <_IO_stdin_used+0xfe0>
              data[0].messages = messages;
    303d:	4d 89 1f             	mov    %r11,(%r15)
              data[1].messages = messages2;
    3040:	4d 89 97 80 04 00 00 	mov    %r10,0x480(%r15)
              data[0].messages_count = 0;
    3047:	41 0f 29 b7 80 00 00 00 	movaps %xmm6,0x80(%r15)
              data[1].messages_count = 0;
    304f:	41 0f 29 b7 00 05 00 00 	movaps %xmm6,0x500(%r15)
    3057:	e9 9c fe ff ff       	jmp    2ef8 <main+0x838>
    305c:	48 89 44 24 70       	mov    %rax,0x70(%rsp)
    3061:	44 89 fb             	mov    %r15d,%ebx
    3064:	eb 1d                	jmp    3083 <main+0x9c3>
    3066:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3070:	83 c3 01             	add    $0x1,%ebx
    3073:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    307a:	83 fb 06             	cmp    $0x6,%ebx
    307d:	0f 84 5a 01 00 00    	je     31dd <main+0xb1d>
            int group_of = b / threads_per_group;
    3083:	41 89 df             	mov    %ebx,%r15d
    3086:	31 c0                	xor    %eax,%eax
    3088:	89 da                	mov    %ebx,%edx
    308a:	bf 01 00 00 00       	mov    $0x1,%edi
    308f:	41 d1 ff             	sar    %r15d
    3092:	48 8d 35 79 64 00 00 	lea    0x6479(%rip),%rsi        # 9512 <_IO_stdin_used+0x512>
    3099:	44 89 f9             	mov    %r15d,%ecx
    309c:	e8 1f f4 ff ff       	call   24c0 <__printf_chk@plt>
            if (k == group_of) {
    30a1:	45 39 ef             	cmp    %r13d,%r15d
    30a4:	75 ca                	jne    3070 <main+0x9b0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    30a6:	be 08 00 00 00       	mov    $0x8,%esi
    30ab:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    30b0:	49 81 c4 00 01 00 00 	add    $0x100,%r12
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    30b7:	e8 54 f3 ff ff       	call   2410 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30bc:	be 08 00 00 00       	mov    $0x8,%esi
    30c1:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    30c6:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30cb:	e8 40 f3 ff ff       	call   2410 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    30d0:	be 80 04 00 00       	mov    $0x480,%esi
    30d5:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30da:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    30df:	e8 2c f3 ff ff       	call   2410 <calloc@plt>
              data[0].a = x;
    30e4:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    30e8:	89 da                	mov    %ebx,%edx
              mailboxes[b].pending_lower = NULL;
    30ea:	49 c7 44 24 88 00 00 00 00 	movq   $0x0,-0x78(%r12)
              struct Data *data = calloc(3, sizeof(struct Data));
    30f3:	49 89 c7             	mov    %rax,%r15
              data[0].c = b;
    30f6:	89 98 14 04 00 00    	mov    %ebx,0x414(%rax)
    30fc:	48 8d 35 bd 69 00 00 	lea    0x69bd(%rip),%rsi        # 9ac0 <_IO_stdin_used+0xac0>
              data[0].a = x;
    3103:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
              data[0].kind = MAILBOX_LOWER;
    3109:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
              data[0].b = y;
    3113:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
              data[0].id = dataid++;
    3119:	41 8d 46 01          	lea    0x1(%r14),%eax
              data[1].id = dataid++;
    311d:	41 89 87 98 08 00 00 	mov    %eax,0x898(%r15)
              mailboxes[b].higher = &data[1];
    3124:	49 8d 87 80 04 00 00 	lea    0x480(%r15),%rax
    312b:	49 89 44 24 80       	mov    %rax,-0x80(%r12)
    3130:	8b 84 24 8c 00 00 00 	mov    0x8c(%rsp),%eax
              data[0].id = dataid++;
    3137:	45 89 b7 18 04 00 00 	mov    %r14d,0x418(%r15)
              data[1].id = dataid++;
    313e:	41 83 c6 02          	add    $0x2,%r14d
    3142:	41 89 44 24 b4       	mov    %eax,-0x4c(%r12)
    3147:	89 c1                	mov    %eax,%ecx
    3149:	31 c0                	xor    %eax,%eax
              data[1].a = x;
    314b:	41 89 bf 8c 08 00 00 	mov    %edi,0x88c(%r15)
    3152:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].c = b;
    3157:	41 89 9f 94 08 00 00 	mov    %ebx,0x894(%r15)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    315e:	83 c3 01             	add    $0x1,%ebx
              mailboxes[b].lower = &data[0];
    3161:	4d 89 bc 24 00 ff ff ff 	mov    %r15,-0x100(%r12)
              mailboxes[b].pending_higher = NULL;
    3169:	49 c7 44 24 90 00 00 00 00 	movq   $0x0,-0x70(%r12)
              mailboxes[b].kind = MAILBOX_FRIEND;
    3172:	41 c7 44 24 b0 01 00 00 00 	movl   $0x1,-0x50(%r12)
              data[1].kind = MAILBOX_HIGHER;
    317b:	41 c7 87 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r15)
              data[1].b = y;
    3186:	41 89 af 90 08 00 00 	mov    %ebp,0x890(%r15)
              data[0].finished_reading = 1;
    318d:	41 c7 87 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r15)
              data[1].finished_reading = 1;
    3198:	41 c7 87 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r15)
    31a3:	e8 18 f3 ff ff       	call   24c0 <__printf_chk@plt>
              data[0].messages = messages;
    31a8:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
              data[1].messages = messages2;
    31ad:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
              data[0].messages_count = 0;
    31b2:	66 0f 6f 35 26 6e 00 00 	movdqa 0x6e26(%rip),%xmm6        # 9fe0 <_IO_stdin_used+0xfe0>
              data[0].messages = messages;
    31ba:	4d 89 1f             	mov    %r11,(%r15)
              data[1].messages = messages2;
    31bd:	4d 89 97 80 04 00 00 	mov    %r10,0x480(%r15)
              data[0].messages_count = 0;
    31c4:	41 0f 29 b7 80 00 00 00 	movaps %xmm6,0x80(%r15)
              data[1].messages_count = 0;
    31cc:	41 0f 29 b7 00 05 00 00 	movaps %xmm6,0x500(%r15)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    31d4:	83 fb 06             	cmp    $0x6,%ebx
    31d7:	0f 85 a6 fe ff ff    	jne    3083 <main+0x9c3>
    31dd:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    31e2:	eb 08                	jmp    31ec <main+0xb2c>
    31e4:	48 8b 8c 24 90 00 00 00 	mov    0x90(%rsp),%rcx
    31ec:	49 89 cf             	mov    %rcx,%r15
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    31ef:	31 db                	xor    %ebx,%ebx
    31f1:	89 e9                	mov    %ebp,%ecx
    31f3:	4c 89 ed             	mov    %r13,%rbp
    31f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            int group_of = b / threads_per_group;
    3200:	89 d8                	mov    %ebx,%eax
    3202:	d1 f8                	sar    %eax
            if (k == group_of) {
    3204:	39 e8                	cmp    %ebp,%eax
    3206:	0f 84 8a 01 00 00    	je     3396 <main+0xcd6>
    320c:	89 da                	mov    %ebx,%edx
    320e:	48 8d 35 0d 63 00 00 	lea    0x630d(%rip),%rsi        # 9522 <_IO_stdin_used+0x522>
    3215:	bf 01 00 00 00       	mov    $0x1,%edi
    321a:	31 c0                	xor    %eax,%eax
    321c:	89 4c 24 10          	mov    %ecx,0x10(%rsp)
    3220:	e8 9b f2 ff ff       	call   24c0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3225:	be 08 00 00 00       	mov    $0x8,%esi
    322a:	bf 01 00 00 00       	mov    $0x1,%edi
    322f:	e8 dc f1 ff ff       	call   2410 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3234:	be 08 00 00 00       	mov    $0x8,%esi
    3239:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    323e:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3243:	e8 c8 f1 ff ff       	call   2410 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    3248:	be 80 04 00 00       	mov    $0x480,%esi
    324d:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3252:	49 89 c5             	mov    %rax,%r13
            struct Data *data = calloc(3, sizeof(struct Data));
    3255:	e8 b6 f1 ff ff       	call   2410 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    325a:	be 80 04 00 00       	mov    $0x480,%esi
    325f:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    3264:	49 89 c4             	mov    %rax,%r12
            struct Data **stack = calloc(3, sizeof(struct Data));
    3267:	e8 a4 f1 ff ff       	call   2410 <calloc@plt>
            data[0].a = x;
    326c:	8b 7c 24 18          	mov    0x18(%rsp),%edi
            data[0].b = y;
    3270:	8b 4c 24 10          	mov    0x10(%rsp),%ecx
            mailboxes[b].lower = &data[0];
    3274:	4d 89 27             	mov    %r12,(%r15)
            data[0].id = dataid++;
    3277:	41 8d 76 01          	lea    0x1(%r14),%esi
            data[0].messages = messages;
    327b:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
            data[0].messages_count = 0;
    3280:	66 0f 6f 35 58 6d 00 00 	movdqa 0x6d58(%rip),%xmm6        # 9fe0 <_IO_stdin_used+0xfe0>
            data[0].id = dataid++;
    3288:	45 89 b4 24 18 04 00 00 	mov    %r14d,0x418(%r12)
            data[1].id = dataid++;
    3290:	41 89 b4 24 98 08 00 00 	mov    %esi,0x898(%r12)
            mailboxes[b].higher = &data[1];
    3298:	49 8d b4 24 80 04 00 00 	lea    0x480(%r12),%rsi
            data[1].id = dataid++;
    32a0:	41 83 c6 02          	add    $0x2,%r14d
            data[0].kind = MAILBOX_LOWER;
    32a4:	41 c7 84 24 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%r12)
            data[0].a = x;
    32b0:	41 89 bc 24 0c 04 00 00 	mov    %edi,0x40c(%r12)
            data[0].b = y;
    32b8:	41 89 8c 24 10 04 00 00 	mov    %ecx,0x410(%r12)
            data[0].c = b;
    32c0:	41 89 9c 24 14 04 00 00 	mov    %ebx,0x414(%r12)
            data[1].kind = MAILBOX_HIGHER;
    32c8:	41 c7 84 24 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r12)
            data[1].a = x;
    32d4:	41 89 bc 24 8c 08 00 00 	mov    %edi,0x88c(%r12)
            data[1].b = y;
    32dc:	41 89 8c 24 90 08 00 00 	mov    %ecx,0x890(%r12)
            data[1].c = b;
    32e4:	41 89 9c 24 94 08 00 00 	mov    %ebx,0x894(%r12)
            mailboxes[b].my_lower = &data[0];
    32ec:	4d 89 a7 a0 00 00 00 	mov    %r12,0xa0(%r15)
            mailboxes[b].higher = &data[1];
    32f3:	49 89 b7 80 00 00 00 	mov    %rsi,0x80(%r15)
            mailboxes[b].pending_lower = NULL;
    32fa:	49 c7 87 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r15)
            mailboxes[b].pending_higher = NULL;
    3305:	49 c7 87 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r15)
            data[0].finished_reading = 1;
    3310:	41 c7 84 24 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r12)
            data[1].finished_reading = 1;
    331c:	41 c7 84 24 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r12)
            mailboxes[b].my_higher = &data[1];
    3328:	49 89 b7 a8 00 00 00 	mov    %rsi,0xa8(%r15)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    332f:	41 c7 87 b0 00 00 00 02 00 00 00 	movl   $0x2,0xb0(%r15)
            stack[0] = mailboxes[b].lower;
    333a:	4c 89 20             	mov    %r12,(%rax)
            stack[1] = mailboxes[b].higher;
    333d:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    3341:	49 89 87 98 00 00 00 	mov    %rax,0x98(%r15)
            data[0].available_sending = 0;
    3348:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
            data[0].available_receiving = 0;
    3354:	41 c7 84 24 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r12)
            data[0].messages = messages;
    3360:	49 89 14 24          	mov    %rdx,(%r12)
            data[1].messages = messages2;
    3364:	4d 89 ac 24 80 04 00 00 	mov    %r13,0x480(%r12)
            data[1].available_sending = 1;
    336c:	41 c7 84 24 80 05 00 00 01 00 00 00 	movl   $0x1,0x580(%r12)
            data[1].available_receiving = 0;
    3378:	41 c7 84 24 00 06 00 00 00 00 00 00 	movl   $0x0,0x600(%r12)
            data[0].messages_count = 0;
    3384:	41 0f 29 b4 24 80 00 00 00 	movaps %xmm6,0x80(%r12)
            data[1].messages_count = 0;
    338d:	41 0f 29 b4 24 00 05 00 00 	movaps %xmm6,0x500(%r12)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3396:	83 c3 01             	add    $0x1,%ebx
    3399:	49 81 c7 00 01 00 00 	add    $0x100,%r15
    33a0:	83 fb 06             	cmp    $0x6,%ebx
    33a3:	0f 85 57 fe ff ff    	jne    3200 <main+0xb40>
          char *message = malloc(sizeof(char) * 256);
    33a9:	be 01 00 00 00       	mov    $0x1,%esi
    33ae:	bf 00 01 00 00       	mov    $0x100,%edi
    33b3:	49 89 ed             	mov    %rbp,%r13
    33b6:	89 cd                	mov    %ecx,%ebp
    33b8:	e8 53 f0 ff ff       	call   2410 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    33bd:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    33c2:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
    33c5:	e8 b6 f0 ff ff       	call   2480 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    33ca:	48 83 ec 08          	sub    $0x8,%rsp
    33ce:	48 89 df             	mov    %rbx,%rdi
    33d1:	41 89 e9             	mov    %ebp,%r9d
    33d4:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    33d9:	44 8b 7c 24 58       	mov    0x58(%rsp),%r15d
    33de:	ba 00 01 00 00       	mov    $0x100,%edx
    33e3:	31 c0                	xor    %eax,%eax
    33e5:	48 8d 0d fc 66 00 00 	lea    0x66fc(%rip),%rcx        # 9ae8 <_IO_stdin_used+0xae8>
    33ec:	be 01 00 00 00       	mov    $0x1,%esi
    33f1:	41 57                	push   %r15
    33f3:	44 8b 44 24 28       	mov    0x28(%rsp),%r8d
    33f8:	e8 c3 f1 ff ff       	call   25c0 <__sprintf_chk@plt>
          messaged->message = message;
    33fd:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
          messaged->task_index = y;
    3402:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
          messaged->group = k;
    3407:	44 89 ff             	mov    %r15d,%edi
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    340a:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->group = k;
    340f:	45 89 7b 18          	mov    %r15d,0x18(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    3413:	4c 8b 7c 24 58       	mov    0x58(%rsp),%r15
          messaged->task_index = y;
    3418:	49 89 43 10          	mov    %rax,0x10(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    341c:	49 63 47 08          	movslq 0x8(%r15),%rax
          thread_data[x].tasks[y].swap = swap;
    3420:	49 8b 57 38          	mov    0x38(%r15),%rdx
          messaged->message = message;
    3424:	49 89 1b             	mov    %rbx,(%r11)
          thread_data[x].tasks[y].swap = swap;
    3427:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
          messaged->thread_index = thread_data[x].real_thread_index;
    342c:	49 89 43 08          	mov    %rax,0x8(%r11)
          thread_data[x].tasks[y].swap = swap;
    3430:	8b 44 24 30          	mov    0x30(%rsp),%eax
    3434:	48 01 d3             	add    %rdx,%rbx
    3437:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    343c:	89 83 a0 01 00 00    	mov    %eax,0x1a0(%rbx)
          swap += 1;
    3442:	83 c0 01             	add    $0x1,%eax
    3445:	89 44 24 30          	mov    %eax,0x30(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3449:	8d 45 01             	lea    0x1(%rbp),%eax
    344c:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].group = k;
    344f:	89 bb 9c 01 00 00    	mov    %edi,0x19c(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3455:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    345a:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3460:	89 83 98 01 00 00    	mov    %eax,0x198(%rbx)
          thread_data[x].tasks[y].message = messaged;
    3466:	4c 89 9b 90 01 00 00 	mov    %r11,0x190(%rbx)
          thread_data[x].tasks[y].sending = 1;
    346d:	c7 83 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    3477:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3482:	e8 89 ef ff ff       	call   2410 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    3487:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3492:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3499:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    349e:	48 8b 00             	mov    (%rax),%rax
    34a1:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    34a4:	49 39 c7             	cmp    %rax,%r15
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    34a7:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    34ae:	89 8b 30 01 00 00    	mov    %ecx,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    34b4:	5a                   	pop    %rdx
    34b5:	59                   	pop    %rcx
    34b6:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    34bb:	0f 85 50 13 00 00    	jne    4811 <main+0x2151>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    34c1:	66 0f 6f 05 27 6b 00 00 	movdqa 0x6b27(%rip),%xmm0        # 9ff0 <_IO_stdin_used+0xff0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    34c9:	89 6b 04             	mov    %ebp,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
    34cc:	48 8b 05 2d 6b 00 00 	mov    0x6b2d(%rip),%rax        # a000 <_IO_stdin_used+0x1000>
          thread_data[x].tasks[y].arrived = 0;
    34d3:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
    34dd:	c7 83 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rbx)
          thread_data[x].tasks[y].available = 1;
    34e7:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    34ee:	0f 11 83 34 01 00 00 	movups %xmm0,0x134(%rbx)
          if (y == barrier_count - 1) {
    34f5:	83 fd 01             	cmp    $0x1,%ebp
    34f8:	0f 84 42 01 00 00    	je     3640 <main+0xf80>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    34fe:	85 ed                	test   %ebp,%ebp
    3500:	0f 84 22 01 00 00    	je     3628 <main+0xf68>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    3506:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
    350b:	48 8d 05 be 4c 00 00 	lea    0x4cbe(%rip),%rax        # 81d0 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3512:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    3517:	45 89 f7             	mov    %r14d,%r15d
    351a:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3521:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
    3526:	41 c7 81 c4 00 00 00 01 00 00 00 	movl   $0x1,0xc4(%r9)
               thread_data[x].tasks[y].run = barriered_work; 
    3531:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
        thread_data[x].buffers_count = buffers_per_thread;
    3536:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    353b:	e8 d0 ee ff ff       	call   2410 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3540:	4c 8b 74 24 68       	mov    0x68(%rsp),%r14
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3545:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        }
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    354a:	be 08 00 00 00       	mov    $0x8,%esi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    354f:	48 8b 9c 24 b0 00 00 00 	mov    0xb0(%rsp),%rbx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3557:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    355c:	83 84 24 80 00 00 00 01 	addl   $0x1,0x80(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3564:	49 89 41 50          	mov    %rax,0x50(%r9)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3568:	4a 8d 0c 73          	lea    (%rbx,%r14,2),%rcx
    356c:	48 89 08             	mov    %rcx,(%rax)
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    356f:	e8 9c ee ff ff       	call   2410 <calloc@plt>
        for (int b = 0 ; b < io_threads; b++) {	
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    3574:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3579:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    357e:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    3583:	83 84 24 84 00 00 00 02 	addl   $0x2,0x84(%rsp)
    358b:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    358f:	49 89 41 58          	mov    %rax,0x58(%r9)
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3593:	66 0f 6f bc 24 c0 00 00 00 	movdqa 0xc0(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    359c:	49 81 c1 20 01 00 00 	add    $0x120,%r9
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    35a3:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    35a6:	48 83 c3 20          	add    $0x20,%rbx
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    35aa:	48 89 48 08          	mov    %rcx,0x8(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    35ae:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    35b3:	48 89 5c 24 60       	mov    %rbx,0x60(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    35b8:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    35bb:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    35c2:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    35cc:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    35d3:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    35dd:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    35e7:	41 8b 81 e4 fe ff ff 	mov    -0x11c(%r9),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    35ee:	c7 82 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    35f8:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
    35fe:	48 8b 05 fb 69 00 00 	mov    0x69fb(%rip),%rax        # a000 <_IO_stdin_used+0x1000>
    3605:	48 89 82 44 05 00 00 	mov    %rax,0x544(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    360c:	49 83 fe 08          	cmp    $0x8,%r14
    3610:	74 3c                	je     364e <main+0xf8e>
    3612:	48 c7 44 24 68 08 00 00 00 	movq   $0x8,0x68(%rsp)
    361b:	44 8b b4 24 88 00 00 00 	mov    0x88(%rsp),%r14d
    3623:	e9 d0 f5 ff ff       	jmp    2bf8 <main+0x538>
    3628:	48 8d 05 61 51 00 00 	lea    0x5161(%rip),%rax        # 8790 <barriered_work_ingest_andwork>
    362f:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    3634:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    363b:	e9 48 f8 ff ff       	jmp    2e88 <main+0x7c8>
    3640:	48 8d 05 89 4b 00 00 	lea    0x4b89(%rip),%rax        # 81d0 <barriered_work>
    3647:	bd 02 00 00 00       	mov    $0x2,%ebp
    364c:	eb e6                	jmp    3634 <main+0xf74>
  for (int k = 0 ; k < group_count ; k++) {
    364e:	49 83 c5 01          	add    $0x1,%r13
    3652:	48 8b ac 24 f8 00 00 00 	mov    0xf8(%rsp),%rbp
    365a:	48 83 84 24 98 00 00 00 18 	addq   $0x18,0x98(%rsp)
    3663:	4c 8b b4 24 08 01 00 00 	mov    0x108(%rsp),%r14
    366b:	49 83 fd 03          	cmp    $0x3,%r13
    366f:	0f 85 b2 f4 ff ff    	jne    2b27 <main+0x467>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3675:	be 08 00 00 00       	mov    $0x8,%esi
    367a:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    367f:	31 ed                	xor    %ebp,%ebp
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3681:	e8 8a ed ff ff       	call   2410 <calloc@plt>
    3686:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    368b:	49 89 c7             	mov    %rax,%r15
    368e:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3690:	49 89 d1             	mov    %rdx,%r9
    3693:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3695:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3699:	45 85 d2             	test   %r10d,%r10d
    369c:	0f 8e af 00 00 00    	jle    3751 <main+0x1091>
    36a2:	49 8b 79 38          	mov    0x38(%r9),%rdi
    36a6:	4d 63 c2             	movslq %r10d,%r8
    36a9:	48 63 cd             	movslq %ebp,%rcx
    36ac:	49 c1 e0 09          	shl    $0x9,%r8
    36b0:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    36b4:	49 01 f8             	add    %rdi,%r8
    36b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    36c0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    36c7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    36ce:	48 83 c6 60          	add    $0x60,%rsi
    36d2:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    36da:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    36de:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    36e6:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    36ee:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    36f6:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    36fd:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3705:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    370c:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3713:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    371a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    371e:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3725:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    372c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3730:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3734:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3738:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    373c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3740:	49 39 f8             	cmp    %rdi,%r8
    3743:	0f 85 77 ff ff ff    	jne    36c0 <main+0x1000>
    3749:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    374d:	8d 6c 8d 00          	lea    0x0(%rbp,%rcx,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3751:	49 81 c1 20 01 00 00 	add    $0x120,%r9
    3758:	85 db                	test   %ebx,%ebx
    375a:	75 37                	jne    3793 <main+0x10d3>
    375c:	bb 01 00 00 00       	mov    $0x1,%ebx
    3761:	e9 2f ff ff ff       	jmp    3695 <main+0xfd5>
        other = (x + 1) % total_threads;
    3766:	41 8d 46 01          	lea    0x1(%r14),%eax
        my_thread_data[1] = &thread_data[other]; 
    376a:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    376f:	4c 89 ca             	mov    %r9,%rdx
    3772:	45 31 c0             	xor    %r8d,%r8d
    3775:	89 84 24 88 00 00 00 	mov    %eax,0x88(%rsp)
        other = (x + 1) % total_threads;
    377c:	89 c1                	mov    %eax,%ecx
        my_thread_data[1] = &thread_data[other]; 
    377e:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3782:	48 c1 e0 05          	shl    $0x5,%rax
    3786:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    378b:	48 01 f8             	add    %rdi,%rax
        thread_data[x].protected_state = &protected_state[k];
    378e:	e9 36 f5 ff ff       	jmp    2cc9 <main+0x609>
  for (int k = 0 ; k < group_count ; k++) {
    3793:	83 c0 02             	add    $0x2,%eax
    3796:	48 81 c2 40 02 00 00 	add    $0x240,%rdx
    379d:	83 f8 06             	cmp    $0x6,%eax
    37a0:	0f 85 ea fe ff ff    	jne    3690 <main+0xfd0>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    37a6:	48 8d 3d 93 5d 00 00 	lea    0x5d93(%rip),%rdi        # 9540 <_IO_stdin_used+0x540>
    37ad:	e8 8e eb ff ff       	call   2340 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    37b2:	48 8d 35 9c 5d 00 00 	lea    0x5d9c(%rip),%rsi        # 9555 <_IO_stdin_used+0x555>
    37b9:	48 8d 3d 97 5d 00 00 	lea    0x5d97(%rip),%rdi        # 9557 <_IO_stdin_used+0x557>
    37c0:	e8 3b ed ff ff       	call   2500 <fopen@plt>
    37c5:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas_size; x++) {
    37c8:	85 ed                	test   %ebp,%ebp
    37ca:	7e 76                	jle    3842 <main+0x1182>
    37cc:	48 63 ed             	movslq %ebp,%rbp
    37cf:	4c 8d 2d 5e 5d 00 00 	lea    0x5d5e(%rip),%r13        # 9534 <_IO_stdin_used+0x534>
    37d6:	4c 8d 25 9b 5d 00 00 	lea    0x5d9b(%rip),%r12        # 9578 <_IO_stdin_used+0x578>
    37dd:	49 8d 04 ef          	lea    (%r15,%rbp,8),%rax
    37e1:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    char * c = calloc(250, sizeof(char));
    37e6:	be 01 00 00 00       	mov    $0x1,%esi
    37eb:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    37f0:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    37f4:	e8 17 ec ff ff       	call   2410 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    37f9:	4c 89 e9             	mov    %r13,%rcx
    37fc:	ba fa 00 00 00       	mov    $0xfa,%edx
    3801:	be 01 00 00 00       	mov    $0x1,%esi
    3806:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    3809:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    380d:	48 89 ef             	mov    %rbp,%rdi
    3810:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3817:	31 c0                	xor    %eax,%eax
    3819:	e8 a2 ed ff ff       	call   25c0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    381e:	48 89 ea             	mov    %rbp,%rdx
    3821:	4c 89 e6             	mov    %r12,%rsi
    3824:	bf 01 00 00 00       	mov    $0x1,%edi
    3829:	31 c0                	xor    %eax,%eax
    382b:	e8 90 ec ff ff       	call   24c0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3830:	4c 89 f6             	mov    %r14,%rsi
    3833:	48 89 ef             	mov    %rbp,%rdi
    3836:	e8 95 eb ff ff       	call   23d0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    383b:	4c 39 7c 24 08       	cmp    %r15,0x8(%rsp)
    3840:	75 a4                	jne    37e6 <main+0x1126>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    3842:	4c 89 f7             	mov    %r14,%rdi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3845:	45 31 f6             	xor    %r14d,%r14d
    3848:	4c 8d 25 53 5d 00 00 	lea    0x5d53(%rip),%r12        # 95a2 <_IO_stdin_used+0x5a2>
    384f:	e8 1c eb ff ff       	call   2370 <fclose@plt>
    3854:	48 8d 3d 05 5d 00 00 	lea    0x5d05(%rip),%rdi        # 9560 <_IO_stdin_used+0x560>
    385b:	4c 89 f5             	mov    %r14,%rbp
    385e:	e8 dd ea ff ff       	call   2340 <puts@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    3863:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    3867:	89 ea                	mov    %ebp,%edx
    3869:	48 8d 35 0b 5d 00 00 	lea    0x5d0b(%rip),%rsi        # 957b <_IO_stdin_used+0x57b>
    3870:	bf 01 00 00 00       	mov    $0x1,%edi
    3875:	31 c0                	xor    %eax,%eax
    3877:	e8 44 ec ff ff       	call   24c0 <__printf_chk@plt>
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    387c:	48 8d 5c ed 00       	lea    0x0(%rbp,%rbp,8),%rbx
    3881:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3886:	45 31 ff             	xor    %r15d,%r15d
    3889:	48 c1 e3 06          	shl    $0x6,%rbx
    388d:	44 8d 6c 2d 00       	lea    0x0(%rbp,%rbp,1),%r13d
    3892:	48 01 c3             	add    %rax,%rbx
      int x = (k * threads_per_group) + d;
    3895:	43 8d 0c 2f          	lea    (%r15,%r13,1),%ecx
    3899:	44 89 fa             	mov    %r15d,%edx
    389c:	48 8d 35 e2 5c 00 00 	lea    0x5ce2(%rip),%rsi        # 9585 <_IO_stdin_used+0x585>
    38a3:	31 c0                	xor    %eax,%eax
    38a5:	bf 01 00 00 00       	mov    $0x1,%edi
    38aa:	45 31 f6             	xor    %r14d,%r14d
    38ad:	e8 0e ec ff ff       	call   24c0 <__printf_chk@plt>
    38b2:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
    38b7:	4c 89 f1             	mov    %r14,%rcx
    38ba:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    38bf:	48 89 dd             	mov    %rbx,%rbp
    38c2:	89 ca                	mov    %ecx,%edx
    38c4:	48 8d 35 cc 5c 00 00 	lea    0x5ccc(%rip),%rsi        # 9597 <_IO_stdin_used+0x597>
    38cb:	bf 01 00 00 00       	mov    $0x1,%edi
    38d0:	31 c0                	xor    %eax,%eax
    38d2:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    38d7:	45 31 ed             	xor    %r13d,%r13d
    38da:	e8 e1 eb ff ff       	call   24c0 <__printf_chk@plt>
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    38df:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    38e4:	48 c1 e3 09          	shl    $0x9,%rbx
    38e8:	eb 32                	jmp    391c <main+0x125c>
    38ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    38f0:	83 fe 01             	cmp    $0x1,%esi
    38f3:	0f 84 a9 00 00 00    	je     39a2 <main+0x12e2>
    38f9:	44 89 f2             	mov    %r14d,%edx
    38fc:	4c 89 e6             	mov    %r12,%rsi
    38ff:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3904:	49 83 c5 01          	add    $0x1,%r13
    3908:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    390f:	31 c0                	xor    %eax,%eax
    3911:	e8 aa eb ff ff       	call   24c0 <__printf_chk@plt>
    3916:	49 83 fd 06          	cmp    $0x6,%r13
    391a:	74 50                	je     396c <main+0x12ac>
          char * mailbox_kind = calloc(100, sizeof(char));
    391c:	be 01 00 00 00       	mov    $0x1,%esi
    3921:	bf 64 00 00 00       	mov    $0x64,%edi
    3926:	45 89 ee             	mov    %r13d,%r14d
    3929:	e8 e2 ea ff ff       	call   2410 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    392e:	4c 8b 45 38          	mov    0x38(%rbp),%r8
    3932:	4c 89 ef             	mov    %r13,%rdi
          char * mailbox_kind = calloc(100, sizeof(char));
    3935:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3938:	48 c1 e7 08          	shl    $0x8,%rdi
    393c:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3944:	48 01 f8             	add    %rdi,%rax
    3947:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    394d:	83 fe 02             	cmp    $0x2,%esi
    3950:	75 9e                	jne    38f0 <main+0x1230>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3952:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    395c:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    395f:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3967:	48 01 f8             	add    %rdi,%rax
    396a:	eb 8d                	jmp    38f9 <main+0x1239>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    396c:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    3971:	48 83 c1 01          	add    $0x1,%rcx
    3975:	48 83 f9 03          	cmp    $0x3,%rcx
    3979:	0f 85 43 ff ff ff    	jne    38c2 <main+0x1202>
    for (int d = 0 ; d < threads_per_group ; d++) {
    397f:	48 89 eb             	mov    %rbp,%rbx
    3982:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    3987:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    398c:	48 81 c3 20 01 00 00 	add    $0x120,%rbx
    3993:	45 85 ff             	test   %r15d,%r15d
    3996:	75 27                	jne    39bf <main+0x12ff>
    3998:	44 8b 7c 24 10       	mov    0x10(%rsp),%r15d
    399d:	e9 f3 fe ff ff       	jmp    3895 <main+0x11d5>
    39a2:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    39a8:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    39af:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    39b7:	48 01 f8             	add    %rdi,%rax
    39ba:	e9 3a ff ff ff       	jmp    38f9 <main+0x1239>
  for (int k = 0 ; k < group_count ; k++) {
    39bf:	48 83 c5 01          	add    $0x1,%rbp
    39c3:	48 83 fd 03          	cmp    $0x3,%rbp
    39c7:	0f 85 9a fe ff ff    	jne    3867 <main+0x11a7>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    39cd:	ba 07 00 00 00       	mov    $0x7,%edx
    39d2:	48 8d 35 e4 5b 00 00 	lea    0x5be4(%rip),%rsi        # 95bd <_IO_stdin_used+0x5bd>
    39d9:	bf 01 00 00 00       	mov    $0x1,%edi
    39de:	31 c0                	xor    %eax,%eax
    39e0:	e8 db ea ff ff       	call   24c0 <__printf_chk@plt>
  

  printf("io index = %d\n", io_index);
  int io_mode = 0;
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    39e5:	be 08 00 00 00       	mov    $0x8,%esi
    39ea:	bf 02 00 00 00       	mov    $0x2,%edi
    39ef:	e8 1c ea ff ff       	call   2410 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    39f4:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    39f9:	be 08 00 00 00       	mov    $0x8,%esi
    my_thread_data[0] = &thread_data[x]; 
    39fe:	49 8d be e0 07 00 00 	lea    0x7e0(%r14),%rdi
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3a05:	4c 89 70 08          	mov    %r14,0x8(%rax)
    my_thread_data[0] = &thread_data[x]; 
    3a09:	49 8d 9e 00 09 00 00 	lea    0x900(%r14),%rbx

    io_mode = (io_mode + 1) % 2;
    thread_data[x].threads = my_thread_data;
    3a10:	49 89 86 f8 07 00 00 	mov    %rax,0x7f8(%r14)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3a17:	4d 8d ae 20 01 00 00 	lea    0x120(%r14),%r13
    thread_data[x].thread_count = 2;
    3a1e:	41 c7 86 08 08 00 00 02 00 00 00 	movl   $0x2,0x808(%r14)
    thread_data[x].thread_index = 0;
    3a29:	41 c7 86 e4 07 00 00 00 00 00 00 	movl   $0x0,0x7e4(%r14)
    thread_data[x].task_count = total_barrier_count;
    3a34:	41 c7 86 20 08 00 00 03 00 00 00 	movl   $0x3,0x820(%r14)
    my_thread_data[0] = &thread_data[x]; 
    3a3f:	48 89 38             	mov    %rdi,(%rax)
    3a42:	48 89 7c 24 18       	mov    %rdi,0x18(%rsp)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    3a47:	bf 02 00 00 00       	mov    $0x2,%edi
    3a4c:	e8 bf e9 ff ff       	call   2410 <calloc@plt>
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a51:	be 38 00 00 00       	mov    $0x38,%esi
    3a56:	bf 0b 00 00 00       	mov    $0xb,%edi
    thread_data[x].thread_count = 2;
    3a5b:	41 c7 86 28 09 00 00 02 00 00 00 	movl   $0x2,0x928(%r14)
    thread_data[x].threads = my_thread_data;
    3a66:	49 89 86 18 09 00 00 	mov    %rax,0x918(%r14)
    my_thread_data[0] = &thread_data[x]; 
    3a6d:	48 89 18             	mov    %rbx,(%rax)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3a70:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3a74:	49 8b 46 38          	mov    0x38(%r14),%rax
    thread_data[x].thread_index = 0;
    3a78:	41 c7 86 04 09 00 00 00 00 00 00 	movl   $0x0,0x904(%r14)
    thread_data[x].task_count = total_barrier_count;
    3a83:	41 c7 86 40 09 00 00 03 00 00 00 	movl   $0x3,0x940(%r14)
    thread_data[n].tasks[0].scheduled = 1;
    3a8e:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3a98:	49 8b 86 58 01 00 00 	mov    0x158(%r14),%rax
    3a9f:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3aa9:	e8 62 e9 ff ff       	call   2410 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3aae:	be 38 00 00 00       	mov    $0x38,%esi
    3ab3:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ab8:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3abb:	e8 50 e9 ff ff       	call   2410 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ac0:	be 38 00 00 00       	mov    $0x38,%esi
    3ac5:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3aca:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3acf:	e8 3c e9 ff ff       	call   2410 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ad4:	be 38 00 00 00       	mov    $0x38,%esi
    3ad9:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ade:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ae3:	e8 28 e9 ff ff       	call   2410 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3ae8:	be 08 00 00 00       	mov    $0x8,%esi
    3aed:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3af2:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3af7:	e8 14 e9 ff ff       	call   2410 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3afc:	be 08 00 00 00       	mov    $0x8,%esi
    3b01:	bf 0b 00 00 00       	mov    $0xb,%edi
  thread_data[timer_threadi].type = TIMER;
    3b06:	41 c7 86 cc 06 00 00 00 00 00 00 	movl   $0x0,0x6cc(%r14)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3b11:	48 89 c5             	mov    %rax,%rbp
  thread_data[timer_threadi].task_count = total_barrier_count;
    3b14:	48 8b 05 fd 64 00 00 	mov    0x64fd(%rip),%rax        # a018 <_IO_stdin_used+0x1018>
    3b1b:	49 89 86 00 07 00 00 	mov    %rax,0x700(%r14)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3b22:	e8 e9 e8 ff ff       	call   2410 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3b27:	49 8d 8e 40 02 00 00 	lea    0x240(%r14),%rcx
    3b2e:	4c 89 f7             	mov    %r14,%rdi
    3b31:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3b36:	48 89 48 10          	mov    %rcx,0x10(%rax)
    3b3a:	49 8d 8e 60 03 00 00 	lea    0x360(%r14),%rcx
    3b41:	48 89 48 18          	mov    %rcx,0x18(%rax)
    3b45:	49 8d 8e 80 04 00 00 	lea    0x480(%r14),%rcx
    3b4c:	48 89 58 40          	mov    %rbx,0x40(%rax)
    3b50:	48 89 fb             	mov    %rdi,%rbx
    3b53:	48 8d bf 20 0a 00 00 	lea    0xa20(%rdi),%rdi
    3b5a:	4c 89 30             	mov    %r14,(%rax)
    3b5d:	48 8d 93 40 0b 00 00 	lea    0xb40(%rbx),%rdx
    3b64:	48 89 48 20          	mov    %rcx,0x20(%rax)
    3b68:	49 8d 8e a0 05 00 00 	lea    0x5a0(%r14),%rcx
    3b6f:	4d 8d b6 c0 06 00 00 	lea    0x6c0(%r14),%r14
    3b76:	48 89 48 28          	mov    %rcx,0x28(%rax)
    3b7a:	4c 89 70 30          	mov    %r14,0x30(%rax)
    3b7e:	48 89 70 38          	mov    %rsi,0x38(%rax)
    3b82:	48 8d 35 43 5a 00 00 	lea    0x5a43(%rip),%rsi        # 95cc <_IO_stdin_used+0x5cc>
    3b89:	48 89 78 48          	mov    %rdi,0x48(%rax)
    3b8d:	48 89 50 50          	mov    %rdx,0x50(%rax)
    3b91:	ba 06 00 00 00       	mov    $0x6,%edx
    3b96:	4c 89 68 08          	mov    %r13,0x8(%rax)
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3b9a:	48 89 83 d8 06 00 00 	mov    %rax,0x6d8(%rbx)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3ba1:	48 8b 05 78 64 00 00 	mov    0x6478(%rip),%rax        # a020 <_IO_stdin_used+0x1020>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3ba8:	c7 83 f0 06 00 00 06 00 00 00 	movl   $0x6,0x6f0(%rbx)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3bb2:	48 89 83 e8 06 00 00 	mov    %rax,0x6e8(%rbx)
    3bb9:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3bbb:	c7 83 c4 06 00 00 00 00 00 00 	movl   $0x0,0x6c4(%rbx)
    my_thread_data[n] = &thread_data[n]; 
    3bc5:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
    3bca:	bf 01 00 00 00       	mov    $0x1,%edi
    3bcf:	e8 ec e8 ff ff       	call   24c0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3bd4:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3bd9:	4c 89 f1             	mov    %r14,%rcx
    3bdc:	48 8d 7d 30          	lea    0x30(%rbp),%rdi
    3be0:	48 8d 15 19 0f 00 00 	lea    0xf19(%rip),%rdx        # 4b00 <timer_thread>
  for (int k = 0 ; k < group_count ; k++) {
    3be7:	45 31 f6             	xor    %r14d,%r14d
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3bea:	48 81 c6 50 01 00 00 	add    $0x150,%rsi
    3bf1:	e8 ea e8 ff ff       	call   24e0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    3bf6:	48 89 6c 24 28       	mov    %rbp,0x28(%rsp)
    3bfb:	48 89 e9             	mov    %rbp,%rcx
    3bfe:	4c 89 e0             	mov    %r12,%rax
    3c01:	4c 89 6c 24 40       	mov    %r13,0x40(%rsp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3c06:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3c0c:	48 89 da             	mov    %rbx,%rdx
    3c0f:	44 89 7c 24 10       	mov    %r15d,0x10(%rsp)
    3c14:	45 89 d7             	mov    %r10d,%r15d
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c17:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3c1c:	43 8d 2c 36          	lea    (%r14,%r14,1),%ebp
    3c20:	49 89 c5             	mov    %rax,%r13
    3c23:	49 89 cc             	mov    %rcx,%r12
    3c26:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    3c2b:	48 89 d3             	mov    %rdx,%rbx
    3c2e:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3c33:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    3c3a:	89 ea                	mov    %ebp,%edx
    3c3c:	44 89 f1             	mov    %r14d,%ecx
    3c3f:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    3c41:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    3c48:	48 8d 35 c9 5e 00 00 	lea    0x5ec9(%rip),%rsi        # 9b18 <_IO_stdin_used+0xb18>
    3c4f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c54:	83 c5 01             	add    $0x1,%ebp
    3c57:	e8 64 e8 ff ff       	call   24c0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3c5c:	48 89 d9             	mov    %rbx,%rcx
    3c5f:	4c 89 ee             	mov    %r13,%rsi
    3c62:	4c 89 e7             	mov    %r12,%rdi
    3c65:	48 8d 15 a4 3c 00 00 	lea    0x3ca4(%rip),%rdx        # 7910 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c6c:	48 81 c3 20 01 00 00 	add    $0x120,%rbx
    3c73:	49 83 c4 08          	add    $0x8,%r12
    3c77:	49 83 c5 38          	add    $0x38,%r13
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3c7b:	e8 60 e8 ff ff       	call   24e0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3c80:	48 8b 53 98          	mov    -0x68(%rbx),%rdx
    3c84:	49 8b 7c 24 f8       	mov    -0x8(%r12),%rdi
    3c89:	be 08 00 00 00       	mov    $0x8,%esi
    3c8e:	e8 9d e6 ff ff       	call   2330 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c93:	41 39 ef             	cmp    %ebp,%r15d
    3c96:	75 9b                	jne    3c33 <main+0x1573>
  for (int k = 0 ; k < group_count ; k++) {
    3c98:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3c9d:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    3ca2:	41 83 c6 01          	add    $0x1,%r14d
    3ca6:	41 83 c7 02          	add    $0x2,%r15d
    3caa:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    3caf:	48 83 c1 10          	add    $0x10,%rcx
    3cb3:	48 83 c0 70          	add    $0x70,%rax
    3cb7:	48 81 c2 40 02 00 00 	add    $0x240,%rdx
    3cbe:	41 83 fe 03          	cmp    $0x3,%r14d
    3cc2:	0f 85 4f ff ff ff    	jne    3c17 <main+0x1557>
    }
  }
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    3cc8:	be 08 00 00 00       	mov    $0x8,%esi
    3ccd:	bf 02 00 00 00       	mov    $0x2,%edi
    3cd2:	4c 8b 6c 24 40       	mov    0x40(%rsp),%r13
    3cd7:	48 8b 6c 24 28       	mov    0x28(%rsp),%rbp
    3cdc:	44 8b 7c 24 10       	mov    0x10(%rsp),%r15d
    3ce1:	e8 2a e7 ff ff       	call   2410 <calloc@plt>

  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    3ce6:	be d8 00 00 00       	mov    $0xd8,%esi
    3ceb:	bf 01 00 00 00       	mov    $0x1,%edi
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    3cf0:	49 89 c4             	mov    %rax,%r12
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    3cf3:	e8 18 e7 ff ff       	call   2410 <calloc@plt>
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3cf8:	be d8 00 00 00       	mov    $0xd8,%esi
    3cfd:	bf 01 00 00 00       	mov    $0x1,%edi
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    3d02:	49 89 04 24          	mov    %rax,(%r12)
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3d06:	e8 05 e7 ff ff       	call   2410 <calloc@plt>

  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    3d0b:	be 10 00 00 00       	mov    $0x10,%esi
    3d10:	bf 02 00 00 00       	mov    $0x2,%edi
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3d15:	49 89 44 24 08       	mov    %rax,0x8(%r12)
  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    3d1a:	e8 f1 e6 ff ff       	call   2410 <calloc@plt>
    3d1f:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    3d24:	49 89 c6             	mov    %rax,%r14
    3d27:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  long iomailboxes_size = 1000;
  for (int x = 0 ; x < io_threads; x++) {
    3d2c:	48 83 c0 20          	add    $0x20,%rax
    3d30:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3d35:	4c 89 e8             	mov    %r13,%rax
    3d38:	4d 89 e5             	mov    %r12,%r13
    3d3b:	4d 89 f4             	mov    %r14,%r12
    3d3e:	49 89 c6             	mov    %rax,%r14
    iomailboxes[x].count = iomailboxes_size;
    3d41:	41 c7 04 24 e8 03 00 00 	movl   $0x3e8,(%r12)
    iomailboxes[x].buffer = calloc(iomailboxes_size, sizeof(struct Buffer));
    3d49:	be 00 01 00 00       	mov    $0x100,%esi
    3d4e:	bf e8 03 00 00       	mov    $0x3e8,%edi
    3d53:	e8 b8 e6 ff ff       	call   2410 <calloc@plt>
    3d58:	49 89 44 24 08       	mov    %rax,0x8(%r12)
    3d5d:	48 89 c5             	mov    %rax,%rbp
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3d60:	48 8d 98 80 00 00 00 	lea    0x80(%rax),%rbx
    3d67:	48 81 c5 80 e8 03 00 	add    $0x3e880,%rbp
    3d6e:	66 90                	xchg   %ax,%ax
      iomailboxes[x].buffer[y].available = 0;
    3d70:	c7 03 00 00 00 00    	movl   $0x0,(%rbx)
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3d76:	be 20 00 00 00       	mov    $0x20,%esi
    3d7b:	bf 64 00 00 00       	mov    $0x64,%edi
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3d80:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
    3d87:	c7 83 10 ff ff ff 64 00 00 00 	movl   $0x64,-0xf0(%rbx)
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3d91:	e8 7a e6 ff ff       	call   2410 <calloc@plt>
    3d96:	48 89 83 08 ff ff ff 	mov    %rax,-0xf8(%rbx)
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3d9d:	48 39 dd             	cmp    %rbx,%rbp
    3da0:	75 ce                	jne    3d70 <main+0x16b0>
  for (int x = 0 ; x < io_threads; x++) {
    3da2:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    3da7:	49 83 c4 10          	add    $0x10,%r12
    3dab:	49 39 c4             	cmp    %rax,%r12
    3dae:	75 91                	jne    3d41 <main+0x1681>
    3db0:	48 8b 6c 24 40       	mov    0x40(%rsp),%rbp
  }
  char * send_identity = "send-thread";
  char * recv_identity = "recv-thread";
  char * unknown_identity = "unknown-thread";
  int counter = 0;
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    3db5:	bb 07 00 00 00       	mov    $0x7,%ebx
    3dba:	4d 89 ec             	mov    %r13,%r12
    3dbd:	4d 89 f5             	mov    %r14,%r13
    3dc0:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    3dc5:	48 8d 45 38          	lea    0x38(%rbp),%rax
    3dc9:	48 89 6c 24 18       	mov    %rbp,0x18(%rsp)
    3dce:	89 dd                	mov    %ebx,%ebp
    3dd0:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3dd5:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    3dda:	48 05 88 01 00 00    	add    $0x188,%rax
    3de0:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    thread_data[x].type = IO;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    int myring = x % 2;
    3de5:	89 eb                	mov    %ebp,%ebx
    thread_data[x].task_count = 0;
    3de7:	48 8b 05 3a 62 00 00 	mov    0x623a(%rip),%rax        # a028 <_IO_stdin_used+0x1028>
    3dee:	89 ea                	mov    %ebp,%edx
    int otherring = (myring + 1) % 2;
    if (myring == IO_MODE_SEND) {
      thread_data[x].identity = send_identity; 
    3df0:	48 8d 3d c7 55 00 00 	lea    0x55c7(%rip),%rdi        # 93be <_IO_stdin_used+0x3be>
    int myring = x % 2;
    3df7:	83 e3 01             	and    $0x1,%ebx
    thread_data[x].type = IO;
    3dfa:	41 c7 46 0c 02 00 00 00 	movl   $0x2,0xc(%r14)
    3e02:	48 8d 35 e1 57 00 00 	lea    0x57e1(%rip),%rsi        # 95ea <_IO_stdin_used+0x5ea>
    int otherring = (myring + 1) % 2;
    3e09:	41 89 d8             	mov    %ebx,%r8d
    thread_data[x].task_count = 0;
    3e0c:	49 89 46 40          	mov    %rax,0x40(%r14)
      thread_data[x].identity = send_identity; 
    3e10:	48 8d 05 9b 55 00 00 	lea    0x559b(%rip),%rax        # 93b2 <_IO_stdin_used+0x3b2>
    3e17:	89 d9                	mov    %ebx,%ecx
    int otherring = (myring + 1) % 2;
    3e19:	41 83 f0 01          	xor    $0x1,%r8d
      thread_data[x].identity = send_identity; 
    3e1d:	85 db                	test   %ebx,%ebx
    } else if (myring == IO_MODE_RECV) {
      thread_data[x].identity = recv_identity;
    } else {
      thread_data[x].identity = unknown_identity;
    }
    thread_data[x].io_mode = myring;
    3e1f:	41 89 9e 04 01 00 00 	mov    %ebx,0x104(%r14)
      thread_data[x].identity = send_identity; 
    3e26:	48 0f 45 c7          	cmovne %rdi,%rax
    thread_data[x].my_io = myring;
    thread_data[x].other_io = otherring;
    3e2a:	45 89 86 10 01 00 00 	mov    %r8d,0x110(%r14)
    3e31:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].my_io = myring;
    3e36:	41 89 9e 14 01 00 00 	mov    %ebx,0x114(%r14)
    3e3d:	49 89 86 18 01 00 00 	mov    %rax,0x118(%r14)
    thread_data[x].iomailboxes = iomailboxes; 
    3e44:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    3e49:	49 89 86 08 01 00 00 	mov    %rax,0x108(%r14)
    3e50:	31 c0                	xor    %eax,%eax
    3e52:	e8 69 e6 ff ff       	call   24c0 <__printf_chk@plt>
    printf("%d myring %d other is %d\n", x, myring, otherring);
    thread_data[x].ring = rings[myring]; 
    3e57:	49 8b 04 dc          	mov    (%r12,%rbx,8),%rax
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3e5b:	be 00 08 00 00       	mov    $0x800,%esi
    3e60:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = rings[myring]; 
    3e62:	49 89 46 60          	mov    %rax,0x60(%r14)
    int myeventfd = eventfd(0, EFD_NONBLOCK);
    3e66:	e8 c5 e6 ff ff       	call   2530 <eventfd@plt>
    thread_data[x]._eventfd = myeventfd; 
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3e6b:	be 08 00 00 00       	mov    $0x8,%esi
    3e70:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = myeventfd; 
    3e75:	41 89 46 68          	mov    %eax,0x68(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3e79:	e8 92 e5 ff ff       	call   2410 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3e7e:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].thread_index = x;
    3e83:	41 89 6e 04          	mov    %ebp,0x4(%r14)
    3e87:	89 ea                	mov    %ebp,%edx
    thread_data[x].threads = my_thread_data;
    3e89:	49 89 46 18          	mov    %rax,0x18(%r14)
    3e8d:	48 8d 35 70 57 00 00 	lea    0x5770(%rip),%rsi        # 9604 <_IO_stdin_used+0x604>
    3e94:	bf 01 00 00 00       	mov    $0x1,%edi
      my_thread_data[n] = &thread_data[n]; 
    3e99:	48 89 18             	mov    %rbx,(%rax)
    3e9c:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3ea0:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_count = thread_count;
    3ea2:	41 c7 46 28 02 00 00 00 	movl   $0x2,0x28(%r14)
    3eaa:	e8 11 e6 ff ff       	call   24c0 <__printf_chk@plt>
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3eaf:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    3eb4:	4c 89 f1             	mov    %r14,%rcx
    3eb7:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3ebc:	48 8d 15 5d 23 00 00 	lea    0x235d(%rip),%rdx        # 6220 <io_thread>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    3ec3:	49 81 c6 20 01 00 00 	add    $0x120,%r14
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3eca:	48 89 df             	mov    %rbx,%rdi
    3ecd:	e8 0e e6 ff ff       	call   24e0 <pthread_create@plt>
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    3ed2:	48 89 d8             	mov    %rbx,%rax
    3ed5:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3edb:	48 83 c0 08          	add    $0x8,%rax
    3edf:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3ee4:	83 fd 07             	cmp    $0x7,%ebp
    3ee7:	75 16                	jne    3eff <main+0x183f>
    3ee9:	bd 08 00 00 00       	mov    $0x8,%ebp
    3eee:	e9 f2 fe ff ff       	jmp    3de5 <main+0x1725>
            CPU_SET(j, sendercpu);
    3ef3:	48 81 0b ff 0f 00 00 	orq    $0xfff,(%rbx)
          for (int j = 0 ; j < cores ; j++) {
    3efa:	e9 66 ee ff ff       	jmp    2d65 <main+0x6a5>
    3eff:	ba 09 00 00 00       	mov    $0x9,%edx
    3f04:	48 8d 35 10 57 00 00 	lea    0x5710(%rip),%rsi        # 961b <_IO_stdin_used+0x61b>
    3f0b:	bf 01 00 00 00       	mov    $0x1,%edi
    3f10:	31 c0                	xor    %eax,%eax
    3f12:	48 8b 6c 24 18       	mov    0x18(%rsp),%rbp
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3f17:	41 be 09 00 00 00    	mov    $0x9,%r14d
    3f1d:	e8 9e e5 ff ff       	call   24c0 <__printf_chk@plt>
    3f22:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    3f27:	4c 8b 64 24 30       	mov    0x30(%rsp),%r12
    3f2c:	48 8d 5d 48          	lea    0x48(%rbp),%rbx
    3f30:	48 05 f8 01 00 00    	add    $0x1f8,%rax
    3f36:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3f3b:	48 89 d8             	mov    %rbx,%rax
    3f3e:	48 89 eb             	mov    %rbp,%rbx
    3f41:	48 89 c5             	mov    %rax,%rbp
    3f44:	44 89 f2             	mov    %r14d,%edx
    3f47:	48 8d 35 e3 56 00 00 	lea    0x56e3(%rip),%rsi        # 9631 <_IO_stdin_used+0x631>
    3f4e:	bf 01 00 00 00       	mov    $0x1,%edi
    3f53:	31 c0                	xor    %eax,%eax
    3f55:	e8 66 e5 ff ff       	call   24c0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3f5a:	be 08 00 00 00       	mov    $0x8,%esi
    3f5f:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3f64:	48 8b 05 bd 60 00 00 	mov    0x60bd(%rip),%rax        # a028 <_IO_stdin_used+0x1028>
    thread_data[x].type = EXTERNAL;
    3f6b:	41 c7 44 24 0c 03 00 00 00 	movl   $0x3,0xc(%r12)
    thread_data[x].task_count = 0;
    3f74:	49 89 44 24 40       	mov    %rax,0x40(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3f79:	e8 92 e4 ff ff       	call   2410 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3f7e:	48 8b bc 24 d8 00 00 00 	mov    0xd8(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3f86:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3f8b:	41 c7 84 24 c4 00 00 00 01 00 00 00 	movl   $0x1,0xc4(%r12)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3f97:	49 89 44 24 50       	mov    %rax,0x50(%r12)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3f9c:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3f9f:	bf 02 00 00 00       	mov    $0x2,%edi
    3fa4:	e8 67 e4 ff ff       	call   2410 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3fa9:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3fae:	4c 89 e1             	mov    %r12,%rcx
    3fb1:	48 89 ef             	mov    %rbp,%rdi
    thread_data[x].threads = my_thread_data;
    3fb4:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3fb9:	48 8d 15 30 0a 00 00 	lea    0xa30(%rip),%rdx        # 49f0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3fc0:	48 83 c5 08          	add    $0x8,%rbp
    3fc4:	49 81 c4 20 01 00 00 	add    $0x120,%r12
      my_thread_data[n] = &thread_data[n]; 
    3fcb:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3fce:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3fd3:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3fd7:	48 8b 05 32 60 00 00 	mov    0x6032(%rip),%rax        # a010 <_IO_stdin_used+0x1010>
    thread_data[x].thread_index = x;
    3fde:	45 89 b4 24 e4 fe ff ff 	mov    %r14d,-0x11c(%r12)
    thread_data[x].thread_count = thread_count;
    3fe6:	49 89 84 24 08 ff ff ff 	mov    %rax,-0xf8(%r12)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3fee:	e8 ed e4 ff ff       	call   24e0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3ff3:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3ff9:	48 83 84 24 d8 00 00 00 10 	addq   $0x10,0xd8(%rsp)
    4002:	41 83 fe 09          	cmp    $0x9,%r14d
    4006:	75 0b                	jne    4013 <main+0x1953>
    4008:	41 be 0a 00 00 00    	mov    $0xa,%r14d
    400e:	e9 31 ff ff ff       	jmp    3f44 <main+0x1884>
    4013:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    4018:	48 89 dd             	mov    %rbx,%rbp
    401b:	48 8d 1d 2c 56 00 00 	lea    0x562c(%rip),%rbx        # 964e <_IO_stdin_used+0x64e>
    4022:	4c 8d 68 04          	lea    0x4(%rax),%r13
    4026:	4c 8d a0 64 0c 00 00 	lea    0xc64(%rax),%r12
    402d:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    4031:	41 8b 55 00          	mov    0x0(%r13),%edx
    4035:	48 89 de             	mov    %rbx,%rsi
    4038:	bf 01 00 00 00       	mov    $0x1,%edi
    403d:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    403f:	49 81 c5 20 01 00 00 	add    $0x120,%r13
    4046:	e8 75 e4 ff ff       	call   24c0 <__printf_chk@plt>
    404b:	4d 39 e5             	cmp    %r12,%r13
    404e:	75 dd                	jne    402d <main+0x196d>
    4050:	48 8d 3d 0a 56 00 00 	lea    0x560a(%rip),%rdi        # 9661 <_IO_stdin_used+0x661>
    4057:	45 31 ed             	xor    %r13d,%r13d
    405a:	4c 8d a4 24 10 01 00 00 	lea    0x110(%rsp),%r12
    4062:	e8 d9 e2 ff ff       	call   2340 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    4067:	48 8d 1d 11 56 00 00 	lea    0x5611(%rip),%rbx        # 967f <_IO_stdin_used+0x67f>
    void * result; 
    pthread_join(thread[x], &result);
    406e:	4a 8b 7c ed 00       	mov    0x0(%rbp,%r13,8),%rdi
    4073:	4c 89 e6             	mov    %r12,%rsi
    4076:	e8 f5 e4 ff ff       	call   2570 <pthread_join@plt>
    407b:	44 89 ea             	mov    %r13d,%edx
    407e:	48 89 de             	mov    %rbx,%rsi
    4081:	bf 01 00 00 00       	mov    $0x1,%edi
    4086:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    4088:	49 83 c5 01          	add    $0x1,%r13
    408c:	e8 2f e4 ff ff       	call   24c0 <__printf_chk@plt>
    4091:	49 83 fd 0b          	cmp    $0xb,%r13
    4095:	75 d7                	jne    406e <main+0x19ae>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    4097:	be 08 00 00 00       	mov    $0x8,%esi
    409c:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    40a1:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    40a3:	e8 68 e3 ff ff       	call   2410 <calloc@plt>
    40a8:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    40ad:	48 89 c5             	mov    %rax,%rbp
    40b0:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    40b2:	49 89 d1             	mov    %rdx,%r9
    40b5:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    40b8:	45 8b 51 40          	mov    0x40(%r9),%r10d
    40bc:	45 85 d2             	test   %r10d,%r10d
    40bf:	0f 8e ab 00 00 00    	jle    4170 <main+0x1ab0>
    40c5:	49 8b 79 38          	mov    0x38(%r9),%rdi
    40c9:	4d 63 c2             	movslq %r10d,%r8
    40cc:	48 63 cb             	movslq %ebx,%rcx
    40cf:	49 c1 e0 09          	shl    $0x9,%r8
    40d3:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    40d8:	49 01 f8             	add    %rdi,%r8
    40db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    40e0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    40e7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    40ee:	48 83 c6 60          	add    $0x60,%rsi
    40f2:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    40fa:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    40fe:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    4106:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    410e:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    4116:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    411d:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    4125:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    412c:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    4133:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    413a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    413e:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    4145:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    414c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    4150:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    4154:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    4158:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    415c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    4160:	4c 39 c7             	cmp    %r8,%rdi
    4163:	0f 85 77 ff ff ff    	jne    40e0 <main+0x1a20>
    4169:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    416d:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    4170:	49 81 c1 20 01 00 00 	add    $0x120,%r9
    4177:	45 85 db             	test   %r11d,%r11d
    417a:	75 08                	jne    4184 <main+0x1ac4>
    417c:	45 89 fb             	mov    %r15d,%r11d
    417f:	e9 34 ff ff ff       	jmp    40b8 <main+0x19f8>
  for (int k = 0 ; k < group_count ; k++) {
    4184:	83 c0 02             	add    $0x2,%eax
    4187:	48 81 c2 40 02 00 00 	add    $0x240,%rdx
    418e:	83 f8 06             	cmp    $0x6,%eax
    4191:	0f 85 1b ff ff ff    	jne    40b2 <main+0x19f2>
    4197:	48 8d 3d f5 54 00 00 	lea    0x54f5(%rip),%rdi        # 9693 <_IO_stdin_used+0x693>
    419e:	e8 9d e1 ff ff       	call   2340 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    41a3:	48 8d 35 ab 53 00 00 	lea    0x53ab(%rip),%rsi        # 9555 <_IO_stdin_used+0x555>
    41aa:	48 8d 3d fa 54 00 00 	lea    0x54fa(%rip),%rdi        # 96ab <_IO_stdin_used+0x6ab>
    41b1:	e8 4a e3 ff ff       	call   2500 <fopen@plt>
    41b6:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas2_size; x++) {
    41b9:	85 db                	test   %ebx,%ebx
    41bb:	7e 73                	jle    4230 <main+0x1b70>
    41bd:	48 63 db             	movslq %ebx,%rbx
    41c0:	49 89 ef             	mov    %rbp,%r15
    41c3:	4c 8d 2d 6a 53 00 00 	lea    0x536a(%rip),%r13        # 9534 <_IO_stdin_used+0x534>
    41ca:	48 8d 6c dd 00       	lea    0x0(%rbp,%rbx,8),%rbp
    41cf:	4c 8d 25 a2 53 00 00 	lea    0x53a2(%rip),%r12        # 9578 <_IO_stdin_used+0x578>
    char * c = calloc(250, sizeof(char));
    41d6:	be 01 00 00 00       	mov    $0x1,%esi
    41db:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    41e0:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    41e4:	e8 27 e2 ff ff       	call   2410 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    41e9:	4c 89 e9             	mov    %r13,%rcx
    41ec:	ba fa 00 00 00       	mov    $0xfa,%edx
    41f1:	be 01 00 00 00       	mov    $0x1,%esi
    41f6:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    41f9:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    41fd:	48 89 df             	mov    %rbx,%rdi
    4200:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    4207:	31 c0                	xor    %eax,%eax
    4209:	e8 b2 e3 ff ff       	call   25c0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    420e:	48 89 da             	mov    %rbx,%rdx
    4211:	4c 89 e6             	mov    %r12,%rsi
    4214:	bf 01 00 00 00       	mov    $0x1,%edi
    4219:	31 c0                	xor    %eax,%eax
    421b:	e8 a0 e2 ff ff       	call   24c0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4220:	4c 89 f6             	mov    %r14,%rsi
    4223:	48 89 df             	mov    %rbx,%rdi
    4226:	e8 a5 e1 ff ff       	call   23d0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    422b:	49 39 ef             	cmp    %rbp,%r15
    422e:	75 a6                	jne    41d6 <main+0x1b16>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    4230:	4c 89 f7             	mov    %r14,%rdi
    4233:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    4239:	31 db                	xor    %ebx,%ebx
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    423b:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    4245:	e8 26 e1 ff ff       	call   2370 <fclose@plt>
  long sents = 0;
    424a:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long sends = 0;
    4253:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long ingests = 0;
    425c:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long total = 0;
    4265:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  int datas2_size = 0; 
    426e:	48 8b 84 24 a8 00 00 00 	mov    0xa8(%rsp),%rax
    4276:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    427b:	4c 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%r14
    4283:	45 89 e5             	mov    %r12d,%r13d
    4286:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    428b:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
      int x = (k * threads_per_group) + d;
    4290:	44 89 e8             	mov    %r13d,%eax
    4293:	41 83 c5 01          	add    $0x1,%r13d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    4297:	bf 0a 00 00 00       	mov    $0xa,%edi
        other = abs(x - 1) % total_threads;
    429c:	41 f6 c5 01          	test   $0x1,%r13b
    42a0:	8d 50 02             	lea    0x2(%rax),%edx
    42a3:	0f 44 c2             	cmove  %edx,%eax
    42a6:	4c 63 e0             	movslq %eax,%r12
    42a9:	e8 72 e0 ff ff       	call   2320 <putchar@plt>
    42ae:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    42b3:	bf 01 00 00 00       	mov    $0x1,%edi
    42b8:	48 8d 35 f5 53 00 00 	lea    0x53f5(%rip),%rsi        # 96b4 <_IO_stdin_used+0x6b4>
    42bf:	48 8b 10             	mov    (%rax),%rdx
    42c2:	31 c0                	xor    %eax,%eax
    42c4:	e8 f7 e1 ff ff       	call   24c0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    42c9:	41 8b 56 40          	mov    0x40(%r14),%edx
    42cd:	85 d2                	test   %edx,%edx
    42cf:	0f 8e 35 05 00 00    	jle    480a <main+0x214a>
    42d5:	48 63 ca             	movslq %edx,%rcx
    42d8:	49 8b 46 38          	mov    0x38(%r14),%rax
      long v = 0;
    42dc:	31 d2                	xor    %edx,%edx
    42de:	48 c1 e1 09          	shl    $0x9,%rcx
    42e2:	48 01 c1             	add    %rax,%rcx
    42e5:	0f 1f 00             	nopl   (%rax)
        v += thread_data[me].tasks[n].v;
    42e8:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    42ef:	48 05 00 02 00 00    	add    $0x200,%rax
    42f5:	48 39 c8             	cmp    %rcx,%rax
    42f8:	75 ee                	jne    42e8 <main+0x1c28>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    42fa:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    42ff:	4b 8d 04 e4          	lea    (%r12,%r12,8),%rax
    4303:	48 c1 e0 05          	shl    $0x5,%rax
    4307:	48 01 f8             	add    %rdi,%rax
    430a:	48 63 48 40          	movslq 0x40(%rax),%rcx
    430e:	85 c9                	test   %ecx,%ecx
    4310:	7e 20                	jle    4332 <main+0x1c72>
    4312:	48 8b 40 38          	mov    0x38(%rax),%rax
    4316:	48 c1 e1 09          	shl    $0x9,%rcx
    431a:	48 01 c1             	add    %rax,%rcx
    431d:	0f 1f 00             	nopl   (%rax)
        v += thread_data[other].tasks[n].v;
    4320:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    4327:	48 05 00 02 00 00    	add    $0x200,%rax
    432d:	48 39 c8             	cmp    %rcx,%rax
    4330:	75 ee                	jne    4320 <main+0x1c60>
    4332:	48 8d 35 90 53 00 00 	lea    0x5390(%rip),%rsi        # 96c9 <_IO_stdin_used+0x6c9>
    4339:	bf 01 00 00 00       	mov    $0x1,%edi
    433e:	31 c0                	xor    %eax,%eax
    4340:	e8 7b e1 ff ff       	call   24c0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    4345:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    434a:	bf 01 00 00 00       	mov    $0x1,%edi
    434f:	48 8d 35 f2 57 00 00 	lea    0x57f2(%rip),%rsi        # 9b48 <_IO_stdin_used+0xb48>
    4356:	48 8b 08             	mov    (%rax),%rcx
    4359:	48 b8 0b d7 a3 70 3d 0a d7 a3 	movabs $0xa3d70a3d70a3d70b,%rax
    4363:	48 f7 e9             	imul   %rcx
    4366:	31 c0                	xor    %eax,%eax
    4368:	48 01 ca             	add    %rcx,%rdx
    436b:	48 c1 f9 3f          	sar    $0x3f,%rcx
    436f:	48 c1 fa 04          	sar    $0x4,%rdx
    4373:	48 29 ca             	sub    %rcx,%rdx
    4376:	e8 45 e1 ff ff       	call   24c0 <__printf_chk@plt>
    437b:	bf 0a 00 00 00       	mov    $0xa,%edi
    4380:	e8 9b df ff ff       	call   2320 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    4385:	45 8b 66 40          	mov    0x40(%r14),%r12d
    4389:	45 85 e4             	test   %r12d,%r12d
    438c:	0f 8e 39 01 00 00    	jle    44cb <main+0x1e0b>
    4392:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    4397:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    439c:	31 d2                	xor    %edx,%edx
    439e:	4c 8b 7c 24 20       	mov    0x20(%rsp),%r15
    43a3:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    43a8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    43ad:	0f 1f 00             	nopl   (%rax)
        total += thread_data[x].tasks[n].n;
    43b0:	49 8b 46 38          	mov    0x38(%r14),%rax
    43b4:	49 89 d1             	mov    %rdx,%r9
        sends += thread_data[x].tasks[n].sends;
    43b7:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    43bc:	41 89 d5             	mov    %edx,%r13d
        total += thread_data[x].tasks[n].n;
    43bf:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    43c3:	45 31 e4             	xor    %r12d,%r12d
        total += thread_data[x].tasks[n].n;
    43c6:	4c 01 c8             	add    %r9,%rax
        sends += thread_data[x].tasks[n].sends;
    43c9:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
        total += thread_data[x].tasks[n].n;
    43ce:	48 03 b0 08 01 00 00 	add    0x108(%rax),%rsi
        ingests += thread_data[x].tasks[n].ingest_count;
    43d5:	48 03 b8 68 01 00 00 	add    0x168(%rax),%rdi
        sends += thread_data[x].tasks[n].sends;
    43dc:	4c 03 90 80 01 00 00 	add    0x180(%rax),%r10
    43e3:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    43e8:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    43ed:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    43f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    43f8:	8b 54 24 08          	mov    0x8(%rsp),%edx
    43fc:	45 89 e0             	mov    %r12d,%r8d
    43ff:	44 89 e9             	mov    %r13d,%ecx
    4402:	bf 01 00 00 00       	mov    $0x1,%edi
    4407:	48 8d 35 c8 52 00 00 	lea    0x52c8(%rip),%rsi        # 96d6 <_IO_stdin_used+0x6d6>
    440e:	31 c0                	xor    %eax,%eax
    4410:	e8 ab e0 ff ff       	call   24c0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4415:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    441a:	4c 89 e0             	mov    %r12,%rax
    441d:	45 89 e0             	mov    %r12d,%r8d
    4420:	49 8b 56 38          	mov    0x38(%r14),%rdx
    4424:	48 c1 e0 08          	shl    $0x8,%rax
    4428:	48 83 ec 08          	sub    $0x8,%rsp
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    442c:	49 83 c4 01          	add    $0x1,%r12
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4430:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    4438:	48 8b 38             	mov    (%rax),%rdi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    443b:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4442:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4449:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4450:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4457:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    445e:	bf 01 00 00 00       	mov    $0x1,%edi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    4463:	48 01 c3             	add    %rax,%rbx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4466:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4469:	49 01 cf             	add    %rcx,%r15
    446c:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4470:	48 01 f3             	add    %rsi,%rbx
    4473:	50                   	push   %rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4474:	49 01 d7             	add    %rdx,%r15
    4477:	8b 54 24 18          	mov    0x18(%rsp),%edx
    447b:	44 89 e9             	mov    %r13d,%ecx
    447e:	48 8d 35 e3 56 00 00 	lea    0x56e3(%rip),%rsi        # 9b68 <_IO_stdin_used+0xb68>
    4485:	31 c0                	xor    %eax,%eax
    4487:	e8 34 e0 ff ff       	call   24c0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    448c:	41 5a                	pop    %r10
    448e:	41 5b                	pop    %r11
    4490:	49 83 fc 06          	cmp    $0x6,%r12
    4494:	0f 85 5e ff ff ff    	jne    43f8 <main+0x1d38>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    449a:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    449f:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    44a4:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    44a9:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    44ae:	48 83 c2 01          	add    $0x1,%rdx
    44b2:	41 39 56 40          	cmp    %edx,0x40(%r14)
    44b6:	0f 8f f4 fe ff ff    	jg     43b0 <main+0x1cf0>
    44bc:	4c 89 7c 24 20       	mov    %r15,0x20(%rsp)
    44c1:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    44c6:	48 89 74 24 30       	mov    %rsi,0x30(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    44cb:	45 31 ff             	xor    %r15d,%r15d
    44ce:	49 83 be a8 00 00 00 00 	cmpq   $0x0,0xa8(%r14)
    44d6:	4c 8d 25 ab 56 00 00 	lea    0x56ab(%rip),%r12        # 9b88 <_IO_stdin_used+0xb88>
    44dd:	7e 59                	jle    4538 <main+0x1e78>
    44df:	90                   	nop
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    44e0:	49 8b 86 98 00 00 00 	mov    0x98(%r14),%rax
    44e7:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    44eb:	48 83 ec 08          	sub    $0x8,%rsp
    44ef:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    44f4:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    44f8:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    44fc:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    4500:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    4504:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4507:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    450b:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    450e:	48 f7 e5             	mul    %rbp
    4511:	8b 49 20             	mov    0x20(%rcx),%ecx
    4514:	56                   	push   %rsi
    4515:	31 c0                	xor    %eax,%eax
    4517:	4c 89 e6             	mov    %r12,%rsi
    451a:	48 c1 ea 12          	shr    $0x12,%rdx
    451e:	49 89 d1             	mov    %rdx,%r9
    4521:	ba 02 00 00 00       	mov    $0x2,%edx
    4526:	e8 95 df ff ff       	call   24c0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    452b:	41 58                	pop    %r8
    452d:	41 59                	pop    %r9
    452f:	4d 39 be a8 00 00 00 	cmp    %r15,0xa8(%r14)
    4536:	7f a8                	jg     44e0 <main+0x1e20>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4538:	41 8b 96 c4 00 00 00 	mov    0xc4(%r14),%edx
    453f:	85 d2                	test   %edx,%edx
    4541:	0f 8e 0a 01 00 00    	jle    4651 <main+0x1f91>
    4547:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    454c:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4550:	45 31 ff             	xor    %r15d,%r15d
    4553:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    4558:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    4560:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    4564:	44 89 fb             	mov    %r15d,%ebx
    4567:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    456f:	8b 30                	mov    (%rax),%esi
    4571:	85 f6                	test   %esi,%esi
    4573:	0f 8e c1 00 00 00    	jle    463a <main+0x1f7a>
    4579:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    457e:	31 d2                	xor    %edx,%edx
    4580:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4584:	49 89 f8             	mov    %rdi,%r8
    4587:	48 89 d7             	mov    %rdx,%rdi
    458a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4590:	49 89 fc             	mov    %rdi,%r12
    4593:	45 31 ff             	xor    %r15d,%r15d
    4596:	49 c1 e4 08          	shl    $0x8,%r12
    459a:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    459e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    45a4:	85 d2                	test   %edx,%edx
    45a6:	7e 77                	jle    461f <main+0x1f5f>
    45a8:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    45ad:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    45b0:	4c 89 f9             	mov    %r15,%rcx
    45b3:	48 83 ec 08          	sub    $0x8,%rsp
    45b7:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    45bc:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    45c0:	48 c1 e1 05          	shl    $0x5,%rcx
    45c4:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    45cb:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    45cf:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    45d3:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    45d6:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    45da:	4c 2b 01             	sub    (%rcx),%r8
    45dd:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    45de:	48 f7 e5             	mul    %rbp
    45e1:	89 d9                	mov    %ebx,%ecx
    45e3:	48 8d 35 ee 55 00 00 	lea    0x55ee(%rip),%rsi        # 9bd8 <_IO_stdin_used+0xbd8>
    45ea:	31 c0                	xor    %eax,%eax
    45ec:	48 c1 ea 12          	shr    $0x12,%rdx
    45f0:	49 89 d1             	mov    %rdx,%r9
    45f3:	ba 02 00 00 00       	mov    $0x2,%edx
    45f8:	e8 c3 de ff ff       	call   24c0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    45fd:	4d 8b 46 50          	mov    0x50(%r14),%r8
    4601:	5e                   	pop    %rsi
    4602:	5f                   	pop    %rdi
    4603:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    4607:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    460b:	4a 8d 04 21          	lea    (%rcx,%r12,1),%rax
    460f:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    4616:	7f 98                	jg     45b0 <main+0x1ef0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4618:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    461d:	8b 32                	mov    (%rdx),%esi
    461f:	48 83 c7 01          	add    $0x1,%rdi
    4623:	39 fe                	cmp    %edi,%esi
    4625:	0f 8f 65 ff ff ff    	jg     4590 <main+0x1ed0>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    462b:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    4630:	41 8b 96 c4 00 00 00 	mov    0xc4(%r14),%edx
    4637:	4c 89 c7             	mov    %r8,%rdi
    463a:	49 83 c7 01          	add    $0x1,%r15
    463e:	44 39 fa             	cmp    %r15d,%edx
    4641:	0f 8f 19 ff ff ff    	jg     4560 <main+0x1ea0>
    4647:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    464c:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    4651:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    4657:	49 81 c6 20 01 00 00 	add    $0x120,%r14
    465e:	44 39 6c 24 48       	cmp    %r13d,0x48(%rsp)
    4663:	0f 85 27 fc ff ff    	jne    4290 <main+0x1bd0>
  for (int k = 0 ; k < group_count ; k++) {
    4669:	48 83 84 24 a8 00 00 00 30 	addq   $0x30,0xa8(%rsp)
    4672:	44 8b 44 24 48       	mov    0x48(%rsp),%r8d
    4677:	48 81 84 24 a0 00 00 00 40 02 00 00 	addq   $0x240,0xa0(%rsp)
    4683:	41 83 f8 05          	cmp    $0x5,%r8d
    4687:	74 08                	je     4691 <main+0x1fd1>
    4689:	45 89 c4             	mov    %r8d,%r12d
    468c:	e9 dd fb ff ff       	jmp    426e <main+0x1bae>
    4691:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    4696:	bf 01 00 00 00       	mov    $0x1,%edi
    469b:	31 c0                	xor    %eax,%eax
    469d:	49 89 df             	mov    %rbx,%r15
    46a0:	48 8d 35 3f 50 00 00 	lea    0x503f(%rip),%rsi        # 96e6 <_IO_stdin_used+0x6e6>
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    46a7:	48 bb 0b d7 a3 70 3d 0a d7 a3 	movabs $0xa3d70a3d70a3d70b,%rbx
    46b1:	4c 89 f2             	mov    %r14,%rdx
    46b4:	e8 07 de ff ff       	call   24c0 <__printf_chk@plt>
    46b9:	bf 0a 00 00 00       	mov    $0xa,%edi
    46be:	e8 5d dc ff ff       	call   2320 <putchar@plt>
    46c3:	48 8b bc 24 b8 00 00 00 	mov    0xb8(%rsp),%rdi
    46cb:	48 8d 35 5e 55 00 00 	lea    0x555e(%rip),%rsi        # 9c30 <_IO_stdin_used+0xc30>
    46d2:	31 c0                	xor    %eax,%eax
    46d4:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    46d8:	bf 01 00 00 00       	mov    $0x1,%edi
    46dd:	e8 de dd ff ff       	call   24c0 <__printf_chk@plt>
    46e2:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    46e7:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    46ec:	48 8d 35 65 55 00 00 	lea    0x5565(%rip),%rsi        # 9c58 <_IO_stdin_used+0xc58>
    46f3:	48 f7 eb             	imul   %rbx
    46f6:	31 c0                	xor    %eax,%eax
    46f8:	48 01 fa             	add    %rdi,%rdx
    46fb:	48 c1 ff 3f          	sar    $0x3f,%rdi
    46ff:	48 c1 fa 04          	sar    $0x4,%rdx
    4703:	48 29 fa             	sub    %rdi,%rdx
    4706:	bf 01 00 00 00       	mov    $0x1,%edi
    470b:	e8 b0 dd ff ff       	call   24c0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    4710:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    4715:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    471a:	48 8d 35 67 55 00 00 	lea    0x5567(%rip),%rsi        # 9c88 <_IO_stdin_used+0xc88>
    4721:	48 f7 eb             	imul   %rbx
    4724:	31 c0                	xor    %eax,%eax
    4726:	48 01 fa             	add    %rdi,%rdx
    4729:	48 c1 ff 3f          	sar    $0x3f,%rdi
    472d:	48 c1 fa 04          	sar    $0x4,%rdx
    4731:	48 29 fa             	sub    %rdi,%rdx
    4734:	bf 01 00 00 00       	mov    $0x1,%edi
    4739:	e8 82 dd ff ff       	call   24c0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    473e:	4c 89 f0             	mov    %r14,%rax
    4741:	bf 01 00 00 00       	mov    $0x1,%edi
    4746:	48 8d 35 6b 55 00 00 	lea    0x556b(%rip),%rsi        # 9cb8 <_IO_stdin_used+0xcb8>
    474d:	48 f7 eb             	imul   %rbx
    4750:	4c 89 f0             	mov    %r14,%rax
    4753:	48 c1 f8 3f          	sar    $0x3f,%rax
    4757:	4c 01 f2             	add    %r14,%rdx
    475a:	48 c1 fa 04          	sar    $0x4,%rdx
    475e:	48 29 c2             	sub    %rax,%rdx
    4761:	31 c0                	xor    %eax,%eax
    4763:	e8 58 dd ff ff       	call   24c0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    4768:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    476d:	bf 01 00 00 00       	mov    $0x1,%edi
    4772:	48 8d 35 81 4f 00 00 	lea    0x4f81(%rip),%rsi        # 96fa <_IO_stdin_used+0x6fa>
    4779:	48 f7 eb             	imul   %rbx
    477c:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4781:	48 8d 2c 02          	lea    (%rdx,%rax,1),%rbp
    4785:	48 c1 f8 3f          	sar    $0x3f,%rax
    4789:	48 c1 fd 04          	sar    $0x4,%rbp
    478d:	48 29 c5             	sub    %rax,%rbp
    4790:	31 c0                	xor    %eax,%eax
    4792:	48 89 ea             	mov    %rbp,%rdx
    4795:	e8 26 dd ff ff       	call   24c0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
    479a:	4c 89 f8             	mov    %r15,%rax
    479d:	bf 01 00 00 00       	mov    $0x1,%edi
    47a2:	48 8d 35 2f 55 00 00 	lea    0x552f(%rip),%rsi        # 9cd8 <_IO_stdin_used+0xcd8>
    47a9:	48 f7 eb             	imul   %rbx
    47ac:	4c 89 f8             	mov    %r15,%rax
    47af:	48 c1 f8 3f          	sar    $0x3f,%rax
    47b3:	48 89 d3             	mov    %rdx,%rbx
    47b6:	4c 01 fb             	add    %r15,%rbx
    47b9:	48 c1 fb 04          	sar    $0x4,%rbx
    47bd:	48 29 c3             	sub    %rax,%rbx
    47c0:	31 c0                	xor    %eax,%eax
    47c2:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    47c5:	48 29 eb             	sub    %rbp,%rbx
    47c8:	e8 f3 dc ff ff       	call   24c0 <__printf_chk@plt>
    47cd:	31 c0                	xor    %eax,%eax
    47cf:	48 89 da             	mov    %rbx,%rdx
    47d2:	bf 01 00 00 00       	mov    $0x1,%edi
    47d7:	48 8d 35 38 4f 00 00 	lea    0x4f38(%rip),%rsi        # 9716 <_IO_stdin_used+0x716>
    47de:	e8 dd dc ff ff       	call   24c0 <__printf_chk@plt>
  return 0;

}
    47e3:	48 8b 84 24 28 01 00 00 	mov    0x128(%rsp),%rax
    47eb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    47f4:	75 25                	jne    481b <main+0x215b>
    47f6:	48 81 c4 38 01 00 00 	add    $0x138,%rsp
    47fd:	31 c0                	xor    %eax,%eax
    47ff:	5b                   	pop    %rbx
    4800:	5d                   	pop    %rbp
    4801:	41 5c                	pop    %r12
    4803:	41 5d                	pop    %r13
    4805:	41 5e                	pop    %r14
    4807:	41 5f                	pop    %r15
    4809:	c3                   	ret
      long v = 0;
    480a:	31 d2                	xor    %edx,%edx
    480c:	e9 e9 fa ff ff       	jmp    42fa <main+0x1c3a>
            exit(1);
    4811:	bf 01 00 00 00       	mov    $0x1,%edi
    4816:	e8 05 dd ff ff       	call   2520 <exit@plt>
}
    481b:	e8 70 db ff ff       	call   2390 <__stack_chk_fail@plt>

0000000000004820 <_start>:
    4820:	f3 0f 1e fa          	endbr64
    4824:	31 ed                	xor    %ebp,%ebp
    4826:	49 89 d1             	mov    %rdx,%r9
    4829:	5e                   	pop    %rsi
    482a:	48 89 e2             	mov    %rsp,%rdx
    482d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4831:	50                   	push   %rax
    4832:	54                   	push   %rsp
    4833:	45 31 c0             	xor    %r8d,%r8d
    4836:	31 c9                	xor    %ecx,%ecx
    4838:	48 8d 3d 81 de ff ff 	lea    -0x217f(%rip),%rdi        # 26c0 <main>
    483f:	ff 15 93 77 00 00    	call   *0x7793(%rip)        # bfd8 <__libc_start_main@GLIBC_2.34>
    4845:	f4                   	hlt
    4846:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004850 <deregister_tm_clones>:
    4850:	48 8d 3d c9 77 00 00 	lea    0x77c9(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4857:	48 8d 05 c2 77 00 00 	lea    0x77c2(%rip),%rax        # c020 <stderr@GLIBC_2.2.5>
    485e:	48 39 f8             	cmp    %rdi,%rax
    4861:	74 15                	je     4878 <deregister_tm_clones+0x28>
    4863:	48 8b 05 76 77 00 00 	mov    0x7776(%rip),%rax        # bfe0 <_ITM_deregisterTMCloneTable@Base>
    486a:	48 85 c0             	test   %rax,%rax
    486d:	74 09                	je     4878 <deregister_tm_clones+0x28>
    486f:	ff e0                	jmp    *%rax
    4871:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4878:	c3                   	ret
    4879:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004880 <register_tm_clones>:
    4880:	48 8d 3d 99 77 00 00 	lea    0x7799(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4887:	48 8d 35 92 77 00 00 	lea    0x7792(%rip),%rsi        # c020 <stderr@GLIBC_2.2.5>
    488e:	48 29 fe             	sub    %rdi,%rsi
    4891:	48 89 f0             	mov    %rsi,%rax
    4894:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4898:	48 c1 f8 03          	sar    $0x3,%rax
    489c:	48 01 c6             	add    %rax,%rsi
    489f:	48 d1 fe             	sar    %rsi
    48a2:	74 14                	je     48b8 <register_tm_clones+0x38>
    48a4:	48 8b 05 45 77 00 00 	mov    0x7745(%rip),%rax        # bff0 <_ITM_registerTMCloneTable@Base>
    48ab:	48 85 c0             	test   %rax,%rax
    48ae:	74 08                	je     48b8 <register_tm_clones+0x38>
    48b0:	ff e0                	jmp    *%rax
    48b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    48b8:	c3                   	ret
    48b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000048c0 <__do_global_dtors_aux>:
    48c0:	f3 0f 1e fa          	endbr64
    48c4:	80 3d 5d 77 00 00 00 	cmpb   $0x0,0x775d(%rip)        # c028 <completed.0>
    48cb:	75 2b                	jne    48f8 <__do_global_dtors_aux+0x38>
    48cd:	55                   	push   %rbp
    48ce:	48 83 3d 22 77 00 00 00 	cmpq   $0x0,0x7722(%rip)        # bff8 <__cxa_finalize@GLIBC_2.2.5>
    48d6:	48 89 e5             	mov    %rsp,%rbp
    48d9:	74 0c                	je     48e7 <__do_global_dtors_aux+0x27>
    48db:	48 8b 3d 26 77 00 00 	mov    0x7726(%rip),%rdi        # c008 <__dso_handle>
    48e2:	e8 19 da ff ff       	call   2300 <__cxa_finalize@plt>
    48e7:	e8 64 ff ff ff       	call   4850 <deregister_tm_clones>
    48ec:	c6 05 35 77 00 00 01 	movb   $0x1,0x7735(%rip)        # c028 <completed.0>
    48f3:	5d                   	pop    %rbp
    48f4:	c3                   	ret
    48f5:	0f 1f 00             	nopl   (%rax)
    48f8:	c3                   	ret
    48f9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004900 <frame_dummy>:
    4900:	f3 0f 1e fa          	endbr64
    4904:	e9 77 ff ff ff       	jmp    4880 <register_tm_clones>
    4909:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004910 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4910:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    4914:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    491b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    491f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4927:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    492b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    492f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4936:	48 85 c9             	test   %rcx,%rcx
    4939:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4940:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4944:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4948:	31 c0                	xor    %eax,%eax
    494a:	c3                   	ret
    494b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004950 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4950:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4954:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    495b:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    for (int x = 0 ; x < data->task_count ; x++) {
    4962:	85 c9                	test   %ecx,%ecx
    4964:	7e 48                	jle    49ae <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4966:	48 63 97 30 01 00 00 	movslq 0x130(%rdi),%rdx
    496d:	49 8b 40 18          	mov    0x18(%r8),%rax
    4971:	48 c1 e1 09          	shl    $0x9,%rcx
      data->thread->tasks[x].available = 1; 
    4975:	49 8b 70 38          	mov    0x38(%r8),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4979:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    497d:	48 8b 50 38          	mov    0x38(%rax),%rdx
      data->thread->tasks[x].available = 1; 
    4981:	31 c0                	xor    %eax,%eax
    4983:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4988:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4990:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4998:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    49a3:	48 05 00 02 00 00    	add    $0x200,%rax
    49a9:	48 39 c1             	cmp    %rax,%rcx
    49ac:	75 da                	jne    4988 <barriered_reset+0x38>
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    49ae:	49 8b 88 f8 00 00 00 	mov    0xf8(%r8),%rcx
    49b5:	8b 01                	mov    (%rcx),%eax
    49b7:	83 f8 ff             	cmp    $0xffffffff,%eax
    49ba:	74 0e                	je     49ca <barriered_reset+0x7a>
    49bc:	41 8b b8 c8 00 00 00 	mov    0xc8(%r8),%edi
    49c3:	8d 57 ff             	lea    -0x1(%rdi),%edx
    49c6:	39 d0                	cmp    %edx,%eax
    49c8:	74 06                	je     49d0 <barriered_reset+0x80>
}
    49ca:	31 c0                	xor    %eax,%eax
    49cc:	c3                   	ret
    49cd:	0f 1f 00             	nopl   (%rax)
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    49d0:	41 83 78 04 01       	cmpl   $0x1,0x4(%r8)
    49d5:	75 f3                	jne    49ca <barriered_reset+0x7a>
    data->thread->group_data->arrived++;
    49d7:	49 8b 80 e0 00 00 00 	mov    0xe0(%r8),%rax
    49de:	83 00 01             	addl   $0x1,(%rax)
    data->thread->global->request_group_sync = -1;
    49e1:	c7 01 ff ff ff ff    	movl   $0xffffffff,(%rcx)
    49e7:	eb e1                	jmp    49ca <barriered_reset+0x7a>
    49e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000049f0 <external_thread>:
void * external_thread(void *arg) {
    49f0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    49f4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    49f8:	0f 85 f8 00 00 00    	jne    4af6 <external_thread+0x106>
void * external_thread(void *arg) {
    49fe:	41 57                	push   %r15
    4a00:	4c 8d 3d fd 45 00 00 	lea    0x45fd(%rip),%r15        # 9004 <_IO_stdin_used+0x4>
    4a07:	41 56                	push   %r14
    4a09:	49 89 fe             	mov    %rdi,%r14
    4a0c:	41 55                	push   %r13
    4a0e:	41 54                	push   %r12
    4a10:	55                   	push   %rbp
    4a11:	53                   	push   %rbx
    4a12:	48 83 ec 08          	sub    $0x8,%rsp
    4a16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int b = 0; b < data->buffers_count; b++) {
    4a20:	41 8b 8e c4 00 00 00 	mov    0xc4(%r14),%ecx
    4a27:	85 c9                	test   %ecx,%ecx
    4a29:	7e 57                	jle    4a82 <external_thread+0x92>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4a2b:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4a2f:	45 31 ed             	xor    %r13d,%r13d
    4a32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4a38:	4e 8d 24 ed 00 00 00 00 	lea    0x0(,%r13,8),%r12
    4a40:	31 db                	xor    %ebx,%ebx
    4a42:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    4a46:	48 8b 06             	mov    (%rsi),%rax
    4a49:	8b 10                	mov    (%rax),%edx
    4a4b:	85 d2                	test   %edx,%edx
    4a4d:	7e 2a                	jle    4a79 <external_thread+0x89>
    4a4f:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    4a53:	48 89 dd             	mov    %rbx,%rbp
    4a56:	48 c1 e5 08          	shl    $0x8,%rbp
    4a5a:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4a5e:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    4a65:	45 85 c0             	test   %r8d,%r8d
    4a68:	74 36                	je     4aa0 <external_thread+0xb0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4a6a:	48 83 c3 01          	add    $0x1,%rbx
    4a6e:	39 da                	cmp    %ebx,%edx
    4a70:	7f e1                	jg     4a53 <external_thread+0x63>
    for (int b = 0; b < data->buffers_count; b++) {
    4a72:	41 8b 8e c4 00 00 00 	mov    0xc4(%r14),%ecx
    4a79:	49 83 c5 01          	add    $0x1,%r13
    4a7d:	44 39 e9             	cmp    %r13d,%ecx
    4a80:	7f b6                	jg     4a38 <external_thread+0x48>
  while (data->running == 1) {
    4a82:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    4a87:	74 97                	je     4a20 <external_thread+0x30>
}
    4a89:	48 83 c4 08          	add    $0x8,%rsp
    4a8d:	31 c0                	xor    %eax,%eax
    4a8f:	5b                   	pop    %rbx
    4a90:	5d                   	pop    %rbp
    4a91:	41 5c                	pop    %r12
    4a93:	41 5d                	pop    %r13
    4a95:	41 5e                	pop    %r14
    4a97:	41 5f                	pop    %r15
    4a99:	c3                   	ret
    4a9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    4aa0:	4c 89 38             	mov    %r15,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    4aa3:	48 8b 06             	mov    (%rsi),%rax
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4aa6:	48 83 c3 01          	add    $0x1,%rbx
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    4aaa:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4aae:	48 01 ef             	add    %rbp,%rdi
    4ab1:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    4ab8:	48 c1 e6 05          	shl    $0x5,%rsi
    4abc:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4ac3:	bf 04 00 00 00       	mov    $0x4,%edi
    4ac8:	e8 93 d8 ff ff       	call   2360 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4acd:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4ad1:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    4ad5:	48 8b 06             	mov    (%rsi),%rax
    4ad8:	48 8b 50 08          	mov    0x8(%rax),%rdx
    4adc:	c7 84 2a 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rdx,%rbp,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4ae7:	8b 10                	mov    (%rax),%edx
    4ae9:	39 da                	cmp    %ebx,%edx
    4aeb:	0f 8f 5e ff ff ff    	jg     4a4f <external_thread+0x5f>
    4af1:	e9 7c ff ff ff       	jmp    4a72 <external_thread+0x82>
}
    4af6:	31 c0                	xor    %eax,%eax
    4af8:	c3                   	ret
    4af9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004b00 <timer_thread>:
void* timer_thread(void *arg) {
    4b00:	f3 0f 1e fa          	endbr64
    4b04:	41 57                	push   %r15
    4b06:	48 8d 35 03 45 00 00 	lea    0x4503(%rip),%rsi        # 9010 <_IO_stdin_used+0x10>
    4b0d:	49 89 ff             	mov    %rdi,%r15
    4b10:	41 56                	push   %r14
    4b12:	41 55                	push   %r13
    4b14:	41 54                	push   %r12
    4b16:	55                   	push   %rbp
    4b17:	53                   	push   %rbx
    4b18:	48 83 ec 58          	sub    $0x58,%rsp
    4b1c:	8b 57 04             	mov    0x4(%rdi),%edx
    4b1f:	bf 01 00 00 00       	mov    $0x1,%edi
    4b24:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b2d:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    4b32:	31 c0                	xor    %eax,%eax
    4b34:	e8 87 d9 ff ff       	call   24c0 <__printf_chk@plt>
  struct timespec preempt = {
    4b39:	66 0f 6f 05 af 53 00 00 	movdqa 0x53af(%rip),%xmm0        # 9ef0 <_IO_stdin_used+0xef0>
    4b41:	ba a8 61 00 00       	mov    $0x61a8,%edx
    4b46:	31 c0                	xor    %eax,%eax
    4b48:	48 8d 35 d3 44 00 00 	lea    0x44d3(%rip),%rsi        # 9022 <_IO_stdin_used+0x22>
    4b4f:	bf 01 00 00 00       	mov    $0x1,%edi
    4b54:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4b59:	e8 62 d9 ff ff       	call   24c0 <__printf_chk@plt>
  while (data->running && n < times) {
    4b5e:	41 8b 47 44          	mov    0x44(%r15),%eax
    4b62:	89 c3                	mov    %eax,%ebx
    4b64:	85 c0                	test   %eax,%eax
    4b66:	0f 84 97 00 00 00    	je     4c03 <timer_thread+0x103>
  int n = 0;
    4b6c:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    4b6f:	31 db                	xor    %ebx,%ebx
    4b71:	49 89 e5             	mov    %rsp,%r13
    y++;
    4b74:	31 ed                	xor    %ebp,%ebp
    4b76:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    nanosleep(&preempt , &rem2);
    4b7b:	4c 89 e7             	mov    %r12,%rdi
    4b7e:	4c 89 ee             	mov    %r13,%rsi
    n++;
    4b81:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    4b85:	e8 26 d8 ff ff       	call   23b0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4b8a:	49 63 47 30          	movslq 0x30(%r15),%rax
    y++;
    4b8e:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4b91:	85 c0                	test   %eax,%eax
    4b93:	7e 4a                	jle    4bdf <timer_thread+0xdf>
    4b95:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4b99:	4c 63 c3             	movslq %ebx,%r8
    4b9c:	49 c1 e0 09          	shl    $0x9,%r8
    4ba0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4ba4:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4ba8:	48 8b 19             	mov    (%rcx),%rbx
    4bab:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4bad:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4bb1:	99                   	cltd
    4bb2:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4bb5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4bb9:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    4bbc:	48 63 d2             	movslq %edx,%rdx
    4bbf:	48 c1 e2 09          	shl    $0x9,%rdx
    4bc3:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4bce:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4bda:	49 39 c9             	cmp    %rcx,%r9
    4bdd:	75 c9                	jne    4ba8 <timer_thread+0xa8>
    if (y >= data->threads[0]->task_count) {
    4bdf:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
    4be3:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    y++;
    4be7:	89 fb                	mov    %edi,%ebx
    if (y >= data->threads[0]->task_count) {
    4be9:	48 8b 00             	mov    (%rax),%rax
    y++;
    4bec:	39 78 40             	cmp    %edi,0x40(%rax)
    4bef:	0f 4e dd             	cmovle %ebp,%ebx
  while (data->running && n < times) {
    4bf2:	85 c9                	test   %ecx,%ecx
    4bf4:	74 0d                	je     4c03 <timer_thread+0x103>
    4bf6:	41 81 fe a8 61 00 00 	cmp    $0x61a8,%r14d
    4bfd:	0f 85 78 ff ff ff    	jne    4b7b <timer_thread+0x7b>
    4c03:	48 8d 3d 2e 44 00 00 	lea    0x442e(%rip),%rdi        # 9038 <_IO_stdin_used+0x38>
    4c0a:	e8 31 d7 ff ff       	call   2340 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c0f:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4c13:	85 d2                	test   %edx,%edx
    4c15:	7e 6e                	jle    4c85 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    4c17:	49 63 47 40          	movslq 0x40(%r15),%rax
    4c1b:	85 c0                	test   %eax,%eax
    4c1d:	7e 66                	jle    4c85 <timer_thread+0x185>
    4c1f:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4c23:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4c27:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4c2f:	31 c9                	xor    %ecx,%ecx
    4c31:	48 89 c6             	mov    %rax,%rsi
    4c34:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4c38:	48 8b 40 38          	mov    0x38(%rax),%rax
    4c3c:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4c40:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4c46:	74 18                	je     4c60 <timer_thread+0x160>
    4c48:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4c52:	48 05 00 02 00 00    	add    $0x200,%rax
    4c58:	48 39 c2             	cmp    %rax,%rdx
    4c5b:	74 1f                	je     4c7c <timer_thread+0x17c>
    4c5d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->tasks[y].sending = 0;
    4c60:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4c6a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4c70:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4c77:	48 39 c2             	cmp    %rax,%rdx
    4c7a:	75 e4                	jne    4c60 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c7c:	48 83 c1 08          	add    $0x8,%rcx
    4c80:	48 39 cf             	cmp    %rcx,%rdi
    4c83:	75 af                	jne    4c34 <timer_thread+0x134>
  struct timespec drain = {
    4c85:	66 0f 6f 05 73 52 00 00 	movdqa 0x5273(%rip),%xmm0        # 9f00 <_IO_stdin_used+0xf00>
    4c8d:	41 89 dc             	mov    %ebx,%r12d
    4c90:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4c95:	49 63 47 28          	movslq 0x28(%r15),%rax
    y++;
    4c99:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    4c9e:	85 c0                	test   %eax,%eax
    4ca0:	7e 49                	jle    4ceb <timer_thread+0x1eb>
    4ca2:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4ca6:	49 63 ec             	movslq %r12d,%rbp
    4ca9:	48 c1 e5 09          	shl    $0x9,%rbp
    4cad:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4cb1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4cb8:	48 8b 19             	mov    (%rcx),%rbx
    4cbb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    4cbd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4cc1:	99                   	cltd
    4cc2:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4cc5:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4cc9:	48 63 d2             	movslq %edx,%rdx
    4ccc:	48 c1 e2 09          	shl    $0x9,%rdx
    4cd0:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4cdb:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4ce6:	49 39 c8             	cmp    %rcx,%r8
    4ce9:	75 cd                	jne    4cb8 <timer_thread+0x1b8>
    if (y >= data->threads[0]->task_count) {
    4ceb:	49 8b 77 18          	mov    0x18(%r15),%rsi
    y++;
    4cef:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    4cf2:	48 8b 06             	mov    (%rsi),%rax
    y++;
    4cf5:	39 78 40             	cmp    %edi,0x40(%rax)
    4cf8:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4cfc:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4d00:	85 ff                	test   %edi,%edi
    4d02:	0f 8e ac 01 00 00    	jle    4eb4 <timer_thread+0x3b4>
    4d08:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    4d0b:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    4d11:	4c 89 f5             	mov    %r14,%rbp
    4d14:	0f 1f 40 00          	nopl   0x0(%rax)
    4d18:	89 eb                	mov    %ebp,%ebx
      for (int y = 0 ; y < 2 ; y++) {
    4d1a:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    4d22:	45 31 f6             	xor    %r14d,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4d25:	85 ff                	test   %edi,%edi
    4d27:	7e 7f                	jle    4da8 <timer_thread+0x2a8>
    4d29:	4c 89 f6             	mov    %r14,%rsi
    4d2c:	48 63 cf             	movslq %edi,%rcx
    4d2f:	45 31 c0             	xor    %r8d,%r8d
    4d32:	48 c1 e6 09          	shl    $0x9,%rsi
    4d36:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (x == k) { continue; }
    4d40:	41 39 e8             	cmp    %ebp,%r8d
    4d43:	74 45                	je     4d8a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4d45:	49 8b 47 18          	mov    0x18(%r15),%rax
    4d49:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    4d4d:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4d51:	4c 89 c0             	mov    %r8,%rax
    4d54:	48 c1 e0 08          	shl    $0x8,%rax
    4d58:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4d60:	48 8b 10             	mov    (%rax),%rdx
    4d63:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    4d6a:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4d71:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4d78:	4d 85 c9             	test   %r9,%r9
    4d7b:	0f 8f 97 00 00 00    	jg     4e18 <timer_thread+0x318>
    4d81:	4d 85 db             	test   %r11,%r11
    4d84:	0f 8f 8e 00 00 00    	jg     4e18 <timer_thread+0x318>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4d8a:	49 83 c0 01          	add    $0x1,%r8
    4d8e:	4c 39 c1             	cmp    %r8,%rcx
    4d91:	75 ad                	jne    4d40 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    4d93:	49 83 fe 01          	cmp    $0x1,%r14
    4d97:	74 0f                	je     4da8 <timer_thread+0x2a8>
    4d99:	41 be 01 00 00 00    	mov    $0x1,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4d9f:	85 ff                	test   %edi,%edi
    4da1:	7f 86                	jg     4d29 <timer_thread+0x229>
    4da3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4da8:	48 83 c5 01          	add    $0x1,%rbp
    4dac:	39 ef                	cmp    %ebp,%edi
    4dae:	0f 8f 64 ff ff ff    	jg     4d18 <timer_thread+0x218>
    4db4:	44 89 d5             	mov    %r10d,%ebp
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4db7:	85 ff                	test   %edi,%edi
    4db9:	7e 3b                	jle    4df6 <timer_thread+0x2f6>
    4dbb:	31 db                	xor    %ebx,%ebx
    int all_waited = 1;
    4dbd:	bf 01 00 00 00       	mov    $0x1,%edi
    4dc2:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4dc6:	41 8b 57 40          	mov    0x40(%r15),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4dca:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4dce:	48 8b 40 38          	mov    0x38(%rax),%rax
    4dd2:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    4dd8:	39 d1                	cmp    %edx,%ecx
    4dda:	0f 8c a8 00 00 00    	jl     4e88 <timer_thread+0x388>
    4de0:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    4de6:	39 d0                	cmp    %edx,%eax
    4de8:	7c 6e                	jl     4e58 <timer_thread+0x358>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4dea:	48 83 c3 01          	add    $0x1,%rbx
    4dee:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4df2:	7f d6                	jg     4dca <timer_thread+0x2ca>
    4df4:	21 fd                	and    %edi,%ebp
    if (all_empty == 1 && all_waited == 1) {
    4df6:	85 ed                	test   %ebp,%ebp
    4df8:	0f 85 b6 00 00 00    	jne    4eb4 <timer_thread+0x3b4>
      nanosleep(&drain , &drainrem);
    4dfe:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4e03:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4e08:	e8 a3 d5 ff ff       	call   23b0 <nanosleep@plt>
    4e0d:	e9 83 fe ff ff       	jmp    4c95 <timer_thread+0x195>
    4e12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4e18:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    4e1e:	48 83 ec 08          	sub    $0x8,%rsp
    4e22:	bf 01 00 00 00       	mov    $0x1,%edi
    4e27:	44 89 f1             	mov    %r14d,%ecx
    4e2a:	48 8d 35 2c 42 00 00 	lea    0x422c(%rip),%rsi        # 905d <_IO_stdin_used+0x5d>
    4e31:	50                   	push   %rax
    4e32:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    4e38:	89 da                	mov    %ebx,%edx
    4e3a:	50                   	push   %rax
    4e3b:	31 c0                	xor    %eax,%eax
    4e3d:	41 53                	push   %r11
    4e3f:	e8 7c d6 ff ff       	call   24c0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4e44:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4e48:	48 83 c4 20          	add    $0x20,%rsp
            all_empty = 0;
    4e4c:	45 31 d2             	xor    %r10d,%r10d
    4e4f:	e9 3f ff ff ff       	jmp    4d93 <timer_thread+0x293>
    4e54:	0f 1f 40 00          	nopl   0x0(%rax)
    4e58:	89 c2                	mov    %eax,%edx
    4e5a:	bf 01 00 00 00       	mov    $0x1,%edi
    4e5f:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4e61:	48 83 c3 01          	add    $0x1,%rbx
    4e65:	48 8d 35 ef 45 00 00 	lea    0x45ef(%rip),%rsi        # 945b <_IO_stdin_used+0x45b>
    4e6c:	e8 4f d6 ff ff       	call   24c0 <__printf_chk@plt>
          all_waited = 0; 
    4e71:	31 ff                	xor    %edi,%edi
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4e73:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4e77:	0f 8f 45 ff ff ff    	jg     4dc2 <timer_thread+0x2c2>
    4e7d:	e9 72 ff ff ff       	jmp    4df4 <timer_thread+0x2f4>
    4e82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4e88:	89 ca                	mov    %ecx,%edx
    4e8a:	48 8d 35 ca 45 00 00 	lea    0x45ca(%rip),%rsi        # 945b <_IO_stdin_used+0x45b>
    4e91:	bf 01 00 00 00       	mov    $0x1,%edi
    4e96:	31 c0                	xor    %eax,%eax
    4e98:	e8 23 d6 ff ff       	call   24c0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4e9d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4ea1:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    4ea5:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4ea7:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4eab:	48 8b 40 38          	mov    0x38(%rax),%rax
    4eaf:	e9 2c ff ff ff       	jmp    4de0 <timer_thread+0x2e0>
    4eb4:	48 8d 3d 99 41 00 00 	lea    0x4199(%rip),%rdi        # 9054 <_IO_stdin_used+0x54>
    4ebb:	e8 80 d4 ff ff       	call   2340 <puts@plt>
  while (data->running) {
    4ec0:	41 8b 57 44          	mov    0x44(%r15),%edx
    4ec4:	85 d2                	test   %edx,%edx
    4ec6:	0f 84 e8 00 00 00    	je     4fb4 <timer_thread+0x4b4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4ecc:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4ed0:	31 db                	xor    %ebx,%ebx
    4ed2:	48 8d 2d a1 41 00 00 	lea    0x41a1(%rip),%rbp        # 907a <_IO_stdin_used+0x7a>
    4ed9:	4c 8d 25 b5 41 00 00 	lea    0x41b5(%rip),%r12        # 9095 <_IO_stdin_used+0x95>
    4ee0:	85 c0                	test   %eax,%eax
    4ee2:	7e 38                	jle    4f1c <timer_thread+0x41c>
    4ee4:	0f 1f 40 00          	nopl   0x0(%rax)
    4ee8:	31 c0                	xor    %eax,%eax
    4eea:	89 da                	mov    %ebx,%edx
    4eec:	48 89 ee             	mov    %rbp,%rsi
    4eef:	bf 01 00 00 00       	mov    $0x1,%edi
    4ef4:	e8 c7 d5 ff ff       	call   24c0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4ef9:	49 8b 47 18          	mov    0x18(%r15),%rax
    4efd:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4f01:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4f05:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4f0c:	0f 84 cf 00 00 00    	je     4fe1 <timer_thread+0x4e1>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4f12:	48 83 c3 01          	add    $0x1,%rbx
    4f16:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4f1a:	7f cc                	jg     4ee8 <timer_thread+0x3e8>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4f1c:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4f20:	85 d2                	test   %edx,%edx
    4f22:	7e 7c                	jle    4fa0 <timer_thread+0x4a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    4f24:	41 8b 47 40          	mov    0x40(%r15),%eax
    4f28:	85 c0                	test   %eax,%eax
    4f2a:	7e 74                	jle    4fa0 <timer_thread+0x4a0>
    4f2c:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4f2f:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4f33:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4f3b:	31 c9                	xor    %ecx,%ecx
    4f3d:	48 c1 e6 09          	shl    $0x9,%rsi
    4f41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4f48:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4f4c:	48 8b 40 38          	mov    0x38(%rax),%rax
    4f50:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4f54:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4f5a:	74 1c                	je     4f78 <timer_thread+0x478>
    4f5c:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4f66:	48 05 00 02 00 00    	add    $0x200,%rax
    4f6c:	48 39 d0             	cmp    %rdx,%rax
    4f6f:	74 26                	je     4f97 <timer_thread+0x497>
    4f71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4f78:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4f82:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4f88:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4f92:	48 39 d0             	cmp    %rdx,%rax
    4f95:	75 e1                	jne    4f78 <timer_thread+0x478>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4f97:	48 83 c1 08          	add    $0x8,%rcx
    4f9b:	48 39 cf             	cmp    %rcx,%rdi
    4f9e:	75 a8                	jne    4f48 <timer_thread+0x448>
    4fa0:	48 8d 3d 00 41 00 00 	lea    0x4100(%rip),%rdi        # 90a7 <_IO_stdin_used+0xa7>
    4fa7:	e8 94 d3 ff ff       	call   2340 <puts@plt>
    data->running = 0;
    4fac:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    4fb4:	48 8d 3d f3 40 00 00 	lea    0x40f3(%rip),%rdi        # 90ae <_IO_stdin_used+0xae>
    4fbb:	e8 80 d3 ff ff       	call   2340 <puts@plt>
}
    4fc0:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    4fc5:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4fce:	75 41                	jne    5011 <timer_thread+0x511>
    4fd0:	48 83 c4 58          	add    $0x58,%rsp
    4fd4:	31 c0                	xor    %eax,%eax
    4fd6:	5b                   	pop    %rbx
    4fd7:	5d                   	pop    %rbp
    4fd8:	41 5c                	pop    %r12
    4fda:	41 5d                	pop    %r13
    4fdc:	41 5e                	pop    %r14
    4fde:	41 5f                	pop    %r15
    4fe0:	c3                   	ret
    4fe1:	4c 89 e7             	mov    %r12,%rdi
    4fe4:	e8 57 d3 ff ff       	call   2340 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4fe9:	49 8b 47 18          	mov    0x18(%r15),%rax
    4fed:	be 01 00 00 00       	mov    $0x1,%esi
    4ff2:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4ff6:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    4ffa:	8b 78 68             	mov    0x68(%rax),%edi
    4ffd:	e8 6e d4 ff ff       	call   2470 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    5002:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    5006:	0f 8f dc fe ff ff    	jg     4ee8 <timer_thread+0x3e8>
    500c:	e9 0b ff ff ff       	jmp    4f1c <timer_thread+0x41c>
}
    5011:	e8 7a d3 ff ff       	call   2390 <__stack_chk_fail@plt>
    5016:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005020 <minf>:
int minf(int a, int b) {
    5020:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    5024:	39 f7                	cmp    %esi,%edi
    5026:	89 f0                	mov    %esi,%eax
    5028:	0f 4e c7             	cmovle %edi,%eax
}
    502b:	c3                   	ret
    502c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005030 <maxf>:
int maxf(int a, int b) {
    5030:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    5034:	39 f7                	cmp    %esi,%edi
    5036:	89 f0                	mov    %esi,%eax
    5038:	0f 4d c7             	cmovge %edi,%eax
}
    503b:	c3                   	ret
    503c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005040 <strtolower>:
void strtolower(char *str) {
    5040:	f3 0f 1e fa          	endbr64
    5044:	55                   	push   %rbp
    5045:	53                   	push   %rbx
    5046:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    504a:	48 0f be 1f          	movsbq (%rdi),%rbx
    504e:	84 db                	test   %bl,%bl
    5050:	74 24                	je     5076 <strtolower+0x36>
    5052:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    5055:	e8 56 d5 ff ff       	call   25b0 <__ctype_tolower_loc@plt>
    505a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5060:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    5063:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    5067:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    506a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    506d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    5072:	84 db                	test   %bl,%bl
    5074:	75 ea                	jne    5060 <strtolower+0x20>
}
    5076:	48 83 c4 08          	add    $0x8,%rsp
    507a:	5b                   	pop    %rbx
    507b:	5d                   	pop    %rbp
    507c:	c3                   	ret
    507d:	0f 1f 00             	nopl   (%rax)

0000000000005080 <zh_malloc>:
void *zh_malloc(size_t size) {
    5080:	f3 0f 1e fa          	endbr64
    5084:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    5088:	e8 f3 d3 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    508d:	48 85 c0             	test   %rax,%rax
    5090:	74 05                	je     5097 <zh_malloc+0x17>
}
    5092:	48 83 c4 08          	add    $0x8,%rsp
    5096:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5097:	48 8b 0d 82 6f 00 00 	mov    0x6f82(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    509e:	ba 28 00 00 00       	mov    $0x28,%edx
    50a3:	be 01 00 00 00       	mov    $0x1,%esi
    50a8:	48 8d 3d 79 46 00 00 	lea    0x4679(%rip),%rdi        # 9728 <_IO_stdin_used+0x728>
    50af:	e8 8c d4 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    50b4:	bf 01 00 00 00       	mov    $0x1,%edi
    50b9:	e8 62 d4 ff ff       	call   2520 <exit@plt>
    50be:	66 90                	xchg   %ax,%ax

00000000000050c0 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    50c0:	f3 0f 1e fa          	endbr64
    50c4:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    50c5:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    50ca:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    50cd:	e8 ee d2 ff ff       	call   23c0 <strrchr@plt>
    if (!dot || dot == filename)
    50d2:	48 85 c0             	test   %rax,%rax
    50d5:	74 11                	je     50e8 <get_filename_ext+0x28>
    50d7:	48 39 c3             	cmp    %rax,%rbx
    50da:	74 0c                	je     50e8 <get_filename_ext+0x28>
    return dot + 1;
    50dc:	48 83 c0 01          	add    $0x1,%rax
}
    50e0:	5b                   	pop    %rbx
    50e1:	c3                   	ret
    50e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    50e8:	48 8d 05 07 40 00 00 	lea    0x4007(%rip),%rax        # 90f6 <_IO_stdin_used+0xf6>
}
    50ef:	5b                   	pop    %rbx
    50f0:	c3                   	ret
    50f1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    50fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005100 <send_headers>:
void send_headers(struct KernelThread *data, struct Buffers *buffers, const char *path, off_t len, struct iovec *iov) {
    5100:	f3 0f 1e fa          	endbr64
    5104:	41 55                	push   %r13
    5106:	48 89 d6             	mov    %rdx,%rsi
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5109:	ba 00 04 00 00       	mov    $0x400,%edx
    510e:	49 89 cd             	mov    %rcx,%r13
    5111:	41 54                	push   %r12
    5113:	55                   	push   %rbp
    5114:	4c 89 c5             	mov    %r8,%rbp
    5117:	53                   	push   %rbx
    5118:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    511f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5128:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    5130:	31 c0                	xor    %eax,%eax
    5132:	49 89 e4             	mov    %rsp,%r12
    5135:	4c 89 e7             	mov    %r12,%rdi
    5138:	e8 63 d3 ff ff       	call   24a0 <__strcpy_chk@plt>
    for (; *str; ++str)
    513d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    5142:	84 db                	test   %bl,%bl
    5144:	74 24                	je     516a <send_headers+0x6a>
        *str = (char)tolower(*str);
    5146:	e8 65 d4 ff ff       	call   25b0 <__ctype_tolower_loc@plt>
    514b:	48 8b 08             	mov    (%rax),%rcx
    514e:	4c 89 e0             	mov    %r12,%rax
    5151:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5158:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    515b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    515f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    5162:	48 0f be 18          	movsbq (%rax),%rbx
    5166:	84 db                	test   %bl,%bl
    5168:	75 ee                	jne    5158 <send_headers+0x58>
    void *buf = malloc(size);
    516a:	bf 11 00 00 00       	mov    $0x11,%edi
    516f:	e8 0c d3 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    5174:	48 85 c0             	test   %rax,%rax
    5177:	0f 84 7e 04 00 00    	je     55fb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    517d:	66 0f 6f 05 8b 4d 00 00 	movdqa 0x4d8b(%rip),%xmm0        # 9f10 <_IO_stdin_used+0xf10>
    iov[0].iov_base = zh_malloc(slen);
    5185:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    5189:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    518e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    5196:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    519a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    519d:	e8 de d2 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    51a2:	48 85 c0             	test   %rax,%rax
    51a5:	0f 84 50 04 00 00    	je     55fb <send_headers+0x4fb>
    51ab:	66 0f 6f 05 6d 4d 00 00 	movdqa 0x4d6d(%rip),%xmm0        # 9f20 <_IO_stdin_used+0xf20>
    iov[1].iov_base = zh_malloc(slen);
    51b3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    51b7:	4c 89 e7             	mov    %r12,%rdi
    51ba:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    51c4:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    51cc:	0f 11 00             	movups %xmm0,(%rax)
    51cf:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    51d3:	be 2e 00 00 00       	mov    $0x2e,%esi
    51d8:	e8 e3 d1 ff ff       	call   23c0 <strrchr@plt>
    if (!dot || dot == filename)
    51dd:	48 85 c0             	test   %rax,%rax
    51e0:	0f 84 ea 02 00 00    	je     54d0 <send_headers+0x3d0>
    51e6:	4c 39 e0             	cmp    %r12,%rax
    51e9:	0f 84 e1 02 00 00    	je     54d0 <send_headers+0x3d0>
    return dot + 1;
    51ef:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    51f3:	48 8d 3d ca 3e 00 00 	lea    0x3eca(%rip),%rdi        # 90c4 <_IO_stdin_used+0xc4>
    51fa:	48 89 de             	mov    %rbx,%rsi
    51fd:	e8 1e d2 ff ff       	call   2420 <strcmp@plt>
    5202:	85 c0                	test   %eax,%eax
    5204:	75 20                	jne    5226 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5206:	66 0f 6f 05 22 4d 00 00 	movdqa 0x4d22(%rip),%xmm0        # 9f30 <_IO_stdin_used+0xf30>
    520e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5216:	66 0f 6f 05 22 4d 00 00 	movdqa 0x4d22(%rip),%xmm0        # 9f40 <_IO_stdin_used+0xf40>
    521e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    5226:	48 89 de             	mov    %rbx,%rsi
    5229:	48 8d 3d 98 3e 00 00 	lea    0x3e98(%rip),%rdi        # 90c8 <_IO_stdin_used+0xc8>
    5230:	e8 eb d1 ff ff       	call   2420 <strcmp@plt>
    5235:	85 c0                	test   %eax,%eax
    5237:	75 20                	jne    5259 <send_headers+0x159>
    5239:	66 0f 6f 05 ef 4c 00 00 	movdqa 0x4cef(%rip),%xmm0        # 9f30 <_IO_stdin_used+0xf30>
    5241:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5249:	66 0f 6f 05 ef 4c 00 00 	movdqa 0x4cef(%rip),%xmm0        # 9f40 <_IO_stdin_used+0xf40>
    5251:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    5259:	48 89 de             	mov    %rbx,%rsi
    525c:	48 8d 3d 6a 3e 00 00 	lea    0x3e6a(%rip),%rdi        # 90cd <_IO_stdin_used+0xcd>
    5263:	e8 b8 d1 ff ff       	call   2420 <strcmp@plt>
    5268:	85 c0                	test   %eax,%eax
    526a:	0f 84 10 02 00 00    	je     5480 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    5270:	48 89 de             	mov    %rbx,%rsi
    5273:	48 8d 3d 57 3e 00 00 	lea    0x3e57(%rip),%rdi        # 90d1 <_IO_stdin_used+0xd1>
    527a:	e8 a1 d1 ff ff       	call   2420 <strcmp@plt>
    527f:	85 c0                	test   %eax,%eax
    5281:	0f 84 a9 02 00 00    	je     5530 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    5287:	48 89 de             	mov    %rbx,%rsi
    528a:	48 8d 3d 44 3e 00 00 	lea    0x3e44(%rip),%rdi        # 90d5 <_IO_stdin_used+0xd5>
    5291:	e8 8a d1 ff ff       	call   2420 <strcmp@plt>
    5296:	85 c0                	test   %eax,%eax
    5298:	0f 84 6a 02 00 00    	je     5508 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    529e:	48 89 de             	mov    %rbx,%rsi
    52a1:	48 8d 3d 8a 3e 00 00 	lea    0x3e8a(%rip),%rdi        # 9132 <_IO_stdin_used+0x132>
    52a8:	e8 73 d1 ff ff       	call   2420 <strcmp@plt>
    52ad:	85 c0                	test   %eax,%eax
    52af:	0f 84 2b 02 00 00    	je     54e0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    52b5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    52b8:	0f 84 52 01 00 00    	je     5410 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    52be:	48 89 de             	mov    %rbx,%rsi
    52c1:	48 8d 3d 11 3e 00 00 	lea    0x3e11(%rip),%rdi        # 90d9 <_IO_stdin_used+0xd9>
    52c8:	e8 53 d1 ff ff       	call   2420 <strcmp@plt>
    52cd:	85 c0                	test   %eax,%eax
    52cf:	0f 84 ab 02 00 00    	je     5580 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    52d5:	48 89 de             	mov    %rbx,%rsi
    52d8:	48 8d 3d fe 3d 00 00 	lea    0x3dfe(%rip),%rdi        # 90dd <_IO_stdin_used+0xdd>
    52df:	e8 3c d1 ff ff       	call   2420 <strcmp@plt>
    52e4:	85 c0                	test   %eax,%eax
    52e6:	0f 84 6c 02 00 00    	je     5558 <send_headers+0x458>
    slen = strlen(send_buffer);
    52ec:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    52f4:	4c 89 e7             	mov    %r12,%rdi
    52f7:	e8 84 d0 ff ff       	call   2380 <strlen@plt>
    void *buf = malloc(size);
    52fc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    52ff:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    5302:	e8 79 d1 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    5307:	48 85 c0             	test   %rax,%rax
    530a:	0f 84 eb 02 00 00    	je     55fb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    5310:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    5314:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5318:	83 fb 08             	cmp    $0x8,%ebx
    531b:	0f 83 3f 01 00 00    	jae    5460 <send_headers+0x360>
    5321:	f6 c3 04             	test   $0x4,%bl
    5324:	0f 85 7b 02 00 00    	jne    55a5 <send_headers+0x4a5>
    532a:	85 db                	test   %ebx,%ebx
    532c:	74 13                	je     5341 <send_headers+0x241>
    532e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    5336:	88 10                	mov    %dl,(%rax)
    5338:	f6 c3 02             	test   $0x2,%bl
    533b:	0f 85 96 02 00 00    	jne    55d7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    5341:	4d 89 e8             	mov    %r13,%r8
    5344:	48 8d 0d 96 3d 00 00 	lea    0x3d96(%rip),%rcx        # 90e1 <_IO_stdin_used+0xe1>
    534b:	4c 89 e7             	mov    %r12,%rdi
    534e:	31 c0                	xor    %eax,%eax
    5350:	ba 00 04 00 00       	mov    $0x400,%edx
    5355:	be 01 00 00 00       	mov    $0x1,%esi
    535a:	e8 61 d2 ff ff       	call   25c0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    535f:	4c 89 e7             	mov    %r12,%rdi
    5362:	e8 19 d0 ff ff       	call   2380 <strlen@plt>
    void *buf = malloc(size);
    5367:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    536a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    536d:	e8 0e d1 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    5372:	48 85 c0             	test   %rax,%rax
    5375:	0f 84 80 02 00 00    	je     55fb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    537b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    537f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    5383:	83 fb 08             	cmp    $0x8,%ebx
    5386:	0f 83 1c 01 00 00    	jae    54a8 <send_headers+0x3a8>
    538c:	f6 c3 04             	test   $0x4,%bl
    538f:	0f 85 29 02 00 00    	jne    55be <send_headers+0x4be>
    5395:	85 db                	test   %ebx,%ebx
    5397:	74 13                	je     53ac <send_headers+0x2ac>
    5399:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    53a1:	88 10                	mov    %dl,(%rax)
    53a3:	f6 c3 02             	test   $0x2,%bl
    53a6:	0f 85 3d 02 00 00    	jne    55e9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    53ac:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    53b1:	bf 02 00 00 00       	mov    $0x2,%edi
    53b6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    53be:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    53c6:	e8 b5 d0 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    53cb:	48 85 c0             	test   %rax,%rax
    53ce:	0f 84 27 02 00 00    	je     55fb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    53d4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    53dc:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    53e0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    53e8:	66 89 10             	mov    %dx,(%rax)
}
    53eb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    53f3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    53fc:	0f 85 20 02 00 00    	jne    5622 <send_headers+0x522>
    5402:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    5409:	5b                   	pop    %rbx
    540a:	5d                   	pop    %rbp
    540b:	41 5c                	pop    %r12
    540d:	41 5d                	pop    %r13
    540f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    5410:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    5414:	0f 85 a4 fe ff ff    	jne    52be <send_headers+0x1be>
    541a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    541e:	0f 85 9a fe ff ff    	jne    52be <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5424:	66 0f 6f 05 64 4b 00 00 	movdqa 0x4b64(%rip),%xmm0        # 9f90 <_IO_stdin_used+0xf90>
    542c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    5436:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    543e:	66 0f 6f 05 5a 4b 00 00 	movdqa 0x4b5a(%rip),%xmm0        # 9fa0 <_IO_stdin_used+0xfa0>
    5446:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    544e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    5456:	e9 63 fe ff ff       	jmp    52be <send_headers+0x1be>
    545b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5460:	89 da                	mov    %ebx,%edx
    5462:	48 89 c7             	mov    %rax,%rdi
    5465:	4c 89 e6             	mov    %r12,%rsi
    5468:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    546d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5472:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5475:	c1 e9 03             	shr    $0x3,%ecx
    5478:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    547b:	e9 c1 fe ff ff       	jmp    5341 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5480:	66 0f 6f 05 a8 4a 00 00 	movdqa 0x4aa8(%rip),%xmm0        # 9f30 <_IO_stdin_used+0xf30>
    5488:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5490:	66 0f 6f 05 b8 4a 00 00 	movdqa 0x4ab8(%rip),%xmm0        # 9f50 <_IO_stdin_used+0xf50>
    5498:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    54a0:	e9 cb fd ff ff       	jmp    5270 <send_headers+0x170>
    54a5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    54a8:	89 da                	mov    %ebx,%edx
    54aa:	48 89 c7             	mov    %rax,%rdi
    54ad:	4c 89 e6             	mov    %r12,%rsi
    54b0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    54b5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    54ba:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    54bd:	c1 e9 03             	shr    $0x3,%ecx
    54c0:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    54c3:	e9 e4 fe ff ff       	jmp    53ac <send_headers+0x2ac>
    54c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    54d0:	48 8d 1d 1f 3c 00 00 	lea    0x3c1f(%rip),%rbx        # 90f6 <_IO_stdin_used+0xf6>
    54d7:	e9 94 fd ff ff       	jmp    5270 <send_headers+0x170>
    54dc:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    54e0:	66 0f 6f 05 88 4a 00 00 	movdqa 0x4a88(%rip),%xmm0        # 9f70 <_IO_stdin_used+0xf70>
    54e8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    54f0:	66 0f 6f 05 88 4a 00 00 	movdqa 0x4a88(%rip),%xmm0        # 9f80 <_IO_stdin_used+0xf80>
    54f8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5500:	e9 b0 fd ff ff       	jmp    52b5 <send_headers+0x1b5>
    5505:	0f 1f 00             	nopl   (%rax)
    5508:	66 0f 6f 05 60 4a 00 00 	movdqa 0x4a60(%rip),%xmm0        # 9f70 <_IO_stdin_used+0xf70>
    5510:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5518:	66 0f 6f 05 60 4a 00 00 	movdqa 0x4a60(%rip),%xmm0        # 9f80 <_IO_stdin_used+0xf80>
    5520:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5528:	e9 71 fd ff ff       	jmp    529e <send_headers+0x19e>
    552d:	0f 1f 00             	nopl   (%rax)
    5530:	66 0f 6f 05 f8 49 00 00 	movdqa 0x49f8(%rip),%xmm0        # 9f30 <_IO_stdin_used+0xf30>
    5538:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5540:	66 0f 6f 05 18 4a 00 00 	movdqa 0x4a18(%rip),%xmm0        # 9f60 <_IO_stdin_used+0xf60>
    5548:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5550:	e9 32 fd ff ff       	jmp    5287 <send_headers+0x187>
    5555:	0f 1f 00             	nopl   (%rax)
    5558:	66 0f 6f 05 10 4a 00 00 	movdqa 0x4a10(%rip),%xmm0        # 9f70 <_IO_stdin_used+0xf70>
    5560:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5568:	66 0f 6f 05 50 4a 00 00 	movdqa 0x4a50(%rip),%xmm0        # 9fc0 <_IO_stdin_used+0xfc0>
    5570:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5578:	e9 6f fd ff ff       	jmp    52ec <send_headers+0x1ec>
    557d:	0f 1f 00             	nopl   (%rax)
    5580:	66 0f 6f 05 e8 49 00 00 	movdqa 0x49e8(%rip),%xmm0        # 9f70 <_IO_stdin_used+0xf70>
    5588:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5590:	66 0f 6f 05 18 4a 00 00 	movdqa 0x4a18(%rip),%xmm0        # 9fb0 <_IO_stdin_used+0xfb0>
    5598:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    55a0:	e9 30 fd ff ff       	jmp    52d5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    55a5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    55ac:	89 db                	mov    %ebx,%ebx
    55ae:	89 10                	mov    %edx,(%rax)
    55b0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    55b5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    55b9:	e9 83 fd ff ff       	jmp    5341 <send_headers+0x241>
    55be:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    55c5:	89 db                	mov    %ebx,%ebx
    55c7:	89 10                	mov    %edx,(%rax)
    55c9:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    55ce:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    55d2:	e9 d5 fd ff ff       	jmp    53ac <send_headers+0x2ac>
    55d7:	89 db                	mov    %ebx,%ebx
    55d9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    55df:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    55e4:	e9 58 fd ff ff       	jmp    5341 <send_headers+0x241>
    55e9:	89 db                	mov    %ebx,%ebx
    55eb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    55f1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    55f6:	e9 b1 fd ff ff       	jmp    53ac <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    55fb:	48 8b 0d 1e 6a 00 00 	mov    0x6a1e(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5602:	ba 28 00 00 00       	mov    $0x28,%edx
    5607:	be 01 00 00 00       	mov    $0x1,%esi
    560c:	48 8d 3d 15 41 00 00 	lea    0x4115(%rip),%rdi        # 9728 <_IO_stdin_used+0x728>
    5613:	e8 28 cf ff ff       	call   2540 <fwrite@plt>
        exit(1);
    5618:	bf 01 00 00 00       	mov    $0x1,%edi
    561d:	e8 fe ce ff ff       	call   2520 <exit@plt>
}
    5622:	e8 69 cd ff ff       	call   2390 <__stack_chk_fail@plt>
    5627:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005630 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5630:	f3 0f 1e fa          	endbr64
    5634:	41 55                	push   %r13
    5636:	49 89 d5             	mov    %rdx,%r13
    5639:	41 54                	push   %r12
    563b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    563e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5641:	55                   	push   %rbp
    5642:	53                   	push   %rbx
    5643:	48 89 f3             	mov    %rsi,%rbx
    5646:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    564a:	e8 31 ce ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    564f:	48 85 c0             	test   %rax,%rax
    5652:	74 6b                	je     56bf <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    5654:	4c 89 e7             	mov    %r12,%rdi
    5657:	48 89 c5             	mov    %rax,%rbp
    565a:	31 f6                	xor    %esi,%esi
    565c:	31 c0                	xor    %eax,%eax
    565e:	e8 8d ce ff ff       	call   24f0 <open@plt>
    5663:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    5666:	85 c0                	test   %eax,%eax
    5668:	0f 88 88 cf ff ff    	js     25f6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    566e:	48 89 da             	mov    %rbx,%rdx
    5671:	48 89 ee             	mov    %rbp,%rsi
    5674:	89 c7                	mov    %eax,%edi
    5676:	e8 85 cd ff ff       	call   2400 <read@plt>
    if (ret < file_size) {
    567b:	48 98                	cltq
    567d:	48 39 d8             	cmp    %rbx,%rax
    5680:	7c 1e                	jl     56a0 <copy_file_contents+0x70>
    close(fd);
    5682:	44 89 e7             	mov    %r12d,%edi
    5685:	e8 56 cd ff ff       	call   23e0 <close@plt>
    iov->iov_base = buf;
    568a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    568e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    5692:	48 83 c4 08          	add    $0x8,%rsp
    5696:	5b                   	pop    %rbx
    5697:	5d                   	pop    %rbp
    5698:	41 5c                	pop    %r12
    569a:	41 5d                	pop    %r13
    569c:	c3                   	ret
    569d:	0f 1f 00             	nopl   (%rax)
    56a0:	48 8b 0d 79 69 00 00 	mov    0x6979(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    56a7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    56ac:	be 01 00 00 00       	mov    $0x1,%esi
    56b1:	48 8d 3d 3f 3a 00 00 	lea    0x3a3f(%rip),%rdi        # 90f7 <_IO_stdin_used+0xf7>
    56b8:	e8 83 ce ff ff       	call   2540 <fwrite@plt>
    56bd:	eb c3                	jmp    5682 <copy_file_contents+0x52>
    56bf:	48 8b 0d 5a 69 00 00 	mov    0x695a(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    56c6:	ba 28 00 00 00       	mov    $0x28,%edx
    56cb:	be 01 00 00 00       	mov    $0x1,%esi
    56d0:	48 8d 3d 51 40 00 00 	lea    0x4051(%rip),%rdi        # 9728 <_IO_stdin_used+0x728>
    56d7:	e8 64 ce ff ff       	call   2540 <fwrite@plt>
        exit(1);
    56dc:	bf 01 00 00 00       	mov    $0x1,%edi
    56e1:	e8 3a ce ff ff       	call   2520 <exit@plt>
    56e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000056f0 <add_write_request>:
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    56f0:	f3 0f 1e fa          	endbr64
    56f4:	41 55                	push   %r13
    struct Write *write = calloc(1, sizeof(struct Write));
    56f6:	be 10 00 00 00       	mov    $0x10,%esi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    56fb:	49 89 fd             	mov    %rdi,%r13
    struct Write *write = calloc(1, sizeof(struct Write));
    56fe:	bf 01 00 00 00       	mov    $0x1,%edi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    5703:	41 54                	push   %r12
    5705:	55                   	push   %rbp
    5706:	53                   	push   %rbx
    5707:	48 89 d3             	mov    %rdx,%rbx
    570a:	48 83 ec 08          	sub    $0x8,%rsp
    struct Write *write = calloc(1, sizeof(struct Write));
    570e:	e8 fd cc ff ff       	call   2410 <calloc@plt>
    req->event_type = EVENT_TYPE_WRITE;
    5713:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5719:	48 8d 3d f2 39 00 00 	lea    0x39f2(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    struct Write *write = calloc(1, sizeof(struct Write));
    5720:	49 89 c4             	mov    %rax,%r12
    write->client_socket = req->client_socket;
    5723:	8b 43 08             	mov    0x8(%rbx),%eax
    write->request = req;
    5726:	49 89 1c 24          	mov    %rbx,(%r12)
    write->client_socket = req->client_socket;
    572a:	41 89 44 24 08       	mov    %eax,0x8(%r12)
    572f:	e8 0c cc ff ff       	call   2340 <puts@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_WRITE, write);
    5734:	49 63 ad 10 01 00 00 	movslq 0x110(%r13),%rbp
    573b:	48 c1 e5 04          	shl    $0x4,%rbp
    573f:	49 03 ad 08 01 00 00 	add    0x108(%r13),%rbp
  while (data->running == 1) {
    5746:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
    574b:	75 6e                	jne    57bb <add_write_request+0xcb>
      for (int x = 0 ; x < buffers->count ; x++) {
    574d:	48 63 45 00          	movslq 0x0(%rbp),%rax
    5751:	85 c0                	test   %eax,%eax
    5753:	7e f1                	jle    5746 <add_write_request+0x56>
        if (buffers->buffer[x].available == 0) {
    5755:	48 8b 55 08          	mov    0x8(%rbp),%rdx
    5759:	48 c1 e0 08          	shl    $0x8,%rax
    575d:	31 db                	xor    %ebx,%ebx
    575f:	eb 13                	jmp    5774 <add_write_request+0x84>
    5761:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    5768:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    576f:	48 39 c3             	cmp    %rax,%rbx
    5772:	74 d2                	je     5746 <add_write_request+0x56>
        if (buffers->buffer[x].available == 0) {
    5774:	8b 8c 1a 80 00 00 00 	mov    0x80(%rdx,%rbx,1),%ecx
    577b:	85 c9                	test   %ecx,%ecx
    577d:	75 e9                	jne    5768 <add_write_request+0x78>
    577f:	8b 8c 1a 98 00 00 00 	mov    0x98(%rdx,%rbx,1),%ecx
    5786:	49 8b 95 18 01 00 00 	mov    0x118(%r13),%rdx
    578d:	bf 01 00 00 00       	mov    $0x1,%edi
    5792:	31 c0                	xor    %eax,%eax
    5794:	48 8d 35 85 39 00 00 	lea    0x3985(%rip),%rsi        # 9120 <_IO_stdin_used+0x120>
    579b:	e8 20 cd ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    57a0:	48 03 5d 08          	add    0x8(%rbp),%rbx
    57a4:	4c 89 23             	mov    %r12,(%rbx)
          buffers->buffer[x].kind = kind;
    57a7:	c7 83 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%rbx)
          buffers->buffer[x].available = 1;
    57b1:	c7 83 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbx)
}
    57bb:	48 83 c4 08          	add    $0x8,%rsp
    57bf:	31 c0                	xor    %eax,%eax
    57c1:	5b                   	pop    %rbx
    57c2:	5d                   	pop    %rbp
    57c3:	41 5c                	pop    %r12
    57c5:	41 5d                	pop    %r13
    57c7:	c3                   	ret
    57c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

00000000000057d0 <add_read_request>:
int add_read_request(struct KernelThread *data, struct Buffers *buffers, int client_socket, struct io_uring *ring) {
    57d0:	f3 0f 1e fa          	endbr64
    57d4:	41 55                	push   %r13
    57d6:	41 89 d5             	mov    %edx,%r13d
    57d9:	41 54                	push   %r12
    57db:	55                   	push   %rbp
    57dc:	53                   	push   %rbx
    57dd:	48 89 cb             	mov    %rcx,%rbx
    57e0:	48 83 ec 08          	sub    $0x8,%rsp
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    57e4:	8b 41 44             	mov    0x44(%rcx),%eax
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    57e7:	48 8b 13             	mov    (%rbx),%rdx
	if (ring->flags & IORING_SETUP_SQE128)
    57ea:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    57f0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    57f3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    57f5:	f6 c1 02             	test   $0x2,%cl
    57f8:	74 00                	je     57fa <add_read_request+0x2a>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    57fa:	89 c2                	mov    %eax,%edx
    57fc:	29 f2                	sub    %esi,%edx
    57fe:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5801:	0f 82 fb cd ff ff    	jb     2602 <add_read_request.cold>
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5807:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    580a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    580d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5810:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    5815:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5818:	23 6b 58             	and    0x58(%rbx),%ebp
    581b:	d3 e5                	shl    %cl,%ebp
    581d:	48 c1 e5 06          	shl    $0x6,%rbp
    5821:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5825:	e8 56 cc ff ff       	call   2480 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    582a:	be 01 00 00 00       	mov    $0x1,%esi
    582f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5834:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    5837:	e8 d4 cb ff ff       	call   2410 <calloc@plt>
    req->client_socket = client_socket;
    583c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5841:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5845:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5848:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    584d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    5852:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    585b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    5863:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    5867:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    586b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    5872:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    587a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    587e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    5886:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    588e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    5892:	e8 09 cb ff ff       	call   23a0 <io_uring_submit@plt>
}
    5897:	48 83 c4 08          	add    $0x8,%rsp
    589b:	31 c0                	xor    %eax,%eax
    589d:	5b                   	pop    %rbx
    589e:	5d                   	pop    %rbp
    589f:	41 5c                	pop    %r12
    58a1:	41 5d                	pop    %r13
    58a3:	c3                   	ret
    58a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    58af:	90                   	nop

00000000000058b0 <_send_static_string_content>:
void _send_static_string_content(struct KernelThread *data, struct Buffers *buffers, const char *str, int client_socket, struct io_uring *ring) {
    58b0:	f3 0f 1e fa          	endbr64
    58b4:	41 56                	push   %r14
    58b6:	41 89 ce             	mov    %ecx,%r14d
    58b9:	41 55                	push   %r13
    58bb:	41 54                	push   %r12
    58bd:	49 89 d4             	mov    %rdx,%r12
    58c0:	55                   	push   %rbp
    58c1:	48 89 fd             	mov    %rdi,%rbp
    void *buf = malloc(size);
    58c4:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(struct KernelThread *data, struct Buffers *buffers, const char *str, int client_socket, struct io_uring *ring) {
    58c9:	53                   	push   %rbx
    void *buf = malloc(size);
    58ca:	e8 b1 cb ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    58cf:	48 85 c0             	test   %rax,%rax
    58d2:	0f 84 05 01 00 00    	je     59dd <_send_static_string_content+0x12d>
    58d8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    58db:	4c 89 e7             	mov    %r12,%rdi
    58de:	e8 9d ca ff ff       	call   2380 <strlen@plt>
    req->iovec_count = 1;
    58e3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    58ea:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    58ee:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    58f1:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    58f4:	e8 87 cb ff ff       	call   2480 <malloc@plt>
    58f9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    58fc:	48 85 c0             	test   %rax,%rax
    58ff:	0f 84 d8 00 00 00    	je     59dd <_send_static_string_content+0x12d>
    req->iov[0].iov_len = slen;
    5905:	4c 89 6b 18          	mov    %r13,0x18(%rbx)
    5909:	4c 89 ea             	mov    %r13,%rdx
    590c:	4c 89 e6             	mov    %r12,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    590f:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5913:	e8 38 cb ff ff       	call   2450 <memcpy@plt>
    5918:	4c 89 e7             	mov    %r12,%rdi
    591b:	e8 20 ca ff ff       	call   2340 <puts@plt>
    struct Write *write = calloc(1, sizeof(struct Write));
    5920:	be 10 00 00 00       	mov    $0x10,%esi
    5925:	bf 01 00 00 00       	mov    $0x1,%edi
    592a:	e8 e1 ca ff ff       	call   2410 <calloc@plt>
    req->event_type = EVENT_TYPE_WRITE;
    592f:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    5935:	48 8d 3d d6 37 00 00 	lea    0x37d6(%rip),%rdi        # 9112 <_IO_stdin_used+0x112>
    struct Write *write = calloc(1, sizeof(struct Write));
    593c:	49 89 c5             	mov    %rax,%r13
    write->client_socket = req->client_socket;
    593f:	8b 43 08             	mov    0x8(%rbx),%eax
    write->request = req;
    5942:	49 89 5d 00          	mov    %rbx,0x0(%r13)
    write->client_socket = req->client_socket;
    5946:	41 89 45 08          	mov    %eax,0x8(%r13)
    594a:	e8 f1 c9 ff ff       	call   2340 <puts@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_WRITE, write);
    594f:	4c 63 a5 10 01 00 00 	movslq 0x110(%rbp),%r12
    5956:	49 c1 e4 04          	shl    $0x4,%r12
    595a:	4c 03 a5 08 01 00 00 	add    0x108(%rbp),%r12
  while (data->running == 1) {
    5961:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5965:	75 6d                	jne    59d4 <_send_static_string_content+0x124>
      for (int x = 0 ; x < buffers->count ; x++) {
    5967:	49 63 04 24          	movslq (%r12),%rax
    596b:	85 c0                	test   %eax,%eax
    596d:	7e f2                	jle    5961 <_send_static_string_content+0xb1>
        if (buffers->buffer[x].available == 0) {
    596f:	49 8b 54 24 08       	mov    0x8(%r12),%rdx
    5974:	48 c1 e0 08          	shl    $0x8,%rax
    5978:	31 db                	xor    %ebx,%ebx
    597a:	eb 10                	jmp    598c <_send_static_string_content+0xdc>
    597c:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    5980:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    5987:	48 39 c3             	cmp    %rax,%rbx
    598a:	74 d5                	je     5961 <_send_static_string_content+0xb1>
        if (buffers->buffer[x].available == 0) {
    598c:	8b 8c 1a 80 00 00 00 	mov    0x80(%rdx,%rbx,1),%ecx
    5993:	85 c9                	test   %ecx,%ecx
    5995:	75 e9                	jne    5980 <_send_static_string_content+0xd0>
    5997:	8b 8c 1a 98 00 00 00 	mov    0x98(%rdx,%rbx,1),%ecx
    599e:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    59a5:	bf 01 00 00 00       	mov    $0x1,%edi
    59aa:	31 c0                	xor    %eax,%eax
    59ac:	48 8d 35 6d 37 00 00 	lea    0x376d(%rip),%rsi        # 9120 <_IO_stdin_used+0x120>
    59b3:	e8 08 cb ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    59b8:	49 03 5c 24 08       	add    0x8(%r12),%rbx
    59bd:	4c 89 2b             	mov    %r13,(%rbx)
          buffers->buffer[x].kind = kind;
    59c0:	c7 83 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%rbx)
          buffers->buffer[x].available = 1;
    59ca:	c7 83 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbx)
}
    59d4:	5b                   	pop    %rbx
    59d5:	5d                   	pop    %rbp
    59d6:	41 5c                	pop    %r12
    59d8:	41 5d                	pop    %r13
    59da:	41 5e                	pop    %r14
    59dc:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    59dd:	48 8b 0d 3c 66 00 00 	mov    0x663c(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    59e4:	ba 28 00 00 00       	mov    $0x28,%edx
    59e9:	be 01 00 00 00       	mov    $0x1,%esi
    59ee:	48 8d 3d 33 3d 00 00 	lea    0x3d33(%rip),%rdi        # 9728 <_IO_stdin_used+0x728>
    59f5:	e8 46 cb ff ff       	call   2540 <fwrite@plt>
        exit(1);
    59fa:	bf 01 00 00 00       	mov    $0x1,%edi
    59ff:	e8 1c cb ff ff       	call   2520 <exit@plt>
    5a04:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5a0f:	90                   	nop

0000000000005a10 <handle_unimplemented_method>:
void handle_unimplemented_method(struct KernelThread *data, struct Buffers *buffers, int client_socket, struct io_uring *ring) {
    5a10:	f3 0f 1e fa          	endbr64
    5a14:	49 89 c8             	mov    %rcx,%r8
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, ring);
    5a17:	89 d1                	mov    %edx,%ecx
    5a19:	48 8b 15 f8 65 00 00 	mov    0x65f8(%rip),%rdx        # c018 <unimplemented_content>
    5a20:	e9 8b fe ff ff       	jmp    58b0 <_send_static_string_content>
    5a25:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005a30 <handle_http_404>:
void handle_http_404(struct KernelThread *data, struct Buffers *buffers, int client_socket, struct io_uring *ring) {
    5a30:	f3 0f 1e fa          	endbr64
    5a34:	49 89 c8             	mov    %rcx,%r8
    _send_static_string_content(data, buffers, http_404_content, client_socket, ring);
    5a37:	89 d1                	mov    %edx,%ecx
    5a39:	48 8b 15 d0 65 00 00 	mov    0x65d0(%rip),%rdx        # c010 <http_404_content>
    5a40:	e9 6b fe ff ff       	jmp    58b0 <_send_static_string_content>
    5a45:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005a50 <handle_get_method>:
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, struct io_uring *ring) {
    5a50:	f3 0f 1e fa          	endbr64
    5a54:	41 57                	push   %r15
    5a56:	41 56                	push   %r14
    5a58:	4d 89 c6             	mov    %r8,%r14
    5a5b:	41 55                	push   %r13
    5a5d:	41 89 cd             	mov    %ecx,%r13d
    5a60:	41 54                	push   %r12
    5a62:	49 89 f4             	mov    %rsi,%r12
    5a65:	55                   	push   %rbp
    5a66:	48 89 fd             	mov    %rdi,%rbp
    if (path[strlen(path) - 1] == '/') {
    5a69:	48 89 d7             	mov    %rdx,%rdi
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, struct io_uring *ring) {
    5a6c:	53                   	push   %rbx
    5a6d:	48 89 d3             	mov    %rdx,%rbx
    5a70:	48 81 ec b8 04 00 00 	sub    $0x4b8,%rsp
    5a77:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5a80:	48 89 84 24 a8 04 00 00 	mov    %rax,0x4a8(%rsp)
    5a88:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    5a8a:	e8 f1 c8 ff ff       	call   2380 <strlen@plt>
    5a8f:	80 7c 03 ff 2f       	cmpb   $0x2f,-0x1(%rbx,%rax,1)
    5a94:	48 89 c2             	mov    %rax,%rdx
    5a97:	0f 84 c3 00 00 00    	je     5b60 <handle_get_method+0x110>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5a9d:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5aa2:	48 83 c2 01          	add    $0x1,%rdx
    5aa6:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5aab:	48 89 de             	mov    %rbx,%rsi
    5aae:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5ab6:	66 89 84 24 a4 00 00 00 	mov    %ax,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5abe:	4c 8d bc 24 a0 00 00 00 	lea    0xa0(%rsp),%r15
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5ac6:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5ad1:	e8 5a c9 ff ff       	call   2430 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    5ad6:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
    5adb:	4c 89 ff             	mov    %r15,%rdi
    5ade:	e8 5d c9 ff ff       	call   2440 <stat@plt>
    5ae3:	83 f8 ff             	cmp    $0xffffffff,%eax
    5ae6:	0f 84 5c 01 00 00    	je     5c48 <handle_get_method+0x1f8>
        if (S_ISREG(path_stat.st_mode)) {
    5aec:	8b 44 24 28          	mov    0x28(%rsp),%eax
    5af0:	25 00 f0 00 00       	and    $0xf000,%eax
    5af5:	3d 00 80 00 00       	cmp    $0x8000,%eax
    5afa:	0f 84 c8 00 00 00    	je     5bc8 <handle_get_method+0x178>
    _send_static_string_content(data, buffers, http_404_content, client_socket, ring);
    5b00:	48 8b 15 09 65 00 00 	mov    0x6509(%rip),%rdx        # c010 <http_404_content>
    5b07:	4c 89 e6             	mov    %r12,%rsi
    5b0a:	48 89 ef             	mov    %rbp,%rdi
    5b0d:	4d 89 f0             	mov    %r14,%r8
    5b10:	44 89 e9             	mov    %r13d,%ecx
    5b13:	e8 98 fd ff ff       	call   58b0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5b18:	4c 89 fa             	mov    %r15,%rdx
    5b1b:	bf 01 00 00 00       	mov    $0x1,%edi
    5b20:	31 c0                	xor    %eax,%eax
    5b22:	48 8d 35 38 36 00 00 	lea    0x3638(%rip),%rsi        # 9161 <_IO_stdin_used+0x161>
    5b29:	e8 92 c9 ff ff       	call   24c0 <__printf_chk@plt>
}
    5b2e:	48 8b 84 24 a8 04 00 00 	mov    0x4a8(%rsp),%rax
    5b36:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5b3f:	0f 85 39 01 00 00    	jne    5c7e <handle_get_method+0x22e>
    5b45:	48 81 c4 b8 04 00 00 	add    $0x4b8,%rsp
    5b4c:	5b                   	pop    %rbx
    5b4d:	5d                   	pop    %rbp
    5b4e:	41 5c                	pop    %r12
    5b50:	41 5d                	pop    %r13
    5b52:	41 5e                	pop    %r14
    5b54:	41 5f                	pop    %r15
    5b56:	c3                   	ret
    5b57:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5b60:	b9 69 63 00 00       	mov    $0x6369,%ecx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5b65:	48 89 de             	mov    %rbx,%rsi
    5b68:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5b70:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
    5b7b:	66 89 8c 24 a4 00 00 00 	mov    %cx,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5b83:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5b88:	4c 8d bc 24 a0 00 00 00 	lea    0xa0(%rsp),%r15
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5b90:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5b95:	e8 96 c8 ff ff       	call   2430 <__memcpy_chk@plt>
    5b9a:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    5b9f:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5ba4:	48 8d 35 81 35 00 00 	lea    0x3581(%rip),%rsi        # 912c <_IO_stdin_used+0x12c>
    5bab:	48 29 d1             	sub    %rdx,%rcx
    5bae:	49 8d 7c 17 06       	lea    0x6(%r15,%rdx,1),%rdi
    5bb3:	ba 0b 00 00 00       	mov    $0xb,%edx
    5bb8:	e8 73 c8 ff ff       	call   2430 <__memcpy_chk@plt>
    5bbd:	e9 14 ff ff ff       	jmp    5ad6 <handle_get_method+0x86>
    5bc2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5bc8:	bf 70 00 00 00       	mov    $0x70,%edi
    5bcd:	e8 ae c8 ff ff       	call   2480 <malloc@plt>
    5bd2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5bd5:	48 85 c0             	test   %rax,%rax
    5bd8:	0f 84 a5 00 00 00    	je     5c83 <handle_get_method+0x233>
            req->client_socket = client_socket;
    5bde:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    5be2:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    5be7:	4c 8d 40 10          	lea    0x10(%rax),%r8
    5beb:	4c 89 fa             	mov    %r15,%rdx
            req->iovec_count = 6;
    5bee:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    5bf5:	4c 89 e6             	mov    %r12,%rsi
    5bf8:	48 89 ef             	mov    %rbp,%rdi
    5bfb:	e8 00 f5 ff ff       	call   5100 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5c00:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    5c05:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    5c09:	4c 89 ff             	mov    %r15,%rdi
    5c0c:	e8 1f fa ff ff       	call   5630 <copy_file_contents>
    5c11:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    5c16:	4c 89 fa             	mov    %r15,%rdx
    5c19:	31 c0                	xor    %eax,%eax
    5c1b:	48 8d 35 2d 35 00 00 	lea    0x352d(%rip),%rsi        # 914f <_IO_stdin_used+0x14f>
    5c22:	bf 01 00 00 00       	mov    $0x1,%edi
    5c27:	e8 94 c8 ff ff       	call   24c0 <__printf_chk@plt>
            add_write_request(data, buffers, req, ring);
    5c2c:	4c 89 f1             	mov    %r14,%rcx
    5c2f:	48 89 da             	mov    %rbx,%rdx
    5c32:	4c 89 e6             	mov    %r12,%rsi
    5c35:	48 89 ef             	mov    %rbp,%rdi
    5c38:	e8 b3 fa ff ff       	call   56f0 <add_write_request>
    5c3d:	e9 ec fe ff ff       	jmp    5b2e <handle_get_method+0xde>
    5c42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5c48:	48 89 d9             	mov    %rbx,%rcx
    5c4b:	4c 89 fa             	mov    %r15,%rdx
    5c4e:	48 8d 35 e2 34 00 00 	lea    0x34e2(%rip),%rsi        # 9137 <_IO_stdin_used+0x137>
    5c55:	31 c0                	xor    %eax,%eax
    5c57:	bf 01 00 00 00       	mov    $0x1,%edi
    5c5c:	e8 5f c8 ff ff       	call   24c0 <__printf_chk@plt>
    _send_static_string_content(data, buffers, http_404_content, client_socket, ring);
    5c61:	4d 89 f0             	mov    %r14,%r8
    5c64:	44 89 e9             	mov    %r13d,%ecx
    5c67:	4c 89 e6             	mov    %r12,%rsi
    5c6a:	48 8b 15 9f 63 00 00 	mov    0x639f(%rip),%rdx        # c010 <http_404_content>
    5c71:	48 89 ef             	mov    %rbp,%rdi
    5c74:	e8 37 fc ff ff       	call   58b0 <_send_static_string_content>
}
    5c79:	e9 b0 fe ff ff       	jmp    5b2e <handle_get_method+0xde>
}
    5c7e:	e8 0d c7 ff ff       	call   2390 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5c83:	48 8b 0d 96 63 00 00 	mov    0x6396(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5c8a:	ba 28 00 00 00       	mov    $0x28,%edx
    5c8f:	be 01 00 00 00       	mov    $0x1,%esi
    5c94:	48 8d 3d 8d 3a 00 00 	lea    0x3a8d(%rip),%rdi        # 9728 <_IO_stdin_used+0x728>
    5c9b:	e8 a0 c8 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    5ca0:	bf 01 00 00 00       	mov    $0x1,%edi
    5ca5:	e8 76 c8 ff ff       	call   2520 <exit@plt>
    5caa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000005cb0 <handle_http_method>:
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, struct io_uring *ring) {
    5cb0:	f3 0f 1e fa          	endbr64
    5cb4:	41 57                	push   %r15
    5cb6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5cb8:	4c 8d 35 ed 33 00 00 	lea    0x33ed(%rip),%r14        # 90ac <_IO_stdin_used+0xac>
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, struct io_uring *ring) {
    5cbf:	41 55                	push   %r13
    5cc1:	4d 89 c5             	mov    %r8,%r13
    5cc4:	41 54                	push   %r12
    5cc6:	41 89 cc             	mov    %ecx,%r12d
    5cc9:	55                   	push   %rbp
    5cca:	48 89 f5             	mov    %rsi,%rbp
    method = strtok_r(method_buffer, " ", &saveptr);
    5ccd:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, struct io_uring *ring) {
    5cd0:	53                   	push   %rbx
    5cd1:	48 83 ec 28          	sub    $0x28,%rsp
    5cd5:	48 89 3c 24          	mov    %rdi,(%rsp)
    method = strtok_r(method_buffer, " ", &saveptr);
    5cd9:	4c 8d 7c 24 10       	lea    0x10(%rsp),%r15
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, struct io_uring *ring) {
    5cde:	48 89 d7             	mov    %rdx,%rdi
    method = strtok_r(method_buffer, " ", &saveptr);
    5ce1:	4c 89 fa             	mov    %r15,%rdx
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, struct io_uring *ring) {
    5ce4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5ced:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    5cf2:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5cf4:	e8 f7 c6 ff ff       	call   23f0 <strtok_r@plt>
    for (; *str; ++str)
    5cf9:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    5cfc:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    5cff:	84 d2                	test   %dl,%dl
    5d01:	88 54 24 0f          	mov    %dl,0xf(%rsp)
    5d05:	74 26                	je     5d2d <handle_http_method+0x7d>
        *str = (char)tolower(*str);
    5d07:	e8 a4 c8 ff ff       	call   25b0 <__ctype_tolower_loc@plt>
    5d0c:	48 0f be 54 24 0f    	movsbq 0xf(%rsp),%rdx
    5d12:	48 89 d9             	mov    %rbx,%rcx
    5d15:	0f 1f 00             	nopl   (%rax)
    5d18:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    5d1b:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    5d1f:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    5d22:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    5d25:	48 0f be 11          	movsbq (%rcx),%rdx
    5d29:	84 d2                	test   %dl,%dl
    5d2b:	75 eb                	jne    5d18 <handle_http_method+0x68>
    path = strtok_r(NULL, " ", &saveptr);
    5d2d:	4c 89 f6             	mov    %r14,%rsi
    5d30:	4c 89 fa             	mov    %r15,%rdx
    5d33:	31 ff                	xor    %edi,%edi
    5d35:	e8 b6 c6 ff ff       	call   23f0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5d3a:	48 8d 35 33 34 00 00 	lea    0x3433(%rip),%rsi        # 9174 <_IO_stdin_used+0x174>
    5d41:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    5d44:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    5d47:	e8 d4 c6 ff ff       	call   2420 <strcmp@plt>
        handle_get_method(data, buffers, path, client_socket, ring);
    5d4c:	4d 89 e8             	mov    %r13,%r8
    5d4f:	44 89 e1             	mov    %r12d,%ecx
    if (strcmp(method, "get") == 0) {
    5d52:	85 c0                	test   %eax,%eax
    5d54:	75 32                	jne    5d88 <handle_http_method+0xd8>
        handle_get_method(data, buffers, path, client_socket, ring);
    5d56:	48 8b 3c 24          	mov    (%rsp),%rdi
    5d5a:	4c 89 f2             	mov    %r14,%rdx
    5d5d:	48 89 ee             	mov    %rbp,%rsi
    5d60:	e8 eb fc ff ff       	call   5a50 <handle_get_method>
}
    5d65:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5d6a:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5d73:	75 28                	jne    5d9d <handle_http_method+0xed>
    5d75:	48 83 c4 28          	add    $0x28,%rsp
    5d79:	5b                   	pop    %rbx
    5d7a:	5d                   	pop    %rbp
    5d7b:	41 5c                	pop    %r12
    5d7d:	41 5d                	pop    %r13
    5d7f:	41 5e                	pop    %r14
    5d81:	41 5f                	pop    %r15
    5d83:	c3                   	ret
    5d84:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, ring);
    5d88:	48 8b 15 89 62 00 00 	mov    0x6289(%rip),%rdx        # c018 <unimplemented_content>
    5d8f:	48 8b 3c 24          	mov    (%rsp),%rdi
    5d93:	48 89 ee             	mov    %rbp,%rsi
    5d96:	e8 15 fb ff ff       	call   58b0 <_send_static_string_content>
}
    5d9b:	eb c8                	jmp    5d65 <handle_http_method+0xb5>
    5d9d:	e8 ee c5 ff ff       	call   2390 <__stack_chk_fail@plt>
    5da2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5dad:	0f 1f 00             	nopl   (%rax)

0000000000005db0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5db0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5db4:	85 d2                	test   %edx,%edx
    5db6:	7e 38                	jle    5df0 <get_line+0x40>
    5db8:	48 63 d2             	movslq %edx,%rdx
    5dbb:	48 83 c7 01          	add    $0x1,%rdi
    5dbf:	48 01 f2             	add    %rsi,%rdx
    5dc2:	eb 11                	jmp    5dd5 <get_line+0x25>
    5dc4:	0f 1f 40 00          	nopl   0x0(%rax)
    5dc8:	48 83 c6 01          	add    $0x1,%rsi
    5dcc:	48 83 c7 01          	add    $0x1,%rdi
    5dd0:	48 39 d6             	cmp    %rdx,%rsi
    5dd3:	74 1b                	je     5df0 <get_line+0x40>
        dest[i] = src[i];
    5dd5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5dd9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5ddb:	3c 0d                	cmp    $0xd,%al
    5ddd:	75 e9                	jne    5dc8 <get_line+0x18>
    5ddf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5de2:	75 e4                	jne    5dc8 <get_line+0x18>
            dest[i] = '\0';
    5de4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5de7:	31 c0                	xor    %eax,%eax
    5de9:	c3                   	ret
    5dea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5df0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5df5:	c3                   	ret
    5df6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005e00 <handle_client_request>:
int handle_client_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    5e00:	f3 0f 1e fa          	endbr64
    5e04:	53                   	push   %rbx
    5e05:	49 89 fa             	mov    %rdi,%r10
    5e08:	48 89 f3             	mov    %rsi,%rbx
    5e0b:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    5e12:	48 8b 72 10          	mov    0x10(%rdx),%rsi
    5e16:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5e1f:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5e27:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5e29:	49 89 e3             	mov    %rsp,%r11
    5e2c:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    5e34:	4c 89 d8             	mov    %r11,%rax
    5e37:	eb 14                	jmp    5e4d <handle_client_request+0x4d>
    5e39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5e40:	48 83 c0 01          	add    $0x1,%rax
    5e44:	48 83 c6 01          	add    $0x1,%rsi
    5e48:	4c 39 c8             	cmp    %r9,%rax
    5e4b:	74 53                	je     5ea0 <handle_client_request+0xa0>
        dest[i] = src[i];
    5e4d:	0f b6 3e             	movzbl (%rsi),%edi
    5e50:	40 88 38             	mov    %dil,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5e53:	40 80 ff 0d          	cmp    $0xd,%dil
    5e57:	75 e7                	jne    5e40 <handle_client_request+0x40>
    5e59:	80 7e 01 0a          	cmpb   $0xa,0x1(%rsi)
    5e5d:	75 e1                	jne    5e40 <handle_client_request+0x40>
            dest[i] = '\0';
    5e5f:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(data, buffers, http_request, req->client_socket, ring);
    5e62:	8b 42 08             	mov    0x8(%rdx),%eax
    5e65:	49 89 c8             	mov    %rcx,%r8
    5e68:	4c 89 da             	mov    %r11,%rdx
    5e6b:	48 89 de             	mov    %rbx,%rsi
    5e6e:	4c 89 d7             	mov    %r10,%rdi
    5e71:	89 c1                	mov    %eax,%ecx
    5e73:	e8 38 fe ff ff       	call   5cb0 <handle_http_method>
}
    5e78:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5e80:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5e89:	75 3c                	jne    5ec7 <handle_client_request+0xc7>
    5e8b:	48 81 c4 10 04 00 00 	add    $0x410,%rsp
    5e92:	31 c0                	xor    %eax,%eax
    5e94:	5b                   	pop    %rbx
    5e95:	c3                   	ret
    5e96:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5ea0:	48 8b 0d 79 61 00 00 	mov    0x6179(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5ea7:	ba 12 00 00 00       	mov    $0x12,%edx
    5eac:	be 01 00 00 00       	mov    $0x1,%esi
    5eb1:	48 8d 3d c0 32 00 00 	lea    0x32c0(%rip),%rdi        # 9178 <_IO_stdin_used+0x178>
    5eb8:	e8 83 c6 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    5ebd:	bf 01 00 00 00       	mov    $0x1,%edi
    5ec2:	e8 59 c6 ff ff       	call   2520 <exit@plt>
}
    5ec7:	e8 c4 c4 ff ff       	call   2390 <__stack_chk_fail@plt>
    5ecc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005ed0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5ed0:	f3 0f 1e fa          	endbr64
    5ed4:	55                   	push   %rbp
    5ed5:	53                   	push   %rbx
    5ed6:	48 89 cb             	mov    %rcx,%rbx
    5ed9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    5edd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5ee0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5ee3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5ee9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5eec:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5eef:	f6 c1 02             	test   $0x2,%cl
    5ef2:	74 00                	je     5ef4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5ef4:	41 89 c0             	mov    %eax,%r8d
    5ef7:	45 29 c8             	sub    %r9d,%r8d
    5efa:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    5efe:	0f 82 08 c7 ff ff    	jb     260c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5f04:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f07:	8b 6b 44             	mov    0x44(%rbx),%ebp
    5f0a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    5f0d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5f10:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5f13:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5f17:	d3 e5                	shl    %cl,%ebp
    5f19:	48 c1 e5 06          	shl    $0x6,%rbp
    5f1d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5f21:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5f24:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5f29:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5f30:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5f34:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5f38:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5f40:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5f48:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    5f4c:	e8 2f c5 ff ff       	call   2480 <malloc@plt>
  io_uring_submit(ring);
    5f51:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5f54:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    5f5a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    5f5e:	48 83 c4 08          	add    $0x8,%rsp
    5f62:	5b                   	pop    %rbx
    5f63:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5f64:	e9 37 c4 ff ff       	jmp    23a0 <io_uring_submit@plt>
    5f69:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005f70 <buffersend>:
int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send) {
    5f70:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    5f74:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    5f78:	0f 85 96 00 00 00    	jne    6014 <buffersend+0xa4>
int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send) {
    5f7e:	41 55                	push   %r13
    5f80:	49 89 cd             	mov    %rcx,%r13
    5f83:	41 54                	push   %r12
    5f85:	41 89 d4             	mov    %edx,%r12d
    5f88:	55                   	push   %rbp
    5f89:	48 89 f5             	mov    %rsi,%rbp
    5f8c:	53                   	push   %rbx
    5f8d:	48 83 ec 08          	sub    $0x8,%rsp
      for (int x = 0 ; x < buffers->count ; x++) {
    5f91:	48 63 45 00          	movslq 0x0(%rbp),%rax
    5f95:	85 c0                	test   %eax,%eax
    5f97:	7e 6f                	jle    6008 <buffersend+0x98>
        if (buffers->buffer[x].available == 0) {
    5f99:	48 8b 55 08          	mov    0x8(%rbp),%rdx
    5f9d:	48 c1 e0 08          	shl    $0x8,%rax
    5fa1:	31 db                	xor    %ebx,%ebx
    5fa3:	eb 0f                	jmp    5fb4 <buffersend+0x44>
    5fa5:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    5fa8:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    5faf:	48 39 c3             	cmp    %rax,%rbx
    5fb2:	74 54                	je     6008 <buffersend+0x98>
        if (buffers->buffer[x].available == 0) {
    5fb4:	8b 8c 1a 80 00 00 00 	mov    0x80(%rdx,%rbx,1),%ecx
    5fbb:	85 c9                	test   %ecx,%ecx
    5fbd:	75 e9                	jne    5fa8 <buffersend+0x38>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5fbf:	8b 8c 1a 98 00 00 00 	mov    0x98(%rdx,%rbx,1),%ecx
    5fc6:	48 8b 97 18 01 00 00 	mov    0x118(%rdi),%rdx
    5fcd:	31 c0                	xor    %eax,%eax
    5fcf:	bf 01 00 00 00       	mov    $0x1,%edi
    5fd4:	48 8d 35 45 31 00 00 	lea    0x3145(%rip),%rsi        # 9120 <_IO_stdin_used+0x120>
    5fdb:	e8 e0 c4 ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    5fe0:	48 03 5d 08          	add    0x8(%rbp),%rbx
    5fe4:	4c 89 2b             	mov    %r13,(%rbx)
          buffers->buffer[x].kind = kind;
    5fe7:	44 89 a3 98 00 00 00 	mov    %r12d,0x98(%rbx)
          buffers->buffer[x].available = 1;
    5fee:	c7 83 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbx)
}
    5ff8:	48 83 c4 08          	add    $0x8,%rsp
    5ffc:	31 c0                	xor    %eax,%eax
    5ffe:	5b                   	pop    %rbx
    5fff:	5d                   	pop    %rbp
    6000:	41 5c                	pop    %r12
    6002:	41 5d                	pop    %r13
    6004:	c3                   	ret
    6005:	0f 1f 00             	nopl   (%rax)
  while (data->running == 1) {
    6008:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    600c:	0f 84 7f ff ff ff    	je     5f91 <buffersend+0x21>
    6012:	eb e4                	jmp    5ff8 <buffersend+0x88>
}
    6014:	31 c0                	xor    %eax,%eax
    6016:	c3                   	ret
    6017:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006020 <bufferrecv>:
void * bufferrecv(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking) {
    6020:	f3 0f 1e fa          	endbr64
    6024:	41 57                	push   %r15
    6026:	49 89 d7             	mov    %rdx,%r15
    6029:	41 56                	push   %r14
    602b:	4c 8d 35 59 31 00 00 	lea    0x3159(%rip),%r14        # 918b <_IO_stdin_used+0x18b>
    6032:	41 55                	push   %r13
    6034:	49 89 f5             	mov    %rsi,%r13
    6037:	41 54                	push   %r12
    6039:	41 89 cc             	mov    %ecx,%r12d
    603c:	55                   	push   %rbp
    603d:	44 89 cd             	mov    %r9d,%ebp
    6040:	53                   	push   %rbx
    6041:	48 83 ec 18          	sub    $0x18,%rsp
    6045:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    604a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
    6050:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
    6055:	75 64                	jne    60bb <bufferrecv+0x9b>
      for (int x = 0 ; x < buffers->count ; x++) {
    6057:	49 63 07             	movslq (%r15),%rax
    605a:	85 c0                	test   %eax,%eax
    605c:	7e 6e                	jle    60cc <bufferrecv+0xac>
        if (buffers->buffer[x].available == 1) {
    605e:	49 8b 4f 08          	mov    0x8(%r15),%rcx
    6062:	48 c1 e0 08          	shl    $0x8,%rax
    6066:	31 db                	xor    %ebx,%ebx
    6068:	eb 12                	jmp    607c <bufferrecv+0x5c>
    606a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    6070:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    6077:	48 39 c3             	cmp    %rax,%rbx
    607a:	74 3a                	je     60b6 <bufferrecv+0x96>
        if (buffers->buffer[x].available == 1) {
    607c:	83 bc 19 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx,%rbx,1)
    6084:	75 ea                	jne    6070 <bufferrecv+0x50>
    6086:	44 8b 84 19 98 00 00 00 	mov    0x98(%rcx,%rbx,1),%r8d
    608e:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    6093:	4c 89 f6             	mov    %r14,%rsi
    6096:	31 c0                	xor    %eax,%eax
    6098:	49 8b 95 18 01 00 00 	mov    0x118(%r13),%rdx
    609f:	bf 01 00 00 00       	mov    $0x1,%edi
    60a4:	e8 17 c4 ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    60a9:	49 03 5f 08          	add    0x8(%r15),%rbx
    60ad:	44 39 a3 98 00 00 00 	cmp    %r12d,0x98(%rbx)
    60b4:	74 22                	je     60d8 <bufferrecv+0xb8>
     if (nonblocking == 1) { return NULL; }
    60b6:	83 fd 01             	cmp    $0x1,%ebp
    60b9:	75 95                	jne    6050 <bufferrecv+0x30>
}
    60bb:	48 83 c4 18          	add    $0x18,%rsp
     if (nonblocking == 1) { return NULL; }
    60bf:	31 c0                	xor    %eax,%eax
}
    60c1:	5b                   	pop    %rbx
    60c2:	5d                   	pop    %rbp
    60c3:	41 5c                	pop    %r12
    60c5:	41 5d                	pop    %r13
    60c7:	41 5e                	pop    %r14
    60c9:	41 5f                	pop    %r15
    60cb:	c3                   	ret
     if (nonblocking == 1) { return NULL; }
    60cc:	83 fd 01             	cmp    $0x1,%ebp
    60cf:	74 ea                	je     60bb <bufferrecv+0x9b>
  while (data->running == 1) {
    60d1:	eb fe                	jmp    60d1 <bufferrecv+0xb1>
    60d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    60d8:	be 00 01 00 00       	mov    $0x100,%esi
    60dd:	bf 01 00 00 00       	mov    $0x1,%edi
    60e2:	e8 29 c3 ff ff       	call   2410 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    60e7:	48 8b 13             	mov    (%rbx),%rdx
            reply->kind = buffers->buffer[x].kind;
    60ea:	44 89 a0 98 00 00 00 	mov    %r12d,0x98(%rax)
            reply->data = buffers->buffer[x].data;
    60f1:	48 89 10             	mov    %rdx,(%rax)
            buffers->buffer[x].available = 0;
    60f4:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
}
    60fe:	48 83 c4 18          	add    $0x18,%rsp
    6102:	5b                   	pop    %rbx
    6103:	5d                   	pop    %rbp
    6104:	41 5c                	pop    %r12
    6106:	41 5d                	pop    %r13
    6108:	41 5e                	pop    %r14
    610a:	41 5f                	pop    %r15
    610c:	c3                   	ret
    610d:	0f 1f 00             	nopl   (%rax)

0000000000006110 <wait_for_new_client>:
int wait_for_new_client(struct KernelThread *data, int nonblocking) {
    6110:	f3 0f 1e fa          	endbr64
    6114:	41 57                	push   %r15
    6116:	49 89 ff             	mov    %rdi,%r15
    6119:	41 56                	push   %r14
    611b:	41 55                	push   %r13
    611d:	4c 8d 2d 77 30 00 00 	lea    0x3077(%rip),%r13        # 919b <_IO_stdin_used+0x19b>
    6124:	41 54                	push   %r12
    6126:	4c 8d 25 5e 30 00 00 	lea    0x305e(%rip),%r12        # 918b <_IO_stdin_used+0x18b>
    612d:	55                   	push   %rbp
    612e:	89 f5                	mov    %esi,%ebp
    6130:	53                   	push   %rbx
    6131:	48 83 ec 08          	sub    $0x8,%rsp
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    6135:	4c 63 b7 14 01 00 00 	movslq 0x114(%rdi),%r14
    613c:	49 c1 e6 04          	shl    $0x4,%r14
    6140:	4c 03 b7 08 01 00 00 	add    0x108(%rdi),%r14
  while (data->running == 1) {
    6147:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    6150:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    6155:	75 62                	jne    61b9 <wait_for_new_client+0xa9>
      for (int x = 0 ; x < buffers->count ; x++) {
    6157:	49 63 06             	movslq (%r14),%rax
    615a:	85 c0                	test   %eax,%eax
    615c:	0f 8e a8 00 00 00    	jle    620a <wait_for_new_client+0xfa>
        if (buffers->buffer[x].available == 1) {
    6162:	49 8b 4e 08          	mov    0x8(%r14),%rcx
    6166:	48 c1 e0 08          	shl    $0x8,%rax
    616a:	31 db                	xor    %ebx,%ebx
    616c:	eb 0e                	jmp    617c <wait_for_new_client+0x6c>
    616e:	66 90                	xchg   %ax,%ax
      for (int x = 0 ; x < buffers->count ; x++) {
    6170:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    6177:	48 39 c3             	cmp    %rax,%rbx
    617a:	74 38                	je     61b4 <wait_for_new_client+0xa4>
        if (buffers->buffer[x].available == 1) {
    617c:	83 bc 19 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx,%rbx,1)
    6184:	75 ea                	jne    6170 <wait_for_new_client+0x60>
    6186:	44 8b 84 19 98 00 00 00 	mov    0x98(%rcx,%rbx,1),%r8d
    618e:	49 8b 97 18 01 00 00 	mov    0x118(%r15),%rdx
    6195:	31 c0                	xor    %eax,%eax
    6197:	4c 89 e9             	mov    %r13,%rcx
    619a:	4c 89 e6             	mov    %r12,%rsi
    619d:	bf 01 00 00 00       	mov    $0x1,%edi
    61a2:	e8 19 c3 ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    61a7:	49 03 5e 08          	add    0x8(%r14),%rbx
    61ab:	83 bb 98 00 00 00 02 	cmpl   $0x2,0x98(%rbx)
    61b2:	74 19                	je     61cd <wait_for_new_client+0xbd>
     if (nonblocking == 1) { return NULL; }
    61b4:	83 fd 01             	cmp    $0x1,%ebp
    61b7:	75 97                	jne    6150 <wait_for_new_client+0x40>
}
    61b9:	48 83 c4 08          	add    $0x8,%rsp
    return -1;
    61bd:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
}
    61c2:	5b                   	pop    %rbx
    61c3:	5d                   	pop    %rbp
    61c4:	41 5c                	pop    %r12
    61c6:	41 5d                	pop    %r13
    61c8:	41 5e                	pop    %r14
    61ca:	41 5f                	pop    %r15
    61cc:	c3                   	ret
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    61cd:	be 00 01 00 00       	mov    $0x100,%esi
    61d2:	bf 01 00 00 00       	mov    $0x1,%edi
    61d7:	e8 34 c2 ff ff       	call   2410 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    61dc:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    61df:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
            reply->kind = buffers->buffer[x].kind;
    61e9:	c7 80 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%rax)
            reply->data = buffers->buffer[x].data;
    61f3:	48 89 10             	mov    %rdx,(%rax)
  return newclientmsg->socket;
    61f6:	48 8b 00             	mov    (%rax),%rax
    61f9:	8b 00                	mov    (%rax),%eax
}
    61fb:	48 83 c4 08          	add    $0x8,%rsp
    61ff:	5b                   	pop    %rbx
    6200:	5d                   	pop    %rbp
    6201:	41 5c                	pop    %r12
    6203:	41 5d                	pop    %r13
    6205:	41 5e                	pop    %r14
    6207:	41 5f                	pop    %r15
    6209:	c3                   	ret
     if (nonblocking == 1) { return NULL; }
    620a:	83 fd 01             	cmp    $0x1,%ebp
    620d:	74 aa                	je     61b9 <wait_for_new_client+0xa9>
  while (data->running == 1) {
    620f:	eb fe                	jmp    620f <wait_for_new_client+0xff>
    6211:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    621c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006220 <io_thread>:
void* io_thread(void *arg) {
    6220:	f3 0f 1e fa          	endbr64
    6224:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    6226:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    6228:	41 56                	push   %r14
    622a:	41 55                	push   %r13
    622c:	41 54                	push   %r12
    622e:	55                   	push   %rbp
    622f:	48 89 fd             	mov    %rdi,%rbp
    6232:	53                   	push   %rbx
    6233:	48 81 ec 78 05 00 00 	sub    $0x578,%rsp
  struct io_uring ring = *data->ring;
    623a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    6243:	48 89 84 24 68 05 00 00 	mov    %rax,0x568(%rsp)
    624b:	48 8b 47 60          	mov    0x60(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    624f:	4c 8d ac 24 80 00 00 00 	lea    0x80(%rsp),%r13
    6257:	bf 00 01 00 00       	mov    $0x100,%edi
    625c:	4c 89 ee             	mov    %r13,%rsi
  struct io_uring ring = *data->ring;
    625f:	f3 0f 6f 10          	movdqu (%rax),%xmm2
    6263:	0f 29 94 24 80 00 00 00 	movaps %xmm2,0x80(%rsp)
    626b:	f3 0f 6f 58 10       	movdqu 0x10(%rax),%xmm3
    6270:	0f 29 9c 24 90 00 00 00 	movaps %xmm3,0x90(%rsp)
    6278:	f3 0f 6f 60 20       	movdqu 0x20(%rax),%xmm4
    627d:	0f 29 a4 24 a0 00 00 00 	movaps %xmm4,0xa0(%rsp)
    6285:	f3 0f 6f 68 30       	movdqu 0x30(%rax),%xmm5
    628a:	0f 29 ac 24 b0 00 00 00 	movaps %xmm5,0xb0(%rsp)
    6292:	f3 0f 6f 70 40       	movdqu 0x40(%rax),%xmm6
    6297:	0f 29 b4 24 c0 00 00 00 	movaps %xmm6,0xc0(%rsp)
    629f:	f3 0f 6f 78 50       	movdqu 0x50(%rax),%xmm7
    62a4:	0f 29 bc 24 d0 00 00 00 	movaps %xmm7,0xd0(%rsp)
    62ac:	f3 0f 6f 48 60       	movdqu 0x60(%rax),%xmm1
    62b1:	0f 29 8c 24 e0 00 00 00 	movaps %xmm1,0xe0(%rsp)
    62b9:	f3 0f 6f 50 70       	movdqu 0x70(%rax),%xmm2
    62be:	0f 29 94 24 f0 00 00 00 	movaps %xmm2,0xf0(%rsp)
    62c6:	f3 0f 6f 98 80 00 00 00 	movdqu 0x80(%rax),%xmm3
    62ce:	0f 29 9c 24 00 01 00 00 	movaps %xmm3,0x100(%rsp)
    62d6:	f3 0f 6f a0 90 00 00 00 	movdqu 0x90(%rax),%xmm4
    62de:	0f 29 a4 24 10 01 00 00 	movaps %xmm4,0x110(%rsp)
    62e6:	f3 0f 6f a8 a0 00 00 00 	movdqu 0xa0(%rax),%xmm5
    62ee:	0f 29 ac 24 20 01 00 00 	movaps %xmm5,0x120(%rsp)
    62f6:	f3 0f 6f b0 b0 00 00 00 	movdqu 0xb0(%rax),%xmm6
    62fe:	0f 29 b4 24 30 01 00 00 	movaps %xmm6,0x130(%rsp)
    6306:	f3 0f 6f b8 c0 00 00 00 	movdqu 0xc0(%rax),%xmm7
    630e:	0f 29 bc 24 40 01 00 00 	movaps %xmm7,0x140(%rsp)
    6316:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    631d:	48 89 84 24 50 01 00 00 	mov    %rax,0x150(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    6325:	e8 36 c1 ff ff       	call   2460 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    632a:	48 8b 7d 60          	mov    0x60(%rbp),%rdi
    632e:	31 f6                	xor    %esi,%esi
    6330:	e8 2b c2 ff ff       	call   2560 <io_uring_register_eventfd@plt>
  if (data->io_mode == IO_MODE_RECV) {
    6335:	8b 85 04 01 00 00    	mov    0x104(%rbp),%eax
    633b:	83 f8 01             	cmp    $0x1,%eax
    633e:	0f 84 f3 0b 00 00    	je     6f37 <io_thread+0xd17>
  if (data->io_mode == IO_MODE_SEND) {
    6344:	85 c0                	test   %eax,%eax
    6346:	0f 85 23 06 00 00    	jne    696f <io_thread+0x74f>
    634c:	48 8d 3d bd 34 00 00 	lea    0x34bd(%rip),%rdi        # 9810 <_IO_stdin_used+0x810>
    6353:	e8 e8 bf ff ff       	call   2340 <puts@plt>
    int epollfd = epoll_create1(0);
    6358:	31 ff                	xor    %edi,%edi
    635a:	e8 41 c2 ff ff       	call   25a0 <epoll_create1@plt>
    635f:	89 44 24 04          	mov    %eax,0x4(%rsp)
				if (epollfd == -1) {
    6363:	83 f8 ff             	cmp    $0xffffffff,%eax
    6366:	0f 84 ec c2 ff ff    	je     2658 <io_thread.cold+0x42>
    636c:	89 c2                	mov    %eax,%edx
    636e:	48 8d 35 f1 2e 00 00 	lea    0x2ef1(%rip),%rsi        # 9266 <_IO_stdin_used+0x266>
    6375:	31 c0                	xor    %eax,%eax
    6377:	bf 01 00 00 00       	mov    $0x1,%edi
    637c:	e8 3f c1 ff ff       	call   24c0 <__printf_chk@plt>
    6381:	48 8d 3d c0 34 00 00 	lea    0x34c0(%rip),%rdi        # 9848 <_IO_stdin_used+0x848>
    6388:	4c 8d 3d ec 2e 00 00 	lea    0x2eec(%rip),%r15        # 927b <_IO_stdin_used+0x27b>
    638f:	e8 ac bf ff ff       	call   2340 <puts@plt>
    6394:	8b 8d 14 01 00 00    	mov    0x114(%rbp),%ecx
    639a:	31 c0                	xor    %eax,%eax
    639c:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    63a3:	44 8b 85 10 01 00 00 	mov    0x110(%rbp),%r8d
    63aa:	48 8d 35 cf 34 00 00 	lea    0x34cf(%rip),%rsi        # 9880 <_IO_stdin_used+0x880>
    63b1:	bf 01 00 00 00       	mov    $0x1,%edi
    63b6:	e8 05 c1 ff ff       	call   24c0 <__printf_chk@plt>
    void * _reply = bufferrecv("waitsocketreply", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET, &reply, 0); 
    63bb:	4c 63 8d 14 01 00 00 	movslq 0x114(%rbp),%r9
    63c2:	49 c1 e1 04          	shl    $0x4,%r9
    63c6:	4c 03 8d 08 01 00 00 	add    0x108(%rbp),%r9
    63cd:	4d 89 cc             	mov    %r9,%r12
  while (data->running == 1) {
    63d0:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    63d4:	0f 85 5c c2 ff ff    	jne    2636 <io_thread.cold+0x20>
      for (int x = 0 ; x < buffers->count ; x++) {
    63da:	49 63 04 24          	movslq (%r12),%rax
    63de:	85 c0                	test   %eax,%eax
    63e0:	0f 8e c0 05 00 00    	jle    69a6 <io_thread+0x786>
        if (buffers->buffer[x].available == 1) {
    63e6:	49 8b 4c 24 08       	mov    0x8(%r12),%rcx
    63eb:	48 c1 e0 08          	shl    $0x8,%rax
                for (int i = 0; i < req->iovec_count; i++) {
    63ef:	45 31 f6             	xor    %r14d,%r14d
    63f2:	eb 10                	jmp    6404 <io_thread+0x1e4>
    63f4:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    63f8:	49 81 c6 00 01 00 00 	add    $0x100,%r14
    63ff:	49 39 c6             	cmp    %rax,%r14
    6402:	74 eb                	je     63ef <io_thread+0x1cf>
        if (buffers->buffer[x].available == 1) {
    6404:	42 8b 9c 31 80 00 00 00 	mov    0x80(%rcx,%r14,1),%ebx
    640c:	83 fb 01             	cmp    $0x1,%ebx
    640f:	75 e7                	jne    63f8 <io_thread+0x1d8>
    6411:	46 8b 84 31 98 00 00 00 	mov    0x98(%rcx,%r14,1),%r8d
    6419:	bf 01 00 00 00       	mov    $0x1,%edi
    641e:	4c 89 f9             	mov    %r15,%rcx
    6421:	31 c0                	xor    %eax,%eax
    6423:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    642a:	48 8d 35 5a 2d 00 00 	lea    0x2d5a(%rip),%rsi        # 918b <_IO_stdin_used+0x18b>
    6431:	e8 8a c0 ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    6436:	4d 03 74 24 08       	add    0x8(%r12),%r14
    643b:	41 8b b6 98 00 00 00 	mov    0x98(%r14),%esi
    6442:	85 f6                	test   %esi,%esi
    6444:	75 8a                	jne    63d0 <io_thread+0x1b0>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6446:	be 00 01 00 00       	mov    $0x100,%esi
    644b:	bf 01 00 00 00       	mov    $0x1,%edi
    6450:	e8 bb bf ff ff       	call   2410 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    6455:	49 8b 16             	mov    (%r14),%rdx
            buffers->buffer[x].available = 0;
    6458:	41 c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r14)
            reply->kind = buffers->buffer[x].kind;
    6463:	c7 80 98 00 00 00 00 00 00 00 	movl   $0x0,0x98(%rax)
            reply->data = buffers->buffer[x].data;
    646d:	48 89 10             	mov    %rdx,(%rax)
    struct NewSocketMessage *msg = bufferreply->data;
    6470:	4c 8b 20             	mov    (%rax),%r12
    6473:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    647a:	48 8d 35 3f 34 00 00 	lea    0x343f(%rip),%rsi        # 98c0 <_IO_stdin_used+0x8c0>
    6481:	31 c0                	xor    %eax,%eax
    6483:	bf 01 00 00 00       	mov    $0x1,%edi
    6488:	41 8b 0c 24          	mov    (%r12),%ecx
    648c:	e8 2f c0 ff ff       	call   24c0 <__printf_chk@plt>
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    6491:	be 04 00 00 00       	mov    $0x4,%esi
    6496:	bf 01 00 00 00       	mov    $0x1,%edi
    649b:	e8 70 bf ff ff       	call   2410 <calloc@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    64a0:	4c 63 85 10 01 00 00 	movslq 0x110(%rbp),%r8
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    64a7:	49 89 c6             	mov    %rax,%r14
    ourreply->nothing = msg->socket;
    64aa:	41 8b 04 24          	mov    (%r12),%eax
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    64ae:	49 c1 e0 04          	shl    $0x4,%r8
    64b2:	4c 03 85 08 01 00 00 	add    0x108(%rbp),%r8
  while (data->running == 1) {
    64b9:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    ourreply->nothing = msg->socket;
    64bd:	41 89 06             	mov    %eax,(%r14)
  while (data->running == 1) {
    64c0:	0f 85 82 00 00 00    	jne    6548 <io_thread+0x328>
      for (int x = 0 ; x < buffers->count ; x++) {
    64c6:	49 63 00             	movslq (%r8),%rax
    64c9:	85 c0                	test   %eax,%eax
    64cb:	0f 8e 45 08 00 00    	jle    6d16 <io_thread+0xaf6>
        if (buffers->buffer[x].available == 0) {
    64d1:	49 8b 50 08          	mov    0x8(%r8),%rdx
    64d5:	48 c1 e0 08          	shl    $0x8,%rax
    64d9:	45 31 e4             	xor    %r12d,%r12d
    64dc:	eb 12                	jmp    64f0 <io_thread+0x2d0>
    64de:	66 90                	xchg   %ax,%ax
      for (int x = 0 ; x < buffers->count ; x++) {
    64e0:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    64e7:	49 39 c4             	cmp    %rax,%r12
    64ea:	0f 84 26 08 00 00    	je     6d16 <io_thread+0xaf6>
        if (buffers->buffer[x].available == 0) {
    64f0:	42 8b 8c 22 80 00 00 00 	mov    0x80(%rdx,%r12,1),%ecx
    64f8:	85 c9                	test   %ecx,%ecx
    64fa:	75 e4                	jne    64e0 <io_thread+0x2c0>
    64fc:	42 8b 8c 22 98 00 00 00 	mov    0x98(%rdx,%r12,1),%ecx
    6504:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    650b:	bf 01 00 00 00       	mov    $0x1,%edi
    6510:	31 c0                	xor    %eax,%eax
    6512:	48 8d 35 07 2c 00 00 	lea    0x2c07(%rip),%rsi        # 9120 <_IO_stdin_used+0x120>
    6519:	4c 89 44 24 08       	mov    %r8,0x8(%rsp)
    651e:	e8 9d bf ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    6523:	4c 8b 44 24 08       	mov    0x8(%rsp),%r8
    6528:	4d 03 60 08          	add    0x8(%r8),%r12
    652c:	4d 89 34 24          	mov    %r14,(%r12)
          buffers->buffer[x].kind = kind;
    6530:	41 c7 84 24 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%r12)
          buffers->buffer[x].available = 1;
    653c:	41 c7 84 24 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r12)
    6548:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    654f:	48 8d 35 a2 33 00 00 	lea    0x33a2(%rip),%rsi        # 98f8 <_IO_stdin_used+0x8f8>
    6556:	bf 01 00 00 00       	mov    $0x1,%edi
    655b:	31 c0                	xor    %eax,%eax
    655d:	e8 5e bf ff ff       	call   24c0 <__printf_chk@plt>
    int new_client_socket = wait_for_new_client(data, 0);
    6562:	31 f6                	xor    %esi,%esi
    6564:	48 89 ef             	mov    %rbp,%rdi
    6567:	e8 a4 fb ff ff       	call   6110 <wait_for_new_client>
    656c:	48 8d 35 18 2d 00 00 	lea    0x2d18(%rip),%rsi        # 928b <_IO_stdin_used+0x28b>
    6573:	bf 01 00 00 00       	mov    $0x1,%edi
    6578:	89 c2                	mov    %eax,%edx
    657a:	41 89 c6             	mov    %eax,%r14d
    657d:	31 c0                	xor    %eax,%eax
    657f:	e8 3c bf ff ff       	call   24c0 <__printf_chk@plt>
    struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    6584:	be 0c 00 00 00       	mov    $0xc,%esi
    6589:	bf 01 00 00 00       	mov    $0x1,%edi
    658e:	e8 7d be ff ff       	call   2410 <calloc@plt>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    6593:	bf 01 00 00 00       	mov    $0x1,%edi
    6598:	be 10 00 00 00       	mov    $0x10,%esi
    ev->events = EPOLLOUT;
    659d:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
    struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    65a3:	49 89 c4             	mov    %rax,%r12
    ev->data.fd = new_client_socket;
    65a6:	44 89 70 04          	mov    %r14d,0x4(%rax)
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    65aa:	e8 61 be ff ff       	call   2410 <calloc@plt>
    void *buf = malloc(size);
    65af:	bf 0a 00 00 00       	mov    $0xa,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    65b4:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    void *buf = malloc(size);
    65b9:	e8 c2 be ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    65be:	48 85 c0             	test   %rax,%rax
    65c1:	0f 84 98 11 00 00    	je     775f <io_thread+0x153f>
    iov->iov_base = zh_malloc(10);
    65c7:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    65cc:	be 18 00 00 00       	mov    $0x18,%esi
    iov->iov_base = zh_malloc(10);
    65d1:	48 89 07             	mov    %rax,(%rdi)
    iov->iov_len = 10;
    65d4:	48 c7 47 08 0a 00 00 00 	movq   $0xa,0x8(%rdi)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    65dc:	bf 01 00 00 00       	mov    $0x1,%edi
    65e1:	e8 2a be ff ff       	call   2410 <calloc@plt>
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    65e6:	be 18 00 00 00       	mov    $0x18,%esi
    65eb:	bf 01 00 00 00       	mov    $0x1,%edi
    eventfdstop->kind = 3; 
    65f0:	c7 00 03 00 00 00    	movl   $0x3,(%rax)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    65f6:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    65fb:	e8 10 be ff ff       	call   2410 <calloc@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    6600:	8b 94 24 40 01 00 00 	mov    0x140(%rsp),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    6607:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
    660f:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    removed->kind = 7; 
    6614:	c7 00 07 00 00 00    	movl   $0x7,(%rax)
	unsigned int head, next = sq->sqe_tail + 1;
    661a:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    6621:	8b 31                	mov    (%rcx),%esi
	unsigned int head, next = sq->sqe_tail + 1;
    6623:	83 c0 01             	add    $0x1,%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6626:	f6 c2 02             	test   $0x2,%dl
    6629:	74 00                	je     662b <io_thread+0x40b>
	if (next - head <= sq->ring_entries) {
    662b:	89 c1                	mov    %eax,%ecx
    662d:	29 f1                	sub    %esi,%ecx
    662f:	39 8c 24 dc 00 00 00 	cmp    %ecx,0xdc(%rsp)
    6636:	0f 82 e4 bf ff ff    	jb     2620 <io_thread.cold+0xa>
	if (ring->flags & IORING_SETUP_SQE128)
    663c:	c1 ea 0a             	shr    $0xa,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    663f:	8b b4 24 c4 00 00 00 	mov    0xc4(%rsp),%esi
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6646:	44 89 f7             	mov    %r14d,%edi
	sqe->addr3 = 0;
    6649:	66 0f ef c0          	pxor   %xmm0,%xmm0
	if (ring->flags & IORING_SETUP_SQE128)
    664d:	83 e2 01             	and    $0x1,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6650:	23 b4 24 d8 00 00 00 	and    0xd8(%rsp),%esi
		sq->sqe_tail = next;
    6657:	89 84 24 c4 00 00 00 	mov    %eax,0xc4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
    665e:	89 d1                	mov    %edx,%ecx
	sqe->fd = fd;
    6660:	8b 44 24 04          	mov    0x4(%rsp),%eax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6664:	d3 e6                	shl    %cl,%esi
    6666:	48 c1 e6 06          	shl    $0x6,%rsi
    666a:	48 03 b4 24 b8 00 00 00 	add    0xb8(%rsp),%rsi
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6672:	48 89 7e 08          	mov    %rdi,0x8(%rsi)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6676:	49 89 f7             	mov    %rsi,%r15
          struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    6679:	bf 01 00 00 00       	mov    $0x1,%edi
	sqe->opcode = (__u8) op;
    667e:	c7 06 1d 00 00 00    	movl   $0x1d,(%rsi)
	sqe->fd = fd;
    6684:	89 46 04             	mov    %eax,0x4(%rsi)
	sqe->addr = (unsigned long) addr;
    6687:	4c 89 66 10          	mov    %r12,0x10(%rsi)
	sqe->len = len;
    668b:	48 c7 46 18 01 00 00 00 	movq   $0x1,0x18(%rsi)
	sqe->buf_index = 0;
    6693:	48 c7 46 28 00 00 00 00 	movq   $0x0,0x28(%rsi)
	sqe->addr3 = 0;
    669b:	0f 11 46 30          	movups %xmm0,0x30(%rsi)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    669f:	48 89 74 24 38       	mov    %rsi,0x38(%rsp)
    66a4:	be 18 00 00 00       	mov    $0x18,%esi
    66a9:	e8 62 bd ff ff       	call   2410 <calloc@plt>
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    66ae:	be 10 00 00 00       	mov    $0x10,%esi
    66b3:	bf 01 00 00 00       	mov    $0x1,%edi
          readywriting->kind = 4; 
    66b8:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
    66be:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    66c3:	e8 48 bd ff ff       	call   2410 <calloc@plt>
          readywriting->data = rr; 
    66c8:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
          io_uring_submit(&ring);
    66cd:	4c 89 ef             	mov    %r13,%rdi
          rr->client_socket = new_client_socket; 
    66d0:	44 89 30             	mov    %r14d,(%rax)
          readywriting->data = rr; 
    66d3:	48 89 46 08          	mov    %rax,0x8(%rsi)
          readywriting->event = ev; 
    66d7:	4c 89 66 10          	mov    %r12,0x10(%rsi)
	sqe->user_data = (unsigned long) data;
    66db:	49 89 77 20          	mov    %rsi,0x20(%r15)
          io_uring_submit(&ring);
    66df:	e8 bc bc ff ff       	call   23a0 <io_uring_submit@plt>
	sqe->fd = fd;
    66e4:	8b 44 24 04          	mov    0x4(%rsp),%eax
	sqe->opcode = (__u8) op;
    66e8:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
	sqe->off = offset;
    66ef:	49 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%r15)
	sqe->fd = fd;
    66f7:	41 89 47 04          	mov    %eax,0x4(%r15)
	sqe->addr = (unsigned long) addr;
    66fb:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
	sqe->len = len;
    6700:	49 c7 47 18 01 00 00 00 	movq   $0x1,0x18(%r15)
	sqe->buf_index = 0;
    6708:	49 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%r15)
	sqe->addr = (unsigned long) addr;
    6710:	49 89 47 10          	mov    %rax,0x10(%r15)
	sqe->buf_index = 0;
    6714:	4c 89 f8             	mov    %r15,%rax
    6717:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
	sqe->user_data = (unsigned long) data;
    6720:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
	sqe->addr3 = 0;
    6725:	66 0f ef c0          	pxor   %xmm0,%xmm0
          io_uring_submit(&ring);
    6729:	4c 89 ef             	mov    %r13,%rdi
    672c:	0f 11 40 30          	movups %xmm0,0x30(%rax)
	sqe->user_data = (unsigned long) data;
    6730:	48 89 70 20          	mov    %rsi,0x20(%rax)
    6734:	e8 67 bc ff ff       	call   23a0 <io_uring_submit@plt>
    while (data->running == 1) {
    6739:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    673d:	0f 85 20 02 00 00    	jne    6963 <io_thread+0x743>
  struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, nonblocking);
    6743:	4c 63 b5 14 01 00 00 	movslq 0x114(%rbp),%r14
    674a:	49 c1 e6 04          	shl    $0x4,%r14
    674e:	4c 03 b5 08 01 00 00 	add    0x108(%rbp),%r14
      for (int x = 0 ; x < buffers->count ; x++) {
    6755:	49 63 06             	movslq (%r14),%rax
    6758:	85 c0                	test   %eax,%eax
    675a:	0f 8e c8 05 00 00    	jle    6d28 <io_thread+0xb08>
        if (buffers->buffer[x].available == 1) {
    6760:	49 8b 4e 08          	mov    0x8(%r14),%rcx
    6764:	48 c1 e0 08          	shl    $0x8,%rax
    6768:	45 31 e4             	xor    %r12d,%r12d
    676b:	eb 0f                	jmp    677c <io_thread+0x55c>
    676d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    6770:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    6777:	49 39 c4             	cmp    %rax,%r12
    677a:	74 47                	je     67c3 <io_thread+0x5a3>
        if (buffers->buffer[x].available == 1) {
    677c:	42 83 bc 21 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx,%r12,1)
    6785:	75 e9                	jne    6770 <io_thread+0x550>
    6787:	46 8b 84 21 98 00 00 00 	mov    0x98(%rcx,%r12,1),%r8d
    678f:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    6796:	31 c0                	xor    %eax,%eax
    6798:	48 8d 0d fc 29 00 00 	lea    0x29fc(%rip),%rcx        # 919b <_IO_stdin_used+0x19b>
    679f:	48 8d 35 e5 29 00 00 	lea    0x29e5(%rip),%rsi        # 918b <_IO_stdin_used+0x18b>
    67a6:	bf 01 00 00 00       	mov    $0x1,%edi
    67ab:	e8 10 bd ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    67b0:	4d 03 66 08          	add    0x8(%r14),%r12
    67b4:	41 83 bc 24 98 00 00 00 02 	cmpl   $0x2,0x98(%r12)
    67bd:	0f 84 ed 01 00 00    	je     69b0 <io_thread+0x790>
        if (clients == 0) { continue; }
    67c3:	85 db                	test   %ebx,%ebx
    67c5:	0f 84 6e ff ff ff    	je     6739 <io_thread+0x519>
	if (ring->flags & IORING_SETUP_CQE32)
    67cb:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    67d2:	8b bc 24 30 01 00 00 	mov    0x130(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    67d9:	c1 e9 0b             	shr    $0xb,%ecx
    67dc:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    67df:	48 8b 84 24 f0 00 00 00 	mov    0xf0(%rsp),%rax
    67e7:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    67e9:	48 8b b4 24 e8 00 00 00 	mov    0xe8(%rsp),%rsi
    67f1:	8b 16                	mov    (%rsi),%edx
		if (!available)
    67f3:	39 d0                	cmp    %edx,%eax
    67f5:	74 36                	je     682d <io_thread+0x60d>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    67f7:	89 f8                	mov    %edi,%eax
    67f9:	21 d0                	and    %edx,%eax
    67fb:	d3 e0                	shl    %cl,%eax
    67fd:	48 c1 e0 04          	shl    $0x4,%rax
    6801:	48 03 84 24 18 01 00 00 	add    0x118(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    6809:	f6 84 24 49 01 00 00 01 	testb  $0x1,0x149(%rsp)
    6811:	0f 85 d7 02 00 00    	jne    6aee <io_thread+0x8ce>
    6817:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    681b:	0f 85 b7 0e 00 00    	jne    76d8 <io_thread+0x14b8>
			if (cqe->res < 0)
    6821:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6824:	83 c2 01             	add    $0x1,%edx
    6827:	89 16                	mov    %edx,(%rsi)
			if (!err)
    6829:	85 c0                	test   %eax,%eax
    682b:	79 b2                	jns    67df <io_thread+0x5bf>
	*cqe_ptr = cqe;
    682d:	48 c7 44 24 58 00 00 00 00 	movq   $0x0,0x58(%rsp)
	return err;
    6836:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    6840:	48 8d 74 24 58       	lea    0x58(%rsp),%rsi
    6845:	45 31 c0             	xor    %r8d,%r8d
    6848:	b9 01 00 00 00       	mov    $0x1,%ecx
    684d:	31 d2                	xor    %edx,%edx
    684f:	4c 89 ef             	mov    %r13,%rdi
    6852:	e8 59 bc ff ff       	call   24b0 <__io_uring_get_cqe@plt>
    6857:	41 89 c7             	mov    %eax,%r15d
    685a:	48 8d 35 50 2a 00 00 	lea    0x2a50(%rip),%rsi        # 92b1 <_IO_stdin_used+0x2b1>
    6861:	bf 01 00 00 00       	mov    $0x1,%edi
    6866:	31 c0                	xor    %eax,%eax
    6868:	e8 53 bc ff ff       	call   24c0 <__printf_chk@plt>
        printf("kind %d\n", ((struct SendUserData*) cqe->user_data)->kind);
    686d:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    6872:	bf 01 00 00 00       	mov    $0x1,%edi
    6877:	48 8d 35 41 2a 00 00 	lea    0x2a41(%rip),%rsi        # 92bf <_IO_stdin_used+0x2bf>
    687e:	48 8b 00             	mov    (%rax),%rax
    6881:	8b 10                	mov    (%rax),%edx
    6883:	31 c0                	xor    %eax,%eax
    6885:	e8 36 bc ff ff       	call   24c0 <__printf_chk@plt>
        if (((struct SendUserData*) cqe->user_data)->kind == 3) {
    688a:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    688f:	4c 8b 30             	mov    (%rax),%r14
    6892:	41 8b 06             	mov    (%r14),%eax
    6895:	4c 89 f2             	mov    %r14,%rdx
    6898:	83 f8 03             	cmp    $0x3,%eax
    689b:	0f 84 a7 00 00 00    	je     6948 <io_thread+0x728>
        if (((struct SendUserData*) cqe->user_data)->kind == 4) {
    68a1:	83 f8 04             	cmp    $0x4,%eax
    68a4:	0f 84 5e 02 00 00    	je     6b08 <io_thread+0x8e8>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
    68aa:	83 f8 05             	cmp    $0x5,%eax
    68ad:	0f 84 0b 03 00 00    	je     6bbe <io_thread+0x99e>
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    68b3:	83 f8 07             	cmp    $0x7,%eax
    68b6:	0f 84 3a 04 00 00    	je     6cf6 <io_thread+0xad6>
	unsigned int head, next = sq->sqe_tail + 1;
    68bc:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    68c3:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    68ca:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    68cd:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    68d5:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    68d7:	f6 c1 02             	test   $0x2,%cl
    68da:	74 00                	je     68dc <io_thread+0x6bc>
	if (next - head <= sq->ring_entries) {
    68dc:	89 d0                	mov    %edx,%eax
    68de:	29 f0                	sub    %esi,%eax
    68e0:	39 84 24 dc 00 00 00 	cmp    %eax,0xdc(%rsp)
    68e7:	0f 82 ad bd ff ff    	jb     269a <io_thread.cold+0x84>
	if (ring->flags & IORING_SETUP_SQE128)
    68ed:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    68f0:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
		sq->sqe_tail = next;
    68f7:	89 94 24 c4 00 00 00 	mov    %edx,0xc4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    68fe:	23 84 24 d8 00 00 00 	and    0xd8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6905:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6908:	d3 e0                	shl    %cl,%eax
    690a:	48 c1 e0 06          	shl    $0x6,%rax
    690e:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6916:	8b 55 68             	mov    0x68(%rbp),%edx
	sqe->opcode = (__u8) op;
    6919:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->addr = (unsigned long) addr;
    691f:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
	sqe->off = offset;
    6924:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->fd = fd;
    692c:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->addr = (unsigned long) addr;
    692f:	48 89 78 10          	mov    %rdi,0x10(%rax)
	sqe->len = len;
    6933:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    693b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
    6943:	e9 d8 fd ff ff       	jmp    6720 <io_thread+0x500>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6948:	48 8b 94 24 e8 00 00 00 	mov    0xe8(%rsp),%rdx
    6950:	48 8d 3d a2 28 00 00 	lea    0x28a2(%rip),%rdi        # 91f9 <_IO_stdin_used+0x1f9>
    6957:	8b 02                	mov    (%rdx),%eax
    6959:	83 c0 01             	add    $0x1,%eax
    695c:	89 02                	mov    %eax,(%rdx)
    695e:	e8 dd b9 ff ff       	call   2340 <puts@plt>
    6963:	48 8d 3d c0 29 00 00 	lea    0x29c0(%rip),%rdi        # 932a <_IO_stdin_used+0x32a>
    696a:	e8 d1 b9 ff ff       	call   2340 <puts@plt>
    696f:	48 8d 3d c3 29 00 00 	lea    0x29c3(%rip),%rdi        # 9339 <_IO_stdin_used+0x339>
    6976:	e8 c5 b9 ff ff       	call   2340 <puts@plt>
}
    697b:	48 8b 84 24 68 05 00 00 	mov    0x568(%rsp),%rax
    6983:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    698c:	0f 85 a1 0d 00 00    	jne    7733 <io_thread+0x1513>
    6992:	48 81 c4 78 05 00 00 	add    $0x578,%rsp
    6999:	31 c0                	xor    %eax,%eax
    699b:	5b                   	pop    %rbx
    699c:	5d                   	pop    %rbp
    699d:	41 5c                	pop    %r12
    699f:	41 5d                	pop    %r13
    69a1:	41 5e                	pop    %r14
    69a3:	41 5f                	pop    %r15
    69a5:	c3                   	ret
      for (int x = 0 ; x < buffers->count ; x++) {
    69a6:	eb fe                	jmp    69a6 <io_thread+0x786>
    69a8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    69b0:	be 00 01 00 00       	mov    $0x100,%esi
    69b5:	bf 01 00 00 00       	mov    $0x1,%edi
    69ba:	e8 51 ba ff ff       	call   2410 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    69bf:	49 8b 14 24          	mov    (%r12),%rdx
            buffers->buffer[x].available = 0;
    69c3:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
            reply->kind = buffers->buffer[x].kind;
    69cf:	c7 80 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%rax)
            reply->data = buffers->buffer[x].data;
    69d9:	48 89 10             	mov    %rdx,(%rax)
  return newclientmsg->socket;
    69dc:	48 8b 00             	mov    (%rax),%rax
    69df:	44 8b 20             	mov    (%rax),%r12d
        if (new_client_socket != -1) {
    69e2:	41 83 fc ff          	cmp    $0xffffffff,%r12d
    69e6:	0f 84 d7 fd ff ff    	je     67c3 <io_thread+0x5a3>
    69ec:	44 89 e2             	mov    %r12d,%edx
    69ef:	48 8d 35 a8 28 00 00 	lea    0x28a8(%rip),%rsi        # 929e <_IO_stdin_used+0x29e>
    69f6:	bf 01 00 00 00       	mov    $0x1,%edi
    69fb:	31 c0                	xor    %eax,%eax
    69fd:	e8 be ba ff ff       	call   24c0 <__printf_chk@plt>
          struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    6a02:	be 0c 00 00 00       	mov    $0xc,%esi
    6a07:	bf 01 00 00 00       	mov    $0x1,%edi
    6a0c:	e8 ff b9 ff ff       	call   2410 <calloc@plt>
          struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    6a11:	be 18 00 00 00       	mov    $0x18,%esi
    6a16:	bf 01 00 00 00       	mov    $0x1,%edi
          ev->events = EPOLLOUT;
    6a1b:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
          struct epoll_event *ev = calloc(1, sizeof(struct epoll_event));
    6a21:	49 89 c7             	mov    %rax,%r15
          ev->data.fd = new_client_socket;
    6a24:	44 89 60 04          	mov    %r12d,0x4(%rax)
          struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    6a28:	e8 e3 b9 ff ff       	call   2410 <calloc@plt>
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    6a2d:	be 10 00 00 00       	mov    $0x10,%esi
    6a32:	bf 01 00 00 00       	mov    $0x1,%edi
          readywriting->kind = 4; 
    6a37:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
          struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    6a3d:	49 89 c6             	mov    %rax,%r14
          readywriting->event = ev;
    6a40:	4c 89 78 10          	mov    %r15,0x10(%rax)
          struct ReadyWriting *rr = calloc(1, sizeof(struct ReadyWriting));
    6a44:	e8 c7 b9 ff ff       	call   2410 <calloc@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    6a49:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
          rr->client_socket = new_client_socket; 
    6a50:	44 89 20             	mov    %r12d,(%rax)
          readywriting->data = rr; 
    6a53:	49 89 46 08          	mov    %rax,0x8(%r14)
	unsigned int head, next = sq->sqe_tail + 1;
    6a57:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
    6a5e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    6a61:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6a69:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6a6b:	f6 c1 02             	test   $0x2,%cl
    6a6e:	74 00                	je     6a70 <io_thread+0x850>
	if (next - head <= sq->ring_entries) {
    6a70:	89 d0                	mov    %edx,%eax
    6a72:	29 f0                	sub    %esi,%eax
    6a74:	39 84 24 dc 00 00 00 	cmp    %eax,0xdc(%rsp)
    6a7b:	0f 82 f9 bb ff ff    	jb     267a <io_thread.cold+0x64>
	if (ring->flags & IORING_SETUP_SQE128)
    6a81:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6a84:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6a8b:	44 89 e6             	mov    %r12d,%esi
          clients++;
    6a8e:	83 c3 01             	add    $0x1,%ebx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6a91:	23 84 24 d8 00 00 00 	and    0xd8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6a98:	83 e1 01             	and    $0x1,%ecx
	sqe->fd = fd;
    6a9b:	8b 7c 24 04          	mov    0x4(%rsp),%edi
		sq->sqe_tail = next;
    6a9f:	89 94 24 c4 00 00 00 	mov    %edx,0xc4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6aa6:	d3 e0                	shl    %cl,%eax
	sqe->addr3 = 0;
    6aa8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6aac:	48 c1 e0 06          	shl    $0x6,%rax
    6ab0:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
	sqe->fd = fd;
    6ab8:	89 78 04             	mov    %edi,0x4(%rax)
          io_uring_submit(&ring);
    6abb:	4c 89 ef             	mov    %r13,%rdi
	sqe->opcode = (__u8) op;
    6abe:	c7 00 1d 00 00 00    	movl   $0x1d,(%rax)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6ac4:	48 89 70 08          	mov    %rsi,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    6ac8:	4c 89 78 10          	mov    %r15,0x10(%rax)
	sqe->len = len;
    6acc:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    6ad4:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    6adc:	4c 89 70 20          	mov    %r14,0x20(%rax)
	sqe->addr3 = 0;
    6ae0:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    6ae4:	e8 b7 b8 ff ff       	call   23a0 <io_uring_submit@plt>
          clients++;
    6ae9:	e9 d5 fc ff ff       	jmp    67c3 <io_thread+0x5a3>
	*cqe_ptr = cqe;
    6aee:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    6af3:	48 85 c0             	test   %rax,%rax
    6af6:	0f 84 44 fd ff ff    	je     6840 <io_thread+0x620>
		return 0;
    6afc:	45 31 ff             	xor    %r15d,%r15d
    6aff:	e9 56 fd ff ff       	jmp    685a <io_thread+0x63a>
    6b04:	0f 1f 40 00          	nopl   0x0(%rax)
          struct Buffer *send = bufferrecv("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1);
    6b08:	4c 63 95 14 01 00 00 	movslq 0x114(%rbp),%r10
          struct ReadyWriting *rr = readywriting->data;
    6b0f:	4d 8b 4e 08          	mov    0x8(%r14),%r9
          struct Buffer *send = bufferrecv("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1);
    6b13:	49 c1 e2 04          	shl    $0x4,%r10
    6b17:	4c 03 95 08 01 00 00 	add    0x108(%rbp),%r10
  while (data->running == 1) {
    6b1e:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    6b22:	0f 85 94 fd ff ff    	jne    68bc <io_thread+0x69c>
      for (int x = 0 ; x < buffers->count ; x++) {
    6b28:	49 63 02             	movslq (%r10),%rax
    6b2b:	85 c0                	test   %eax,%eax
    6b2d:	0f 8e 89 fd ff ff    	jle    68bc <io_thread+0x69c>
        if (buffers->buffer[x].available == 1) {
    6b33:	49 8b 4a 08          	mov    0x8(%r10),%rcx
    6b37:	48 c1 e0 08          	shl    $0x8,%rax
    6b3b:	45 31 e4             	xor    %r12d,%r12d
    6b3e:	eb 10                	jmp    6b50 <io_thread+0x930>
      for (int x = 0 ; x < buffers->count ; x++) {
    6b40:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    6b47:	4c 39 e0             	cmp    %r12,%rax
    6b4a:	0f 84 6c fd ff ff    	je     68bc <io_thread+0x69c>
        if (buffers->buffer[x].available == 1) {
    6b50:	42 83 bc 21 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx,%r12,1)
    6b59:	75 e5                	jne    6b40 <io_thread+0x920>
    6b5b:	46 8b 84 21 98 00 00 00 	mov    0x98(%rcx,%r12,1),%r8d
    6b63:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    6b6a:	31 c0                	xor    %eax,%eax
    6b6c:	48 8d 0d 70 27 00 00 	lea    0x2770(%rip),%rcx        # 92e3 <_IO_stdin_used+0x2e3>
    6b73:	48 8d 35 11 26 00 00 	lea    0x2611(%rip),%rsi        # 918b <_IO_stdin_used+0x18b>
    6b7a:	bf 01 00 00 00       	mov    $0x1,%edi
    6b7f:	4c 89 54 24 30       	mov    %r10,0x30(%rsp)
    6b84:	4c 89 4c 24 28       	mov    %r9,0x28(%rsp)
    6b89:	e8 32 b9 ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    6b8e:	4c 8b 54 24 30       	mov    0x30(%rsp),%r10
    6b93:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
    6b98:	4d 03 62 08          	add    0x8(%r10),%r12
    6b9c:	41 83 bc 24 98 00 00 00 02 	cmpl   $0x2,0x98(%r12)
    6ba5:	0f 84 ab 01 00 00    	je     6d56 <io_thread+0xb36>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
    6bab:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    6bb0:	48 8b 10             	mov    (%rax),%rdx
    6bb3:	8b 02                	mov    (%rdx),%eax
    6bb5:	83 f8 05             	cmp    $0x5,%eax
    6bb8:	0f 85 f5 fc ff ff    	jne    68b3 <io_thread+0x693>
    6bbe:	48 8d 35 24 27 00 00 	lea    0x2724(%rip),%rsi        # 92e9 <_IO_stdin_used+0x2e9>
    6bc5:	bf 01 00 00 00       	mov    $0x1,%edi
    6bca:	31 c0                	xor    %eax,%eax
    6bcc:	e8 ef b8 ff ff       	call   24c0 <__printf_chk@plt>
    6bd1:	48 8d 3d 1d 27 00 00 	lea    0x271d(%rip),%rdi        # 92f5 <_IO_stdin_used+0x2f5>
    6bd8:	e8 63 b7 ff ff       	call   2340 <puts@plt>
          struct Request *req = ((struct SendUserData *) cqe->user_data)->data;
    6bdd:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    6be2:	48 8b 10             	mov    (%rax),%rdx
    6be5:	4c 8b 72 08          	mov    0x8(%rdx),%r14
          if (ret < 0)
    6be9:	45 85 ff             	test   %r15d,%r15d
    6bec:	0f 88 92 ba ff ff    	js     2684 <io_thread.cold+0x6e>
    6bf2:	8b 50 08             	mov    0x8(%rax),%edx
    6bf5:	48 8d 35 0c 27 00 00 	lea    0x270c(%rip),%rsi        # 9308 <_IO_stdin_used+0x308>
    6bfc:	bf 01 00 00 00       	mov    $0x1,%edi
    6c01:	31 c0                	xor    %eax,%eax
    6c03:	e8 b8 b8 ff ff       	call   24c0 <__printf_chk@plt>
          if (cqe->res < 0) {
    6c08:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    6c0d:	8b 40 08             	mov    0x8(%rax),%eax
    6c10:	85 c0                	test   %eax,%eax
    6c12:	0f 88 6e 0b 00 00    	js     7786 <io_thread+0x1566>
          switch (req->event_type) {
    6c18:	41 8b 16             	mov    (%r14),%edx
    6c1b:	83 fa 01             	cmp    $0x1,%edx
    6c1e:	0f 84 e4 02 00 00    	je     6f08 <io_thread+0xce8>
    6c24:	83 fa 02             	cmp    $0x2,%edx
    6c27:	0f 85 0b 01 00 00    	jne    6d38 <io_thread+0xb18>
                  for (int i = 0; i < req->iovec_count; i++) {
    6c2d:	41 8b 46 04          	mov    0x4(%r14),%eax
    6c31:	45 31 e4             	xor    %r12d,%r12d
    6c34:	85 c0                	test   %eax,%eax
    6c36:	7e 23                	jle    6c5b <io_thread+0xa3b>
    6c38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
                      free(req->iov[i].iov_base);
    6c40:	4c 89 e0             	mov    %r12,%rax
                  for (int i = 0; i < req->iovec_count; i++) {
    6c43:	49 83 c4 01          	add    $0x1,%r12
                      free(req->iov[i].iov_base);
    6c47:	48 c1 e0 04          	shl    $0x4,%rax
    6c4b:	49 8b 7c 06 10       	mov    0x10(%r14,%rax,1),%rdi
    6c50:	e8 bb b6 ff ff       	call   2310 <free@plt>
                  for (int i = 0; i < req->iovec_count; i++) {
    6c55:	45 39 66 04          	cmp    %r12d,0x4(%r14)
    6c59:	7f e5                	jg     6c40 <io_thread+0xa20>
    6c5b:	41 8b 56 08          	mov    0x8(%r14),%edx
    6c5f:	48 8d 35 aa 26 00 00 	lea    0x26aa(%rip),%rsi        # 9310 <_IO_stdin_used+0x310>
    6c66:	31 c0                	xor    %eax,%eax
                  clients--;
    6c68:	83 eb 01             	sub    $0x1,%ebx
    6c6b:	bf 01 00 00 00       	mov    $0x1,%edi
    6c70:	e8 4b b8 ff ff       	call   24c0 <__printf_chk@plt>
                  io_uring_prep_epoll_ctl(sqe, epollfd, req->client_socket, EPOLL_CTL_DEL, readywriting->event);
    6c75:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6c7a:	66 41 0f 6e 46 08    	movd   0x8(%r14),%xmm0
	sqe->user_data = (unsigned long) data;
    6c80:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
	sqe->fd = fd;
    6c85:	8b 7c 24 04          	mov    0x4(%rsp),%edi
    6c89:	f3 0f 7e 48 10       	movq   0x10(%rax),%xmm1
	sqe->opcode = (__u8) op;
    6c8e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	sqe->off = offset;
    6c93:	66 0f 6c c1          	punpcklqdq %xmm1,%xmm0
	sqe->user_data = (unsigned long) data;
    6c97:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->fd = fd;
    6c9b:	89 78 04             	mov    %edi,0x4(%rax)
                  io_uring_submit(&ring);
    6c9e:	4c 89 ef             	mov    %r13,%rdi
	sqe->opcode = (__u8) op;
    6ca1:	c7 00 1d 00 00 00    	movl   $0x1d,(%rax)
	sqe->len = len;
    6ca7:	48 c7 40 18 02 00 00 00 	movq   $0x2,0x18(%rax)
	sqe->buf_index = 0;
    6caf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->off = offset;
    6cb7:	0f 11 40 08          	movups %xmm0,0x8(%rax)
	sqe->addr3 = 0;
    6cbb:	66 0f ef c0          	pxor   %xmm0,%xmm0
    6cbf:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    6cc3:	e8 d8 b6 ff ff       	call   23a0 <io_uring_submit@plt>
                  close(req->client_socket);
    6cc8:	41 8b 7e 08          	mov    0x8(%r14),%edi
    6ccc:	e8 0f b7 ff ff       	call   23e0 <close@plt>
                  free(req);
    6cd1:	4c 89 f7             	mov    %r14,%rdi
    6cd4:	e8 37 b6 ff ff       	call   2310 <free@plt>
            io_uring_cqe_seen(&ring, cqe);
    6cd9:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
	if (cqe)
    6cde:	48 85 c0             	test   %rax,%rax
    6ce1:	75 55                	jne    6d38 <io_thread+0xb18>
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    6ce3:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    6ceb:	8b 00                	mov    (%rax),%eax
    6ced:	83 f8 07             	cmp    $0x7,%eax
    6cf0:	0f 85 c6 fb ff ff    	jne    68bc <io_thread+0x69c>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6cf6:	48 8b 94 24 e8 00 00 00 	mov    0xe8(%rsp),%rdx
    6cfe:	48 8d 3d 1d 26 00 00 	lea    0x261d(%rip),%rdi        # 9322 <_IO_stdin_used+0x322>
    6d05:	8b 02                	mov    (%rdx),%eax
    6d07:	83 c0 01             	add    $0x1,%eax
    6d0a:	89 02                	mov    %eax,(%rdx)
    6d0c:	e8 2f b6 ff ff       	call   2340 <puts@plt>
    6d11:	e9 a6 fb ff ff       	jmp    68bc <io_thread+0x69c>
  while (data->running == 1) {
    6d16:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    6d1a:	0f 84 a6 f7 ff ff    	je     64c6 <io_thread+0x2a6>
    6d20:	e9 23 f8 ff ff       	jmp    6548 <io_thread+0x328>
    6d25:	0f 1f 00             	nopl   (%rax)
        if (clients == 0) { continue; }
    6d28:	85 db                	test   %ebx,%ebx
    6d2a:	0f 85 9b fa ff ff    	jne    67cb <io_thread+0x5ab>
    while (data->running == 1) {
    6d30:	eb fe                	jmp    6d30 <io_thread+0xb10>
    6d32:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    6d38:	48 8b 94 24 e8 00 00 00 	mov    0xe8(%rsp),%rdx
    6d40:	8b 02                	mov    (%rdx),%eax
    6d42:	83 c0 01             	add    $0x1,%eax
    6d45:	89 02                	mov    %eax,(%rdx)
          if (((struct SendUserData*) cqe->user_data)->kind == 7) { 
    6d47:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    6d4c:	48 8b 00             	mov    (%rax),%rax
    6d4f:	8b 00                	mov    (%rax),%eax
}
    6d51:	e9 5d fb ff ff       	jmp    68b3 <io_thread+0x693>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6d56:	be 00 01 00 00       	mov    $0x100,%esi
    6d5b:	bf 01 00 00 00       	mov    $0x1,%edi
    6d60:	4c 89 4c 24 28       	mov    %r9,0x28(%rsp)
    6d65:	e8 a6 b6 ff ff       	call   2410 <calloc@plt>
            buffers->buffer[x].available = 0;
    6d6a:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6d76:	49 89 c7             	mov    %rax,%r15
            reply->data = buffers->buffer[x].data;
    6d79:	49 8b 04 24          	mov    (%r12),%rax
            reply->kind = buffers->buffer[x].kind;
    6d7d:	41 c7 87 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%r15)
            reply->data = buffers->buffer[x].data;
    6d88:	49 89 07             	mov    %rax,(%r15)
    6d8b:	48 8d 3d 36 25 00 00 	lea    0x2536(%rip),%rdi        # 92c8 <_IO_stdin_used+0x2c8>
    6d92:	e8 a9 b5 ff ff       	call   2340 <puts@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    6d97:	8b b4 24 c4 00 00 00 	mov    0xc4(%rsp),%esi
            struct Write *write = send->data;
    6d9e:	49 8b 07             	mov    (%r15),%rax
	if (ring->flags & IORING_SETUP_SQE128)
    6da1:	8b 94 24 40 01 00 00 	mov    0x140(%rsp),%edx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6da8:	4c 8b 4c 24 28       	mov    0x28(%rsp),%r9
	unsigned int head, next = sq->sqe_tail + 1;
    6dad:	83 c6 01             	add    $0x1,%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6db0:	f6 c2 02             	test   $0x2,%dl
    6db3:	0f 84 da 08 00 00    	je     7693 <io_thread+0x1473>
		head = io_uring_smp_load_acquire(sq->khead);
    6db9:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
    6dc1:	8b 09                	mov    (%rcx),%ecx
            struct Request *req = write->request;
    6dc3:	4c 8b 38             	mov    (%rax),%r15
	if (next - head <= sq->ring_entries) {
    6dc6:	89 f0                	mov    %esi,%eax
    6dc8:	29 c8                	sub    %ecx,%eax
    6dca:	39 84 24 dc 00 00 00 	cmp    %eax,0xdc(%rsp)
    6dd1:	0f 82 d7 b8 ff ff    	jb     26ae <io_thread.cold+0x98>
	if (ring->flags & IORING_SETUP_SQE128)
    6dd7:	c1 ea 0a             	shr    $0xa,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6dda:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	sqe->addr3 = 0;
    6de1:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6de5:	23 84 24 d8 00 00 00 	and    0xd8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6dec:	83 e2 01             	and    $0x1,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6def:	41 89 c4             	mov    %eax,%r12d
            io_uring_prep_writev(sqe, rr->client_socket, req->iov, req->iovec_count, 0);
    6df2:	41 8b 47 04          	mov    0x4(%r15),%eax
		sq->sqe_tail = next;
    6df6:	89 b4 24 c4 00 00 00 	mov    %esi,0xc4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
    6dfd:	89 d1                	mov    %edx,%ecx
    6dff:	41 8b 11             	mov    (%r9),%edx
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    6e02:	be 18 00 00 00       	mov    $0x18,%esi
    6e07:	bf 01 00 00 00       	mov    $0x1,%edi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6e0c:	41 d3 e4             	shl    %cl,%r12d
    6e0f:	49 c1 e4 06          	shl    $0x6,%r12
    6e13:	4c 03 a4 24 b8 00 00 00 	add    0xb8(%rsp),%r12
            req->event_type = EVENT_TYPE_WRITE;
    6e1b:	41 c7 07 02 00 00 00 	movl   $0x2,(%r15)
	sqe->fd = fd;
    6e22:	41 89 54 24 04       	mov    %edx,0x4(%r12)
            io_uring_prep_writev(sqe, rr->client_socket, req->iov, req->iovec_count, 0);
    6e27:	49 8d 57 10          	lea    0x10(%r15),%rdx
    6e2b:	49 89 54 24 10       	mov    %rdx,0x10(%r12)
	sqe->opcode = (__u8) op;
    6e30:	41 c7 04 24 02 00 00 00 	movl   $0x2,(%r12)
	sqe->off = offset;
    6e38:	49 c7 44 24 08 00 00 00 00 	movq   $0x0,0x8(%r12)
	sqe->len = len;
    6e41:	41 89 44 24 18       	mov    %eax,0x18(%r12)
	sqe->rw_flags = 0;
    6e46:	41 c7 44 24 1c 00 00 00 00 	movl   $0x0,0x1c(%r12)
	sqe->buf_index = 0;
    6e4f:	49 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%r12)
	sqe->addr3 = 0;
    6e58:	41 0f 11 44 24 30    	movups %xmm0,0x30(%r12)
            struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    6e5e:	e8 ad b5 ff ff       	call   2410 <calloc@plt>
            finishedwrite->data = req;
    6e63:	66 49 0f 6e c7       	movq   %r15,%xmm0
            io_uring_submit(&ring);
    6e68:	4c 89 ef             	mov    %r13,%rdi
            finishedwrite->data = req;
    6e6b:	41 0f 16 46 10       	movhps 0x10(%r14),%xmm0
            finishedwrite->kind = 5; 
    6e70:	c7 00 05 00 00 00    	movl   $0x5,(%rax)
            finishedwrite->data = req;
    6e76:	0f 11 40 08          	movups %xmm0,0x8(%rax)
	sqe->user_data = (unsigned long) data;
    6e7a:	49 89 44 24 20       	mov    %rax,0x20(%r12)
            io_uring_submit(&ring);
    6e7f:	e8 1c b5 ff ff       	call   23a0 <io_uring_submit@plt>
	if (cqe)
    6e84:	48 83 7c 24 58 00    	cmpq   $0x0,0x58(%rsp)
    6e8a:	74 0f                	je     6e9b <io_thread+0xc7b>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6e8c:	48 8b 94 24 e8 00 00 00 	mov    0xe8(%rsp),%rdx
    6e94:	8b 02                	mov    (%rdx),%eax
    6e96:	83 c0 01             	add    $0x1,%eax
    6e99:	89 02                	mov    %eax,(%rdx)
    6e9b:	48 8d 3d 37 24 00 00 	lea    0x2437(%rip),%rdi        # 92d9 <_IO_stdin_used+0x2d9>
    6ea2:	e8 99 b4 ff ff       	call   2340 <puts@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    6ea7:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6eae:	8b 94 24 40 01 00 00 	mov    0x140(%rsp),%edx
	unsigned int head, next = sq->sqe_tail + 1;
    6eb5:	8d 70 01             	lea    0x1(%rax),%esi
		head = IO_URING_READ_ONCE(*sq->khead);
    6eb8:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    6ec0:	8b 08                	mov    (%rax),%ecx
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6ec2:	f6 c2 02             	test   $0x2,%dl
    6ec5:	74 00                	je     6ec7 <io_thread+0xca7>
	if (next - head <= sq->ring_entries) {
    6ec7:	89 f0                	mov    %esi,%eax
    6ec9:	29 c8                	sub    %ecx,%eax
    6ecb:	39 84 24 dc 00 00 00 	cmp    %eax,0xdc(%rsp)
    6ed2:	0f 82 cc b7 ff ff    	jb     26a4 <io_thread.cold+0x8e>
	if (ring->flags & IORING_SETUP_SQE128)
    6ed8:	c1 ea 0a             	shr    $0xa,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6edb:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
    6ee2:	23 84 24 d8 00 00 00 	and    0xd8(%rsp),%eax
		sq->sqe_tail = next;
    6ee9:	89 b4 24 c4 00 00 00 	mov    %esi,0xc4(%rsp)
	if (ring->flags & IORING_SETUP_SQE128)
    6ef0:	83 e2 01             	and    $0x1,%edx
    6ef3:	89 d1                	mov    %edx,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6ef5:	d3 e0                	shl    %cl,%eax
    6ef7:	48 c1 e0 06          	shl    $0x6,%rax
    6efb:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
              io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6f03:	e9 0e fa ff ff       	jmp    6916 <io_thread+0x6f6>
                  if (!cqe->res) {
    6f08:	85 c0                	test   %eax,%eax
    6f0a:	0f 85 92 07 00 00    	jne    76a2 <io_thread+0x1482>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6f10:	48 8b 0d 09 51 00 00 	mov    0x5109(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6f17:	ba 0f 00 00 00       	mov    $0xf,%edx
    6f1c:	be 01 00 00 00       	mov    $0x1,%esi
    6f21:	48 8d 3d 15 23 00 00 	lea    0x2315(%rip),%rdi        # 923d <_IO_stdin_used+0x23d>
    6f28:	e8 13 b6 ff ff       	call   2540 <fwrite@plt>
            io_uring_cqe_seen(&ring, cqe);
    6f2d:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    6f32:	e9 a7 fd ff ff       	jmp    6cde <io_thread+0xabe>
    sock = socket(PF_INET, SOCK_STREAM, 0);
    6f37:	31 d2                	xor    %edx,%edx
    6f39:	be 01 00 00 00       	mov    $0x1,%esi
    6f3e:	bf 02 00 00 00       	mov    $0x2,%edi
    6f43:	e8 88 b6 ff ff       	call   25d0 <socket@plt>
    6f48:	89 44 24 04          	mov    %eax,0x4(%rsp)
    if (sock == -1)
    6f4c:	83 f8 ff             	cmp    $0xffffffff,%eax
    6f4f:	0f 84 d5 b6 ff ff    	je     262a <io_thread.cold+0x14>
    6f55:	89 c7                	mov    %eax,%edi
    if (setsockopt(sock,
    6f57:	48 8d 4c 24 48       	lea    0x48(%rsp),%rcx
    6f5c:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    6f62:	ba 02 00 00 00       	mov    $0x2,%edx
    6f67:	be 01 00 00 00       	mov    $0x1,%esi
    int enable = 1;
    6f6c:	c7 44 24 48 01 00 00 00 	movl   $0x1,0x48(%rsp)
    if (setsockopt(sock,
    6f74:	e8 d7 b3 ff ff       	call   2350 <setsockopt@plt>
    6f79:	85 c0                	test   %eax,%eax
    6f7b:	0f 88 bf b6 ff ff    	js     2640 <io_thread.cold+0x2a>
    if (bind(sock,
    6f81:	8b 7c 24 04          	mov    0x4(%rsp),%edi
  return __builtin___memset_chk (__dest, __ch, __len,
    6f85:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
    6f8a:	ba 10 00 00 00       	mov    $0x10,%edx
    6f8f:	48 c7 44 24 64 00 00 00 00 	movq   $0x0,0x64(%rsp)
    6f98:	c7 44 24 6c 00 00 00 00 	movl   $0x0,0x6c(%rsp)
    srv_addr.sin_family = AF_INET;
    6fa0:	c7 44 24 60 02 00 18 db 	movl   $0xdb180002,0x60(%rsp)
    if (bind(sock,
    6fa8:	e8 23 b5 ff ff       	call   24d0 <bind@plt>
    6fad:	85 c0                	test   %eax,%eax
    6faf:	0f 88 97 b6 ff ff    	js     264c <io_thread.cold+0x36>
    if (listen(sock, 10) < 0) {
    6fb5:	8b 7c 24 04          	mov    0x4(%rsp),%edi
    6fb9:	be 0a 00 00 00       	mov    $0xa,%esi
    6fbe:	e8 cd b4 ff ff       	call   2490 <listen@plt>
    6fc3:	85 c0                	test   %eax,%eax
    6fc5:	0f 88 a3 b6 ff ff    	js     266e <io_thread.cold+0x58>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6fcb:	8b 5c 24 04          	mov    0x4(%rsp),%ebx
    6fcf:	ba db 18 00 00       	mov    $0x18db,%edx
    6fd4:	bf 01 00 00 00       	mov    $0x1,%edi
    6fd9:	31 c0                	xor    %eax,%eax
    6fdb:	48 8d 35 76 27 00 00 	lea    0x2776(%rip),%rsi        # 9758 <_IO_stdin_used+0x758>
    6fe2:	89 d9                	mov    %ebx,%ecx
    6fe4:	e8 d7 b4 ff ff       	call   24c0 <__printf_chk@plt>
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    6fe9:	be 04 00 00 00       	mov    $0x4,%esi
    6fee:	bf 01 00 00 00       	mov    $0x1,%edi
    6ff3:	e8 18 b4 ff ff       	call   2410 <calloc@plt>
    6ff8:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    6fff:	bf 01 00 00 00       	mov    $0x1,%edi
    7004:	48 8d 35 6d 27 00 00 	lea    0x276d(%rip),%rsi        # 9778 <_IO_stdin_used+0x778>
    msg->socket = sock;
    700b:	89 18                	mov    %ebx,(%rax)
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    700d:	49 89 c6             	mov    %rax,%r14
    7010:	31 c0                	xor    %eax,%eax
    7012:	e8 a9 b4 ff ff       	call   24c0 <__printf_chk@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET, msg);
    7017:	4c 63 bd 10 01 00 00 	movslq 0x110(%rbp),%r15
    701e:	4c 8b 8d 08 01 00 00 	mov    0x108(%rbp),%r9
  while (data->running == 1) {
    7025:	8b 45 44             	mov    0x44(%rbp),%eax
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET, msg);
    7028:	49 c1 e7 04          	shl    $0x4,%r15
    702c:	4d 01 cf             	add    %r9,%r15
  while (data->running == 1) {
    702f:	83 f8 01             	cmp    $0x1,%eax
    7032:	0f 85 81 00 00 00    	jne    70b9 <io_thread+0xe99>
      for (int x = 0 ; x < buffers->count ; x++) {
    7038:	49 63 07             	movslq (%r15),%rax
    703b:	85 c0                	test   %eax,%eax
    703d:	0f 8e 77 06 00 00    	jle    76ba <io_thread+0x149a>
        if (buffers->buffer[x].available == 0) {
    7043:	49 8b 57 08          	mov    0x8(%r15),%rdx
    7047:	48 c1 e0 08          	shl    $0x8,%rax
    704b:	45 31 e4             	xor    %r12d,%r12d
    704e:	eb 10                	jmp    7060 <io_thread+0xe40>
      for (int x = 0 ; x < buffers->count ; x++) {
    7050:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    7057:	49 39 c4             	cmp    %rax,%r12
    705a:	0f 84 5a 06 00 00    	je     76ba <io_thread+0x149a>
        if (buffers->buffer[x].available == 0) {
    7060:	46 8b 8c 22 80 00 00 00 	mov    0x80(%rdx,%r12,1),%r9d
    7068:	45 85 c9             	test   %r9d,%r9d
    706b:	75 e3                	jne    7050 <io_thread+0xe30>
    706d:	42 8b 8c 22 98 00 00 00 	mov    0x98(%rdx,%r12,1),%ecx
    7075:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    707c:	bf 01 00 00 00       	mov    $0x1,%edi
    7081:	31 c0                	xor    %eax,%eax
    7083:	48 8d 35 96 20 00 00 	lea    0x2096(%rip),%rsi        # 9120 <_IO_stdin_used+0x120>
    708a:	e8 31 b4 ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    708f:	4d 03 67 08          	add    0x8(%r15),%r12
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
    7093:	4c 8b 8d 08 01 00 00 	mov    0x108(%rbp),%r9
          buffers->buffer[x].data = send;
    709a:	4d 89 34 24          	mov    %r14,(%r12)
  while (data->running == 1) {
    709e:	8b 45 44             	mov    0x44(%rbp),%eax
          buffers->buffer[x].kind = kind;
    70a1:	41 c7 84 24 98 00 00 00 00 00 00 00 	movl   $0x0,0x98(%r12)
          buffers->buffer[x].available = 1;
    70ad:	41 c7 84 24 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r12)
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
    70b9:	48 63 95 14 01 00 00 	movslq 0x114(%rbp),%rdx
    70c0:	4c 8d 3d 11 21 00 00 	lea    0x2111(%rip),%r15        # 91d8 <_IO_stdin_used+0x1d8>
    70c7:	4c 8d 35 bd 20 00 00 	lea    0x20bd(%rip),%r14        # 918b <_IO_stdin_used+0x18b>
    70ce:	48 c1 e2 04          	shl    $0x4,%rdx
    70d2:	49 8d 1c 11          	lea    (%r9,%rdx,1),%rbx
  while (data->running == 1) {
    70d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    70e0:	83 f8 01             	cmp    $0x1,%eax
    70e3:	0f 85 97 00 00 00    	jne    7180 <io_thread+0xf60>
      for (int x = 0 ; x < buffers->count ; x++) {
    70e9:	48 63 03             	movslq (%rbx),%rax
    70ec:	85 c0                	test   %eax,%eax
    70ee:	7f 08                	jg     70f8 <io_thread+0xed8>
    70f0:	eb fe                	jmp    70f0 <io_thread+0xed0>
    70f2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (buffers->buffer[x].available == 1) {
    70f8:	48 8b 4b 08          	mov    0x8(%rbx),%rcx
    70fc:	48 c1 e0 08          	shl    $0x8,%rax
        if (buffers->buffer[x].available == 0) {
    7100:	45 31 e4             	xor    %r12d,%r12d
    7103:	eb 0f                	jmp    7114 <io_thread+0xef4>
    7105:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    7108:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    710f:	4c 39 e0             	cmp    %r12,%rax
    7112:	74 ec                	je     7100 <io_thread+0xee0>
        if (buffers->buffer[x].available == 1) {
    7114:	42 83 bc 21 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx,%r12,1)
    711d:	75 e9                	jne    7108 <io_thread+0xee8>
    711f:	46 8b 84 21 98 00 00 00 	mov    0x98(%rcx,%r12,1),%r8d
    7127:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    712e:	31 c0                	xor    %eax,%eax
    7130:	4c 89 f9             	mov    %r15,%rcx
    7133:	4c 89 f6             	mov    %r14,%rsi
    7136:	bf 01 00 00 00       	mov    $0x1,%edi
    713b:	e8 80 b3 ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    7140:	4c 03 63 08          	add    0x8(%rbx),%r12
    7144:	41 83 bc 24 98 00 00 00 01 	cmpl   $0x1,0x98(%r12)
    714d:	74 05                	je     7154 <io_thread+0xf34>
  while (data->running == 1) {
    714f:	8b 45 44             	mov    0x44(%rbp),%eax
    7152:	eb 8c                	jmp    70e0 <io_thread+0xec0>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    7154:	be 00 01 00 00       	mov    $0x100,%esi
    7159:	bf 01 00 00 00       	mov    $0x1,%edi
    715e:	e8 ad b2 ff ff       	call   2410 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    7163:	49 8b 14 24          	mov    (%r12),%rdx
            buffers->buffer[x].available = 0;
    7167:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
            reply->kind = buffers->buffer[x].kind;
    7173:	c7 80 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%rax)
            reply->data = buffers->buffer[x].data;
    717d:	48 89 10             	mov    %rdx,(%rax)
    7180:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    7187:	48 8d 35 12 26 00 00 	lea    0x2612(%rip),%rsi        # 97a0 <_IO_stdin_used+0x7a0>
    718e:	bf 01 00 00 00       	mov    $0x1,%edi
    7193:	31 c0                	xor    %eax,%eax
    7195:	e8 26 b3 ff ff       	call   24c0 <__printf_chk@plt>
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    719a:	48 8d 44 24 70       	lea    0x70(%rsp),%rax
    719f:	8b 7c 24 04          	mov    0x4(%rsp),%edi
    71a3:	4c 89 e9             	mov    %r13,%rcx
    71a6:	48 8d 54 24 4c       	lea    0x4c(%rsp),%rdx
    71ab:	48 89 c6             	mov    %rax,%rsi
    71ae:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    71b3:	48 89 54 24 20       	mov    %rdx,0x20(%rsp)
    socklen_t client_addr_len = sizeof(client_addr);
    71b8:	c7 44 24 4c 10 00 00 00 	movl   $0x10,0x4c(%rsp)
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    71c0:	e8 0b ed ff ff       	call   5ed0 <add_accept_request>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    71c5:	bf 01 00 00 00       	mov    $0x1,%edi
    71ca:	be 10 00 00 00       	mov    $0x10,%esi
    71cf:	e8 3c b2 ff ff       	call   2410 <calloc@plt>
    void *buf = malloc(size);
    71d4:	bf 0a 00 00 00       	mov    $0xa,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    71d9:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    71dc:	e8 9f b2 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    71e1:	48 85 c0             	test   %rax,%rax
    71e4:	0f 84 4e 05 00 00    	je     7738 <io_thread+0x1518>
    iov->iov_base = zh_malloc(10);
    71ea:	49 89 04 24          	mov    %rax,(%r12)
	unsigned int head, next = sq->sqe_tail + 1;
    71ee:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
    iov->iov_len = 10;
    71f5:	49 c7 44 24 08 0a 00 00 00 	movq   $0xa,0x8(%r12)
	if (ring->flags & IORING_SETUP_SQE128)
    71fe:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    7205:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    7208:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    7210:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    7212:	f6 c1 02             	test   $0x2,%cl
    7215:	0f 85 9a 04 00 00    	jne    76b5 <io_thread+0x1495>
	if (next - head <= sq->ring_entries) {
    721b:	89 d0                	mov    %edx,%eax
    721d:	29 f0                	sub    %esi,%eax
    721f:	39 84 24 dc 00 00 00 	cmp    %eax,0xdc(%rsp)
    7226:	0f 82 ea b3 ff ff    	jb     2616 <io_thread.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    722c:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    722f:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
    7236:	48 8d 7d 68          	lea    0x68(%rbp),%rdi
    723a:	23 84 24 d8 00 00 00 	and    0xd8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    7241:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    7244:	89 94 24 c4 00 00 00 	mov    %edx,0xc4(%rsp)
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    724b:	8b 55 68             	mov    0x68(%rbp),%edx
	sqe->addr3 = 0;
    724e:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    7252:	d3 e0                	shl    %cl,%eax
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
    7254:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    7259:	4c 8d 35 82 1f 00 00 	lea    0x1f82(%rip),%r14        # 91e2 <_IO_stdin_used+0x1e2>
    7260:	48 c1 e0 06          	shl    $0x6,%rax
    7264:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
	sqe->user_data = (unsigned long) data;
    726c:	48 89 78 20          	mov    %rdi,0x20(%rax)
    io_uring_submit(&ring);
    7270:	4c 89 ef             	mov    %r13,%rdi
	sqe->opcode = (__u8) op;
    7273:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    7279:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    727c:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    7284:	4c 89 60 10          	mov    %r12,0x10(%rax)
	sqe->len = len;
    7288:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    7290:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    7298:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    729c:	e8 ff b0 ff ff       	call   23a0 <io_uring_submit@plt>
    while (data->running == 1) {
    72a1:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    72a5:	0f 85 aa 02 00 00    	jne    7555 <io_thread+0x1335>
    72ab:	4c 89 f7             	mov    %r14,%rdi
    72ae:	e8 8d b0 ff ff       	call   2340 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    72b3:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    72ba:	8b bc 24 30 01 00 00 	mov    0x130(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    72c1:	c1 e9 0b             	shr    $0xb,%ecx
    72c4:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    72c7:	48 8b 84 24 f0 00 00 00 	mov    0xf0(%rsp),%rax
    72cf:	8b 10                	mov    (%rax),%edx
		unsigned head = *ring->cq.khead;
    72d1:	48 8b b4 24 e8 00 00 00 	mov    0xe8(%rsp),%rsi
    72d9:	8b 06                	mov    (%rsi),%eax
		if (!available)
    72db:	39 c2                	cmp    %eax,%edx
    72dd:	74 36                	je     7315 <io_thread+0x10f5>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    72df:	89 fa                	mov    %edi,%edx
    72e1:	21 c2                	and    %eax,%edx
    72e3:	d3 e2                	shl    %cl,%edx
    72e5:	48 c1 e2 04          	shl    $0x4,%rdx
    72e9:	48 03 94 24 18 01 00 00 	add    0x118(%rsp),%rdx
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    72f1:	f6 84 24 49 01 00 00 01 	testb  $0x1,0x149(%rsp)
    72f9:	0f 85 61 02 00 00    	jne    7560 <io_thread+0x1340>
    72ff:	48 83 3a ff          	cmpq   $0xffffffffffffffff,(%rdx)
    7303:	0f 85 20 04 00 00    	jne    7729 <io_thread+0x1509>
			if (cqe->res < 0)
    7309:	8b 52 08             	mov    0x8(%rdx),%edx
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    730c:	83 c0 01             	add    $0x1,%eax
    730f:	89 06                	mov    %eax,(%rsi)
			if (!err)
    7311:	85 d2                	test   %edx,%edx
    7313:	79 b2                	jns    72c7 <io_thread+0x10a7>
	*cqe_ptr = cqe;
    7315:	48 c7 44 24 50 00 00 00 00 	movq   $0x0,0x50(%rsp)
	return err;
    731e:	66 90                	xchg   %ax,%ax
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    7320:	31 d2                	xor    %edx,%edx
    7322:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
    7327:	45 31 c0             	xor    %r8d,%r8d
    732a:	b9 01 00 00 00       	mov    $0x1,%ecx
    732f:	4c 89 ef             	mov    %r13,%rdi
    7332:	e8 79 b1 ff ff       	call   24b0 <__io_uring_get_cqe@plt>
        if (cqe->user_data == 1) {
    7337:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    733c:	4c 8b 0a             	mov    (%rdx),%r9
    733f:	49 83 f9 01          	cmp    $0x1,%r9
    7343:	0f 84 c0 03 00 00    	je     7709 <io_thread+0x14e9>
        struct Request *req = (struct Request *) cqe->user_data;
    7349:	4d 89 cf             	mov    %r9,%r15
        if (ret < 0)
    734c:	85 c0                	test   %eax,%eax
    734e:	0f 88 30 b3 ff ff    	js     2684 <io_thread.cold+0x6e>
        if (cqe->res < 0) {
    7354:	8b 52 08             	mov    0x8(%rdx),%edx
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    7357:	45 8b 07             	mov    (%r15),%r8d
        if (cqe->res < 0) {
    735a:	85 d2                	test   %edx,%edx
    735c:	0f 88 5a 04 00 00    	js     77bc <io_thread+0x159c>
        switch (req->event_type) {
    7362:	41 83 f8 01          	cmp    $0x1,%r8d
    7366:	0f 84 72 02 00 00    	je     75de <io_thread+0x13be>
    736c:	41 83 f8 02          	cmp    $0x2,%r8d
    7370:	0f 84 21 02 00 00    	je     7597 <io_thread+0x1377>
    7376:	45 85 c0             	test   %r8d,%r8d
    7379:	0f 85 04 02 00 00    	jne    7583 <io_thread+0x1363>
    737f:	48 8d 35 6a 24 00 00 	lea    0x246a(%rip),%rsi        # 97f0 <_IO_stdin_used+0x7f0>
    7386:	bf 01 00 00 00       	mov    $0x1,%edi
    738b:	31 c0                	xor    %eax,%eax
    738d:	e8 2e b1 ff ff       	call   24c0 <__printf_chk@plt>
                add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    7392:	48 8b 54 24 20       	mov    0x20(%rsp),%rdx
    7397:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    739c:	4c 89 e9             	mov    %r13,%rcx
    739f:	8b 7c 24 04          	mov    0x4(%rsp),%edi
    73a3:	e8 28 eb ff ff       	call   5ed0 <add_accept_request>
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
    73a8:	be 04 00 00 00       	mov    $0x4,%esi
    73ad:	bf 01 00 00 00       	mov    $0x1,%edi
    73b2:	e8 59 b0 ff ff       	call   2410 <calloc@plt>
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
    73b7:	4c 63 95 10 01 00 00 	movslq 0x110(%rbp),%r10
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
    73be:	49 89 c7             	mov    %rax,%r15
                newclientmsg->socket = cqe->res;
    73c1:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
    73c6:	49 c1 e2 04          	shl    $0x4,%r10
    73ca:	4c 03 95 08 01 00 00 	add    0x108(%rbp),%r10
                newclientmsg->socket = cqe->res;
    73d1:	8b 40 08             	mov    0x8(%rax),%eax
    73d4:	41 89 07             	mov    %eax,(%r15)
  while (data->running == 1) {
    73d7:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    73db:	0f 85 82 00 00 00    	jne    7463 <io_thread+0x1243>
      for (int x = 0 ; x < buffers->count ; x++) {
    73e1:	49 63 02             	movslq (%r10),%rax
    73e4:	85 c0                	test   %eax,%eax
    73e6:	7e ef                	jle    73d7 <io_thread+0x11b7>
        if (buffers->buffer[x].available == 0) {
    73e8:	49 8b 52 08          	mov    0x8(%r10),%rdx
    73ec:	48 c1 e0 08          	shl    $0x8,%rax
    73f0:	45 31 c0             	xor    %r8d,%r8d
    73f3:	eb 0f                	jmp    7404 <io_thread+0x11e4>
    73f5:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    73f8:	49 81 c0 00 01 00 00 	add    $0x100,%r8
    73ff:	49 39 c0             	cmp    %rax,%r8
    7402:	74 d3                	je     73d7 <io_thread+0x11b7>
        if (buffers->buffer[x].available == 0) {
    7404:	42 8b bc 02 80 00 00 00 	mov    0x80(%rdx,%r8,1),%edi
    740c:	85 ff                	test   %edi,%edi
    740e:	75 e8                	jne    73f8 <io_thread+0x11d8>
    7410:	42 8b 8c 02 98 00 00 00 	mov    0x98(%rdx,%r8,1),%ecx
    7418:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    741f:	bf 01 00 00 00       	mov    $0x1,%edi
    7424:	31 c0                	xor    %eax,%eax
    7426:	48 8d 35 f3 1c 00 00 	lea    0x1cf3(%rip),%rsi        # 9120 <_IO_stdin_used+0x120>
    742d:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    7432:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    7437:	e8 84 b0 ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    743c:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    7441:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    7446:	4d 03 42 08          	add    0x8(%r10),%r8
    744a:	4d 89 38             	mov    %r15,(%r8)
          buffers->buffer[x].kind = kind;
    744d:	41 c7 80 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%r8)
          buffers->buffer[x].available = 1;
    7458:	41 c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r8)
    7463:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    746a:	48 8d 35 ae 1d 00 00 	lea    0x1dae(%rip),%rsi        # 921f <_IO_stdin_used+0x21f>
    7471:	bf 01 00 00 00       	mov    $0x1,%edi
    7476:	31 c0                	xor    %eax,%eax
    7478:	e8 43 b0 ff ff       	call   24c0 <__printf_chk@plt>
                add_read_request(data, &data->iomailboxes[data->other_io], cqe->res, &ring);
    747d:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    7482:	4c 89 e9             	mov    %r13,%rcx
    7485:	48 89 ef             	mov    %rbp,%rdi
    7488:	48 63 b5 10 01 00 00 	movslq 0x110(%rbp),%rsi
    748f:	8b 50 08             	mov    0x8(%rax),%edx
    7492:	48 c1 e6 04          	shl    $0x4,%rsi
    7496:	48 03 b5 08 01 00 00 	add    0x108(%rbp),%rsi
    749d:	e8 2e e3 ff ff       	call   57d0 <add_read_request>
          io_uring_cqe_seen(&ring, cqe);
    74a2:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
	if (cqe)
    74a7:	48 85 c0             	test   %rax,%rax
    74aa:	0f 85 d3 00 00 00    	jne    7583 <io_thread+0x1363>
	unsigned int head, next = sq->sqe_tail + 1;
    74b0:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    74b7:	8b 8c 24 40 01 00 00 	mov    0x140(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    74be:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    74c1:	48 8b 84 24 80 00 00 00 	mov    0x80(%rsp),%rax
    74c9:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    74cb:	f6 c1 02             	test   $0x2,%cl
    74ce:	74 00                	je     74d0 <io_thread+0x12b0>
	if (next - head <= sq->ring_entries) {
    74d0:	89 d0                	mov    %edx,%eax
    74d2:	29 f0                	sub    %esi,%eax
    74d4:	39 84 24 dc 00 00 00 	cmp    %eax,0xdc(%rsp)
    74db:	0f 82 af b1 ff ff    	jb     2690 <io_thread.cold+0x7a>
	if (ring->flags & IORING_SETUP_SQE128)
    74e1:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    74e4:	8b 84 24 c4 00 00 00 	mov    0xc4(%rsp),%eax
    74eb:	23 84 24 d8 00 00 00 	and    0xd8(%rsp),%eax
	sqe->addr3 = 0;
    74f2:	66 0f ef c0          	pxor   %xmm0,%xmm0
	if (ring->flags & IORING_SETUP_SQE128)
    74f6:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    74f9:	89 94 24 c4 00 00 00 	mov    %edx,0xc4(%rsp)
	sqe->user_data = (unsigned long) data;
    7500:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    7505:	8b 55 68             	mov    0x68(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    7508:	d3 e0                	shl    %cl,%eax
    750a:	48 c1 e0 06          	shl    $0x6,%rax
    750e:	48 03 84 24 b8 00 00 00 	add    0xb8(%rsp),%rax
	sqe->user_data = (unsigned long) data;
    7516:	48 89 78 20          	mov    %rdi,0x20(%rax)
        io_uring_submit(&ring);
    751a:	4c 89 ef             	mov    %r13,%rdi
	sqe->opcode = (__u8) op;
    751d:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    7523:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    7526:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    752e:	4c 89 60 10          	mov    %r12,0x10(%rax)
	sqe->len = len;
    7532:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    753a:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    7542:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    7546:	e8 55 ae ff ff       	call   23a0 <io_uring_submit@plt>
    while (data->running == 1) {
    754b:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    754f:	0f 84 56 fd ff ff    	je     72ab <io_thread+0x108b>
  if (data->io_mode == IO_MODE_SEND) {
    7555:	8b 85 04 01 00 00    	mov    0x104(%rbp),%eax
    755b:	e9 e4 ed ff ff       	jmp    6344 <io_thread+0x124>
	*cqe_ptr = cqe;
    7560:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    7565:	48 85 d2             	test   %rdx,%rdx
    7568:	0f 84 b2 fd ff ff    	je     7320 <io_thread+0x1100>
        if (cqe->user_data == 1) {
    756e:	4c 8b 0a             	mov    (%rdx),%r9
    7571:	49 83 f9 01          	cmp    $0x1,%r9
    7575:	0f 84 8e 01 00 00    	je     7709 <io_thread+0x14e9>
        struct Request *req = (struct Request *) cqe->user_data;
    757b:	4d 89 cf             	mov    %r9,%r15
        if (ret < 0)
    757e:	e9 d1 fd ff ff       	jmp    7354 <io_thread+0x1134>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    7583:	48 8b 94 24 e8 00 00 00 	mov    0xe8(%rsp),%rdx
    758b:	8b 02                	mov    (%rdx),%eax
    758d:	83 c0 01             	add    $0x1,%eax
    7590:	89 02                	mov    %eax,(%rdx)
}
    7592:	e9 19 ff ff ff       	jmp    74b0 <io_thread+0x1290>
                for (int i = 0; i < req->iovec_count; i++) {
    7597:	45 8b 47 04          	mov    0x4(%r15),%r8d
    759b:	31 db                	xor    %ebx,%ebx
    759d:	45 85 c0             	test   %r8d,%r8d
    75a0:	7e 21                	jle    75c3 <io_thread+0x13a3>
    75a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
                    free(req->iov[i].iov_base);
    75a8:	48 89 d8             	mov    %rbx,%rax
                for (int i = 0; i < req->iovec_count; i++) {
    75ab:	48 83 c3 01          	add    $0x1,%rbx
                    free(req->iov[i].iov_base);
    75af:	48 c1 e0 04          	shl    $0x4,%rax
    75b3:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    75b8:	e8 53 ad ff ff       	call   2310 <free@plt>
                for (int i = 0; i < req->iovec_count; i++) {
    75bd:	41 39 5f 04          	cmp    %ebx,0x4(%r15)
    75c1:	7f e5                	jg     75a8 <io_thread+0x1388>
                close(req->client_socket);
    75c3:	41 8b 7f 08          	mov    0x8(%r15),%edi
    75c7:	e8 14 ae ff ff       	call   23e0 <close@plt>
                free(req);
    75cc:	4c 89 ff             	mov    %r15,%rdi
    75cf:	e8 3c ad ff ff       	call   2310 <free@plt>
          io_uring_cqe_seen(&ring, cqe);
    75d4:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
                break;
    75d9:	e9 c9 fe ff ff       	jmp    74a7 <io_thread+0x1287>
                if (!cqe->res) {
    75de:	85 d2                	test   %edx,%edx
    75e0:	0f 84 86 00 00 00    	je     766c <io_thread+0x144c>
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    75e6:	4c 8d 94 24 60 01 00 00 	lea    0x160(%rsp),%r10
    75ee:	4c 8b 85 08 01 00 00 	mov    0x108(%rbp),%r8
    75f5:	49 8b 57 10          	mov    0x10(%r15),%rdx
    75f9:	48 8d b4 24 60 05 00 00 	lea    0x560(%rsp),%rsi
    7601:	8b bd 10 01 00 00    	mov    0x110(%rbp),%edi
    for (int i = 0; i < dest_sz; i++) {
    7607:	4c 89 d0             	mov    %r10,%rax
    760a:	eb 15                	jmp    7621 <io_thread+0x1401>
    760c:	0f 1f 40 00          	nopl   0x0(%rax)
    7610:	48 83 c0 01          	add    $0x1,%rax
    7614:	48 83 c2 01          	add    $0x1,%rdx
    7618:	48 39 c6             	cmp    %rax,%rsi
    761b:	0f 84 c1 00 00 00    	je     76e2 <io_thread+0x14c2>
        dest[i] = src[i];
    7621:	0f b6 0a             	movzbl (%rdx),%ecx
    7624:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    7626:	80 f9 0d             	cmp    $0xd,%cl
    7629:	75 e5                	jne    7610 <io_thread+0x13f0>
    762b:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    762f:	75 df                	jne    7610 <io_thread+0x13f0>
            dest[i] = '\0';
    7631:	c6 00 00             	movb   $0x0,(%rax)
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    7634:	48 63 c7             	movslq %edi,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, ring);
    7637:	41 8b 4f 08          	mov    0x8(%r15),%ecx
    763b:	4c 89 d2             	mov    %r10,%rdx
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    763e:	48 c1 e0 04          	shl    $0x4,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, ring);
    7642:	48 89 ef             	mov    %rbp,%rdi
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    7645:	49 8d 34 00          	lea    (%r8,%rax,1),%rsi
    handle_http_method(data, buffers, http_request, req->client_socket, ring);
    7649:	4d 89 e8             	mov    %r13,%r8
    764c:	e8 5f e6 ff ff       	call   5cb0 <handle_http_method>
                free(req->iov[0].iov_base);
    7651:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    7655:	e8 b6 ac ff ff       	call   2310 <free@plt>
                free(req);
    765a:	4c 89 ff             	mov    %r15,%rdi
    765d:	e8 ae ac ff ff       	call   2310 <free@plt>
          io_uring_cqe_seen(&ring, cqe);
    7662:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
                break;
    7667:	e9 3b fe ff ff       	jmp    74a7 <io_thread+0x1287>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    766c:	48 8b 0d ad 49 00 00 	mov    0x49ad(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    7673:	ba 0f 00 00 00       	mov    $0xf,%edx
    7678:	be 01 00 00 00       	mov    $0x1,%esi
    767d:	48 8d 3d b9 1b 00 00 	lea    0x1bb9(%rip),%rdi        # 923d <_IO_stdin_used+0x23d>
    7684:	e8 b7 ae ff ff       	call   2540 <fwrite@plt>
          io_uring_cqe_seen(&ring, cqe);
    7689:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    768e:	e9 14 fe ff ff       	jmp    74a7 <io_thread+0x1287>
		head = IO_URING_READ_ONCE(*sq->khead);
    7693:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
    769b:	8b 09                	mov    (%rcx),%ecx
    769d:	e9 21 f7 ff ff       	jmp    6dc3 <io_thread+0xba3>
                  free(req->iov[0].iov_base);
    76a2:	49 8b 7e 10          	mov    0x10(%r14),%rdi
    76a6:	e8 65 ac ff ff       	call   2310 <free@plt>
            io_uring_cqe_seen(&ring, cqe);
    76ab:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
                  break;
    76b0:	e9 29 f6 ff ff       	jmp    6cde <io_thread+0xabe>
		head = io_uring_smp_load_acquire(sq->khead);
    76b5:	e9 61 fb ff ff       	jmp    721b <io_thread+0xffb>
  while (data->running == 1) {
    76ba:	8b 45 44             	mov    0x44(%rbp),%eax
    76bd:	83 f8 01             	cmp    $0x1,%eax
    76c0:	0f 84 72 f9 ff ff    	je     7038 <io_thread+0xe18>
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
    76c6:	4c 8b 8d 08 01 00 00 	mov    0x108(%rbp),%r9
    76cd:	e9 e7 f9 ff ff       	jmp    70b9 <io_thread+0xe99>
    76d2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    76d8:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
	return err;
    76dd:	e9 1a f4 ff ff       	jmp    6afc <io_thread+0x8dc>
    76e2:	48 8b 0d 37 49 00 00 	mov    0x4937(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    76e9:	ba 12 00 00 00       	mov    $0x12,%edx
    76ee:	be 01 00 00 00       	mov    $0x1,%esi
    76f3:	48 8d 3d 7e 1a 00 00 	lea    0x1a7e(%rip),%rdi        # 9178 <_IO_stdin_used+0x178>
    76fa:	e8 41 ae ff ff       	call   2540 <fwrite@plt>
        exit(1);
    76ff:	bf 01 00 00 00       	mov    $0x1,%edi
    7704:	e8 17 ae ff ff       	call   2520 <exit@plt>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    7709:	48 8b 94 24 e8 00 00 00 	mov    0xe8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    7711:	48 8d 3d e1 1a 00 00 	lea    0x1ae1(%rip),%rdi        # 91f9 <_IO_stdin_used+0x1f9>
    7718:	8b 02                	mov    (%rdx),%eax
    771a:	83 c0 01             	add    $0x1,%eax
    771d:	89 02                	mov    %eax,(%rdx)
    771f:	e8 1c ac ff ff       	call   2340 <puts@plt>
    7724:	e9 2c fe ff ff       	jmp    7555 <io_thread+0x1335>
	*cqe_ptr = cqe;
    7729:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
	return err;
    772e:	e9 3b fe ff ff       	jmp    756e <io_thread+0x134e>
}
    7733:	e8 58 ac ff ff       	call   2390 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    7738:	48 8b 0d e1 48 00 00 	mov    0x48e1(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    773f:	ba 28 00 00 00       	mov    $0x28,%edx
    7744:	be 01 00 00 00       	mov    $0x1,%esi
    7749:	48 8d 3d d8 1f 00 00 	lea    0x1fd8(%rip),%rdi        # 9728 <_IO_stdin_used+0x728>
    7750:	e8 eb ad ff ff       	call   2540 <fwrite@plt>
        exit(1);
    7755:	bf 01 00 00 00       	mov    $0x1,%edi
    775a:	e8 c1 ad ff ff       	call   2520 <exit@plt>
    775f:	48 8b 0d ba 48 00 00 	mov    0x48ba(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    7766:	ba 28 00 00 00       	mov    $0x28,%edx
    776b:	be 01 00 00 00       	mov    $0x1,%esi
    7770:	48 8d 3d b1 1f 00 00 	lea    0x1fb1(%rip),%rdi        # 9728 <_IO_stdin_used+0x728>
    7777:	e8 c4 ad ff ff       	call   2540 <fwrite@plt>
    777c:	bf 01 00 00 00       	mov    $0x1,%edi
    7781:	e8 9a ad ff ff       	call   2520 <exit@plt>
              fprintf(stderr, "Async request failed: %s for event: %d\n",
    7786:	f7 d8                	neg    %eax
    7788:	41 8b 1e             	mov    (%r14),%ebx
    778b:	89 c7                	mov    %eax,%edi
    778d:	e8 ee ad ff ff       	call   2580 <strerror@plt>
    7792:	48 8b 3d 87 48 00 00 	mov    0x4887(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    7799:	41 89 d8             	mov    %ebx,%r8d
    779c:	48 8d 15 25 20 00 00 	lea    0x2025(%rip),%rdx        # 97c8 <_IO_stdin_used+0x7c8>
    77a3:	48 89 c1             	mov    %rax,%rcx
    77a6:	be 01 00 00 00       	mov    $0x1,%esi
    77ab:	31 c0                	xor    %eax,%eax
    77ad:	e8 9e ad ff ff       	call   2550 <__fprintf_chk@plt>
              exit(1);
    77b2:	bf 01 00 00 00       	mov    $0x1,%edi
    77b7:	e8 64 ad ff ff       	call   2520 <exit@plt>
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    77bc:	89 d7                	mov    %edx,%edi
    77be:	44 89 44 24 04       	mov    %r8d,0x4(%rsp)
    77c3:	f7 df                	neg    %edi
    77c5:	e8 b6 ad ff ff       	call   2580 <strerror@plt>
    77ca:	44 8b 44 24 04       	mov    0x4(%rsp),%r8d
    77cf:	be 01 00 00 00       	mov    $0x1,%esi
    77d4:	48 8b 3d 45 48 00 00 	mov    0x4845(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    77db:	48 89 c1             	mov    %rax,%rcx
    77de:	48 8d 15 e3 1f 00 00 	lea    0x1fe3(%rip),%rdx        # 97c8 <_IO_stdin_used+0x7c8>
    77e5:	31 c0                	xor    %eax,%eax
    77e7:	e8 64 ad ff ff       	call   2550 <__fprintf_chk@plt>
            exit(1);
    77ec:	bf 01 00 00 00       	mov    $0x1,%edi
    77f1:	e8 2a ad ff ff       	call   2520 <exit@plt>
    77f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000007800 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    7800:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    7804:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    780b:	8b 8e c4 00 00 00    	mov    0xc4(%rsi),%ecx
    7811:	85 c9                	test   %ecx,%ecx
    7813:	0f 8e e7 00 00 00    	jle    7900 <barriered_work_ingest+0x100>
int barriered_work_ingest(struct BarrierTask *data) {
    7819:	41 56                	push   %r14
    781b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    781d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    7820:	41 54                	push   %r12
    7822:	49 89 fc             	mov    %rdi,%r12
    7825:	55                   	push   %rbp
    7826:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    7827:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    782b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7830:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    7834:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    783c:	31 db                	xor    %ebx,%ebx
    783e:	8b 10                	mov    (%rax),%edx
    7840:	85 d2                	test   %edx,%edx
    7842:	7e 26                	jle    786a <barriered_work_ingest+0x6a>
    7844:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    7848:	48 89 dd             	mov    %rbx,%rbp
    784b:	48 c1 e5 08          	shl    $0x8,%rbp
    784f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    7853:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    785a:	74 24                	je     7880 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    785c:	48 83 c3 01          	add    $0x1,%rbx
    7860:	39 da                	cmp    %ebx,%edx
    7862:	7f e4                	jg     7848 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    7864:	8b 8e c4 00 00 00    	mov    0xc4(%rsi),%ecx
    786a:	49 83 c5 01          	add    $0x1,%r13
    786e:	44 39 e9             	cmp    %r13d,%ecx
    7871:	7f bd                	jg     7830 <barriered_work_ingest+0x30>
}
    7873:	5b                   	pop    %rbx
    7874:	31 c0                	xor    %eax,%eax
    7876:	5d                   	pop    %rbp
    7877:	41 5c                	pop    %r12
    7879:	41 5d                	pop    %r13
    787b:	41 5e                	pop    %r14
    787d:	c3                   	ret
    787e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    7880:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    7889:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    7890:	bf 04 00 00 00       	mov    $0x4,%edi
    7895:	48 c1 e6 05          	shl    $0x5,%rsi
    7899:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    78a0:	48 83 c6 10          	add    $0x10,%rsi
    78a4:	e8 b7 aa ff ff       	call   2360 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    78a9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    78b1:	48 8b 40 50          	mov    0x50(%rax),%rax
    78b5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    78b9:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    78bd:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    78c7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    78cd:	83 c0 01             	add    $0x1,%eax
    78d0:	99                   	cltd
    78d1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    78d7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    78dd:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    78e5:	48 83 c3 01          	add    $0x1,%rbx
    78e9:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    78ed:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    78f1:	8b 10                	mov    (%rax),%edx
    78f3:	39 da                	cmp    %ebx,%edx
    78f5:	0f 8f 49 ff ff ff    	jg     7844 <barriered_work_ingest+0x44>
    78fb:	e9 64 ff ff ff       	jmp    7864 <barriered_work_ingest+0x64>
}
    7900:	31 c0                	xor    %eax,%eax
    7902:	c3                   	ret
    7903:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    790e:	66 90                	xchg   %ax,%ax

0000000000007910 <barriered_thread>:
void* barriered_thread(void *arg) {
    7910:	f3 0f 1e fa          	endbr64
    7914:	41 56                	push   %r14
    7916:	41 55                	push   %r13
    7918:	41 54                	push   %r12
  int t = 0;
    791a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    791d:	55                   	push   %rbp
  int waiting = 0;
    791e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    7920:	53                   	push   %rbx
    7921:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    7924:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7928:	0f 85 7c 02 00 00    	jne    7baa <barriered_thread+0x29a>
    if (t >= data->task_count) {
    792e:	8b 43 40             	mov    0x40(%rbx),%eax
    7931:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7938:	41 39 c4             	cmp    %eax,%r12d
    793b:	0f 8d 6f 01 00 00    	jge    7ab0 <barriered_thread+0x1a0>
    7941:	49 63 fc             	movslq %r12d,%rdi
    7944:	48 c1 e7 09          	shl    $0x9,%rdi
    7948:	49 89 fd             	mov    %rdi,%r13
    794b:	eb 32                	jmp    797f <barriered_thread+0x6f>
    794d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    7950:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    7954:	48 8b 43 18          	mov    0x18(%rbx),%rax
    7958:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    795c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7960:	4c 01 ef             	add    %r13,%rdi
    7963:	e8 98 fe ff ff       	call   7800 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    7968:	8b 43 40             	mov    0x40(%rbx),%eax
    796b:	41 83 c4 01          	add    $0x1,%r12d
    796f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    7976:	44 39 e0             	cmp    %r12d,%eax
    7979:	0f 8e 21 02 00 00    	jle    7ba0 <barriered_thread+0x290>
      if (data->tasks[t].available == 1) {
    797f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    7983:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    7987:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    798e:	75 c0                	jne    7950 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    7990:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    7994:	83 e8 01             	sub    $0x1,%eax
    7997:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    799c:	45 85 e4             	test   %r12d,%r12d
    799f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    79a2:	45 85 c0             	test   %r8d,%r8d
    79a5:	0f 8e 2d 01 00 00    	jle    7ad8 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    79ab:	48 63 c8             	movslq %eax,%rcx
    79ae:	48 8b 43 18          	mov    0x18(%rbx),%rax
    79b2:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    79b5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    79bb:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    79c2:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    79c6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    79c9:	45 31 f6             	xor    %r14d,%r14d
    79cc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    79d0:	48 8b 10             	mov    (%rax),%rdx
    79d3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    79d7:	49 01 cb             	add    %rcx,%r11
    79da:	4c 89 da             	mov    %r11,%rdx
    79dd:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    79e4:	75 04                	jne    79ea <barriered_thread+0xda>
            arrived++;
    79e6:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    79ea:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    79f0:	75 04                	jne    79f6 <barriered_thread+0xe6>
            prearrive++;
    79f2:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    79f6:	48 83 c0 08          	add    $0x8,%rax
    79fa:	48 39 c6             	cmp    %rax,%rsi
    79fd:	75 d1                	jne    79d0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    79ff:	45 85 d2             	test   %r10d,%r10d
    7a02:	0f 84 c0 00 00 00    	je     7ac8 <barriered_thread+0x1b8>
    7a08:	45 39 d0             	cmp    %r10d,%r8d
    7a0b:	0f 84 b7 00 00 00    	je     7ac8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    7a11:	45 85 f6             	test   %r14d,%r14d
    7a14:	74 0a                	je     7a20 <barriered_thread+0x110>
    7a16:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    7a1a:	0f 85 b6 01 00 00    	jne    7bd6 <barriered_thread+0x2c6>
    7a20:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    7a24:	4c 01 ea             	add    %r13,%rdx
    7a27:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    7a2e:	45 85 e4             	test   %r12d,%r12d
    7a31:	75 14                	jne    7a47 <barriered_thread+0x137>
    7a33:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    7a3a:	48 3b b3 90 00 00 00 	cmp    0x90(%rbx),%rsi
    7a41:	0f 8c 71 01 00 00    	jl     7bb8 <barriered_thread+0x2a8>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    7a47:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    7a4b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    7a4f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    7a59:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    7a5d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7a61:	4c 01 ef             	add    %r13,%rdi
    7a64:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    7a6a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    7a6e:	4c 01 e8             	add    %r13,%rax
    7a71:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7a78:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    7a7b:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7a83:	83 e8 01             	sub    $0x1,%eax
    7a86:	44 39 e0             	cmp    %r12d,%eax
    7a89:	0f 84 a1 00 00 00    	je     7b30 <barriered_thread+0x220>
          if (waiting == 0) {
    7a8f:	85 ed                	test   %ebp,%ebp
    7a91:	0f 84 d9 00 00 00    	je     7b70 <barriered_thread+0x260>
        int arrived = 0; 
    7a97:	bd 01 00 00 00       	mov    $0x1,%ebp
    7a9c:	e9 c7 fe ff ff       	jmp    7968 <barriered_thread+0x58>
  while (data->running == 1) {
    7aa1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7aa5:	0f 85 ff 00 00 00    	jne    7baa <barriered_thread+0x29a>
    7aab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    7ab0:	48 83 83 b0 00 00 00 01 	addq   $0x1,0xb0(%rbx)
    for (; t < data->task_count; t++) {
    7ab8:	85 c0                	test   %eax,%eax
    7aba:	7e e5                	jle    7aa1 <barriered_thread+0x191>
    7abc:	45 31 e4             	xor    %r12d,%r12d
    7abf:	e9 7d fe ff ff       	jmp    7941 <barriered_thread+0x31>
    7ac4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    7ac8:	83 fd 01             	cmp    $0x1,%ebp
    7acb:	74 1b                	je     7ae8 <barriered_thread+0x1d8>
        int arrived = 0; 
    7acd:	31 ed                	xor    %ebp,%ebp
    7acf:	e9 3d ff ff ff       	jmp    7a11 <barriered_thread+0x101>
    7ad4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    7ad8:	83 fd 01             	cmp    $0x1,%ebp
    7adb:	0f 85 43 ff ff ff    	jne    7a24 <barriered_thread+0x114>
        int arrived = 0; 
    7ae1:	45 31 f6             	xor    %r14d,%r14d
    7ae4:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    7ae8:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    7aef:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    7af4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    7af6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    7afa:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    7b01:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    7b06:	e8 55 a8 ff ff       	call   2360 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    7b0b:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    7b12:	48 83 c0 01          	add    $0x1,%rax
    7b16:	48 99                	cqto
    7b18:	48 f7 bb a8 00 00 00 	idivq  0xa8(%rbx)
    7b1f:	48 89 93 a0 00 00 00 	mov    %rdx,0xa0(%rbx)
            waiting = 0; 
    7b26:	e9 e6 fe ff ff       	jmp    7a11 <barriered_thread+0x101>
    7b2b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7b30:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    7b37:	48 3b b3 90 00 00 00 	cmp    0x90(%rbx),%rsi
    7b3e:	0f 8d 4b ff ff ff    	jge    7a8f <barriered_thread+0x17f>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    7b44:	48 c1 e6 04          	shl    $0x4,%rsi
    7b48:	bf 04 00 00 00       	mov    $0x4,%edi
    7b4d:	48 03 73 78          	add    0x78(%rbx),%rsi
    7b51:	e8 0a a8 ff ff       	call   2360 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    7b56:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
          if (waiting == 0) {
    7b5e:	85 ed                	test   %ebp,%ebp
    7b60:	0f 85 31 ff ff ff    	jne    7a97 <barriered_thread+0x187>
    7b66:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    7b70:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    7b77:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    7b7c:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    7b80:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    7b87:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    7b8b:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    7b8f:	e8 cc a7 ff ff       	call   2360 <clock_gettime@plt>
            waiting = 1;
    7b94:	e9 fe fe ff ff       	jmp    7a97 <barriered_thread+0x187>
    7b99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    7ba0:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7ba4:	0f 84 8e fd ff ff    	je     7938 <barriered_thread+0x28>
}
    7baa:	5b                   	pop    %rbx
    7bab:	31 c0                	xor    %eax,%eax
    7bad:	5d                   	pop    %rbp
    7bae:	41 5c                	pop    %r12
    7bb0:	41 5d                	pop    %r13
    7bb2:	41 5e                	pop    %r14
    7bb4:	c3                   	ret
    7bb5:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    7bb8:	48 c1 e6 04          	shl    $0x4,%rsi
    7bbc:	bf 04 00 00 00       	mov    $0x4,%edi
    7bc1:	48 03 73 70          	add    0x70(%rbx),%rsi
    7bc5:	e8 96 a7 ff ff       	call   2360 <clock_gettime@plt>
          data->tasks[t].available = 0;
    7bca:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    7bce:	4c 01 ea             	add    %r13,%rdx
    7bd1:	e9 71 fe ff ff       	jmp    7a47 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    7bd6:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    7bda:	48 8b 43 18          	mov    0x18(%rbx),%rax
    7bde:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7be2:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7be6:	4c 01 ef             	add    %r13,%rdi
    7be9:	e8 12 fc ff ff       	call   7800 <barriered_work_ingest>
          break;
    7bee:	e9 31 fd ff ff       	jmp    7924 <barriered_thread+0x14>
    7bf3:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    7bfe:	66 90                	xchg   %ax,%ax

0000000000007c00 <receive>:
int receive(struct BarrierTask *data) {
    7c00:	f3 0f 1e fa          	endbr64
    7c04:	41 56                	push   %r14
    7c06:	41 55                	push   %r13
    7c08:	41 54                	push   %r12
    7c0a:	55                   	push   %rbp
    7c0b:	53                   	push   %rbx
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7c0c:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    7c13:	45 85 e4             	test   %r12d,%r12d
    7c16:	0f 8e 27 01 00 00    	jle    7d43 <receive+0x143>
    if (n == data->thread->real_thread_index) { continue; }
    7c1c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    7c23:	48 89 fe             	mov    %rdi,%rsi
    7c26:	31 db                	xor    %ebx,%ebx
    7c28:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    7c2c:	49 89 ed             	mov    %rbp,%r13
    7c2f:	90                   	nop
    7c30:	41 39 dd             	cmp    %ebx,%r13d
    7c33:	0f 84 fd 00 00 00    	je     7d36 <receive+0x136>
    struct Data *me = data->mailboxes[n].lower;
    7c39:	48 89 d8             	mov    %rbx,%rax
    7c3c:	48 c1 e0 08          	shl    $0x8,%rax
    7c40:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    7c47:	48 8b 10             	mov    (%rax),%rdx
    if (me->available_reading == 1) {
    7c4a:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    7c50:	83 f8 01             	cmp    $0x1,%eax
    7c53:	74 11                	je     7c66 <receive+0x66>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    7c55:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    7c5c:	75 08                	jne    7c66 <receive+0x66>
    7c5e:	85 c0                	test   %eax,%eax
    7c60:	0f 84 d0 00 00 00    	je     7d36 <receive+0x136>
    for (; me->messages_count > 0 ; ) {
    7c66:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    7c6d:	48 85 ff             	test   %rdi,%rdi
    7c70:	0f 8e a2 00 00 00    	jle    7d18 <receive+0x118>
    7c76:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    7c7d:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    7c84:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
    7c88:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    7c8b:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    7c8f:	49 01 f9             	add    %rdi,%r9
    7c92:	49 01 f8             	add    %rdi,%r8
    7c95:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    7c9c:	eb 08                	jmp    7ca6 <receive+0xa6>
    7c9e:	66 90                	xchg   %ax,%ax
    for (; me->messages_count > 0 ; ) {
    7ca0:	48 83 e8 01          	sub    $0x1,%rax
    7ca4:	72 72                	jb     7d18 <receive+0x118>
      data->sends++;
    7ca6:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
    7ca9:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
    7cb0:	48 29 c1             	sub    %rax,%rcx
    7cb3:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      data->n++;
    7cba:	4c 89 c1             	mov    %r8,%rcx
    7cbd:	48 29 c1             	sub    %rax,%rcx
    7cc0:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
    7cc7:	48 89 f9             	mov    %rdi,%rcx
    7cca:	48 29 c1             	sub    %rax,%rcx
    7ccd:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
      if (me->messages[x]->group == data->group) {
    7cd4:	48 63 c8             	movslq %eax,%rcx
    7cd7:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    7cdb:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    7cdf:	75 bf                	jne    7ca0 <receive+0xa0>
    7ce1:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    7ce5:	75 b9                	jne    7ca0 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    7ce7:	49 63 46 04          	movslq 0x4(%r14),%rax
    7ceb:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    7ced:	bf 01 00 00 00       	mov    $0x1,%edi
    7cf2:	ba 01 00 00 00       	mov    $0x1,%edx
    7cf7:	48 8d 35 32 1c 00 00 	lea    0x1c32(%rip),%rsi        # 9930 <_IO_stdin_used+0x930>
    7cfe:	48 39 e8             	cmp    %rbp,%rax
    7d01:	0f 94 c1             	sete   %cl
    7d04:	31 c0                	xor    %eax,%eax
    7d06:	e8 b5 a7 ff ff       	call   24c0 <__printf_chk@plt>
        exit(1);
    7d0b:	bf 01 00 00 00       	mov    $0x1,%edi
    7d10:	e8 0b a8 ff ff       	call   2520 <exit@plt>
    7d15:	0f 1f 00             	nopl   (%rax)
      me->available_reading = 0;
    7d18:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    7d22:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
    7d2c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7d36:	48 83 c3 01          	add    $0x1,%rbx
    7d3a:	49 39 dc             	cmp    %rbx,%r12
    7d3d:	0f 85 ed fe ff ff    	jne    7c30 <receive+0x30>
}
    7d43:	31 c0                	xor    %eax,%eax
    7d45:	5b                   	pop    %rbx
    7d46:	5d                   	pop    %rbp
    7d47:	41 5c                	pop    %r12
    7d49:	41 5d                	pop    %r13
    7d4b:	41 5e                	pop    %r14
    7d4d:	c3                   	ret
    7d4e:	66 90                	xchg   %ax,%ax

0000000000007d50 <sendm>:
int sendm(struct BarrierTask *data) {
    7d50:	f3 0f 1e fa          	endbr64
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7d54:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    7d5a:	85 c0                	test   %eax,%eax
    7d5c:	0f 8e 96 02 00 00    	jle    7ff8 <sendm+0x2a8>
int sendm(struct BarrierTask *data) {
    7d62:	41 57                	push   %r15
    7d64:	41 56                	push   %r14
    7d66:	41 55                	push   %r13
        if (n == data->thread->real_thread_index) { continue; }
    7d68:	45 31 ed             	xor    %r13d,%r13d
int sendm(struct BarrierTask *data) {
    7d6b:	41 54                	push   %r12
    7d6d:	4c 63 e0             	movslq %eax,%r12
    7d70:	55                   	push   %rbp
    7d71:	48 89 fd             	mov    %rdi,%rbp
    7d74:	53                   	push   %rbx
        if (n == data->thread->real_thread_index) { continue; }
    7d75:	48 8b 9f 28 01 00 00 	mov    0x128(%rdi),%rbx
    7d7c:	44 8b 7b 08          	mov    0x8(%rbx),%r15d
    7d80:	48 89 5c 24 c8       	mov    %rbx,-0x38(%rsp)
    7d85:	0f 1f 00             	nopl   (%rax)
    7d88:	45 39 ef             	cmp    %r13d,%r15d
    7d8b:	0f 84 97 00 00 00    	je     7e28 <sendm+0xd8>
        struct Data *them = data->mailboxes[n].higher;
    7d91:	4c 89 e8             	mov    %r13,%rax
    7d94:	48 c1 e0 08          	shl    $0x8,%rax
    7d98:	48 03 85 70 01 00 00 	add    0x170(%rbp),%rax
        data->mailboxes[n].counter++;
    7d9f:	48 8b 98 b8 00 00 00 	mov    0xb8(%rax),%rbx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7da6:	83 b8 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax)
        struct Data *them = data->mailboxes[n].higher;
    7dad:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7db4:	40 0f 94 c7          	sete   %dil
        data->mailboxes[n].counter++;
    7db8:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    7dbc:	48 89 90 b8 00 00 00 	mov    %rdx,0xb8(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7dc3:	48 85 d2             	test   %rdx,%rdx
    7dc6:	7f 05                	jg     7dcd <sendm+0x7d>
    7dc8:	40 84 ff             	test   %dil,%dil
    7dcb:	75 5b                	jne    7e28 <sendm+0xd8>
        if (them->messages_count > 0) {
    7dcd:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    7dd4:	48 85 f6             	test   %rsi,%rsi
    7dd7:	7f 4f                	jg     7e28 <sendm+0xd8>
        if (them->available_sending == 1) {
    7dd9:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    7de0:	41 83 f8 01          	cmp    $0x1,%r8d
    7de4:	74 0e                	je     7df4 <sendm+0xa4>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    7de6:	83 b9 08 04 00 00 02 	cmpl   $0x2,0x408(%rcx)
    7ded:	75 05                	jne    7df4 <sendm+0xa4>
    7def:	45 85 c0             	test   %r8d,%r8d
    7df2:	74 34                	je     7e28 <sendm+0xd8>
        if (data->sending == 1) {
    7df4:	83 bd 88 01 00 00 01 	cmpl   $0x1,0x188(%rbp)
    7dfb:	74 4b                	je     7e48 <sendm+0xf8>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter >= limit) {
    7dfd:	48 85 d2             	test   %rdx,%rdx
    7e00:	7e 26                	jle    7e28 <sendm+0xd8>
    7e02:	40 84 ff             	test   %dil,%dil
    7e05:	74 21                	je     7e28 <sendm+0xd8>
          data->mailboxes[n].counter = 0;
    7e07:	48 c7 80 b8 00 00 00 00 00 00 00 	movq   $0x0,0xb8(%rax)
          data->thread->have_foreign = 1;
    7e12:	48 8b 44 24 c8       	mov    -0x38(%rsp),%rax
    7e17:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    7e21:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7e28:	49 83 c5 01          	add    $0x1,%r13
    7e2c:	4d 39 ec             	cmp    %r13,%r12
    7e2f:	0f 85 53 ff ff ff    	jne    7d88 <sendm+0x38>
}
    7e35:	31 c0                	xor    %eax,%eax
    7e37:	5b                   	pop    %rbx
    7e38:	5d                   	pop    %rbp
    7e39:	41 5c                	pop    %r12
    7e3b:	41 5d                	pop    %r13
    7e3d:	41 5e                	pop    %r14
    7e3f:	41 5f                	pop    %r15
    7e41:	c3                   	ret
    7e42:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (; them->messages_count < min;) {
    7e48:	4c 63 99 88 00 00 00 	movslq 0x88(%rcx),%r11
    7e4f:	4c 39 de             	cmp    %r11,%rsi
    7e52:	0f 8d c2 00 00 00    	jge    7f1a <sendm+0x1ca>
    7e58:	48 8b 9d 08 01 00 00 	mov    0x108(%rbp),%rbx
    7e5f:	4d 89 de             	mov    %r11,%r14
            them->messages[them->messages_count++] = data->message; 
    7e62:	4c 8b 11             	mov    (%rcx),%r10
    7e65:	49 29 f6             	sub    %rsi,%r14
    7e68:	48 89 5c 24 d8       	mov    %rbx,-0x28(%rsp)
    7e6d:	48 8b 99 80 03 00 00 	mov    0x380(%rcx),%rbx
    7e74:	4d 8d 46 ff          	lea    -0x1(%r14),%r8
    7e78:	48 89 5c 24 e0       	mov    %rbx,-0x20(%rsp)
    7e7d:	49 83 f8 02          	cmp    $0x2,%r8
    7e81:	0f 86 51 01 00 00    	jbe    7fd8 <sendm+0x288>
    7e87:	48 8d 1c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rbx
    7e8f:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    7e97:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    7e9c:	4c 01 d3             	add    %r10,%rbx
    7e9f:	4c 8d 85 90 01 00 00 	lea    0x190(%rbp),%r8
    7ea6:	48 89 5c 24 d0       	mov    %rbx,-0x30(%rsp)
    7eab:	4b 8d 1c 0a          	lea    (%r10,%r9,1),%rbx
    7eaf:	49 39 d8             	cmp    %rbx,%r8
    7eb2:	0f 83 88 00 00 00    	jae    7f40 <sendm+0x1f0>
    7eb8:	48 8d 9d 98 01 00 00 	lea    0x198(%rbp),%rbx
    7ebf:	48 39 5c 24 d0       	cmp    %rbx,-0x30(%rsp)
    7ec4:	73 7a                	jae    7f40 <sendm+0x1f0>
    7ec6:	4c 8b 44 24 e8       	mov    -0x18(%rsp),%r8
    7ecb:	4b 8d 34 0a          	lea    (%r10,%r9,1),%rsi
    7ecf:	4d 01 d0             	add    %r10,%r8
    7ed2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    7ed8:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
          for (; them->messages_count < min;) {
    7edf:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    7ee3:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    7ee7:	4c 39 c6             	cmp    %r8,%rsi
    7eea:	75 ec                	jne    7ed8 <sendm+0x188>
    7eec:	0f 1f 40 00          	nopl   0x0(%rax)
    7ef0:	48 8b 74 24 d8       	mov    -0x28(%rsp),%rsi
    7ef5:	4c 01 f6             	add    %r14,%rsi
    7ef8:	48 89 b5 08 01 00 00 	mov    %rsi,0x108(%rbp)
    7eff:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    7f04:	4c 89 99 80 00 00 00 	mov    %r11,0x80(%rcx)
    7f0b:	4c 01 f6             	add    %r14,%rsi
    7f0e:	48 89 b1 80 03 00 00 	mov    %rsi,0x380(%rcx)
    7f15:	4f 89 4c da f8       	mov    %r9,-0x8(%r10,%r11,8)
          them->available_sending = 0;
    7f1a:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_reading = 1;
    7f24:	c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rcx)
          them->available_receiving = 1;
    7f2e:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    7f38:	e9 c0 fe ff ff       	jmp    7dfd <sendm+0xad>
    7f3d:	0f 1f 00             	nopl   (%rax)
    7f40:	4c 89 f3             	mov    %r14,%rbx
    7f43:	4c 8b 44 24 d0       	mov    -0x30(%rsp),%r8
    7f48:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    7f4f:	48 d1 eb             	shr    %rbx
    7f52:	48 c1 e3 04          	shl    $0x4,%rbx
    7f56:	66 49 0f 6e c1       	movq   %r9,%xmm0
    7f5b:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    7f60:	4c 01 c3             	add    %r8,%rbx
    7f63:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    7f67:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    7f6c:	48 8b 5c 24 e8       	mov    -0x18(%rsp),%rbx
    7f71:	83 e3 10             	and    $0x10,%ebx
    7f74:	75 4a                	jne    7fc0 <sendm+0x270>
    7f76:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    7f7b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    7f80:	41 0f 11 00          	movups %xmm0,(%r8)
    7f84:	49 83 c0 20          	add    $0x20,%r8
    7f88:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    7f8d:	49 39 d8             	cmp    %rbx,%r8
    7f90:	75 ee                	jne    7f80 <sendm+0x230>
    7f92:	4d 89 f0             	mov    %r14,%r8
    7f95:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    7f99:	49 01 f0             	add    %rsi,%r8
    7f9c:	41 f6 c6 01          	test   $0x1,%r14b
    7fa0:	0f 84 4a ff ff ff    	je     7ef0 <sendm+0x1a0>
            them->messages[them->messages_count++] = data->message; 
    7fa6:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    7fad:	4f 89 0c c2          	mov    %r9,(%r10,%r8,8)
          for (; them->messages_count < min;) {
    7fb1:	e9 3a ff ff ff       	jmp    7ef0 <sendm+0x1a0>
    7fb6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    7fc0:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    7fc5:	41 0f 11 00          	movups %xmm0,(%r8)
          for (; them->messages_count < min;) {
    7fc9:	49 83 c0 10          	add    $0x10,%r8
    7fcd:	49 39 d8             	cmp    %rbx,%r8
    7fd0:	75 ae                	jne    7f80 <sendm+0x230>
    7fd2:	eb be                	jmp    7f92 <sendm+0x242>
    7fd4:	0f 1f 40 00          	nopl   0x0(%rax)
    7fd8:	48 8d 34 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rsi
    7fe0:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    7fe8:	48 89 74 24 e8       	mov    %rsi,-0x18(%rsp)
    7fed:	e9 d4 fe ff ff       	jmp    7ec6 <sendm+0x176>
    7ff2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
}
    7ff8:	31 c0                	xor    %eax,%eax
    7ffa:	c3                   	ret
    7ffb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000008000 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    8000:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    8004:	85 f6                	test   %esi,%esi
    8006:	74 18                	je     8020 <mailboxkind+0x20>
  return NULL;
    8008:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    800a:	83 fe 01             	cmp    $0x1,%esi
    800d:	74 01                	je     8010 <mailboxkind+0x10>
}
    800f:	c3                   	ret
    return mailbox->higher;
    8010:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
}
    8017:	c3                   	ret
    8018:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    return mailbox->lower;
    8020:	48 8b 07             	mov    (%rdi),%rax
    8023:	c3                   	ret
    8024:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    802f:	90                   	nop

0000000000008030 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    8030:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    8034:	85 d2                	test   %edx,%edx
    8036:	75 08                	jne    8040 <setmailboxkind+0x10>
    mailbox->lower = data;
    8038:	48 89 37             	mov    %rsi,(%rdi)
}
    803b:	31 c0                	xor    %eax,%eax
    803d:	c3                   	ret
    803e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    8040:	83 fa 01             	cmp    $0x1,%edx
    8043:	74 13                	je     8058 <setmailboxkind+0x28>
  if (kind == 2) {
    8045:	83 fa 02             	cmp    $0x2,%edx
    8048:	75 1e                	jne    8068 <setmailboxkind+0x38>
    mailbox->pending_lower = data;
    804a:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
}
    8051:	31 c0                	xor    %eax,%eax
    8053:	c3                   	ret
    8054:	0f 1f 40 00          	nopl   0x0(%rax)
    mailbox->higher = data;
    8058:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
}
    805f:	31 c0                	xor    %eax,%eax
    8061:	c3                   	ret
    8062:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (kind == 3) {
    8068:	83 fa 03             	cmp    $0x3,%edx
    806b:	75 ce                	jne    803b <setmailboxkind+0xb>
    mailbox->pending_higher = data;
    806d:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
}
    8074:	31 c0                	xor    %eax,%eax
    8076:	c3                   	ret
    8077:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000008080 <fswap>:
int fswap(struct BarrierTask *data) {
    8080:	f3 0f 1e fa          	endbr64
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    8084:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    808b:	8b 97 9c 01 00 00    	mov    0x19c(%rdi),%edx
    8091:	44 8b 97 30 01 00 00 	mov    0x130(%rdi),%r10d
  int t = data->task_index;
    8098:	48 63 4f 04          	movslq 0x4(%rdi),%rcx
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    809c:	8b 86 cc 00 00 00    	mov    0xcc(%rsi),%eax
    80a2:	0f af d0             	imul   %eax,%edx
    80a5:	41 01 d2             	add    %edx,%r10d
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    80a8:	85 c0                	test   %eax,%eax
    80aa:	0f 8e 1b 01 00 00    	jle    81cb <fswap+0x14b>
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    80b0:	4d 63 d2             	movslq %r10d,%r10
int fswap(struct BarrierTask *data) {
    80b3:	41 56                	push   %r14
    80b5:	48 63 d2             	movslq %edx,%rdx
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    80b8:	48 c1 e1 09          	shl    $0x9,%rcx
int fswap(struct BarrierTask *data) {
    80bc:	41 55                	push   %r13
    80be:	4c 63 d8             	movslq %eax,%r11
    80c1:	41 54                	push   %r12
    80c3:	49 01 d3             	add    %rdx,%r11
    80c6:	55                   	push   %rbp
    80c7:	49 c1 e3 08          	shl    $0x8,%r11
    80cb:	53                   	push   %rbx
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    80cc:	48 8b 76 20          	mov    0x20(%rsi),%rsi
        int next_task = abs((t + 1) % (data->thread_count));
    80d0:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    80d7:	4b 8d 3c d2          	lea    (%r10,%r10,8),%rdi
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    80db:	49 c1 e2 08          	shl    $0x8,%r10
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    80df:	48 c1 e7 05          	shl    $0x5,%rdi
    80e3:	48 8b 5c 3e 38       	mov    0x38(%rsi,%rdi,1),%rbx
    80e8:	48 8b ac 0b 70 01 00 00 	mov    0x170(%rbx,%rcx,1),%rbp
    80f0:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    80f4:	48 c1 e1 05          	shl    $0x5,%rcx
    80f8:	4c 8d 4c 0e 38       	lea    0x38(%rsi,%rcx,1),%r9
    80fd:	48 89 d6             	mov    %rdx,%rsi
    8100:	48 c1 e6 08          	shl    $0x8,%rsi
    8104:	eb 21                	jmp    8127 <fswap+0xa7>
    8106:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    8110:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    8117:	49 81 c1 20 01 00 00 	add    $0x120,%r9
    811e:	49 39 f3             	cmp    %rsi,%r11
    8121:	0f 84 99 00 00 00    	je     81c0 <fswap+0x140>
        if (kind == MAILBOX_FRIEND) {
    8127:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    812f:	75 df                	jne    8110 <fswap+0x90>
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    8131:	49 8b 39             	mov    (%r9),%rdi
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    8134:	45 85 c0             	test   %r8d,%r8d
    8137:	7e d7                	jle    8110 <fswap+0x90>
    8139:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    8140:	31 c9                	xor    %ecx,%ecx
    8142:	eb 59                	jmp    819d <fswap+0x11d>
    8144:	0f 1f 40 00          	nopl   0x0(%rax)
              struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    8148:	48 63 d2             	movslq %edx,%rdx
    814b:	48 c1 e2 09          	shl    $0x9,%rdx
    814f:	4c 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%r13
    8157:	49 01 f5             	add    %rsi,%r13
    815a:	4c 89 ea             	mov    %r13,%rdx
    return mailbox->lower;
    815d:	4d 8b 6d 00          	mov    0x0(%r13),%r13
                if (dest->messages_count != 0) { 
    8161:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    8169:	75 22                	jne    818d <fswap+0x10d>
    mailbox->lower = data;
    816b:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    8172:	4c 89 32             	mov    %r14,(%rdx)
    8175:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    mailbox->higher = data;
    817c:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    mailbox->lower = data;
    8183:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    8186:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    818d:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    8194:	41 39 c8             	cmp    %ecx,%r8d
    8197:	0f 84 73 ff ff ff    	je     8110 <fswap+0x90>
              int next_task = abs((nn + 1) % (data->thread_count));
    819d:	83 c1 01             	add    $0x1,%ecx
    81a0:	89 c8                	mov    %ecx,%eax
    81a2:	99                   	cltd
    81a3:	41 f7 f8             	idiv   %r8d
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    81a6:	48 8b 07             	mov    (%rdi),%rax
    81a9:	4c 01 d0             	add    %r10,%rax
    return mailbox->lower;
    81ac:	4c 8b 20             	mov    (%rax),%r12
                if (source2->messages_count != 0) { 
    81af:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    81b8:	74 8e                	je     8148 <fswap+0xc8>
    81ba:	e9 51 ff ff ff       	jmp    8110 <fswap+0x90>
    81bf:	90                   	nop
}
    81c0:	5b                   	pop    %rbx
    81c1:	31 c0                	xor    %eax,%eax
    81c3:	5d                   	pop    %rbp
    81c4:	41 5c                	pop    %r12
    81c6:	41 5d                	pop    %r13
    81c8:	41 5e                	pop    %r14
    81ca:	c3                   	ret
    81cb:	31 c0                	xor    %eax,%eax
    81cd:	c3                   	ret
    81ce:	66 90                	xchg   %ax,%ax

00000000000081d0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    81d0:	f3 0f 1e fa          	endbr64
    81d4:	41 57                	push   %r15
    81d6:	41 56                	push   %r14
    81d8:	41 55                	push   %r13
    81da:	41 54                	push   %r12
    81dc:	55                   	push   %rbp
    81dd:	53                   	push   %rbx
    81de:	48 89 fb             	mov    %rdi,%rbx
    81e1:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
  struct timespec preempt = {
    81e8:	66 0f 6f 05 00 1d 00 00 	movdqa 0x1d00(%rip),%xmm0        # 9ef0 <_IO_stdin_used+0xef0>
int barriered_work(struct BarrierTask *data) {
    81f0:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    81f9:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    81fe:	31 c0                	xor    %eax,%eax
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    8200:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  struct timespec preempt = {
    8207:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    820c:	48 8b 88 f8 00 00 00 	mov    0xf8(%rax),%rcx
  struct timespec rem = {
    8213:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    8218:	8b 11                	mov    (%rcx),%edx
    821a:	83 fa ff             	cmp    $0xffffffff,%edx
    821d:	0f 84 cd 02 00 00    	je     84f0 <barriered_work+0x320>
    8223:	3b 90 f0 00 00 00    	cmp    0xf0(%rax),%edx
    8229:	74 2d                	je     8258 <barriered_work+0x88>
}
    822b:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    8230:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    8239:	0f 85 20 05 00 00    	jne    875f <barriered_work+0x58f>
    823f:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    8246:	31 c0                	xor    %eax,%eax
    8248:	5b                   	pop    %rbx
    8249:	5d                   	pop    %rbp
    824a:	41 5c                	pop    %r12
    824c:	41 5d                	pop    %r13
    824e:	41 5e                	pop    %r14
    8250:	41 5f                	pop    %r15
    8252:	c3                   	ret
    8253:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    8258:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    825f:	8b 41 04             	mov    0x4(%rcx),%eax
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    8262:	85 ed                	test   %ebp,%ebp
    8264:	0f 85 76 04 00 00    	jne    86e0 <barriered_work+0x510>
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    826a:	85 c0                	test   %eax,%eax
    826c:	0f 84 76 04 00 00    	je     86e8 <barriered_work+0x518>
    8272:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          int t = data->task_index;
    8278:	44 8b 63 04          	mov    0x4(%rbx),%r12d
      receive(data);
    827c:	48 89 df             	mov    %rbx,%rdi
    if (data->thread_index == data->task_index) {
    827f:	41 39 ec             	cmp    %ebp,%r12d
    8282:	0f 85 b0 03 00 00    	jne    8638 <barriered_work+0x468>
      receive(data);
    8288:	e8 73 f9 ff ff       	call   7c00 <receive>
        if (data->thread->have_foreign == 1) {
    828d:	4c 8b b3 28 01 00 00 	mov    0x128(%rbx),%r14
    8294:	41 83 be 00 01 00 00 01 	cmpl   $0x1,0x100(%r14)
    829c:	0f 85 a1 02 00 00    	jne    8543 <barriered_work+0x373>
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    82a2:	48 63 93 40 01 00 00 	movslq 0x140(%rbx),%rdx
    82a9:	85 d2                	test   %edx,%edx
    82ab:	0f 8e 92 02 00 00    	jle    8543 <barriered_work+0x373>
                int next_task = abs((t + 1) % (data->thread_count));
    82b1:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    82b7:	48 c1 e5 09          	shl    $0x9,%rbp
    82bb:	31 f6                	xor    %esi,%esi
    82bd:	49 89 d2             	mov    %rdx,%r10
    82c0:	49 89 ed             	mov    %rbp,%r13
    82c3:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
                int next_task = abs((t + 1) % (data->thread_count));
    82cb:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
          int b = data->thread->real_thread_index;
    82cf:	49 63 46 08          	movslq 0x8(%r14),%rax
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    82d3:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
          int b = data->thread->real_thread_index;
    82d7:	49 89 c7             	mov    %rax,%r15
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    82da:	48 c1 e0 08          	shl    $0x8,%rax
    82de:	48 c1 e1 05          	shl    $0x5,%rcx
    82e2:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    82e7:	48 89 cd             	mov    %rcx,%rbp
    82ea:	44 89 e1             	mov    %r12d,%ecx
    82ed:	eb 1a                	jmp    8309 <barriered_work+0x139>
    82ef:	90                   	nop
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    82f0:	48 83 04 24 01       	addq   $0x1,(%rsp)
    82f5:	48 8b 04 24          	mov    (%rsp),%rax
    82f9:	48 81 c6 20 01 00 00 	add    $0x120,%rsi
    8300:	49 39 c2             	cmp    %rax,%r10
    8303:	0f 84 37 02 00 00    	je     8540 <barriered_work+0x370>
                if (y == b) { continue; }
    8309:	8b 04 24             	mov    (%rsp),%eax
    830c:	41 39 c7             	cmp    %eax,%r15d
    830f:	74 df                	je     82f0 <barriered_work+0x120>
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    8311:	49 8b 56 20          	mov    0x20(%r14),%rdx
    8315:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    831a:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    831e:	44 8b 80 a0 01 00 00 	mov    0x1a0(%rax),%r8d
    8325:	45 85 c0             	test   %r8d,%r8d
    8328:	75 c6                	jne    82f0 <barriered_work+0x120>
    832a:	4c 8b 44 2a 38       	mov    0x38(%rdx,%rbp,1),%r8
    832f:	4b 8d 14 28          	lea    (%r8,%r13,1),%rdx
    8333:	44 8b 8a a0 01 00 00 	mov    0x1a0(%rdx),%r9d
    833a:	45 85 c9             	test   %r9d,%r9d
    833d:	75 b1                	jne    82f0 <barriered_work+0x120>
    833f:	4c 8b 24 24          	mov    (%rsp),%r12
    8343:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    834a:	49 c1 e4 08          	shl    $0x8,%r12
    834e:	42 83 bc 22 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r12,1)
    8357:	75 97                	jne    82f0 <barriered_work+0x120>
    8359:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    8360:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    8365:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    836d:	75 81                	jne    82f0 <barriered_work+0x120>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    836f:	48 63 44 24 1c       	movslq 0x1c(%rsp),%rax
    8374:	85 c0                	test   %eax,%eax
    8376:	0f 8e 74 ff ff ff    	jle    82f0 <barriered_work+0x120>
    837c:	48 89 c2             	mov    %rax,%rdx
    837f:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    8384:	b8 70 01 00 00       	mov    $0x170,%eax
    8389:	48 c1 e2 09          	shl    $0x9,%rdx
    838d:	89 4c 24 30          	mov    %ecx,0x30(%rsp)
    8391:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    8396:	4c 8d 9a a0 01 00 00 	lea    0x1a0(%rdx),%r11
    839d:	48 89 54 24 38       	mov    %rdx,0x38(%rsp)
    83a2:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    83a7:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    83ac:	4c 89 54 24 40       	mov    %r10,0x40(%rsp)
    83b1:	44 8b 54 24 1c       	mov    0x1c(%rsp),%r10d
    83b6:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    83bb:	48 89 c6             	mov    %rax,%rsi
    83be:	66 90                	xchg   %ax,%ax
                        int next_task = abs((nn + 1) % data->thread_count);
    83c0:	41 83 c1 01          	add    $0x1,%r9d
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    83c4:	49 8b 0c 30          	mov    (%r8,%rsi,1),%rcx
                        int next_task = abs((nn + 1) % data->thread_count);
    83c8:	44 89 c8             	mov    %r9d,%eax
    83cb:	99                   	cltd
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    83cc:	4c 01 e1             	add    %r12,%rcx
                        int next_task = abs((nn + 1) % data->thread_count);
    83cf:	41 f7 fa             	idiv   %r10d
    return mailbox->lower;
    83d2:	4c 8b 31             	mov    (%rcx),%r14
    83d5:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    mailbox->lower = data;
    83da:	4c 8b b1 80 00 00 00 	mov    0x80(%rcx),%r14
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    83e1:	48 63 d2             	movslq %edx,%rdx
    83e4:	48 c1 e2 09          	shl    $0x9,%rdx
    83e8:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    83f0:	4c 01 e8             	add    %r13,%rax
    return mailbox->lower;
    83f3:	4c 8b 38             	mov    (%rax),%r15
    return mailbox->higher;
    83f6:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    mailbox->lower = data;
    83fd:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    8400:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    8405:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    mailbox->lower = data;
    840c:	48 89 11             	mov    %rdx,(%rcx)
    mailbox->higher = data;
    840f:	4c 89 b9 80 00 00 00 	mov    %r15,0x80(%rcx)
    8416:	b9 a0 01 00 00       	mov    $0x1a0,%ecx
    841b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
    8420:	41 c7 04 08 01 00 00 00 	movl   $0x1,(%r8,%rcx,1)
                          data->thread->all_threads[t2].tasks[jj].swap = 1;
    8428:	c7 04 0f 01 00 00 00 	movl   $0x1,(%rdi,%rcx,1)
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
    842f:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    8436:	4c 39 d9             	cmp    %r11,%rcx
    8439:	75 e5                	jne    8420 <barriered_work+0x250>
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    843b:	48 8b 0c 37          	mov    (%rdi,%rsi,1),%rcx
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    843f:	48 8b 00             	mov    (%rax),%rax
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    8442:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    844d:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    8454:	4a 8b 8c 29 80 00 00 00 	mov    0x80(%rcx,%r13,1),%rcx
    845c:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
                            ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    8466:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    8470:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    847a:	45 39 ca             	cmp    %r9d,%r10d
    847d:	0f 85 3d ff ff ff    	jne    83c0 <barriered_work+0x1f0>
    8483:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
    8488:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    848d:	b8 70 01 00 00       	mov    $0x170,%eax
    8492:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    8497:	8b 4c 24 30          	mov    0x30(%rsp),%ecx
    849b:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    84a0:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    84a5:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    84aa:	4c 8d 9a 70 01 00 00 	lea    0x170(%rdx),%r11
    84b1:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    84b6:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    84bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                          if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    84c0:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    84c4:	4d 8b 0c 00          	mov    (%r8,%rax,1),%r9
    84c8:	4a 8b 14 32          	mov    (%rdx,%r14,1),%rdx
    84cc:	4b 39 14 21          	cmp    %rdx,(%r9,%r12,1)
    84d0:	0f 84 8e 02 00 00    	je     8764 <barriered_work+0x594>
                        for (int nn = 0; nn < data->thread_count; nn++) {
    84d6:	48 05 00 02 00 00    	add    $0x200,%rax
    84dc:	4c 39 d8             	cmp    %r11,%rax
    84df:	75 df                	jne    84c0 <barriered_work+0x2f0>
    84e1:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    84e6:	e9 05 fe ff ff       	jmp    82f0 <barriered_work+0x120>
    84eb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    84f0:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    84f7:	85 ed                	test   %ebp,%ebp
    84f9:	0f 85 79 fd ff ff    	jne    8278 <barriered_work+0xa8>
    84ff:	44 8b 88 f0 00 00 00 	mov    0xf0(%rax),%r9d
    8506:	45 85 c9             	test   %r9d,%r9d
    8509:	0f 85 69 fd ff ff    	jne    8278 <barriered_work+0xa8>
    850f:	69 87 80 00 00 00 1d e6 cb 0b 	imul   $0xbcbe61d,0x80(%rdi),%eax
    8519:	05 40 7c 0a 00       	add    $0xa7c40,%eax
    851e:	c1 c8 05             	ror    $0x5,%eax
    8521:	3d c4 a7 00 00       	cmp    $0xa7c4,%eax
    8526:	0f 87 4c fd ff ff    	ja     8278 <barriered_work+0xa8>
      data->thread->global->request_group_sync = 0;
    852c:	48 c7 01 00 00 00 00 	movq   $0x0,(%rcx)
    8533:	e9 40 fd ff ff       	jmp    8278 <barriered_work+0xa8>
    8538:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    8540:	41 89 cc             	mov    %ecx,%r12d
        fswap(data); 
    8543:	48 89 df             	mov    %rbx,%rdi
    8546:	e8 35 fb ff ff       	call   8080 <fswap>
        receive(data);
    854b:	48 89 df             	mov    %rbx,%rdi
    854e:	e8 ad f6 ff ff       	call   7c00 <receive>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    8553:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    855a:	31 ff                	xor    %edi,%edi
    855c:	48 c1 e6 05          	shl    $0x5,%rsi
    8560:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    8567:	e8 f4 9d ff ff       	call   2360 <clock_gettime@plt>
      int modcount = ++data->thread->protected_state->modcount;
    856c:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    8573:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      int modcount = ++data->thread->protected_state->modcount;
    857a:	48 8b 50 48          	mov    0x48(%rax),%rdx
    857e:	8b 72 10             	mov    0x10(%rdx),%esi
    8581:	8d 6e 01             	lea    0x1(%rsi),%ebp
    8584:	89 6a 10             	mov    %ebp,0x10(%rdx)
      while (data->scheduled == 1) {
    8587:	75 55                	jne    85de <barriered_work+0x40e>
    8589:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    8590:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    8597:	48 8b 40 18          	mov    0x18(%rax),%rax
    859b:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
        data->n++;
    859f:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    85a7:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    85ab:	48 c1 e7 09          	shl    $0x9,%rdi
    85af:	48 03 78 38          	add    0x38(%rax),%rdi
    85b3:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      while (data->scheduled == 1) {
    85b9:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      if (modcount != data->thread->protected_state->modcount) {
    85c0:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    85c7:	74 c7                	je     8590 <barriered_work+0x3c0>
      if (modcount != data->thread->protected_state->modcount) {
    85c9:	48 8b 40 48          	mov    0x48(%rax),%rax
    85cd:	3b 68 10             	cmp    0x10(%rax),%ebp
    85d0:	74 0c                	je     85de <barriered_work+0x40e>
    85d2:	48 8d 3d ab 0d 00 00 	lea    0xdab(%rip),%rdi        # 9384 <_IO_stdin_used+0x384>
    85d9:	e8 62 9d ff ff       	call   2340 <puts@plt>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    85de:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    85e5:	31 ff                	xor    %edi,%edi
    85e7:	48 c1 e6 05          	shl    $0x5,%rsi
    85eb:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    85f2:	48 83 c6 10          	add    $0x10,%rsi
    85f6:	e8 65 9d ff ff       	call   2360 <clock_gettime@plt>
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    85fb:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    8602:	48 83 c0 01          	add    $0x1,%rax
    8606:	48 99                	cqto
    8608:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    if (t == data->thread_count - 1) {
    860f:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    8615:	83 e8 01             	sub    $0x1,%eax
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    8618:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    if (t == data->thread_count - 1) {
    861f:	44 39 e0             	cmp    %r12d,%eax
    8622:	74 53                	je     8677 <barriered_work+0x4a7>
    data->swap = 0;
    8624:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    return 0;
    862e:	e9 f8 fb ff ff       	jmp    822b <barriered_work+0x5b>
    8633:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      receive(data);
    8638:	e8 c3 f5 ff ff       	call   7c00 <receive>
      while (data->scheduled == 1) {
    863d:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    8644:	75 1b                	jne    8661 <barriered_work+0x491>
    8646:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        data->n++;
    8650:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      while (data->scheduled == 1) {
    8658:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    865f:	74 ef                	je     8650 <barriered_work+0x480>
      sendm(data);
    8661:	48 89 df             	mov    %rbx,%rdi
    8664:	e8 e7 f6 ff ff       	call   7d50 <sendm>
    if (t == data->thread_count - 1) {
    8669:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    866f:	83 e8 01             	sub    $0x1,%eax
    8672:	44 39 e0             	cmp    %r12d,%eax
    8675:	75 ad                	jne    8624 <barriered_work+0x454>
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    8677:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    867e:	85 d2                	test   %edx,%edx
    8680:	7e a2                	jle    8624 <barriered_work+0x454>
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    8682:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    8689:	48 c1 e2 09          	shl    $0x9,%rdx
    868d:	48 63 41 08          	movslq 0x8(%rcx),%rax
    8691:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    8695:	48 c1 e0 05          	shl    $0x5,%rax
    8699:	48 03 41 20          	add    0x20(%rcx),%rax
    869d:	48 8b 40 38          	mov    0x38(%rax),%rax
    86a1:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    86a5:	80 e6 02             	and    $0x2,%dh
    86a8:	74 16                	je     86c0 <barriered_work+0x4f0>
    86aa:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    86b1:	48 05 00 02 00 00    	add    $0x200,%rax
    86b7:	48 39 c8             	cmp    %rcx,%rax
    86ba:	0f 84 64 ff ff ff    	je     8624 <barriered_work+0x454>
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    86c0:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    86c7:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    86ce:	48 05 00 04 00 00    	add    $0x400,%rax
    86d4:	48 39 c8             	cmp    %rcx,%rax
    86d7:	75 e7                	jne    86c0 <barriered_work+0x4f0>
    86d9:	e9 46 ff ff ff       	jmp    8624 <barriered_work+0x454>
    86de:	66 90                	xchg   %ax,%ax
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    86e0:	39 c5                	cmp    %eax,%ebp
    86e2:	0f 85 90 fb ff ff    	jne    8278 <barriered_work+0xa8>
      struct ProtectedState *protected = data->thread->global->protected_state;
    86e8:	48 8b 69 08          	mov    0x8(%rcx),%rbp
      nanosleep(&preempt , &rem);
    86ec:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
    86f1:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
      int modcount = ++protected->modcount;
    86f6:	8b 45 10             	mov    0x10(%rbp),%eax
      protected->protected++;
    86f9:	48 83 45 00 01       	addq   $0x1,0x0(%rbp)
      int modcount = ++protected->modcount;
    86fe:	44 8d 60 01          	lea    0x1(%rax),%r12d
    8702:	44 89 65 10          	mov    %r12d,0x10(%rbp)
      nanosleep(&preempt , &rem);
    8706:	e8 a5 9c ff ff       	call   23b0 <nanosleep@plt>
      if (protected->modcount != modcount) {
    870b:	44 3b 65 10          	cmp    0x10(%rbp),%r12d
    870f:	74 0c                	je     871d <barriered_work+0x54d>
    8711:	48 8d 3d 34 0c 00 00 	lea    0xc34(%rip),%rdi        # 934c <_IO_stdin_used+0x34c>
    8718:	e8 23 9c ff ff       	call   2340 <puts@plt>
      data->thread->global->request_thread_sync = (data->thread_index + 1) % data->thread_count;
    871d:	48 63 ab 30 01 00 00 	movslq 0x130(%rbx),%rbp
    8724:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    872b:	8d 45 01             	lea    0x1(%rbp),%eax
    872e:	48 8b b1 f8 00 00 00 	mov    0xf8(%rcx),%rsi
    8735:	99                   	cltd
    8736:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    873c:	89 56 04             	mov    %edx,0x4(%rsi)
      if (data->thread_index == 1) {
    873f:	83 fd 01             	cmp    $0x1,%ebp
    8742:	0f 85 30 fb ff ff    	jne    8278 <barriered_work+0xa8>
        data->thread->global->request_group_sync = (data->thread->group + 1) % data->thread->group_count;
    8748:	8b 81 f0 00 00 00    	mov    0xf0(%rcx),%eax
    874e:	83 c0 01             	add    $0x1,%eax
    8751:	99                   	cltd
    8752:	f7 b9 c8 00 00 00    	idivl  0xc8(%rcx)
    8758:	89 16                	mov    %edx,(%rsi)
    875a:	e9 19 fb ff ff       	jmp    8278 <barriered_work+0xa8>
}
    875f:	e8 2c 9c ff ff       	call   2390 <__stack_chk_fail@plt>
    8764:	bf 01 00 00 00       	mov    $0x1,%edi
    8769:	48 8d 35 f9 0b 00 00 	lea    0xbf9(%rip),%rsi        # 9369 <_IO_stdin_used+0x369>
    8770:	31 c0                	xor    %eax,%eax
    8772:	e8 49 9d ff ff       	call   24c0 <__printf_chk@plt>
                            exit(1);
    8777:	bf 01 00 00 00       	mov    $0x1,%edi
    877c:	e8 9f 9d ff ff       	call   2520 <exit@plt>
    8781:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    878c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000008790 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    8790:	f3 0f 1e fa          	endbr64
    8794:	53                   	push   %rbx
    8795:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    8798:	e8 63 f0 ff ff       	call   7800 <barriered_work_ingest>
  barriered_work(data);
    879d:	48 89 df             	mov    %rbx,%rdi
}
    87a0:	5b                   	pop    %rbx
  barriered_work(data);
    87a1:	e9 2a fa ff ff       	jmp    81d0 <barriered_work>
    87a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000087b0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    87b0:	f3 0f 1e fa          	endbr64
}
    87b4:	31 c0                	xor    %eax,%eax
    87b6:	c3                   	ret
    87b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000087c0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    87c0:	f3 0f 1e fa          	endbr64
    87c4:	31 c0                	xor    %eax,%eax
    87c6:	c3                   	ret
    87c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000087d0 <after>:
int after(struct timespec left, struct timespec right) {
    87d0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    87d4:	31 c0                	xor    %eax,%eax
    87d6:	48 39 d7             	cmp    %rdx,%rdi
    87d9:	7e 08                	jle    87e3 <after+0x13>
    87db:	31 c0                	xor    %eax,%eax
    87dd:	48 39 ce             	cmp    %rcx,%rsi
    87e0:	0f 9f c0             	setg   %al
}
    87e3:	c3                   	ret
    87e4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    87ef:	90                   	nop

00000000000087f0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    87f0:	f3 0f 1e fa          	endbr64
    87f4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    87f9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    87fe:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8800:	48 39 d7             	cmp    %rdx,%rdi
    8803:	7f 18                	jg     881d <within+0x2d>
    8805:	4d 39 d8             	cmp    %r11,%r8
    8808:	0f 9e c2             	setle  %dl
    880b:	48 39 ce             	cmp    %rcx,%rsi
    880e:	0f 9e c0             	setle  %al
    8811:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8813:	31 c0                	xor    %eax,%eax
    8815:	4d 39 d1             	cmp    %r10,%r9
    8818:	0f 9e c0             	setle  %al
    881b:	21 d0                	and    %edx,%eax
}
    881d:	c3                   	ret
    881e:	66 90                	xchg   %ax,%ax

0000000000008820 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    8820:	f3 0f 1e fa          	endbr64
    8824:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    8829:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    882e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    8833:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    8838:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    883d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    8842:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    8847:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    884c:	48 39 fe             	cmp    %rdi,%rsi
    884f:	7d 2f                	jge    8880 <overlap+0x60>
    8851:	48 39 ca             	cmp    %rcx,%rdx
    8854:	7d 62                	jge    88b8 <overlap+0x98>
    8856:	4d 39 da             	cmp    %r11,%r10
    8859:	7d 0e                	jge    8869 <overlap+0x49>
    return 1;
    885b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    8860:	4d 39 c1             	cmp    %r8,%r9
    8863:	0f 8c 7f 00 00 00    	jl     88e8 <overlap+0xc8>
  return 0;
    8869:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    886b:	4d 39 c1             	cmp    %r8,%r9
    886e:	7f 4c                	jg     88bc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8870:	31 c0                	xor    %eax,%eax
    8872:	4d 39 da             	cmp    %r11,%r10
    8875:	0f 9e c0             	setle  %al
    8878:	c3                   	ret
    8879:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    8880:	7e 4e                	jle    88d0 <overlap+0xb0>
    8882:	48 39 ca             	cmp    %rcx,%rdx
    8885:	7f 39                	jg     88c0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8887:	75 31                	jne    88ba <overlap+0x9a>
    8889:	4d 39 c1             	cmp    %r8,%r9
    888c:	7c 2c                	jl     88ba <overlap+0x9a>
    return 1;
    888e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8893:	4d 39 da             	cmp    %r11,%r10
    8896:	7d 24                	jge    88bc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8898:	48 39 ca             	cmp    %rcx,%rdx
    889b:	0f 94 c2             	sete   %dl
    889e:	48 39 fe             	cmp    %rdi,%rsi
    88a1:	0f 94 c0             	sete   %al
    88a4:	21 c2                	and    %eax,%edx
    88a6:	31 c0                	xor    %eax,%eax
    88a8:	4d 39 c1             	cmp    %r8,%r9
    88ab:	0f 94 c0             	sete   %al
    88ae:	21 d0                	and    %edx,%eax
    88b0:	c3                   	ret
    88b1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    88b8:	74 af                	je     8869 <overlap+0x49>
  return 0;
    88ba:	31 c0                	xor    %eax,%eax
}
    88bc:	c3                   	ret
    88bd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    88c0:	4d 39 da             	cmp    %r11,%r10
    88c3:	7e c4                	jle    8889 <overlap+0x69>
    return 1;
    88c5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    88ca:	4d 39 c1             	cmp    %r8,%r9
    88cd:	7e ba                	jle    8889 <overlap+0x69>
    88cf:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    88d0:	48 39 ca             	cmp    %rcx,%rdx
    88d3:	7c 94                	jl     8869 <overlap+0x49>
    88d5:	4d 39 c1             	cmp    %r8,%r9
    88d8:	7d b4                	jge    888e <overlap+0x6e>
    88da:	48 39 ca             	cmp    %rcx,%rdx
    88dd:	74 91                	je     8870 <overlap+0x50>
    88df:	eb d9                	jmp    88ba <overlap+0x9a>
    88e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    88e8:	c3                   	ret
    88e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000088f0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    88f0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    88f4:	85 f6                	test   %esi,%esi
    88f6:	0f 8e 44 03 00 00    	jle    8c40 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    88fc:	41 57                	push   %r15
    88fe:	41 89 f7             	mov    %esi,%r15d
    8901:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    8903:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    8906:	41 55                	push   %r13
    8908:	41 54                	push   %r12
    890a:	55                   	push   %rbp
    890b:	53                   	push   %rbx
    890c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    8910:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    8914:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    8919:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    891e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    8921:	45 39 e6             	cmp    %r12d,%r14d
    8924:	0f 84 4e 02 00 00    	je     8b78 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    892a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    892f:	8b 50 08             	mov    0x8(%rax),%edx
    8932:	85 d2                	test   %edx,%edx
    8934:	0f 8e 3e 02 00 00    	jle    8b78 <verify+0x288>
    893a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    893f:	31 c9                	xor    %ecx,%ecx
    8941:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    8946:	31 c0                	xor    %eax,%eax
    8948:	44 89 f2             	mov    %r14d,%edx
    894b:	bf 01 00 00 00       	mov    $0x1,%edi
    8950:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    8955:	48 8d 35 38 0a 00 00 	lea    0xa38(%rip),%rsi        # 9394 <_IO_stdin_used+0x394>
    895c:	e8 5f 9b ff ff       	call   24c0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    8961:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    8966:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    896b:	8b 40 08             	mov    0x8(%rax),%eax
    896e:	85 c0                	test   %eax,%eax
    8970:	0f 8e e6 01 00 00    	jle    8b5c <verify+0x26c>
    8976:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    8979:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    897e:	31 db                	xor    %ebx,%ebx
    8980:	48 c1 e0 09          	shl    $0x9,%rax
    8984:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    8989:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    898e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8993:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    8998:	4c 8b 20             	mov    (%rax),%r12
    899b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    89a0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    89a5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    89aa:	49 89 de             	mov    %rbx,%r14
    89ad:	48 8d 35 f5 09 00 00 	lea    0x9f5(%rip),%rsi        # 93a9 <_IO_stdin_used+0x3a9>
    89b4:	49 c1 e6 09          	shl    $0x9,%r14
    89b8:	bf 01 00 00 00       	mov    $0x1,%edi
    89bd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    89c1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    89c9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    89ce:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    89d6:	31 c0                	xor    %eax,%eax
    89d8:	e8 e3 9a ff ff       	call   24c0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    89dd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    89e2:	4c 8b 20             	mov    (%rax),%r12
    89e5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    89ee:	0f 8e 47 01 00 00    	jle    8b3b <verify+0x24b>
    89f4:	4c 03 75 00          	add    0x0(%rbp),%r14
    89f8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    89fd:	ba 01 00 00 00       	mov    $0x1,%edx
    8a02:	4d 89 f5             	mov    %r14,%r13
    8a05:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    8a0c:	4d 85 f6             	test   %r14,%r14
    8a0f:	0f 8e 21 01 00 00    	jle    8b36 <verify+0x246>
    8a15:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    8a18:	48 89 d5             	mov    %rdx,%rbp
    8a1b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8a20:	31 db                	xor    %ebx,%ebx
    8a22:	4d 89 f2             	mov    %r14,%r10
    8a25:	48 c1 e5 05          	shl    $0x5,%rbp
    8a29:	48 83 ed 20          	sub    $0x20,%rbp
    8a2d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    8a31:	49 89 ee             	mov    %rbp,%r14
    8a34:	48 89 dd             	mov    %rbx,%rbp
    8a37:	48 89 d3             	mov    %rdx,%rbx
    8a3a:	eb 31                	jmp    8a6d <verify+0x17d>
    8a3c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    8a40:	4c 39 c2             	cmp    %r8,%rdx
    8a43:	0f 8d 57 01 00 00    	jge    8ba0 <verify+0x2b0>
    8a49:	4c 39 df             	cmp    %r11,%rdi
    8a4c:	7e 05                	jle    8a53 <verify+0x163>
    8a4e:	49 39 c1             	cmp    %rax,%r9
    8a51:	7c 75                	jl     8ac8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8a53:	4c 39 df             	cmp    %r11,%rdi
    8a56:	0f 8d ab 01 00 00    	jge    8c07 <verify+0x317>
    8a5c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8a60:	48 83 c5 01          	add    $0x1,%rbp
    8a64:	49 39 ea             	cmp    %rbp,%r10
    8a67:	0f 8e a9 00 00 00    	jle    8b16 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    8a6d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    8a74:	48 89 e8             	mov    %rbp,%rax
    8a77:	48 c1 e0 05          	shl    $0x5,%rax
    8a7b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    8a82:	4c 01 f2             	add    %r14,%rdx
    8a85:	48 8b 08             	mov    (%rax),%rcx
    8a88:	48 8b 78 10          	mov    0x10(%rax),%rdi
    8a8c:	48 8b 32             	mov    (%rdx),%rsi
    8a8f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    8a93:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    8a97:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    8a9b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    8a9f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    8aa3:	48 39 f1             	cmp    %rsi,%rcx
    8aa6:	7c 98                	jl     8a40 <verify+0x150>
    8aa8:	0f 8e 42 01 00 00    	jle    8bf0 <verify+0x300>
    8aae:	4c 39 c2             	cmp    %r8,%rdx
    8ab1:	0f 8f f9 00 00 00    	jg     8bb0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8ab7:	75 a7                	jne    8a60 <verify+0x170>
    8ab9:	4c 39 df             	cmp    %r11,%rdi
    8abc:	7f a2                	jg     8a60 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8abe:	49 39 c1             	cmp    %rax,%r9
    8ac1:	7c 9d                	jl     8a60 <verify+0x170>
    8ac3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    8ac8:	49 89 c1             	mov    %rax,%r9
    8acb:	48 89 f9             	mov    %rdi,%rcx
    8ace:	48 89 f2             	mov    %rsi,%rdx
    8ad1:	bf 01 00 00 00       	mov    $0x1,%edi
    8ad6:	48 8d 35 7b 0e 00 00 	lea    0xe7b(%rip),%rsi        # 9958 <_IO_stdin_used+0x958>
    8add:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8adf:	48 83 c5 01          	add    $0x1,%rbp
    8ae3:	e8 d8 99 ff ff       	call   24c0 <__printf_chk@plt>
    8ae8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    8aed:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    8af2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8af5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8afa:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8b01:	4c 8b 20             	mov    (%rax),%r12
    8b04:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8b09:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8b0d:	49 39 ea             	cmp    %rbp,%r10
    8b10:	0f 8f 57 ff ff ff    	jg     8a6d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8b16:	48 89 da             	mov    %rbx,%rdx
    8b19:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    8b20:	7d 14                	jge    8b36 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8b22:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    8b29:	48 83 c2 01          	add    $0x1,%rdx
    8b2d:	4d 85 f6             	test   %r14,%r14
    8b30:	0f 8f e2 fe ff ff    	jg     8a18 <verify+0x128>
    8b36:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    8b3b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    8b40:	48 83 c3 01          	add    $0x1,%rbx
    8b44:	39 58 08             	cmp    %ebx,0x8(%rax)
    8b47:	0f 8f 53 fe ff ff    	jg     89a0 <verify+0xb0>
    8b4d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    8b52:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    8b57:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    8b5c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8b61:	48 83 c1 01          	add    $0x1,%rcx
    8b65:	39 48 08             	cmp    %ecx,0x8(%rax)
    8b68:	0f 8f d8 fd ff ff    	jg     8946 <verify+0x56>
    8b6e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    8b73:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    8b78:	48 81 44 24 10 20 01 00 00 	addq   $0x120,0x10(%rsp)
    8b81:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    8b86:	41 39 c7             	cmp    %eax,%r15d
    8b89:	0f 84 86 00 00 00    	je     8c15 <verify+0x325>
    8b8f:	41 89 c4             	mov    %eax,%r12d
    8b92:	e9 8a fd ff ff       	jmp    8921 <verify+0x31>
    8b97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8ba0:	0f 85 ba fe ff ff    	jne    8a60 <verify+0x170>
    8ba6:	e9 a8 fe ff ff       	jmp    8a53 <verify+0x163>
    8bab:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    8bb0:	49 39 c1             	cmp    %rax,%r9
    8bb3:	7e 09                	jle    8bbe <verify+0x2ce>
    8bb5:	4c 39 df             	cmp    %r11,%rdi
    8bb8:	0f 8c 0a ff ff ff    	jl     8ac8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8bbe:	4c 39 df             	cmp    %r11,%rdi
    8bc1:	0f 8f 99 fe ff ff    	jg     8a60 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8bc7:	49 39 c1             	cmp    %rax,%r9
    8bca:	0f 8d f8 fe ff ff    	jge    8ac8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8bd0:	48 39 f1             	cmp    %rsi,%rcx
    8bd3:	0f 85 87 fe ff ff    	jne    8a60 <verify+0x170>
    8bd9:	4c 39 c2             	cmp    %r8,%rdx
    8bdc:	0f 85 7e fe ff ff    	jne    8a60 <verify+0x170>
    8be2:	4c 39 df             	cmp    %r11,%rdi
    8be5:	0f 84 dd fe ff ff    	je     8ac8 <verify+0x1d8>
    8beb:	e9 70 fe ff ff       	jmp    8a60 <verify+0x170>
    8bf0:	4c 39 c2             	cmp    %r8,%rdx
    8bf3:	0f 8c 5a fe ff ff    	jl     8a53 <verify+0x163>
    8bf9:	4c 39 df             	cmp    %r11,%rdi
    8bfc:	7e c9                	jle    8bc7 <verify+0x2d7>
    8bfe:	4c 39 c2             	cmp    %r8,%rdx
    8c01:	0f 85 59 fe ff ff    	jne    8a60 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8c07:	49 39 c1             	cmp    %rax,%r9
    8c0a:	0f 8f 50 fe ff ff    	jg     8a60 <verify+0x170>
    8c10:	e9 b3 fe ff ff       	jmp    8ac8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    8c15:	48 81 44 24 18 20 01 00 00 	addq   $0x120,0x18(%rsp)
    8c1e:	41 8d 46 01          	lea    0x1(%r14),%eax
    8c22:	45 39 e6             	cmp    %r12d,%r14d
    8c25:	74 08                	je     8c2f <verify+0x33f>
    8c27:	41 89 c6             	mov    %eax,%r14d
    8c2a:	e9 ea fc ff ff       	jmp    8919 <verify+0x29>
}
    8c2f:	48 83 c4 58          	add    $0x58,%rsp
    8c33:	31 c0                	xor    %eax,%eax
    8c35:	5b                   	pop    %rbx
    8c36:	5d                   	pop    %rbp
    8c37:	41 5c                	pop    %r12
    8c39:	41 5d                	pop    %r13
    8c3b:	41 5e                	pop    %r14
    8c3d:	41 5f                	pop    %r15
    8c3f:	c3                   	ret
    8c40:	31 c0                	xor    %eax,%eax
    8c42:	c3                   	ret

Disassembly of section .fini:

0000000000008c44 <_fini>:
    8c44:	f3 0f 1e fa          	endbr64
    8c48:	48 83 ec 08          	sub    $0x8,%rsp
    8c4c:	48 83 c4 08          	add    $0x8,%rsp
    8c50:	c3                   	ret
