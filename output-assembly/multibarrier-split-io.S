
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
    25f6:	48 8d 3d fc 6c 00 00 	lea    0x6cfc(%rip),%rdi        # 92f9 <_IO_stdin_used+0x2f9>
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

    sock = socket(PF_INET, SOCK_STREAM, 0);


    if (sock == -1)
        fatal_error("socket()");
    2620:	48 8d 3d 56 6b 00 00 	lea    0x6b56(%rip),%rdi        # 917d <_IO_stdin_used+0x17d>
    2627:	e8 b4 ff ff ff       	call   25e0 <fatal_error>

    int enable = 1;
    if (setsockopt(sock,
                   SOL_SOCKET, SO_REUSEADDR,
                   &enable, sizeof(int)) < 0)
        fatal_error("setsockopt(SO_REUSEADDR)");
    262c:	48 8d 3d 53 6b 00 00 	lea    0x6b53(%rip),%rdi        # 9186 <_IO_stdin_used+0x186>
    2633:	e8 a8 ff ff ff       	call   25e0 <fatal_error>
    srv_addr.sin_addr.s_addr = htonl(INADDR_ANY);

    if (bind(sock,
             (const struct sockaddr *)&srv_addr,
             sizeof(srv_addr)) < 0)
        fatal_error("bind()");
    2638:	48 8d 3d 60 6b 00 00 	lea    0x6b60(%rip),%rdi        # 919f <_IO_stdin_used+0x19f>
    263f:	e8 9c ff ff ff       	call   25e0 <fatal_error>

    if (listen(sock, 10) < 0) {
      fatal_error("listen()");
    2644:	48 8d 3d 5b 6b 00 00 	lea    0x6b5b(%rip),%rdi        # 91a6 <_IO_stdin_used+0x1a6>
    264b:	e8 90 ff ff ff       	call   25e0 <fatal_error>
    2650:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2658:	0f 0b                	ud2
            continue;
          }
          struct Write *write = send->data;
          struct io_uring_sqe *sqe = io_uring_get_sqe(&ring);
          struct Request *req = write->request;
          req->event_type = EVENT_TYPE_WRITE;
    265a:	41 c7 00 02 00 00 00 	movl   $0x2,(%r8)
    2661:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2669:	0f 0b                	ud2
				   perror("new client epoll_create1");
    266b:	48 8d 3d d9 6b 00 00 	lea    0x6bd9(%rip),%rdi        # 924b <_IO_stdin_used+0x24b>
    2672:	e8 99 fe ff ff       	call   2510 <perror@plt>
				   exit(EXIT_FAILURE);
    2677:	bf 01 00 00 00       	mov    $0x1,%edi
    267c:	e8 9f fe ff ff       	call   2520 <exit@plt>
    2681:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2689:	0f 0b                	ud2
    struct NewSocketMessage *msg = bufferreply->data;
    268b:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    2693:	0f 0b                	ud2
    struct NewClientMessage *newclientmsg = newclient->data;
    2695:	48 8b 04 25 00 00 00 00 	mov    0x0,%rax
    269d:	0f 0b                	ud2
    269f:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    26a7:	0f 0b                	ud2
            fatal_error("io_uring_wait_cqe");
    26a9:	48 8d 3d 5b 6b 00 00 	lea    0x6b5b(%rip),%rdi        # 920b <_IO_stdin_used+0x20b>
    26b0:	e8 2b ff ff ff       	call   25e0 <fatal_error>
    26b5:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
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
    26c6:	48 8d 3d 6b 72 00 00 	lea    0x726b(%rip),%rdi        # 9938 <_IO_stdin_used+0x938>
    26cd:	41 56                	push   %r14
    26cf:	41 55                	push   %r13
    26d1:	41 54                	push   %r12
    26d3:	4c 8d 25 92 6d 00 00 	lea    0x6d92(%rip),%r12        # 946c <_IO_stdin_used+0x46c>
    26da:	55                   	push   %rbp
    26db:	53                   	push   %rbx
    26dc:	48 81 ec 38 01 00 00 	sub    $0x138,%rsp
    26e3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    26ec:	48 89 84 24 28 01 00 00 	mov    %rax,0x128(%rsp)
    26f4:	48 8d 05 25 23 00 00 	lea    0x2325(%rip),%rax        # 4a20 <barriered_reset>
    26fb:	66 48 0f 6e f0       	movq   %rax,%xmm6
    2700:	0f 16 35 49 95 00 00 	movhps 0x9549(%rip),%xmm6        # bc50 <__do_global_dtors_aux_fini_array_entry+0x8>
    2707:	0f 29 b4 24 c0 00 00 00 	movaps %xmm6,0xc0(%rsp)
    270f:	e8 2c fc ff ff       	call   2340 <puts@plt>
    2714:	bf 0a 00 00 00       	mov    $0xa,%edi
    2719:	e8 02 fc ff ff       	call   2320 <putchar@plt>
    271e:	ba 01 00 00 00       	mov    $0x1,%edx
    2723:	48 8d 35 3a 6c 00 00 	lea    0x6c3a(%rip),%rsi        # 9364 <_IO_stdin_used+0x364>
    272a:	31 c0                	xor    %eax,%eax
    272c:	bf 01 00 00 00       	mov    $0x1,%edi
    2731:	e8 8a fd ff ff       	call   24c0 <__printf_chk@plt>
    2736:	ba 06 00 00 00       	mov    $0x6,%edx
    273b:	48 8d 35 32 6c 00 00 	lea    0x6c32(%rip),%rsi        # 9374 <_IO_stdin_used+0x374>
    2742:	31 c0                	xor    %eax,%eax
    2744:	bf 01 00 00 00       	mov    $0x1,%edi
    2749:	e8 72 fd ff ff       	call   24c0 <__printf_chk@plt>
    274e:	ba 03 00 00 00       	mov    $0x3,%edx
    2753:	48 8d 35 2f 6c 00 00 	lea    0x6c2f(%rip),%rsi        # 9389 <_IO_stdin_used+0x389>
    275a:	31 c0                	xor    %eax,%eax
    275c:	bf 01 00 00 00       	mov    $0x1,%edi
    2761:	e8 5a fd ff ff       	call   24c0 <__printf_chk@plt>
    2766:	ba 02 00 00 00       	mov    $0x2,%edx
    276b:	48 8d 35 27 6c 00 00 	lea    0x6c27(%rip),%rsi        # 9399 <_IO_stdin_used+0x399>
    2772:	31 c0                	xor    %eax,%eax
    2774:	bf 01 00 00 00       	mov    $0x1,%edi
    2779:	e8 42 fd ff ff       	call   24c0 <__printf_chk@plt>
    277e:	48 8d 3d 2a 6c 00 00 	lea    0x6c2a(%rip),%rdi        # 93af <_IO_stdin_used+0x3af>
    2785:	e8 b6 fb ff ff       	call   2340 <puts@plt>
    278a:	ba 02 00 00 00       	mov    $0x2,%edx
    278f:	48 8d 35 35 6c 00 00 	lea    0x6c35(%rip),%rsi        # 93cb <_IO_stdin_used+0x3cb>
    2796:	31 c0                	xor    %eax,%eax
    2798:	bf 01 00 00 00       	mov    $0x1,%edi
    279d:	e8 1e fd ff ff       	call   24c0 <__printf_chk@plt>
    27a2:	ba 0b 00 00 00       	mov    $0xb,%edx
    27a7:	48 8d 35 37 6c 00 00 	lea    0x6c37(%rip),%rsi        # 93e5 <_IO_stdin_used+0x3e5>
    27ae:	31 c0                	xor    %eax,%eax
    27b0:	bf 01 00 00 00       	mov    $0x1,%edi
    27b5:	e8 06 fd ff ff       	call   24c0 <__printf_chk@plt>
    27ba:	ba 02 00 00 00       	mov    $0x2,%edx
    27bf:	48 8d 35 33 6c 00 00 	lea    0x6c33(%rip),%rsi        # 93f9 <_IO_stdin_used+0x3f9>
    27c6:	31 c0                	xor    %eax,%eax
    27c8:	bf 01 00 00 00       	mov    $0x1,%edi
    27cd:	e8 ee fc ff ff       	call   24c0 <__printf_chk@plt>
    27d2:	ba 01 00 00 00       	mov    $0x1,%edx
    27d7:	48 8d 35 2c 6c 00 00 	lea    0x6c2c(%rip),%rsi        # 940a <_IO_stdin_used+0x40a>
    27de:	31 c0                	xor    %eax,%eax
    27e0:	bf 01 00 00 00       	mov    $0x1,%edi
    27e5:	e8 d6 fc ff ff       	call   24c0 <__printf_chk@plt>
    27ea:	ba 02 00 00 00       	mov    $0x2,%edx
    27ef:	48 8d 35 2c 6c 00 00 	lea    0x6c2c(%rip),%rsi        # 9422 <_IO_stdin_used+0x422>
    27f6:	31 c0                	xor    %eax,%eax
    27f8:	bf 01 00 00 00       	mov    $0x1,%edi
    27fd:	e8 be fc ff ff       	call   24c0 <__printf_chk@plt>
    2802:	ba 01 00 00 00       	mov    $0x1,%edx
    2807:	48 8d 35 92 71 00 00 	lea    0x7192(%rip),%rsi        # 99a0 <_IO_stdin_used+0x9a0>
    280e:	31 c0                	xor    %eax,%eax
    2810:	bf 01 00 00 00       	mov    $0x1,%edi
    2815:	e8 a6 fc ff ff       	call   24c0 <__printf_chk@plt>
    281a:	ba 01 00 00 00       	mov    $0x1,%edx
    281f:	48 8d 35 aa 71 00 00 	lea    0x71aa(%rip),%rsi        # 99d0 <_IO_stdin_used+0x9d0>
    2826:	31 c0                	xor    %eax,%eax
    2828:	bf 01 00 00 00       	mov    $0x1,%edi
    282d:	e8 8e fc ff ff       	call   24c0 <__printf_chk@plt>
    2832:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2837:	48 8d 35 00 6c 00 00 	lea    0x6c00(%rip),%rsi        # 943e <_IO_stdin_used+0x43e>
    283e:	31 c0                	xor    %eax,%eax
    2840:	bf 01 00 00 00       	mov    $0x1,%edi
    2845:	e8 76 fc ff ff       	call   24c0 <__printf_chk@plt>
    284a:	ba 19 00 00 00       	mov    $0x19,%edx
    284f:	48 8d 35 02 6c 00 00 	lea    0x6c02(%rip),%rsi        # 9458 <_IO_stdin_used+0x458>
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
    28a1:	48 89 84 24 b0 00 00 00 	mov    %rax,0xb0(%rsp)
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
    28f0:	41 8d 14 2e          	lea    (%r14,%rbp,1),%edx
    28f4:	41 89 e8             	mov    %ebp,%r8d
    28f7:	44 89 f9             	mov    %r15d,%ecx
    28fa:	4c 89 e6             	mov    %r12,%rsi
    28fd:	bf 01 00 00 00       	mov    $0x1,%edi
    2902:	31 c0                	xor    %eax,%eax
    2904:	83 c5 01             	add    $0x1,%ebp
    2907:	e8 b4 fb ff ff       	call   24c0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    290c:	4c 89 ef             	mov    %r13,%rdi
    290f:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    2911:	49 83 c5 28          	add    $0x28,%r13
      pthread_mutex_init(&swapmutex[cc++], NULL);
    2915:	e8 76 fc ff ff       	call   2590 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    291a:	83 fd 0b             	cmp    $0xb,%ebp
    291d:	75 d1                	jne    28f0 <main+0x230>
    291f:	41 83 c6 0b          	add    $0xb,%r14d
  for (int x = 0 ; x < total_threads; x++) {
    2923:	41 83 c7 01          	add    $0x1,%r15d
    2927:	48 81 c3 b8 01 00 00 	add    $0x1b8,%rbx
    292e:	41 83 fe 79          	cmp    $0x79,%r14d
    2932:	75 b0                	jne    28e4 <main+0x224>
    2934:	ba 06 00 00 00       	mov    $0x6,%edx
    2939:	48 8d 35 3c 6b 00 00 	lea    0x6b3c(%rip),%rsi        # 947c <_IO_stdin_used+0x47c>
    2940:	bf 01 00 00 00       	mov    $0x1,%edi
    2945:	31 c0                	xor    %eax,%eax
    2947:	e8 74 fb ff ff       	call   24c0 <__printf_chk@plt>
    294c:	ba 0c 00 00 00       	mov    $0xc,%edx
    2951:	48 8d 35 3a 6b 00 00 	lea    0x6b3a(%rip),%rsi        # 9492 <_IO_stdin_used+0x492>
    2958:	31 c0                	xor    %eax,%eax
    295a:	bf 01 00 00 00       	mov    $0x1,%edi
    295f:	e8 5c fb ff ff       	call   24c0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2964:	be 10 00 00 00       	mov    $0x10,%esi
    2969:	bf 0c 00 00 00       	mov    $0xc,%edi
    296e:	e8 9d fa ff ff       	call   2410 <calloc@plt>
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2973:	be 10 00 00 00       	mov    $0x10,%esi
    2978:	bf 02 00 00 00       	mov    $0x2,%edi
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    297d:	48 89 c5             	mov    %rax,%rbp
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2980:	e8 8b fa ff ff       	call   2410 <calloc@plt>


  int snapshot_limit = 100;
  for (int x = 0 ; x < io_threads; x++) {
    iobuffers[x].count = buffer_size;
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2985:	be 00 01 00 00       	mov    $0x100,%esi
    298a:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int y = 0 ; y < buffer_size; y++) {
      iobuffers[x].buffer[y].available = 0;
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    298f:	49 89 ee             	mov    %rbp,%r14
    iobuffers[x].count = buffer_size;
    2992:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
  struct Buffers *iobuffers = calloc(io_threads, sizeof(struct Buffers));
    2998:	49 89 c4             	mov    %rax,%r12
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    299b:	e8 70 fa ff ff       	call   2410 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29a0:	be 20 00 00 00       	mov    $0x20,%esi
    29a5:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29aa:	49 89 44 24 08       	mov    %rax,0x8(%r12)
    29af:	49 89 c5             	mov    %rax,%r13
      iobuffers[x].buffer[y].available = 0;
    29b2:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    29bc:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29c6:	e8 45 fa ff ff       	call   2410 <calloc@plt>
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29cb:	be 00 01 00 00       	mov    $0x100,%esi
    29d0:	bf 01 00 00 00       	mov    $0x1,%edi
    iobuffers[x].count = buffer_size;
    29d5:	41 c7 44 24 10 01 00 00 00 	movl   $0x1,0x10(%r12)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29de:	49 89 85 88 00 00 00 	mov    %rax,0x88(%r13)
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29e5:	e8 26 fa ff ff       	call   2410 <calloc@plt>
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29ea:	be 20 00 00 00       	mov    $0x20,%esi
    29ef:	bf 64 00 00 00       	mov    $0x64,%edi
    iobuffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    29f4:	49 89 44 24 18       	mov    %rax,0x18(%r12)
    29f9:	49 89 c5             	mov    %rax,%r13
    29fc:	4c 8d a5 c0 00 00 00 	lea    0xc0(%rbp),%r12
      iobuffers[x].buffer[y].available = 0;
    2a03:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      iobuffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2a0d:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      iobuffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a17:	e8 f4 f9 ff ff       	call   2410 <calloc@plt>
    2a1c:	48 89 ac 24 d0 00 00 00 	mov    %rbp,0xd0(%rsp)
    2a24:	49 89 85 88 00 00 00 	mov    %rax,0x88(%r13)
    }
  }
  for (int x = 0 ; x < buffers_required; x++) {
    buffers[x].count = buffer_size;
    2a2b:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a32:	be 00 01 00 00       	mov    $0x100,%esi
    2a37:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2a3c:	49 83 c6 10          	add    $0x10,%r14
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a40:	e8 cb f9 ff ff       	call   2410 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a45:	be 20 00 00 00       	mov    $0x20,%esi
    2a4a:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2a4f:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    2a53:	48 89 c3             	mov    %rax,%rbx
      buffers[x].buffer[y].available = 0;
    2a56:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2a60:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2a6a:	e8 a1 f9 ff ff       	call   2410 <calloc@plt>
    2a6f:	48 89 83 88 00 00 00 	mov    %rax,0x88(%rbx)
  for (int x = 0 ; x < buffers_required; x++) {
    2a76:	4d 39 f4             	cmp    %r14,%r12
    2a79:	75 b0                	jne    2a2b <main+0x36b>
  int iocur_buffer = 0;
  int swap = 0;
  int groupcount = 0;
  int seq = 0;
  int seqs[] = {1, 3, 6};
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a7b:	be 08 00 00 00       	mov    $0x8,%esi
    2a80:	bf 64 00 00 00       	mov    $0x64,%edi
  struct Global *global = calloc(1, sizeof(struct Global));
  global->request_group_sync = -1;
  global->protected_state = global_protected_state;
    2a85:	45 31 ff             	xor    %r15d,%r15d
  int dataid = 0;
    2a88:	31 db                	xor    %ebx,%ebx
  int seqs[] = {1, 3, 6};
    2a8a:	48 8b 05 2f 75 00 00 	mov    0x752f(%rip),%rax        # 9fc0 <_IO_stdin_used+0xfc0>
              }
              printf("Creating friend mailbox %d other is %d\n", b, mailboxes[b].other);
              data[0].messages = messages;
              data[1].messages = messages2;
              data[0].messages_limit = messages_limit;
              data[0].messages_count = 0;
    2a91:	4d 89 fd             	mov    %r15,%r13
  int seqs[] = {1, 3, 6};
    2a94:	c7 84 24 20 01 00 00 06 00 00 00 	movl   $0x6,0x120(%rsp)
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2a9f:	4c 8d b4 24 18 01 00 00 	lea    0x118(%rsp),%r14
              data[0].messages_count = 0;
    2aa7:	41 89 df             	mov    %ebx,%r15d
  int seqs[] = {1, 3, 6};
    2aaa:	48 89 84 24 18 01 00 00 	mov    %rax,0x118(%rsp)
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2ab2:	e8 59 f9 ff ff       	call   2410 <calloc@plt>
  struct Global *global = calloc(1, sizeof(struct Global));
    2ab7:	be 10 00 00 00       	mov    $0x10,%esi
    2abc:	bf 01 00 00 00       	mov    $0x1,%edi
  struct Group **all_groups = calloc(100, sizeof(struct Group*));
    2ac1:	48 89 84 24 b8 00 00 00 	mov    %rax,0xb8(%rsp)
  struct Global *global = calloc(1, sizeof(struct Global));
    2ac9:	e8 42 f9 ff ff       	call   2410 <calloc@plt>
  int swap = 0;
    2ace:	c7 44 24 20 00 00 00 00 	movl   $0x0,0x20(%rsp)
  struct Global *global = calloc(1, sizeof(struct Global));
    2ad6:	49 89 c3             	mov    %rax,%r11
  global->request_group_sync = -1;
    2ad9:	c7 00 ff ff ff ff    	movl   $0xffffffff,(%rax)
  global->protected_state = global_protected_state;
    2adf:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  int iocur_buffer = 0;
    2ae4:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
  global->protected_state = global_protected_state;
    2aec:	49 89 43 08          	mov    %rax,0x8(%r11)
  for (int k = 0 ; k < group_count ; k++) {
    2af0:	48 8b 84 24 b0 00 00 00 	mov    0xb0(%rsp),%rax
  int cur_buffer = 0;
    2af8:	c7 84 24 84 00 00 00 00 00 00 00 	movl   $0x0,0x84(%rsp)
    2b03:	48 89 84 24 d8 00 00 00 	mov    %rax,0xd8(%rsp)
  global->protected_state = global_protected_state;
    2b0b:	48 89 84 24 a0 00 00 00 	mov    %rax,0xa0(%rsp)
  int curcpu = 0;
    2b13:	c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rsp)
              data[0].messages_count = 0;
    2b1e:	4c 89 9c 24 e0 00 00 00 	mov    %r11,0xe0(%rsp)
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2b26:	be 00 01 00 00       	mov    $0x100,%esi
    2b2b:	bf 01 00 00 00       	mov    $0x1,%edi
    2b30:	44 89 6c 24 50       	mov    %r13d,0x50(%rsp)
    2b35:	e8 d6 f8 ff ff       	call   2410 <calloc@plt>
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2b3a:	be 08 00 00 00       	mov    $0x8,%esi
    2b3f:	bf 64 00 00 00       	mov    $0x64,%edi
    struct Group * group_data = calloc(1, sizeof(struct Group));
    2b44:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    struct KernelThread ** group_threads = calloc(100, sizeof(struct KernelThread*));
    2b49:	e8 c2 f8 ff ff       	call   2410 <calloc@plt>
    all_groups[groupcount++] = group_data;
    2b4e:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    2b53:	48 8b 9c 24 b8 00 00 00 	mov    0xb8(%rsp),%rbx
        thread_data[x].protected_state = &protected_state[k];
    2b5b:	48 c7 44 24 68 00 00 00 00 	movq   $0x0,0x68(%rsp)
    2b64:	48 89 ac 24 f8 00 00 00 	mov    %rbp,0xf8(%rsp)
    group_data->threads = group_threads;
    2b6c:	48 89 82 88 00 00 00 	mov    %rax,0x88(%rdx)
    group_data->global = global;
    2b73:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
    all_groups[groupcount++] = group_data;
    2b7b:	4a 89 14 eb          	mov    %rdx,(%rbx,%r13,8)
    group_data->thread_count = threads_per_group * group_count;
    2b7f:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
    group_data->global = global;
    2b84:	48 89 82 98 00 00 00 	mov    %rax,0x98(%rdx)
    group_data->seq = seqs[seq++ % 3];
    2b8b:	43 8b 04 ae          	mov    (%r14,%r13,4),%eax
    group_data->thread_count = threads_per_group * group_count;
    2b8f:	c7 82 90 00 00 00 06 00 00 00 	movl   $0x6,0x90(%rdx)
    group_data->seq = seqs[seq++ % 3];
    2b99:	89 82 a0 00 00 00    	mov    %eax,0xa0(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    2b9f:	4b 8d 44 ed 00       	lea    0x0(%r13,%r13,8),%rax
    2ba4:	48 c1 e0 06          	shl    $0x6,%rax
    2ba8:	48 89 94 24 00 01 00 00 	mov    %rdx,0x100(%rsp)
    2bb0:	4c 8d 0c 18          	lea    (%rax,%rbx,1),%r9
    2bb4:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2bb9:	48 89 9c 24 98 00 00 00 	mov    %rbx,0x98(%rsp)
    2bc1:	43 8d 5c 2d 00       	lea    0x0(%r13,%r13,1),%ebx
    2bc6:	4c 89 b4 24 08 01 00 00 	mov    %r14,0x108(%rsp)
    2bce:	41 89 de             	mov    %ebx,%r14d
    2bd1:	48 c1 e0 04          	shl    $0x4,%rax
    2bd5:	48 01 e8             	add    %rbp,%rax
    2bd8:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    2bdd:	48 63 84 24 84 00 00 00 	movslq 0x84(%rsp),%rax
    2be5:	48 c1 e0 04          	shl    $0x4,%rax
    2be9:	48 01 e8             	add    %rbp,%rax
    2bec:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
      thread_data[x].all_groups = all_groups;
    2bf4:	48 8b 84 24 b8 00 00 00 	mov    0xb8(%rsp),%rax
      thread_data[x].group = k;
    2bfc:	8b 54 24 50          	mov    0x50(%rsp),%edx
    2c00:	44 89 f1             	mov    %r14d,%ecx
    2c03:	bf 01 00 00 00       	mov    $0x1,%edi
      thread_data[x].group_data = group_data;
    2c08:	48 8b 9c 24 00 01 00 00 	mov    0x100(%rsp),%rbx
    2c10:	48 8d 35 e1 6d 00 00 	lea    0x6de1(%rip),%rsi        # 99f8 <_IO_stdin_used+0x9f8>
      thread_data[x].global = global;
    2c17:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].all_groups = all_groups;
    2c1c:	49 89 81 e8 00 00 00 	mov    %rax,0xe8(%r9)
      thread_data[x].global = global;
    2c23:	48 8b 84 24 e0 00 00 00 	mov    0xe0(%rsp),%rax
      thread_data[x].group_data = group_data;
    2c2b:	49 89 99 e0 00 00 00 	mov    %rbx,0xe0(%r9)
      thread_data[x].group = k;
    2c32:	41 89 91 f0 00 00 00 	mov    %edx,0xf0(%r9)
      thread_data[x].global = global;
    2c39:	49 89 81 f8 00 00 00 	mov    %rax,0xf8(%r9)
    2c40:	31 c0                	xor    %eax,%eax
    2c42:	e8 79 f8 ff ff       	call   24c0 <__printf_chk@plt>
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c47:	be 08 00 00 00       	mov    $0x8,%esi
    2c4c:	bf 02 00 00 00       	mov    $0x2,%edi
    2c51:	e8 ba f7 ff ff       	call   2410 <calloc@plt>
      group_data->threads[group_thread_count++] = &thread_data[x];  
    2c56:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2c5b:	be 80 00 00 00       	mov    $0x80,%esi
    2c60:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2c65:	48 89 c5             	mov    %rax,%rbp
      group_data->threads[group_thread_count++] = &thread_data[x];  
    2c68:	48 8b 83 88 00 00 00 	mov    0x88(%rbx),%rax
    2c6f:	48 8b 5c 24 68       	mov    0x68(%rsp),%rbx
    2c74:	4c 89 0c 18          	mov    %r9,(%rax,%rbx,1)
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2c78:	e8 93 f7 ff ff       	call   2410 <calloc@plt>
      if (x % 2 == 1) {
    2c7d:	45 89 f0             	mov    %r14d,%r8d
    2c80:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2c85:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2c89:	48 89 c3             	mov    %rax,%rbx
      if (x % 2 == 1) {
    2c8c:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2c91:	0f 84 bf 0a 00 00    	je     3756 <main+0x1096>
        other = abs(x - 1) % total_threads;
    2c97:	41 8d 46 ff          	lea    -0x1(%r14),%eax
    2c9b:	41 8d 7e 01          	lea    0x1(%r14),%edi
        my_thread_data[0] = &thread_data[other]; 
    2c9f:	48 8d 14 c0          	lea    (%rax,%rax,8),%rdx
        other = abs(x - 1) % total_threads;
    2ca3:	48 89 c1             	mov    %rax,%rcx
        my_thread_data[0] = &thread_data[other]; 
    2ca6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    2cab:	89 bc 24 88 00 00 00 	mov    %edi,0x88(%rsp)
    2cb2:	48 c1 e2 05          	shl    $0x5,%rdx
    2cb6:	48 01 c2             	add    %rax,%rdx
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2cb9:	48 8d 45 08          	lea    0x8(%rbp),%rax
    2cbd:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2cc2:	4c 89 c8             	mov    %r9,%rax
        my_thread_data[1] = &thread_data[x]; 
    2cc5:	48 89 45 08          	mov    %rax,0x8(%rbp)
        thread_data[x].protected_state = &protected_state[k];
    2cc9:	48 8b 84 24 a0 00 00 00 	mov    0xa0(%rsp),%rax
    2cd1:	48 8d 35 50 6d 00 00 	lea    0x6d50(%rip),%rsi        # 9a28 <_IO_stdin_used+0xa28>
    2cd8:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].thread_index = 1;
    2cdd:	45 89 41 04          	mov    %r8d,0x4(%r9)
        thread_data[x].protected_state = &protected_state[k];
    2ce1:	49 89 41 48          	mov    %rax,0x48(%r9)
    2ce5:	31 c0                	xor    %eax,%eax
        my_thread_data[0] = &thread_data[other]; 
    2ce7:	48 89 55 00          	mov    %rdx,0x0(%rbp)
    2ceb:	44 89 f2             	mov    %r14d,%edx
        thread_data[x].protected_state = &protected_state[k];
    2cee:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2cf3:	89 4c 24 08          	mov    %ecx,0x8(%rsp)
    2cf7:	e8 c4 f7 ff ff       	call   24c0 <__printf_chk@plt>
      thread_data[x].other = other;
    2cfc:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    2d00:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2d05:	31 c0                	xor    %eax,%eax
    2d07:	44 89 f2             	mov    %r14d,%edx
    2d0a:	48 8d 35 47 6d 00 00 	lea    0x6d47(%rip),%rsi        # 9a58 <_IO_stdin_used+0xa58>
    2d11:	bf 01 00 00 00       	mov    $0x1,%edi
    2d16:	41 89 89 c0 00 00 00 	mov    %ecx,0xc0(%r9)
    2d1d:	8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%ecx
    2d24:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2d29:	e8 92 f7 ff ff       	call   24c0 <__printf_chk@plt>
        if (x < thread_count) {
    2d2e:	41 83 fe 01          	cmp    $0x1,%r14d
    2d32:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2d37:	0f 8f 71 13 00 00    	jg     40ae <main+0x19ee>
          CPU_SET(curcpu, sendercpu);
    2d3d:	48 63 84 24 80 00 00 00 	movslq 0x80(%rsp),%rax
    2d45:	48 89 c7             	mov    %rax,%rdi
    2d48:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2d4e:	77 12                	ja     2d62 <main+0x6a2>
    2d50:	48 c1 e8 06          	shr    $0x6,%rax
    2d54:	ba 01 00 00 00       	mov    $0x1,%edx
    2d59:	89 f9                	mov    %edi,%ecx
    2d5b:	48 d3 e2             	shl    %cl,%rdx
    2d5e:	48 09 14 c3          	or     %rdx,(%rbx,%rax,8)
          curcpu += 2;
    2d62:	83 84 24 80 00 00 00 02 	addl   $0x2,0x80(%rsp)
      thread_data[x].real_thread_index = x;
    2d6a:	45 89 71 08          	mov    %r14d,0x8(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2d6e:	be 10 00 00 00       	mov    $0x10,%esi
    2d73:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].swapmutex = swapmutex;
    2d78:	48 8b 84 24 f0 00 00 00 	mov    0xf0(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    2d80:	49 89 99 b8 00 00 00 	mov    %rbx,0xb8(%r9)
      thread_data[x].swapmutex = swapmutex;
    2d87:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2d8e:	48 8b 84 24 e8 00 00 00 	mov    0xe8(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2d96:	49 89 69 18          	mov    %rbp,0x18(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2d9a:	31 ed                	xor    %ebp,%ebp
      thread_data[x].mswapmutex = mswapmutex;
    2d9c:	49 89 81 d8 00 00 00 	mov    %rax,0xd8(%r9)
      thread_data[x].all_threads = thread_data;
    2da3:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].kind = KERNEL_THREAD;
    2da8:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].all_threads = thread_data;
    2daf:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2db3:	48 8b 05 0e 72 00 00 	mov    0x720e(%rip),%rax        # 9fc8 <_IO_stdin_used+0xfc8>
      thread_data[x].task_count = total_barrier_count;
    2dba:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].group_count = group_count;
    2dc2:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].thread_count = 2;
    2dc9:	48 8b 05 00 72 00 00 	mov    0x7200(%rip),%rax        # 9fd0 <_IO_stdin_used+0xfd0>
      thread_data[x].task_count = total_barrier_count;
    2dd0:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].thread_count = 2;
    2dd5:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2dd9:	e8 32 f6 ff ff       	call   2410 <calloc@plt>
    2dde:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2de3:	be 10 00 00 00       	mov    $0x10,%esi
    2de8:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2ded:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2df1:	e8 1a f6 ff ff       	call   2410 <calloc@plt>
    2df6:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2dfb:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2e00:	66 0f 6f 3d 88 71 00 00 	movdqa 0x7188(%rip),%xmm7        # 9f90 <_IO_stdin_used+0xf90>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2e08:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2e0d:	49 89 41 78          	mov    %rax,0x78(%r9)
      thread_data[x].timestamp_count = 0;
    2e11:	41 0f 11 b9 88 00 00 00 	movups %xmm7,0x88(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2e19:	e8 f2 f5 ff ff       	call   2410 <calloc@plt>
    2e1e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e23:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2e28:	66 0f 6f 35 60 71 00 00 	movdqa 0x7160(%rip),%xmm6        # 9f90 <_IO_stdin_used+0xf90>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e30:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2e35:	49 89 81 98 00 00 00 	mov    %rax,0x98(%r9)
      thread_data[x].task_timestamp_count = 0;
    2e3c:	41 0f 11 b1 a0 00 00 00 	movups %xmm6,0xa0(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e44:	e8 c7 f5 ff ff       	call   2410 <calloc@plt>
        thread_data[x].tasks = barriers;
    2e49:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
            data[0].messages_count = 0;
    2e4e:	44 89 74 24 18       	mov    %r14d,0x18(%rsp)
    2e53:	45 89 fe             	mov    %r15d,%r14d
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2e56:	48 63 bc 24 88 00 00 00 	movslq 0x88(%rsp),%rdi
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2e5e:	48 89 c2             	mov    %rax,%rdx
        thread_data[x].tasks = barriers;
    2e61:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2e65:	48 89 fb             	mov    %rdi,%rbx
    2e68:	48 69 ff ab aa aa 2a 	imul   $0x2aaaaaab,%rdi,%rdi
            data[0].messages_count = 0;
    2e6f:	4c 89 4c 24 48       	mov    %r9,0x48(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2e74:	89 d8                	mov    %ebx,%eax
    2e76:	c1 f8 1f             	sar    $0x1f,%eax
    2e79:	48 c1 ef 20          	shr    $0x20,%rdi
    2e7d:	29 c7                	sub    %eax,%edi
    2e7f:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2e82:	01 c0                	add    %eax,%eax
    2e84:	29 c3                	sub    %eax,%ebx
            data[0].messages_count = 0;
    2e86:	89 9c 24 8c 00 00 00 	mov    %ebx,0x8c(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2e8d:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2e90:	be 00 01 00 00       	mov    $0x100,%esi
    2e95:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e9a:	45 31 ff             	xor    %r15d,%r15d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2e9d:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2ea2:	48 c1 e0 09          	shl    $0x9,%rax
    2ea6:	48 8d 1c 02          	lea    (%rdx,%rax,1),%rbx
    2eaa:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2eaf:	48 8d 05 2a 1b 00 00 	lea    0x1b2a(%rip),%rax        # 49e0 <do_protected_write>
    2eb6:	48 89 83 20 01 00 00 	mov    %rax,0x120(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ebd:	e8 4e f5 ff ff       	call   2410 <calloc@plt>
    2ec2:	8b 74 24 58          	mov    0x58(%rsp),%esi
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2ec6:	48 89 83 70 01 00 00 	mov    %rax,0x170(%rbx)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2ecd:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ed0:	85 f6                	test   %esi,%esi
    2ed2:	0f 84 84 01 00 00    	je     305c <main+0x99c>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2ed8:	8b 44 24 18          	mov    0x18(%rsp),%eax
    2edc:	48 89 8c 24 90 00 00 00 	mov    %rcx,0x90(%rsp)
    2ee4:	48 89 cb             	mov    %rcx,%rbx
    2ee7:	45 89 fc             	mov    %r15d,%r12d
    2eea:	83 e8 01             	sub    $0x1,%eax
    2eed:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2ef1:	eb 1a                	jmp    2f0d <main+0x84d>
    2ef3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ef8:	41 83 c4 01          	add    $0x1,%r12d
    2efc:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    2f03:	41 83 fc 06          	cmp    $0x6,%r12d
    2f07:	0f 84 ca 02 00 00    	je     31d7 <main+0xb17>
            int group_of = b / threads_per_group;
    2f0d:	45 89 e7             	mov    %r12d,%r15d
    2f10:	31 c0                	xor    %eax,%eax
    2f12:	44 89 e2             	mov    %r12d,%edx
    2f15:	bf 01 00 00 00       	mov    $0x1,%edi
    2f1a:	41 d1 ff             	sar    %r15d
    2f1d:	48 8d 35 88 65 00 00 	lea    0x6588(%rip),%rsi        # 94ac <_IO_stdin_used+0x4ac>
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
    2f83:	48 8d 35 ee 6a 00 00 	lea    0x6aee(%rip),%rsi        # 9a78 <_IO_stdin_used+0xa78>
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
    3035:	66 0f 6f 35 63 6f 00 00 	movdqa 0x6f63(%rip),%xmm6        # 9fa0 <_IO_stdin_used+0xfa0>
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
    3061:	48 89 c3             	mov    %rax,%rbx
    3064:	45 89 fc             	mov    %r15d,%r12d
    3067:	eb 1c                	jmp    3085 <main+0x9c5>
    3069:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3070:	41 83 c4 01          	add    $0x1,%r12d
    3074:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    307b:	41 83 fc 06          	cmp    $0x6,%r12d
    307f:	0f 84 8c 05 00 00    	je     3611 <main+0xf51>
            int group_of = b / threads_per_group;
    3085:	45 89 e7             	mov    %r12d,%r15d
    3088:	31 c0                	xor    %eax,%eax
    308a:	44 89 e2             	mov    %r12d,%edx
    308d:	bf 01 00 00 00       	mov    $0x1,%edi
    3092:	41 d1 ff             	sar    %r15d
    3095:	48 8d 35 10 64 00 00 	lea    0x6410(%rip),%rsi        # 94ac <_IO_stdin_used+0x4ac>
    309c:	44 89 f9             	mov    %r15d,%ecx
    309f:	e8 1c f4 ff ff       	call   24c0 <__printf_chk@plt>
            if (k == group_of) {
    30a4:	45 39 ef             	cmp    %r13d,%r15d
    30a7:	75 c7                	jne    3070 <main+0x9b0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    30a9:	be 08 00 00 00       	mov    $0x8,%esi
    30ae:	bf 01 00 00 00       	mov    $0x1,%edi
    30b3:	e8 58 f3 ff ff       	call   2410 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30b8:	be 08 00 00 00       	mov    $0x8,%esi
    30bd:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    30c2:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30c7:	e8 44 f3 ff ff       	call   2410 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    30cc:	be 80 04 00 00       	mov    $0x480,%esi
    30d1:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    30d6:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    30db:	e8 30 f3 ff ff       	call   2410 <calloc@plt>
              data[0].a = x;
    30e0:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    30e4:	44 89 e2             	mov    %r12d,%edx
              mailboxes[b].pending_lower = NULL;
    30e7:	48 c7 83 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%rbx)
              struct Data *data = calloc(3, sizeof(struct Data));
    30f2:	49 89 c7             	mov    %rax,%r15
              data[0].b = y;
    30f5:	89 a8 10 04 00 00    	mov    %ebp,0x410(%rax)
    30fb:	48 8d 35 76 69 00 00 	lea    0x6976(%rip),%rsi        # 9a78 <_IO_stdin_used+0xa78>
              data[0].a = x;
    3102:	89 b8 0c 04 00 00    	mov    %edi,0x40c(%rax)
              data[0].kind = MAILBOX_LOWER;
    3108:	c7 80 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%rax)
              data[0].c = b;
    3112:	44 89 a0 14 04 00 00 	mov    %r12d,0x414(%rax)
              data[0].id = dataid++;
    3119:	41 8d 46 01          	lea    0x1(%r14),%eax
              data[1].id = dataid++;
    311d:	41 89 87 98 08 00 00 	mov    %eax,0x898(%r15)
              mailboxes[b].higher = &data[1];
    3124:	49 8d 87 80 04 00 00 	lea    0x480(%r15),%rax
    312b:	48 89 83 80 00 00 00 	mov    %rax,0x80(%rbx)
    3132:	8b 84 24 8c 00 00 00 	mov    0x8c(%rsp),%eax
              data[0].id = dataid++;
    3139:	45 89 b7 18 04 00 00 	mov    %r14d,0x418(%r15)
              data[1].id = dataid++;
    3140:	41 83 c6 02          	add    $0x2,%r14d
              data[1].a = x;
    3144:	41 89 bf 8c 08 00 00 	mov    %edi,0x88c(%r15)
    314b:	89 c1                	mov    %eax,%ecx
    314d:	bf 01 00 00 00       	mov    $0x1,%edi
    3152:	89 83 b4 00 00 00    	mov    %eax,0xb4(%rbx)
    3158:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    315a:	41 c7 87 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r15)
              data[1].b = y;
    3165:	41 89 af 90 08 00 00 	mov    %ebp,0x890(%r15)
              data[1].c = b;
    316c:	45 89 a7 94 08 00 00 	mov    %r12d,0x894(%r15)
              mailboxes[b].lower = &data[0];
    3173:	4c 89 3b             	mov    %r15,(%rbx)
              mailboxes[b].pending_higher = NULL;
    3176:	48 c7 83 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%rbx)
              data[0].finished_reading = 1;
    3181:	41 c7 87 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r15)
              data[1].finished_reading = 1;
    318c:	41 c7 87 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r15)
              mailboxes[b].kind = MAILBOX_FRIEND;
    3197:	c7 83 b0 00 00 00 01 00 00 00 	movl   $0x1,0xb0(%rbx)
    31a1:	e8 1a f3 ff ff       	call   24c0 <__printf_chk@plt>
              data[0].messages = messages;
    31a6:	4c 8b 5c 24 10       	mov    0x10(%rsp),%r11
              data[1].messages = messages2;
    31ab:	4c 8b 54 24 08       	mov    0x8(%rsp),%r10
              data[0].messages_count = 0;
    31b0:	66 0f 6f 35 e8 6d 00 00 	movdqa 0x6de8(%rip),%xmm6        # 9fa0 <_IO_stdin_used+0xfa0>
              data[0].messages = messages;
    31b8:	4d 89 1f             	mov    %r11,(%r15)
              data[1].messages = messages2;
    31bb:	4d 89 97 80 04 00 00 	mov    %r10,0x480(%r15)
              data[0].messages_count = 0;
    31c2:	41 0f 29 b7 80 00 00 00 	movaps %xmm6,0x80(%r15)
              data[1].messages_count = 0;
    31ca:	41 0f 29 b7 00 05 00 00 	movaps %xmm6,0x500(%r15)
    31d2:	e9 99 fe ff ff       	jmp    3070 <main+0x9b0>
    31d7:	48 8b 8c 24 90 00 00 00 	mov    0x90(%rsp),%rcx
    31df:	4c 89 6c 24 08       	mov    %r13,0x8(%rsp)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    31e4:	31 db                	xor    %ebx,%ebx
    31e6:	49 89 cf             	mov    %rcx,%r15
    31e9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
            int group_of = b / threads_per_group;
    31f0:	89 d8                	mov    %ebx,%eax
            if (k == group_of) {
    31f2:	8b 7c 24 08          	mov    0x8(%rsp),%edi
            int group_of = b / threads_per_group;
    31f6:	d1 f8                	sar    %eax
            if (k == group_of) {
    31f8:	39 f8                	cmp    %edi,%eax
    31fa:	0f 84 82 01 00 00    	je     3382 <main+0xcc2>
    3200:	89 da                	mov    %ebx,%edx
    3202:	48 8d 35 b3 62 00 00 	lea    0x62b3(%rip),%rsi        # 94bc <_IO_stdin_used+0x4bc>
    3209:	bf 01 00 00 00       	mov    $0x1,%edi
    320e:	31 c0                	xor    %eax,%eax
    3210:	e8 ab f2 ff ff       	call   24c0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3215:	be 08 00 00 00       	mov    $0x8,%esi
    321a:	bf 01 00 00 00       	mov    $0x1,%edi
    321f:	e8 ec f1 ff ff       	call   2410 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3224:	be 08 00 00 00       	mov    $0x8,%esi
    3229:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    322e:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3233:	e8 d8 f1 ff ff       	call   2410 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    3238:	be 80 04 00 00       	mov    $0x480,%esi
    323d:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3242:	49 89 c5             	mov    %rax,%r13
            struct Data *data = calloc(3, sizeof(struct Data));
    3245:	e8 c6 f1 ff ff       	call   2410 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    324a:	be 80 04 00 00       	mov    $0x480,%esi
    324f:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    3254:	49 89 c4             	mov    %rax,%r12
            struct Data **stack = calloc(3, sizeof(struct Data));
    3257:	e8 b4 f1 ff ff       	call   2410 <calloc@plt>
            data[0].a = x;
    325c:	8b 7c 24 18          	mov    0x18(%rsp),%edi
            data[0].id = dataid++;
    3260:	41 8d 76 01          	lea    0x1(%r14),%esi
            mailboxes[b].lower = &data[0];
    3264:	4d 89 27             	mov    %r12,(%r15)
            data[0].messages = messages;
    3267:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
            data[0].messages_count = 0;
    326c:	66 0f 6f 35 2c 6d 00 00 	movdqa 0x6d2c(%rip),%xmm6        # 9fa0 <_IO_stdin_used+0xfa0>
            data[1].id = dataid++;
    3274:	41 89 b4 24 98 08 00 00 	mov    %esi,0x898(%r12)
            mailboxes[b].higher = &data[1];
    327c:	49 8d b4 24 80 04 00 00 	lea    0x480(%r12),%rsi
            data[0].id = dataid++;
    3284:	45 89 b4 24 18 04 00 00 	mov    %r14d,0x418(%r12)
            data[1].id = dataid++;
    328c:	41 83 c6 02          	add    $0x2,%r14d
            data[0].kind = MAILBOX_LOWER;
    3290:	41 c7 84 24 08 04 00 00 01 00 00 00 	movl   $0x1,0x408(%r12)
            data[0].a = x;
    329c:	41 89 bc 24 0c 04 00 00 	mov    %edi,0x40c(%r12)
            data[0].b = y;
    32a4:	41 89 ac 24 10 04 00 00 	mov    %ebp,0x410(%r12)
            data[0].c = b;
    32ac:	41 89 9c 24 14 04 00 00 	mov    %ebx,0x414(%r12)
            data[1].kind = MAILBOX_HIGHER;
    32b4:	41 c7 84 24 88 08 00 00 02 00 00 00 	movl   $0x2,0x888(%r12)
            data[1].a = x;
    32c0:	41 89 bc 24 8c 08 00 00 	mov    %edi,0x88c(%r12)
            data[1].b = y;
    32c8:	41 89 ac 24 90 08 00 00 	mov    %ebp,0x890(%r12)
            data[1].c = b;
    32d0:	41 89 9c 24 94 08 00 00 	mov    %ebx,0x894(%r12)
            mailboxes[b].my_lower = &data[0];
    32d8:	4d 89 a7 a0 00 00 00 	mov    %r12,0xa0(%r15)
            mailboxes[b].higher = &data[1];
    32df:	49 89 b7 80 00 00 00 	mov    %rsi,0x80(%r15)
            mailboxes[b].pending_lower = NULL;
    32e6:	49 c7 87 88 00 00 00 00 00 00 00 	movq   $0x0,0x88(%r15)
            mailboxes[b].pending_higher = NULL;
    32f1:	49 c7 87 90 00 00 00 00 00 00 00 	movq   $0x0,0x90(%r15)
            data[0].finished_reading = 1;
    32fc:	41 c7 84 24 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r12)
            data[1].finished_reading = 1;
    3308:	41 c7 84 24 80 07 00 00 01 00 00 00 	movl   $0x1,0x780(%r12)
            mailboxes[b].my_higher = &data[1];
    3314:	49 89 b7 a8 00 00 00 	mov    %rsi,0xa8(%r15)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    331b:	41 c7 87 b0 00 00 00 02 00 00 00 	movl   $0x2,0xb0(%r15)
            stack[0] = mailboxes[b].lower;
    3326:	4c 89 20             	mov    %r12,(%rax)
            stack[1] = mailboxes[b].higher;
    3329:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    332d:	49 89 87 98 00 00 00 	mov    %rax,0x98(%r15)
            data[0].available_sending = 0;
    3334:	41 c7 84 24 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r12)
            data[0].available_receiving = 0;
    3340:	41 c7 84 24 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r12)
            data[0].messages = messages;
    334c:	49 89 14 24          	mov    %rdx,(%r12)
            data[1].messages = messages2;
    3350:	4d 89 ac 24 80 04 00 00 	mov    %r13,0x480(%r12)
            data[1].available_sending = 1;
    3358:	41 c7 84 24 80 05 00 00 01 00 00 00 	movl   $0x1,0x580(%r12)
            data[1].available_receiving = 0;
    3364:	41 c7 84 24 00 06 00 00 00 00 00 00 	movl   $0x0,0x600(%r12)
            data[0].messages_count = 0;
    3370:	41 0f 29 b4 24 80 00 00 00 	movaps %xmm6,0x80(%r12)
            data[1].messages_count = 0;
    3379:	41 0f 29 b4 24 00 05 00 00 	movaps %xmm6,0x500(%r12)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3382:	83 c3 01             	add    $0x1,%ebx
    3385:	49 81 c7 00 01 00 00 	add    $0x100,%r15
    338c:	83 fb 06             	cmp    $0x6,%ebx
    338f:	0f 85 5b fe ff ff    	jne    31f0 <main+0xb30>
          char *message = malloc(sizeof(char) * 256);
    3395:	be 01 00 00 00       	mov    $0x1,%esi
    339a:	bf 00 01 00 00       	mov    $0x100,%edi
    339f:	4c 8b 6c 24 08       	mov    0x8(%rsp),%r13
    33a4:	e8 67 f0 ff ff       	call   2410 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    33a9:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    33ae:	48 89 c3             	mov    %rax,%rbx
          struct Message *messaged = malloc(sizeof(struct Message));
    33b1:	e8 ca f0 ff ff       	call   2480 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    33b6:	48 83 ec 08          	sub    $0x8,%rsp
    33ba:	48 89 df             	mov    %rbx,%rdi
    33bd:	41 89 e9             	mov    %ebp,%r9d
    33c0:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    33c5:	44 8b 7c 24 58       	mov    0x58(%rsp),%r15d
    33ca:	ba 00 01 00 00       	mov    $0x100,%edx
    33cf:	31 c0                	xor    %eax,%eax
    33d1:	48 8d 0d c8 66 00 00 	lea    0x66c8(%rip),%rcx        # 9aa0 <_IO_stdin_used+0xaa0>
    33d8:	be 01 00 00 00       	mov    $0x1,%esi
    33dd:	41 57                	push   %r15
    33df:	44 8b 44 24 28       	mov    0x28(%rsp),%r8d
    33e4:	e8 d7 f1 ff ff       	call   25c0 <__sprintf_chk@plt>
          messaged->message = message;
    33e9:	4c 8b 5c 24 18       	mov    0x18(%rsp),%r11
          messaged->task_index = y;
    33ee:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
          messaged->group = k;
    33f3:	44 89 ff             	mov    %r15d,%edi
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    33f6:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->group = k;
    33fb:	45 89 7b 18          	mov    %r15d,0x18(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    33ff:	4c 8b 7c 24 58       	mov    0x58(%rsp),%r15
          messaged->task_index = y;
    3404:	49 89 43 10          	mov    %rax,0x10(%r11)
          messaged->thread_index = thread_data[x].real_thread_index;
    3408:	49 63 47 08          	movslq 0x8(%r15),%rax
          thread_data[x].tasks[y].swap = swap;
    340c:	49 8b 57 38          	mov    0x38(%r15),%rdx
          messaged->message = message;
    3410:	49 89 1b             	mov    %rbx,(%r11)
          thread_data[x].tasks[y].swap = swap;
    3413:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
          messaged->thread_index = thread_data[x].real_thread_index;
    3418:	49 89 43 08          	mov    %rax,0x8(%r11)
          thread_data[x].tasks[y].swap = swap;
    341c:	8b 44 24 30          	mov    0x30(%rsp),%eax
    3420:	48 01 d3             	add    %rdx,%rbx
    3423:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    3428:	89 83 a0 01 00 00    	mov    %eax,0x1a0(%rbx)
          swap += 1;
    342e:	83 c0 01             	add    $0x1,%eax
    3431:	89 44 24 30          	mov    %eax,0x30(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3435:	8d 45 01             	lea    0x1(%rbp),%eax
    3438:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].group = k;
    343b:	89 bb 9c 01 00 00    	mov    %edi,0x19c(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3441:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    3446:	c7 03 41 00 00 00    	movl   $0x41,(%rbx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    344c:	89 83 98 01 00 00    	mov    %eax,0x198(%rbx)
          thread_data[x].tasks[y].message = messaged;
    3452:	4c 89 9b 90 01 00 00 	mov    %r11,0x190(%rbx)
          thread_data[x].tasks[y].sending = 1;
    3459:	c7 83 88 01 00 00 01 00 00 00 	movl   $0x1,0x188(%rbx)
          thread_data[x].tasks[y].snapshot_count = 99;
    3463:	48 c7 83 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    346e:	e8 9d ef ff ff       	call   2410 <calloc@plt>
          thread_data[x].tasks[y].current_snapshot = 0;
    3473:	48 c7 83 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rbx)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    347e:	48 89 83 50 01 00 00 	mov    %rax,0x150(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    3485:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    348a:	48 8b 00             	mov    (%rax),%rax
    348d:	8b 48 04             	mov    0x4(%rax),%ecx
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    3490:	49 39 c7             	cmp    %rax,%r15
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    3493:	48 89 83 28 01 00 00 	mov    %rax,0x128(%rbx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    349a:	89 8b 30 01 00 00    	mov    %ecx,0x130(%rbx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    34a0:	5a                   	pop    %rdx
    34a1:	59                   	pop    %rcx
    34a2:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    34a7:	0f 85 26 14 00 00    	jne    48d3 <main+0x2213>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    34ad:	66 0f 6f 05 fb 6a 00 00 	movdqa 0x6afb(%rip),%xmm0        # 9fb0 <_IO_stdin_used+0xfb0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    34b5:	89 6b 04             	mov    %ebp,0x4(%rbx)
          thread_data[x].tasks[y].available = 1;
    34b8:	48 8b 05 01 6b 00 00 	mov    0x6b01(%rip),%rax        # 9fc0 <_IO_stdin_used+0xfc0>
          thread_data[x].tasks[y].arrived = 0;
    34bf:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
          thread_data[x].tasks[y].worker_count = thread_count;
    34c9:	c7 83 8c 01 00 00 02 00 00 00 	movl   $0x2,0x18c(%rbx)
          thread_data[x].tasks[y].available = 1;
    34d3:	48 89 83 44 01 00 00 	mov    %rax,0x144(%rbx)
          thread_data[x].tasks[y].thread_count = 2;
    34da:	0f 11 83 34 01 00 00 	movups %xmm0,0x134(%rbx)
          if (y == barrier_count - 1) {
    34e1:	83 fd 01             	cmp    $0x1,%ebp
    34e4:	0f 84 49 01 00 00    	je     3633 <main+0xf73>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    34ea:	85 ed                	test   %ebp,%ebp
    34ec:	0f 84 29 01 00 00    	je     361b <main+0xf5b>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    34f2:	4c 8b 4c 24 48       	mov    0x48(%rsp),%r9
    34f7:	48 8d 05 f2 4a 00 00 	lea    0x4af2(%rip),%rax        # 7ff0 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    34fe:	be 08 00 00 00       	mov    $0x8,%esi
               thread_data[x].tasks[y].run = barriered_work; 
    3503:	45 89 f7             	mov    %r14d,%r15d
    3506:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    350d:	bf 01 00 00 00       	mov    $0x1,%edi
        thread_data[x].buffers_count = buffers_per_thread;
    3512:	41 c7 81 c4 00 00 00 01 00 00 00 	movl   $0x1,0xc4(%r9)
               thread_data[x].tasks[y].run = barriered_work; 
    351d:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
        thread_data[x].buffers_count = buffers_per_thread;
    3522:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3527:	e8 e4 ee ff ff       	call   2410 <calloc@plt>
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    352c:	4c 8b 74 24 68       	mov    0x68(%rsp),%r14
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3531:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        }
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3536:	be 08 00 00 00       	mov    $0x8,%esi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    353b:	48 8b 9c 24 a8 00 00 00 	mov    0xa8(%rsp),%rbx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3543:	bf 02 00 00 00       	mov    $0x2,%edi
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3548:	83 84 24 84 00 00 00 01 	addl   $0x1,0x84(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3550:	49 89 41 50          	mov    %rax,0x50(%r9)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3554:	4a 8d 0c 73          	lea    (%rbx,%r14,2),%rcx
    3558:	48 89 08             	mov    %rcx,(%rax)
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    355b:	e8 b0 ee ff ff       	call   2410 <calloc@plt>
        for (int b = 0 ; b < io_threads; b++) {	
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    3560:	48 8b 5c 24 60       	mov    0x60(%rsp),%rbx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3565:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    356a:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    356f:	83 44 24 7c 02       	addl   $0x2,0x7c(%rsp)
    3574:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
        thread_data[x].iobuffers = calloc(io_threads, sizeof(struct Buffers*)); 
    3578:	49 89 41 58          	mov    %rax,0x58(%r9)
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    357c:	66 0f 6f bc 24 c0 00 00 00 	movdqa 0xc0(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    3585:	49 81 c1 20 01 00 00 	add    $0x120,%r9
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    358c:	48 89 18             	mov    %rbx,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    358f:	48 83 c3 20          	add    $0x20,%rbx
          thread_data[x].iobuffers[b] = &buffers[iocur_buffer++];
    3593:	48 89 48 08          	mov    %rcx,0x8(%rax)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3597:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    359c:	48 89 5c 24 60       	mov    %rbx,0x60(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    35a1:	48 8b 00             	mov    (%rax),%rax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    35a4:	0f 11 ba 18 05 00 00 	movups %xmm7,0x518(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    35ab:	c7 82 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%rdx)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    35b5:	48 89 82 28 05 00 00 	mov    %rax,0x528(%rdx)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    35bc:	c7 82 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%rdx)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    35c6:	c7 82 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    35d0:	41 8b 81 e4 fe ff ff 	mov    -0x11c(%r9),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    35d7:	c7 82 8c 05 00 00 02 00 00 00 	movl   $0x2,0x58c(%rdx)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    35e1:	89 82 30 05 00 00    	mov    %eax,0x530(%rdx)
        thread_data[x].tasks[barrier_count].available = 1; 
    35e7:	48 8b 05 d2 69 00 00 	mov    0x69d2(%rip),%rax        # 9fc0 <_IO_stdin_used+0xfc0>
    35ee:	48 89 82 44 05 00 00 	mov    %rax,0x544(%rdx)
    for (int d = 0 ; d < threads_per_group ; d++) {
    35f5:	49 83 fe 08          	cmp    $0x8,%r14
    35f9:	74 46                	je     3641 <main+0xf81>
    35fb:	48 c7 44 24 68 08 00 00 00 	movq   $0x8,0x68(%rsp)
    3604:	44 8b b4 24 88 00 00 00 	mov    0x88(%rsp),%r14d
    360c:	e9 e3 f5 ff ff       	jmp    2bf4 <main+0x534>
    3611:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    3616:	e9 c4 fb ff ff       	jmp    31df <main+0xb1f>
    361b:	48 8d 05 8e 4f 00 00 	lea    0x4f8e(%rip),%rax        # 85b0 <barriered_work_ingest_andwork>
    3622:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    3627:	48 89 83 18 01 00 00 	mov    %rax,0x118(%rbx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    362e:	e9 5a f8 ff ff       	jmp    2e8d <main+0x7cd>
    3633:	48 8d 05 b6 49 00 00 	lea    0x49b6(%rip),%rax        # 7ff0 <barriered_work>
    363a:	bd 02 00 00 00       	mov    $0x2,%ebp
    363f:	eb e6                	jmp    3627 <main+0xf67>
  for (int k = 0 ; k < group_count ; k++) {
    3641:	49 83 c5 01          	add    $0x1,%r13
    3645:	48 8b ac 24 f8 00 00 00 	mov    0xf8(%rsp),%rbp
    364d:	48 83 84 24 a0 00 00 00 18 	addq   $0x18,0xa0(%rsp)
    3656:	4c 8b b4 24 08 01 00 00 	mov    0x108(%rsp),%r14
    365e:	49 83 fd 03          	cmp    $0x3,%r13
    3662:	0f 85 be f4 ff ff    	jne    2b26 <main+0x466>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3668:	be 08 00 00 00       	mov    $0x8,%esi
    366d:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    3672:	31 ed                	xor    %ebp,%ebp
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    3674:	e8 97 ed ff ff       	call   2410 <calloc@plt>
    3679:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    367e:	49 89 c7             	mov    %rax,%r15
    3681:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3683:	49 89 d1             	mov    %rdx,%r9
    3686:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3688:	45 8b 51 40          	mov    0x40(%r9),%r10d
    368c:	45 85 d2             	test   %r10d,%r10d
    368f:	0f 8e ac 00 00 00    	jle    3741 <main+0x1081>
    3695:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3699:	4d 63 c2             	movslq %r10d,%r8
    369c:	48 63 cd             	movslq %ebp,%rcx
    369f:	49 c1 e0 09          	shl    $0x9,%r8
    36a3:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    36a7:	49 01 f8             	add    %rdi,%r8
    36aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    36b0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    36b7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    36be:	48 83 c6 60          	add    $0x60,%rsi
    36c2:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    36ca:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    36ce:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    36d6:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    36de:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    36e6:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    36ed:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    36f5:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    36fc:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3703:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    370a:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    370e:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3715:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    371c:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3720:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3724:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3728:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    372c:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3730:	49 39 f8             	cmp    %rdi,%r8
    3733:	0f 85 77 ff ff ff    	jne    36b0 <main+0xff0>
    3739:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    373d:	8d 6c 8d 00          	lea    0x0(%rbp,%rcx,4),%ebp
    for (int d = 0 ; d < threads_per_group ; d++) {
    3741:	49 81 c1 20 01 00 00 	add    $0x120,%r9
    3748:	85 db                	test   %ebx,%ebx
    374a:	75 37                	jne    3783 <main+0x10c3>
    374c:	bb 01 00 00 00       	mov    $0x1,%ebx
    3751:	e9 32 ff ff ff       	jmp    3688 <main+0xfc8>
        other = (x + 1) % total_threads;
    3756:	41 8d 46 01          	lea    0x1(%r14),%eax
        my_thread_data[1] = &thread_data[other]; 
    375a:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    375f:	4c 89 ca             	mov    %r9,%rdx
    3762:	45 31 c0             	xor    %r8d,%r8d
    3765:	89 84 24 88 00 00 00 	mov    %eax,0x88(%rsp)
        other = (x + 1) % total_threads;
    376c:	89 c1                	mov    %eax,%ecx
        my_thread_data[1] = &thread_data[other]; 
    376e:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3772:	48 c1 e0 05          	shl    $0x5,%rax
    3776:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    377b:	48 01 f8             	add    %rdi,%rax
        thread_data[x].protected_state = &protected_state[k];
    377e:	e9 42 f5 ff ff       	jmp    2cc5 <main+0x605>
  for (int k = 0 ; k < group_count ; k++) {
    3783:	83 c0 02             	add    $0x2,%eax
    3786:	48 81 c2 40 02 00 00 	add    $0x240,%rdx
    378d:	83 f8 06             	cmp    $0x6,%eax
    3790:	0f 85 ed fe ff ff    	jne    3683 <main+0xfc3>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3796:	48 8d 3d 3d 5d 00 00 	lea    0x5d3d(%rip),%rdi        # 94da <_IO_stdin_used+0x4da>
    379d:	e8 9e eb ff ff       	call   2340 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    37a2:	48 8d 35 46 5d 00 00 	lea    0x5d46(%rip),%rsi        # 94ef <_IO_stdin_used+0x4ef>
    37a9:	48 8d 3d 41 5d 00 00 	lea    0x5d41(%rip),%rdi        # 94f1 <_IO_stdin_used+0x4f1>
    37b0:	e8 4b ed ff ff       	call   2500 <fopen@plt>
    37b5:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas_size; x++) {
    37b8:	85 ed                	test   %ebp,%ebp
    37ba:	7e 76                	jle    3832 <main+0x1172>
    37bc:	48 63 ed             	movslq %ebp,%rbp
    37bf:	4c 8d 2d 08 5d 00 00 	lea    0x5d08(%rip),%r13        # 94ce <_IO_stdin_used+0x4ce>
    37c6:	4c 8d 25 45 5d 00 00 	lea    0x5d45(%rip),%r12        # 9512 <_IO_stdin_used+0x512>
    37cd:	49 8d 04 ef          	lea    (%r15,%rbp,8),%rax
    37d1:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    char * c = calloc(250, sizeof(char));
    37d6:	be 01 00 00 00       	mov    $0x1,%esi
    37db:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    37e0:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    37e4:	e8 27 ec ff ff       	call   2410 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    37e9:	4c 89 e9             	mov    %r13,%rcx
    37ec:	ba fa 00 00 00       	mov    $0xfa,%edx
    37f1:	be 01 00 00 00       	mov    $0x1,%esi
    37f6:	48 89 c5             	mov    %rax,%rbp
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    37f9:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    37fd:	48 89 ef             	mov    %rbp,%rdi
    3800:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    3807:	31 c0                	xor    %eax,%eax
    3809:	e8 b2 ed ff ff       	call   25c0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    380e:	48 89 ea             	mov    %rbp,%rdx
    3811:	4c 89 e6             	mov    %r12,%rsi
    3814:	bf 01 00 00 00       	mov    $0x1,%edi
    3819:	31 c0                	xor    %eax,%eax
    381b:	e8 a0 ec ff ff       	call   24c0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3820:	4c 89 f6             	mov    %r14,%rsi
    3823:	48 89 ef             	mov    %rbp,%rdi
    3826:	e8 a5 eb ff ff       	call   23d0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    382b:	4c 39 7c 24 08       	cmp    %r15,0x8(%rsp)
    3830:	75 a4                	jne    37d6 <main+0x1116>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    3832:	4c 89 f7             	mov    %r14,%rdi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3835:	45 31 f6             	xor    %r14d,%r14d
    3838:	4c 8d 25 fd 5c 00 00 	lea    0x5cfd(%rip),%r12        # 953c <_IO_stdin_used+0x53c>
    383f:	e8 2c eb ff ff       	call   2370 <fclose@plt>
    3844:	48 8d 3d af 5c 00 00 	lea    0x5caf(%rip),%rdi        # 94fa <_IO_stdin_used+0x4fa>
    384b:	4c 89 f5             	mov    %r14,%rbp
    384e:	e8 ed ea ff ff       	call   2340 <puts@plt>

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    3853:	89 5c 24 10          	mov    %ebx,0x10(%rsp)
    3857:	89 ea                	mov    %ebp,%edx
    3859:	48 8d 35 b5 5c 00 00 	lea    0x5cb5(%rip),%rsi        # 9515 <_IO_stdin_used+0x515>
    3860:	bf 01 00 00 00       	mov    $0x1,%edi
    3865:	31 c0                	xor    %eax,%eax
    3867:	e8 54 ec ff ff       	call   24c0 <__printf_chk@plt>
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    386c:	48 8d 5c ed 00       	lea    0x0(%rbp,%rbp,8),%rbx
    3871:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3876:	45 31 ff             	xor    %r15d,%r15d
    3879:	48 c1 e3 06          	shl    $0x6,%rbx
    387d:	44 8d 6c 2d 00       	lea    0x0(%rbp,%rbp,1),%r13d
    3882:	48 01 c3             	add    %rax,%rbx
      int x = (k * threads_per_group) + d;
    3885:	43 8d 0c 2f          	lea    (%r15,%r13,1),%ecx
    3889:	44 89 fa             	mov    %r15d,%edx
    388c:	48 8d 35 8c 5c 00 00 	lea    0x5c8c(%rip),%rsi        # 951f <_IO_stdin_used+0x51f>
    3893:	31 c0                	xor    %eax,%eax
    3895:	bf 01 00 00 00       	mov    $0x1,%edi
    389a:	45 31 f6             	xor    %r14d,%r14d
    389d:	e8 1e ec ff ff       	call   24c0 <__printf_chk@plt>
    38a2:	44 89 6c 24 18       	mov    %r13d,0x18(%rsp)
    38a7:	4c 89 f1             	mov    %r14,%rcx
    38aa:	48 89 6c 24 20       	mov    %rbp,0x20(%rsp)
    38af:	48 89 dd             	mov    %rbx,%rbp
    38b2:	89 ca                	mov    %ecx,%edx
    38b4:	48 8d 35 76 5c 00 00 	lea    0x5c76(%rip),%rsi        # 9531 <_IO_stdin_used+0x531>
    38bb:	bf 01 00 00 00       	mov    $0x1,%edi
    38c0:	31 c0                	xor    %eax,%eax
    38c2:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    38c7:	45 31 ed             	xor    %r13d,%r13d
    38ca:	e8 f1 eb ff ff       	call   24c0 <__printf_chk@plt>
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    38cf:	48 8b 5c 24 08       	mov    0x8(%rsp),%rbx
    38d4:	48 c1 e3 09          	shl    $0x9,%rbx
    38d8:	eb 32                	jmp    390c <main+0x124c>
    38da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    38e0:	83 fe 01             	cmp    $0x1,%esi
    38e3:	0f 84 a9 00 00 00    	je     3992 <main+0x12d2>
    38e9:	44 89 f2             	mov    %r14d,%edx
    38ec:	4c 89 e6             	mov    %r12,%rsi
    38ef:	bf 01 00 00 00       	mov    $0x1,%edi
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    38f4:	49 83 c5 01          	add    $0x1,%r13
    38f8:	44 8b 80 b4 00 00 00 	mov    0xb4(%rax),%r8d
    38ff:	31 c0                	xor    %eax,%eax
    3901:	e8 ba eb ff ff       	call   24c0 <__printf_chk@plt>
    3906:	49 83 fd 06          	cmp    $0x6,%r13
    390a:	74 50                	je     395c <main+0x129c>
          char * mailbox_kind = calloc(100, sizeof(char));
    390c:	be 01 00 00 00       	mov    $0x1,%esi
    3911:	bf 64 00 00 00       	mov    $0x64,%edi
    3916:	45 89 ee             	mov    %r13d,%r14d
    3919:	e8 f2 ea ff ff       	call   2410 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    391e:	4c 8b 45 38          	mov    0x38(%rbp),%r8
    3922:	4c 89 ef             	mov    %r13,%rdi
          char * mailbox_kind = calloc(100, sizeof(char));
    3925:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3928:	48 c1 e7 08          	shl    $0x8,%rdi
    392c:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3934:	48 01 f8             	add    %rdi,%rax
    3937:	8b b0 b0 00 00 00    	mov    0xb0(%rax),%esi
    393d:	83 fe 02             	cmp    $0x2,%esi
    3940:	75 9e                	jne    38e0 <main+0x1220>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3942:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    394c:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    394f:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    3957:	48 01 f8             	add    %rdi,%rax
    395a:	eb 8d                	jmp    38e9 <main+0x1229>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    395c:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    3961:	48 83 c1 01          	add    $0x1,%rcx
    3965:	48 83 f9 03          	cmp    $0x3,%rcx
    3969:	0f 85 43 ff ff ff    	jne    38b2 <main+0x11f2>
    for (int d = 0 ; d < threads_per_group ; d++) {
    396f:	48 89 eb             	mov    %rbp,%rbx
    3972:	44 8b 6c 24 18       	mov    0x18(%rsp),%r13d
    3977:	48 8b 6c 24 20       	mov    0x20(%rsp),%rbp
    397c:	48 81 c3 20 01 00 00 	add    $0x120,%rbx
    3983:	45 85 ff             	test   %r15d,%r15d
    3986:	75 27                	jne    39af <main+0x12ef>
    3988:	44 8b 7c 24 10       	mov    0x10(%rsp),%r15d
    398d:	e9 f3 fe ff ff       	jmp    3885 <main+0x11c5>
    3992:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3998:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    399f:	49 8b 84 18 70 01 00 00 	mov    0x170(%r8,%rbx,1),%rax
    39a7:	48 01 f8             	add    %rdi,%rax
    39aa:	e9 3a ff ff ff       	jmp    38e9 <main+0x1229>
  for (int k = 0 ; k < group_count ; k++) {
    39af:	48 83 c5 01          	add    $0x1,%rbp
    39b3:	48 83 fd 03          	cmp    $0x3,%rbp
    39b7:	0f 85 9a fe ff ff    	jne    3857 <main+0x1197>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    39bd:	ba 07 00 00 00       	mov    $0x7,%edx
    39c2:	48 8d 35 8e 5b 00 00 	lea    0x5b8e(%rip),%rsi        # 9557 <_IO_stdin_used+0x557>
    39c9:	bf 01 00 00 00       	mov    $0x1,%edi
    39ce:	31 c0                	xor    %eax,%eax
    39d0:	e8 eb ea ff ff       	call   24c0 <__printf_chk@plt>
  

  printf("io index = %d\n", io_index);
  int io_mode = 0;
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    39d5:	be 08 00 00 00       	mov    $0x8,%esi
    39da:	bf 02 00 00 00       	mov    $0x2,%edi
    39df:	e8 2c ea ff ff       	call   2410 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    39e4:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    39e9:	be 08 00 00 00       	mov    $0x8,%esi
    my_thread_data[0] = &thread_data[x]; 
    39ee:	49 8d be e0 07 00 00 	lea    0x7e0(%r14),%rdi
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    39f5:	4c 89 70 08          	mov    %r14,0x8(%rax)
    39f9:	49 8d ae 20 01 00 00 	lea    0x120(%r14),%rbp

    io_mode = (io_mode + 1) % 2;
    thread_data[x].threads = my_thread_data;
    3a00:	49 89 86 f8 07 00 00 	mov    %rax,0x7f8(%r14)
    thread_data[x].thread_count = 2;
    3a07:	41 c7 86 08 08 00 00 02 00 00 00 	movl   $0x2,0x808(%r14)
    thread_data[x].thread_index = 0;
    3a12:	41 c7 86 e4 07 00 00 00 00 00 00 	movl   $0x0,0x7e4(%r14)
    thread_data[x].task_count = total_barrier_count;
    3a1d:	41 c7 86 20 08 00 00 03 00 00 00 	movl   $0x3,0x820(%r14)
    my_thread_data[0] = &thread_data[x]; 
    3a28:	48 89 38             	mov    %rdi,(%rax)
    3a2b:	48 89 7c 24 10       	mov    %rdi,0x10(%rsp)
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    3a30:	bf 02 00 00 00       	mov    $0x2,%edi
    3a35:	e8 d6 e9 ff ff       	call   2410 <calloc@plt>
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a3a:	be 38 00 00 00       	mov    $0x38,%esi
    3a3f:	bf 0b 00 00 00       	mov    $0xb,%edi
    my_thread_data[0] = &thread_data[x]; 
    3a44:	49 8d 96 00 09 00 00 	lea    0x900(%r14),%rdx
    3a4b:	48 89 10             	mov    %rdx,(%rax)
    thread_data[x].threads = my_thread_data;
    3a4e:	49 89 86 18 09 00 00 	mov    %rax,0x918(%r14)
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3a55:	48 89 68 08          	mov    %rbp,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3a59:	49 8b 46 38          	mov    0x38(%r14),%rax
    thread_data[x].thread_count = 2;
    3a5d:	41 c7 86 28 09 00 00 02 00 00 00 	movl   $0x2,0x928(%r14)
    thread_data[x].thread_index = 0;
    3a68:	41 c7 86 04 09 00 00 00 00 00 00 	movl   $0x0,0x904(%r14)
    thread_data[x].task_count = total_barrier_count;
    3a73:	41 c7 86 40 09 00 00 03 00 00 00 	movl   $0x3,0x940(%r14)
    thread_data[n].tasks[0].scheduled = 1;
    3a7e:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3a88:	49 8b 86 58 01 00 00 	mov    0x158(%r14),%rax
    my_thread_data[0] = &thread_data[x]; 
    3a8f:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
    thread_data[n].tasks[0].scheduled = 1;
    3a94:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3a9e:	e8 6d e9 ff ff       	call   2410 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3aa3:	be 38 00 00 00       	mov    $0x38,%esi
    3aa8:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3aad:	49 89 c5             	mov    %rax,%r13
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ab0:	e8 5b e9 ff ff       	call   2410 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ab5:	be 38 00 00 00       	mov    $0x38,%esi
    3aba:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3abf:	49 89 c4             	mov    %rax,%r12
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ac2:	e8 49 e9 ff ff       	call   2410 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ac7:	be 38 00 00 00       	mov    $0x38,%esi
    3acc:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ad1:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ad6:	e8 35 e9 ff ff       	call   2410 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3adb:	be 08 00 00 00       	mov    $0x8,%esi
    3ae0:	bf 0b 00 00 00       	mov    $0xb,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3ae5:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3aea:	e8 21 e9 ff ff       	call   2410 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3aef:	be 08 00 00 00       	mov    $0x8,%esi
    3af4:	bf 0b 00 00 00       	mov    $0xb,%edi
  thread_data[timer_threadi].type = TIMER;
    3af9:	41 c7 86 cc 06 00 00 00 00 00 00 	movl   $0x0,0x6cc(%r14)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3b04:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    3b07:	48 8b 05 ca 64 00 00 	mov    0x64ca(%rip),%rax        # 9fd8 <_IO_stdin_used+0xfd8>
    3b0e:	49 89 86 00 07 00 00 	mov    %rax,0x700(%r14)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3b15:	e8 f6 e8 ff ff       	call   2410 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3b1a:	49 8d 96 40 02 00 00 	lea    0x240(%r14),%rdx
    3b21:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3b26:	4c 89 f7             	mov    %r14,%rdi
    3b29:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3b2d:	49 8d 96 60 03 00 00 	lea    0x360(%r14),%rdx
    3b34:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3b38:	49 8d 96 80 04 00 00 	lea    0x480(%r14),%rdx
    3b3f:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3b43:	49 8d 96 a0 05 00 00 	lea    0x5a0(%r14),%rdx
    3b4a:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3b4e:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    3b53:	4c 89 30             	mov    %r14,(%rax)
    3b56:	4d 8d b6 c0 06 00 00 	lea    0x6c0(%r14),%r14
    3b5d:	48 89 70 38          	mov    %rsi,0x38(%rax)
    3b61:	48 8d b7 20 0a 00 00 	lea    0xa20(%rdi),%rsi
    3b68:	48 89 50 40          	mov    %rdx,0x40(%rax)
    3b6c:	48 8d 97 40 0b 00 00 	lea    0xb40(%rdi),%rdx
    3b73:	4c 89 70 30          	mov    %r14,0x30(%rax)
    3b77:	48 89 70 48          	mov    %rsi,0x48(%rax)
    3b7b:	48 89 50 50          	mov    %rdx,0x50(%rax)
    3b7f:	ba 06 00 00 00       	mov    $0x6,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3b84:	48 89 87 d8 06 00 00 	mov    %rax,0x6d8(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    3b8b:	48 89 68 08          	mov    %rbp,0x8(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3b8f:	48 8b 05 4a 64 00 00 	mov    0x644a(%rip),%rax        # 9fe0 <_IO_stdin_used+0xfe0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    3b96:	c7 87 f0 06 00 00 06 00 00 00 	movl   $0x6,0x6f0(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3ba0:	48 89 87 e8 06 00 00 	mov    %rax,0x6e8(%rdi)
    3ba7:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    3ba9:	c7 87 c4 06 00 00 00 00 00 00 	movl   $0x0,0x6c4(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    3bb3:	48 89 74 24 40       	mov    %rsi,0x40(%rsp)
    3bb8:	48 8d 35 a7 59 00 00 	lea    0x59a7(%rip),%rsi        # 9566 <_IO_stdin_used+0x566>
  thread_data[timer_threadi].thread_index = 0;
    3bbf:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
    3bc4:	bf 01 00 00 00       	mov    $0x1,%edi
    3bc9:	e8 f2 e8 ff ff       	call   24c0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3bce:	4c 89 f1             	mov    %r14,%rcx
    3bd1:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
  for (int k = 0 ; k < group_count ; k++) {
    3bd5:	45 31 f6             	xor    %r14d,%r14d
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3bd8:	48 8d 15 f1 0f 00 00 	lea    0xff1(%rip),%rdx        # 4bd0 <timer_thread>
    3bdf:	49 8d b4 24 50 01 00 00 	lea    0x150(%r12),%rsi
    3be7:	e8 f4 e8 ff ff       	call   24e0 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    3bec:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    3bf1:	48 89 d9             	mov    %rbx,%rcx
    3bf4:	4c 89 e8             	mov    %r13,%rax
    3bf7:	48 89 6c 24 48       	mov    %rbp,0x48(%rsp)
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3bfc:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3c02:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3c07:	44 89 7c 24 20       	mov    %r15d,0x20(%rsp)
    3c0c:	45 89 d7             	mov    %r10d,%r15d
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c0f:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
    3c14:	43 8d 1c 36          	lea    (%r14,%r14,1),%ebx
    3c18:	48 89 c5             	mov    %rax,%rbp
    3c1b:	49 89 cd             	mov    %rcx,%r13
    3c1e:	48 89 4c 24 58       	mov    %rcx,0x58(%rsp)
    3c23:	49 89 d4             	mov    %rdx,%r12
    3c26:	48 89 54 24 60       	mov    %rdx,0x60(%rsp)
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3c2b:	41 c7 44 24 0c 01 00 00 00 	movl   $0x1,0xc(%r12)
    3c34:	89 da                	mov    %ebx,%edx
    3c36:	44 89 f1             	mov    %r14d,%ecx
    3c39:	31 c0                	xor    %eax,%eax
    3c3b:	48 8d 35 8e 5e 00 00 	lea    0x5e8e(%rip),%rsi        # 9ad0 <_IO_stdin_used+0xad0>
    3c42:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c47:	83 c3 01             	add    $0x1,%ebx
      thread_data[x].running = 1;
    3c4a:	41 c7 44 24 44 01 00 00 00 	movl   $0x1,0x44(%r12)
    3c53:	e8 68 e8 ff ff       	call   24c0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3c58:	4c 89 e1             	mov    %r12,%rcx
    3c5b:	48 89 ee             	mov    %rbp,%rsi
    3c5e:	4c 89 ef             	mov    %r13,%rdi
    3c61:	48 8d 15 c8 3a 00 00 	lea    0x3ac8(%rip),%rdx        # 7730 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c68:	49 81 c4 20 01 00 00 	add    $0x120,%r12
    3c6f:	49 83 c5 08          	add    $0x8,%r13
    3c73:	48 83 c5 38          	add    $0x38,%rbp
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3c77:	e8 64 e8 ff ff       	call   24e0 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3c7c:	49 8b 54 24 98       	mov    -0x68(%r12),%rdx
    3c81:	49 8b 7d f8          	mov    -0x8(%r13),%rdi
    3c85:	be 08 00 00 00       	mov    $0x8,%esi
    3c8a:	e8 a1 e6 ff ff       	call   2330 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c8f:	41 39 df             	cmp    %ebx,%r15d
    3c92:	75 97                	jne    3c2b <main+0x156b>
  for (int k = 0 ; k < group_count ; k++) {
    3c94:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    3c99:	48 8b 4c 24 58       	mov    0x58(%rsp),%rcx
    3c9e:	41 83 c6 01          	add    $0x1,%r14d
    3ca2:	41 83 c7 02          	add    $0x2,%r15d
    3ca6:	48 8b 54 24 60       	mov    0x60(%rsp),%rdx
    3cab:	48 83 c1 10          	add    $0x10,%rcx
    3caf:	48 83 c0 70          	add    $0x70,%rax
    3cb3:	48 81 c2 40 02 00 00 	add    $0x240,%rdx
    3cba:	41 83 fe 03          	cmp    $0x3,%r14d
    3cbe:	0f 85 4b ff ff ff    	jne    3c0f <main+0x154f>
    }
  }
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    3cc4:	be 08 00 00 00       	mov    $0x8,%esi
    3cc9:	bf 02 00 00 00       	mov    $0x2,%edi
    3cce:	48 8b 6c 24 48       	mov    0x48(%rsp),%rbp
    3cd3:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    3cd8:	44 8b 7c 24 20       	mov    0x20(%rsp),%r15d
    3cdd:	e8 2e e7 ff ff       	call   2410 <calloc@plt>

  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    3ce2:	be d8 00 00 00       	mov    $0xd8,%esi
    3ce7:	bf 01 00 00 00       	mov    $0x1,%edi
  struct io_uring **rings = calloc(2, sizeof(struct io_uring*));
    3cec:	49 89 c4             	mov    %rax,%r12
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    3cef:	e8 1c e7 ff ff       	call   2410 <calloc@plt>
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3cf4:	be d8 00 00 00       	mov    $0xd8,%esi
    3cf9:	bf 01 00 00 00       	mov    $0x1,%edi
  rings[IO_MODE_SEND] = calloc(1, sizeof(struct io_uring));
    3cfe:	49 89 04 24          	mov    %rax,(%r12)
    3d02:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3d07:	e8 04 e7 ff ff       	call   2410 <calloc@plt>

  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    3d0c:	be 10 00 00 00       	mov    $0x10,%esi
    3d11:	bf 02 00 00 00       	mov    $0x2,%edi
  rings[IO_MODE_RECV] = calloc(1, sizeof(struct io_uring));
    3d16:	49 89 44 24 08       	mov    %rax,0x8(%r12)
    3d1b:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
  struct Buffers *iomailboxes = calloc(io_threads, sizeof(struct Buffers));
    3d20:	e8 eb e6 ff ff       	call   2410 <calloc@plt>
    3d25:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
    3d2a:	49 89 c6             	mov    %rax,%r14
  long iomailboxes_size = 1000;
  for (int x = 0 ; x < io_threads; x++) {
    3d2d:	48 8d 40 20          	lea    0x20(%rax),%rax
    3d31:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    3d36:	48 89 e8             	mov    %rbp,%rax
    3d39:	4c 89 f5             	mov    %r14,%rbp
    3d3c:	49 89 c5             	mov    %rax,%r13
    iomailboxes[x].count = iomailboxes_size;
    3d3f:	c7 45 00 e8 03 00 00 	movl   $0x3e8,0x0(%rbp)
    iomailboxes[x].buffer = calloc(iomailboxes_size, sizeof(struct Buffer));
    3d46:	be 00 01 00 00       	mov    $0x100,%esi
    3d4b:	bf e8 03 00 00       	mov    $0x3e8,%edi
    3d50:	e8 bb e6 ff ff       	call   2410 <calloc@plt>
    3d55:	48 89 45 08          	mov    %rax,0x8(%rbp)
    3d59:	48 89 c3             	mov    %rax,%rbx
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3d5c:	4c 8d a0 80 00 00 00 	lea    0x80(%rax),%r12
    3d63:	48 81 c3 80 e8 03 00 	add    $0x3e880,%rbx
    3d6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      iomailboxes[x].buffer[y].available = 0;
    3d70:	41 c7 04 24 00 00 00 00 	movl   $0x0,(%r12)
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3d78:	be 20 00 00 00       	mov    $0x20,%esi
    3d7d:	bf 64 00 00 00       	mov    $0x64,%edi
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3d82:	49 81 c4 00 01 00 00 	add    $0x100,%r12
      iomailboxes[x].buffer[y].snapshot_limit = snapshot_limit;
    3d89:	41 c7 84 24 10 ff ff ff 64 00 00 00 	movl   $0x64,-0xf0(%r12)
      iomailboxes[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    3d95:	e8 76 e6 ff ff       	call   2410 <calloc@plt>
    3d9a:	49 89 84 24 08 ff ff ff 	mov    %rax,-0xf8(%r12)
    for (int y = 0 ; y < iomailboxes_size; y++) {
    3da2:	4c 39 e3             	cmp    %r12,%rbx
    3da5:	75 c9                	jne    3d70 <main+0x16b0>
  for (int x = 0 ; x < io_threads; x++) {
    3da7:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    3dac:	48 83 c5 10          	add    $0x10,%rbp
    3db0:	48 39 c5             	cmp    %rax,%rbp
    3db3:	75 8a                	jne    3d3f <main+0x167f>
  char * send_identity = "send-thread";
  char * recv_identity = "recv-thread";
  char * unknown_identity = "unknown-thread";
  int counter = 0;
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    3db5:	4c 89 ed             	mov    %r13,%rbp
    3db8:	4c 8b 6c 24 38       	mov    0x38(%rsp),%r13
    3dbd:	45 31 c0             	xor    %r8d,%r8d
    3dc0:	b9 01 00 00 00       	mov    $0x1,%ecx
    3dc5:	ba 07 00 00 00       	mov    $0x7,%edx
    3dca:	bf 01 00 00 00       	mov    $0x1,%edi
    3dcf:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    3dd4:	4c 8b 25 0d 62 00 00 	mov    0x620d(%rip),%r12        # 9fe8 <_IO_stdin_used+0xfe8>
    3ddb:	48 8d 05 a2 57 00 00 	lea    0x57a2(%rip),%rax        # 9584 <_IO_stdin_used+0x584>
      thread_data[x].identity = unknown_identity;
    }
    thread_data[x].io_mode = myring;
    thread_data[x].my_io = myring;
    thread_data[x].other_io = otherring;
    thread_data[x].iomailboxes = iomailboxes; 
    3de2:	4d 89 b5 e8 08 00 00 	mov    %r14,0x8e8(%r13)
    3de9:	4c 8d 1d a0 57 00 00 	lea    0x57a0(%rip),%r11        # 9590 <_IO_stdin_used+0x590>
    3df0:	49 89 85 f8 08 00 00 	mov    %rax,0x8f8(%r13)
    3df7:	4c 89 de             	mov    %r11,%rsi
    3dfa:	31 c0                	xor    %eax,%eax
    thread_data[x].type = IO;
    3dfc:	41 c7 85 ec 07 00 00 02 00 00 00 	movl   $0x2,0x7ec(%r13)
    thread_data[x].task_count = 0;
    3e07:	4d 89 a5 20 08 00 00 	mov    %r12,0x820(%r13)
    thread_data[x].io_mode = myring;
    3e0e:	41 c7 85 e4 08 00 00 01 00 00 00 	movl   $0x1,0x8e4(%r13)
    thread_data[x].other_io = otherring;
    3e19:	4d 89 a5 f0 08 00 00 	mov    %r12,0x8f0(%r13)
    3e20:	e8 9b e6 ff ff       	call   24c0 <__printf_chk@plt>
    printf("%d myring %d other is %d\n", x, myring, otherring);
    thread_data[x].ring = rings[myring]; 
    3e25:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    int myeventfd = eventfd(counter++, EFD_NONBLOCK);
    3e2a:	be 00 08 00 00       	mov    $0x800,%esi
    3e2f:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = rings[myring]; 
    3e31:	49 89 85 40 08 00 00 	mov    %rax,0x840(%r13)
    int myeventfd = eventfd(counter++, EFD_NONBLOCK);
    3e38:	e8 f3 e6 ff ff       	call   2530 <eventfd@plt>
    thread_data[x]._eventfd = myeventfd; 
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3e3d:	be 08 00 00 00       	mov    $0x8,%esi
    3e42:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = myeventfd; 
    3e47:	41 89 85 48 08 00 00 	mov    %eax,0x848(%r13)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3e4e:	e8 bd e5 ff ff       	call   2410 <calloc@plt>
    3e53:	ba 07 00 00 00       	mov    $0x7,%edx
    3e58:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3e5d:	41 c7 85 08 08 00 00 02 00 00 00 	movl   $0x2,0x808(%r13)
      my_thread_data[n] = &thread_data[n]; 
    3e68:	4c 89 28             	mov    %r13,(%rax)
    3e6b:	4c 8d 15 38 57 00 00 	lea    0x5738(%rip),%r10        # 95aa <_IO_stdin_used+0x5aa>
    thread_data[x].threads = my_thread_data;
    3e72:	49 89 85 f8 07 00 00 	mov    %rax,0x7f8(%r13)
    3e79:	4c 89 d6             	mov    %r10,%rsi
      my_thread_data[n] = &thread_data[n]; 
    3e7c:	48 89 68 08          	mov    %rbp,0x8(%rax)
    3e80:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3e82:	41 c7 85 e4 07 00 00 07 00 00 00 	movl   $0x7,0x7e4(%r13)
    3e8d:	4c 89 6c 24 38       	mov    %r13,0x38(%rsp)
    printf("Creating IO thread %d\n", x);
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3e92:	4c 8d 2d 27 22 00 00 	lea    0x2227(%rip),%r13        # 60c0 <io_thread>
    3e99:	e8 22 e6 ff ff       	call   24c0 <__printf_chk@plt>
    3e9e:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3ea3:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    3ea8:	4c 89 ea             	mov    %r13,%rdx
    3eab:	48 8d b7 88 01 00 00 	lea    0x188(%rdi),%rsi
    3eb2:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3eb6:	e8 25 e6 ff ff       	call   24e0 <pthread_create@plt>
    thread_data[x].type = IO;
    3ebb:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3ec0:	31 c9                	xor    %ecx,%ecx
    3ec2:	48 8d 35 f8 56 00 00 	lea    0x56f8(%rip),%rsi        # 95c1 <_IO_stdin_used+0x5c1>
    3ec9:	41 b8 01 00 00 00    	mov    $0x1,%r8d
    3ecf:	ba 08 00 00 00       	mov    $0x8,%edx
    3ed4:	bf 01 00 00 00       	mov    $0x1,%edi
    3ed9:	48 89 b0 18 0a 00 00 	mov    %rsi,0xa18(%rax)
    3ee0:	4c 8d 1d a9 56 00 00 	lea    0x56a9(%rip),%r11        # 9590 <_IO_stdin_used+0x590>
    thread_data[x].iomailboxes = iomailboxes; 
    3ee7:	4c 89 b0 08 0a 00 00 	mov    %r14,0xa08(%rax)
    3eee:	4c 89 de             	mov    %r11,%rsi
    thread_data[x].type = IO;
    3ef1:	c7 80 0c 09 00 00 02 00 00 00 	movl   $0x2,0x90c(%rax)
    thread_data[x].task_count = 0;
    3efb:	4c 89 a0 40 09 00 00 	mov    %r12,0x940(%rax)
    thread_data[x].io_mode = myring;
    3f02:	c7 80 04 0a 00 00 00 00 00 00 	movl   $0x0,0xa04(%rax)
    thread_data[x].other_io = otherring;
    3f0c:	48 c7 80 10 0a 00 00 01 00 00 00 	movq   $0x1,0xa10(%rax)
    3f17:	31 c0                	xor    %eax,%eax
    3f19:	e8 a2 e5 ff ff       	call   24c0 <__printf_chk@plt>
    thread_data[x].ring = rings[myring]; 
    3f1e:	4c 8b 74 24 38       	mov    0x38(%rsp),%r14
    3f23:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    int myeventfd = eventfd(counter++, EFD_NONBLOCK);
    3f28:	be 00 08 00 00       	mov    $0x800,%esi
    3f2d:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].ring = rings[myring]; 
    3f32:	49 89 86 60 09 00 00 	mov    %rax,0x960(%r14)
    int myeventfd = eventfd(counter++, EFD_NONBLOCK);
    3f39:	e8 f2 e5 ff ff       	call   2530 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3f3e:	be 08 00 00 00       	mov    $0x8,%esi
    3f43:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = myeventfd; 
    3f48:	41 89 86 68 09 00 00 	mov    %eax,0x968(%r14)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3f4f:	e8 bc e4 ff ff       	call   2410 <calloc@plt>
    3f54:	ba 08 00 00 00       	mov    $0x8,%edx
    3f59:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].thread_count = thread_count;
    3f5e:	41 c7 86 28 09 00 00 02 00 00 00 	movl   $0x2,0x928(%r14)
      my_thread_data[n] = &thread_data[n]; 
    3f69:	4c 89 30             	mov    %r14,(%rax)
    3f6c:	4c 8d 15 37 56 00 00 	lea    0x5637(%rip),%r10        # 95aa <_IO_stdin_used+0x5aa>
    thread_data[x].threads = my_thread_data;
    3f73:	49 89 86 18 09 00 00 	mov    %rax,0x918(%r14)
    3f7a:	4c 89 d6             	mov    %r10,%rsi
      my_thread_data[n] = &thread_data[n]; 
    3f7d:	48 89 68 08          	mov    %rbp,0x8(%rax)
    3f81:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3f83:	41 c7 86 04 09 00 00 08 00 00 00 	movl   $0x8,0x904(%r14)
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3f8e:	41 be 09 00 00 00    	mov    $0x9,%r14d
    3f94:	e8 27 e5 ff ff       	call   24c0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3f99:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    3f9e:	48 8b 4c 24 18       	mov    0x18(%rsp),%rcx
    3fa3:	4c 89 ea             	mov    %r13,%rdx
    3fa6:	48 8d b7 c0 01 00 00 	lea    0x1c0(%rdi),%rsi
    3fad:	48 8d 7b 40          	lea    0x40(%rbx),%rdi
    3fb1:	e8 2a e5 ff ff       	call   24e0 <pthread_create@plt>
    3fb6:	ba 09 00 00 00       	mov    $0x9,%edx
    3fbb:	48 8d 35 0b 56 00 00 	lea    0x560b(%rip),%rsi        # 95cd <_IO_stdin_used+0x5cd>
    3fc2:	31 c0                	xor    %eax,%eax
    3fc4:	bf 01 00 00 00       	mov    $0x1,%edi
    3fc9:	e8 f2 e4 ff ff       	call   24c0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3fce:	48 8d 43 48          	lea    0x48(%rbx),%rax
    3fd2:	4c 8b 6c 24 40       	mov    0x40(%rsp),%r13
    3fd7:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    3fdc:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3fe1:	48 05 f8 01 00 00    	add    $0x1f8,%rax
    3fe7:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3fec:	44 89 f2             	mov    %r14d,%edx
    3fef:	48 8d 35 ed 55 00 00 	lea    0x55ed(%rip),%rsi        # 95e3 <_IO_stdin_used+0x5e3>
    3ff6:	bf 01 00 00 00       	mov    $0x1,%edi
    3ffb:	31 c0                	xor    %eax,%eax
    3ffd:	e8 be e4 ff ff       	call   24c0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    4002:	4d 89 65 40          	mov    %r12,0x40(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    4006:	be 08 00 00 00       	mov    $0x8,%esi
    400b:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].type = EXTERNAL;
    4010:	41 c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    4018:	e8 f3 e3 ff ff       	call   2410 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    401d:	48 8b bc 24 d0 00 00 00 	mov    0xd0(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    4025:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    402a:	41 c7 85 c4 00 00 00 01 00 00 00 	movl   $0x1,0xc4(%r13)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    4035:	49 89 45 50          	mov    %rax,0x50(%r13)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    4039:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    403c:	bf 02 00 00 00       	mov    $0x2,%edi
    4041:	e8 ca e3 ff ff       	call   2410 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    4046:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    404b:	45 89 75 04          	mov    %r14d,0x4(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    404f:	4c 89 e9             	mov    %r13,%rcx
    thread_data[x].threads = my_thread_data;
    4052:	49 89 45 18          	mov    %rax,0x18(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    4056:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    405b:	48 8d 15 5e 0a 00 00 	lea    0xa5e(%rip),%rdx        # 4ac0 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    4062:	49 81 c5 20 01 00 00 	add    $0x120,%r13
      my_thread_data[n] = &thread_data[n]; 
    4069:	48 89 30             	mov    %rsi,(%rax)
    thread_data[x].thread_count = thread_count;
    406c:	48 8b 35 5d 5f 00 00 	mov    0x5f5d(%rip),%rsi        # 9fd0 <_IO_stdin_used+0xfd0>
      my_thread_data[n] = &thread_data[n]; 
    4073:	48 89 68 08          	mov    %rbp,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    4077:	49 89 b5 08 ff ff ff 	mov    %rsi,-0xf8(%r13)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    407e:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    4083:	e8 58 e4 ff ff       	call   24e0 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    4088:	48 83 44 24 10 08    	addq   $0x8,0x10(%rsp)
    408e:	48 83 84 24 d0 00 00 00 10 	addq   $0x10,0xd0(%rsp)
    4097:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    409d:	41 83 fe 09          	cmp    $0x9,%r14d
    40a1:	75 17                	jne    40ba <main+0x19fa>
    40a3:	41 be 0a 00 00 00    	mov    $0xa,%r14d
    40a9:	e9 3e ff ff ff       	jmp    3fec <main+0x192c>
            CPU_SET(j, sendercpu);
    40ae:	48 81 0b ff 0f 00 00 	orq    $0xfff,(%rbx)
          for (int j = 0 ; j < cores ; j++) {
    40b5:	e9 b0 ec ff ff       	jmp    2d6a <main+0x6aa>
    40ba:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    40bf:	48 8d 2d 3a 55 00 00 	lea    0x553a(%rip),%rbp        # 9600 <_IO_stdin_used+0x600>
    40c6:	4c 8d 68 04          	lea    0x4(%rax),%r13
    40ca:	4c 8d a0 64 0c 00 00 	lea    0xc64(%rax),%r12
    40d1:	41 8b 4d 04          	mov    0x4(%r13),%ecx
    40d5:	41 8b 55 00          	mov    0x0(%r13),%edx
    40d9:	48 89 ee             	mov    %rbp,%rsi
    40dc:	bf 01 00 00 00       	mov    $0x1,%edi
    40e1:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    40e3:	49 81 c5 20 01 00 00 	add    $0x120,%r13
    40ea:	e8 d1 e3 ff ff       	call   24c0 <__printf_chk@plt>
    40ef:	4d 39 ec             	cmp    %r13,%r12
    40f2:	75 dd                	jne    40d1 <main+0x1a11>
    40f4:	48 8d 3d 18 55 00 00 	lea    0x5518(%rip),%rdi        # 9613 <_IO_stdin_used+0x613>
    40fb:	45 31 ed             	xor    %r13d,%r13d
    40fe:	4c 8d a4 24 10 01 00 00 	lea    0x110(%rsp),%r12
    4106:	e8 35 e2 ff ff       	call   2340 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    410b:	48 8d 2d 1f 55 00 00 	lea    0x551f(%rip),%rbp        # 9631 <_IO_stdin_used+0x631>
    void * result; 
    pthread_join(thread[x], &result);
    4112:	4a 8b 3c eb          	mov    (%rbx,%r13,8),%rdi
    4116:	4c 89 e6             	mov    %r12,%rsi
    4119:	e8 52 e4 ff ff       	call   2570 <pthread_join@plt>
    411e:	44 89 ea             	mov    %r13d,%edx
    4121:	48 89 ee             	mov    %rbp,%rsi
    4124:	bf 01 00 00 00       	mov    $0x1,%edi
    4129:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    412b:	49 83 c5 01          	add    $0x1,%r13
    412f:	e8 8c e3 ff ff       	call   24c0 <__printf_chk@plt>
    4134:	49 83 fd 0b          	cmp    $0xb,%r13
    4138:	75 d8                	jne    4112 <main+0x1a52>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    413a:	be 08 00 00 00       	mov    $0x8,%esi
    413f:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    4144:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    4146:	e8 c5 e2 ff ff       	call   2410 <calloc@plt>
    414b:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    4150:	48 89 c5             	mov    %rax,%rbp
    4153:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    4155:	49 89 d1             	mov    %rdx,%r9
    4158:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    415b:	45 8b 51 40          	mov    0x40(%r9),%r10d
    415f:	45 85 d2             	test   %r10d,%r10d
    4162:	0f 8e a8 00 00 00    	jle    4210 <main+0x1b50>
    4168:	49 8b 79 38          	mov    0x38(%r9),%rdi
    416c:	4d 63 c2             	movslq %r10d,%r8
    416f:	48 63 cb             	movslq %ebx,%rcx
    4172:	49 c1 e0 09          	shl    $0x9,%r8
    4176:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    417b:	49 01 f8             	add    %rdi,%r8
    417e:	66 90                	xchg   %ax,%ax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    4180:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    4187:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    418e:	48 83 c6 60          	add    $0x60,%rsi
    4192:	f3 0f 7e a1 00 01 00 00 	movq   0x100(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    419a:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    419e:	f3 0f 7e 99 00 02 00 00 	movq   0x200(%rcx),%xmm3
    41a6:	f3 0f 7e 91 00 03 00 00 	movq   0x300(%rcx),%xmm2
    41ae:	f3 0f 7e 89 00 04 00 00 	movq   0x400(%rcx),%xmm1
    41b6:	0f 16 a1 80 01 00 00 	movhps 0x180(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    41bd:	f3 0f 7e 81 00 05 00 00 	movq   0x500(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    41c5:	0f 16 a9 80 00 00 00 	movhps 0x80(%rcx),%xmm5
    41cc:	0f 16 99 80 02 00 00 	movhps 0x280(%rcx),%xmm3
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    41d3:	0f 16 91 80 03 00 00 	movhps 0x380(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    41da:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    41de:	0f 16 89 80 04 00 00 	movhps 0x480(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    41e5:	0f 16 81 80 05 00 00 	movhps 0x580(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    41ec:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    41f0:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    41f4:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    41f8:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    41fc:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    4200:	4c 39 c7             	cmp    %r8,%rdi
    4203:	0f 85 77 ff ff ff    	jne    4180 <main+0x1ac0>
    4209:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    420d:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    4210:	49 81 c1 20 01 00 00 	add    $0x120,%r9
    4217:	45 85 db             	test   %r11d,%r11d
    421a:	75 08                	jne    4224 <main+0x1b64>
    421c:	45 89 fb             	mov    %r15d,%r11d
    421f:	e9 37 ff ff ff       	jmp    415b <main+0x1a9b>
  for (int k = 0 ; k < group_count ; k++) {
    4224:	83 c0 02             	add    $0x2,%eax
    4227:	48 81 c2 40 02 00 00 	add    $0x240,%rdx
    422e:	83 f8 06             	cmp    $0x6,%eax
    4231:	0f 85 1e ff ff ff    	jne    4155 <main+0x1a95>
    4237:	48 8d 3d 07 54 00 00 	lea    0x5407(%rip),%rdi        # 9645 <_IO_stdin_used+0x645>
    423e:	e8 fd e0 ff ff       	call   2340 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    4243:	48 8d 35 a5 52 00 00 	lea    0x52a5(%rip),%rsi        # 94ef <_IO_stdin_used+0x4ef>
    424a:	48 8d 3d 0c 54 00 00 	lea    0x540c(%rip),%rdi        # 965d <_IO_stdin_used+0x65d>
    4251:	e8 aa e2 ff ff       	call   2500 <fopen@plt>
    4256:	49 89 c6             	mov    %rax,%r14
  for (int x = 0 ; x < datas2_size; x++) {
    4259:	85 db                	test   %ebx,%ebx
    425b:	7e 73                	jle    42d0 <main+0x1c10>
    425d:	48 63 db             	movslq %ebx,%rbx
    4260:	49 89 ef             	mov    %rbp,%r15
    4263:	4c 8d 2d 64 52 00 00 	lea    0x5264(%rip),%r13        # 94ce <_IO_stdin_used+0x4ce>
    426a:	48 8d 6c dd 00       	lea    0x0(%rbp,%rbx,8),%rbp
    426f:	4c 8d 25 9c 52 00 00 	lea    0x529c(%rip),%r12        # 9512 <_IO_stdin_used+0x512>
    char * c = calloc(250, sizeof(char));
    4276:	be 01 00 00 00       	mov    $0x1,%esi
    427b:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    4280:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    4284:	e8 87 e1 ff ff       	call   2410 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4289:	4c 89 e9             	mov    %r13,%rcx
    428c:	ba fa 00 00 00       	mov    $0xfa,%edx
    4291:	be 01 00 00 00       	mov    $0x1,%esi
    4296:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    4299:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    429d:	48 89 df             	mov    %rbx,%rdi
    42a0:	44 8b 80 18 04 00 00 	mov    0x418(%rax),%r8d
    42a7:	31 c0                	xor    %eax,%eax
    42a9:	e8 12 e3 ff ff       	call   25c0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    42ae:	48 89 da             	mov    %rbx,%rdx
    42b1:	4c 89 e6             	mov    %r12,%rsi
    42b4:	bf 01 00 00 00       	mov    $0x1,%edi
    42b9:	31 c0                	xor    %eax,%eax
    42bb:	e8 00 e2 ff ff       	call   24c0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    42c0:	4c 89 f6             	mov    %r14,%rsi
    42c3:	48 89 df             	mov    %rbx,%rdi
    42c6:	e8 05 e1 ff ff       	call   23d0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    42cb:	49 39 ef             	cmp    %rbp,%r15
    42ce:	75 a6                	jne    4276 <main+0x1bb6>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    42d0:	4c 89 f7             	mov    %r14,%rdi
    42d3:	41 bc ff ff ff ff    	mov    $0xffffffff,%r12d
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    42d9:	31 db                	xor    %ebx,%ebx
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    42db:	48 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%rbp
  fclose(m2);
    42e5:	e8 86 e0 ff ff       	call   2370 <fclose@plt>
  long sents = 0;
    42ea:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long sends = 0;
    42f3:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long ingests = 0;
    42fc:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long total = 0;
    4305:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  int datas2_size = 0; 
    430e:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
    4316:	45 8d 44 24 02       	lea    0x2(%r12),%r8d
    431b:	4c 8b b4 24 98 00 00 00 	mov    0x98(%rsp),%r14
    4323:	45 89 e5             	mov    %r12d,%r13d
    4326:	44 89 44 24 48       	mov    %r8d,0x48(%rsp)
    432b:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    4330:	4d 89 f4             	mov    %r14,%r12
      int x = (k * threads_per_group) + d;
    4333:	44 89 e8             	mov    %r13d,%eax
    4336:	41 83 c5 01          	add    $0x1,%r13d
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    433a:	bf 0a 00 00 00       	mov    $0xa,%edi
        other = abs(x - 1) % total_threads;
    433f:	41 f6 c5 01          	test   $0x1,%r13b
    4343:	8d 50 02             	lea    0x2(%rax),%edx
    4346:	0f 44 c2             	cmove  %edx,%eax
    4349:	41 89 c6             	mov    %eax,%r14d
    434c:	e8 cf df ff ff       	call   2320 <putchar@plt>
    4351:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    4356:	bf 01 00 00 00       	mov    $0x1,%edi
    435b:	48 8d 35 04 53 00 00 	lea    0x5304(%rip),%rsi        # 9666 <_IO_stdin_used+0x666>
    4362:	48 8b 10             	mov    (%rax),%rdx
    4365:	31 c0                	xor    %eax,%eax
    4367:	e8 54 e1 ff ff       	call   24c0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    436c:	41 8b 54 24 40       	mov    0x40(%r12),%edx
    4371:	85 d2                	test   %edx,%edx
    4373:	0f 8e 53 05 00 00    	jle    48cc <main+0x220c>
    4379:	48 63 ca             	movslq %edx,%rcx
    437c:	49 8b 44 24 38       	mov    0x38(%r12),%rax
      long v = 0;
    4381:	31 d2                	xor    %edx,%edx
    4383:	48 c1 e1 09          	shl    $0x9,%rcx
    4387:	48 01 c1             	add    %rax,%rcx
    438a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    4390:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    4397:	48 05 00 02 00 00    	add    $0x200,%rax
    439d:	48 39 c8             	cmp    %rcx,%rax
    43a0:	75 ee                	jne    4390 <main+0x1cd0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    43a2:	49 63 c6             	movslq %r14d,%rax
    43a5:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    43aa:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    43ae:	48 c1 e0 05          	shl    $0x5,%rax
    43b2:	48 01 f8             	add    %rdi,%rax
    43b5:	48 63 48 40          	movslq 0x40(%rax),%rcx
    43b9:	85 c9                	test   %ecx,%ecx
    43bb:	7e 25                	jle    43e2 <main+0x1d22>
    43bd:	48 8b 40 38          	mov    0x38(%rax),%rax
    43c1:	48 c1 e1 09          	shl    $0x9,%rcx
    43c5:	48 01 c1             	add    %rax,%rcx
    43c8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    43d0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    43d7:	48 05 00 02 00 00    	add    $0x200,%rax
    43dd:	48 39 c1             	cmp    %rax,%rcx
    43e0:	75 ee                	jne    43d0 <main+0x1d10>
    43e2:	48 8d 35 92 52 00 00 	lea    0x5292(%rip),%rsi        # 967b <_IO_stdin_used+0x67b>
    43e9:	bf 01 00 00 00       	mov    $0x1,%edi
    43ee:	31 c0                	xor    %eax,%eax
    43f0:	e8 cb e0 ff ff       	call   24c0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    43f5:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    43fa:	bf 01 00 00 00       	mov    $0x1,%edi
    43ff:	48 8d 35 fa 56 00 00 	lea    0x56fa(%rip),%rsi        # 9b00 <_IO_stdin_used+0xb00>
    4406:	48 8b 08             	mov    (%rax),%rcx
    4409:	48 b8 0b d7 a3 70 3d 0a d7 a3 	movabs $0xa3d70a3d70a3d70b,%rax
    4413:	48 f7 e9             	imul   %rcx
    4416:	31 c0                	xor    %eax,%eax
    4418:	48 01 ca             	add    %rcx,%rdx
    441b:	48 c1 f9 3f          	sar    $0x3f,%rcx
    441f:	48 c1 fa 04          	sar    $0x4,%rdx
    4423:	48 29 ca             	sub    %rcx,%rdx
    4426:	e8 95 e0 ff ff       	call   24c0 <__printf_chk@plt>
    442b:	bf 0a 00 00 00       	mov    $0xa,%edi
    4430:	e8 eb de ff ff       	call   2320 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    4435:	45 8b 74 24 40       	mov    0x40(%r12),%r14d
    443a:	45 85 f6             	test   %r14d,%r14d
    443d:	0f 8e 43 01 00 00    	jle    4586 <main+0x1ec6>
    4443:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    4448:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    444d:	44 89 6c 24 08       	mov    %r13d,0x8(%rsp)
    4452:	31 d2                	xor    %edx,%edx
    4454:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    4459:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    445e:	4d 89 e5             	mov    %r12,%r13
    4461:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        total += thread_data[x].tasks[n].n;
    4468:	49 8b 45 38          	mov    0x38(%r13),%rax
    446c:	49 89 d1             	mov    %rdx,%r9
        sends += thread_data[x].tasks[n].sends;
    446f:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
    4474:	41 89 d4             	mov    %edx,%r12d
        total += thread_data[x].tasks[n].n;
    4477:	49 c1 e1 09          	shl    $0x9,%r9
        sends += thread_data[x].tasks[n].sends;
    447b:	45 31 f6             	xor    %r14d,%r14d
        total += thread_data[x].tasks[n].n;
    447e:	4c 01 c8             	add    %r9,%rax
        sends += thread_data[x].tasks[n].sends;
    4481:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
        total += thread_data[x].tasks[n].n;
    4486:	48 03 b8 08 01 00 00 	add    0x108(%rax),%rdi
        ingests += thread_data[x].tasks[n].ingest_count;
    448d:	48 03 b0 68 01 00 00 	add    0x168(%rax),%rsi
        sends += thread_data[x].tasks[n].sends;
    4494:	4c 03 90 80 01 00 00 	add    0x180(%rax),%r10
    449b:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    44a0:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    44a5:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    44aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    44b0:	8b 54 24 08          	mov    0x8(%rsp),%edx
    44b4:	45 89 f0             	mov    %r14d,%r8d
    44b7:	44 89 e1             	mov    %r12d,%ecx
    44ba:	bf 01 00 00 00       	mov    $0x1,%edi
    44bf:	48 8d 35 c2 51 00 00 	lea    0x51c2(%rip),%rsi        # 9688 <_IO_stdin_used+0x688>
    44c6:	31 c0                	xor    %eax,%eax
    44c8:	e8 f3 df ff ff       	call   24c0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    44cd:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    44d2:	4c 89 f0             	mov    %r14,%rax
    44d5:	45 89 f0             	mov    %r14d,%r8d
    44d8:	49 8b 55 38          	mov    0x38(%r13),%rdx
    44dc:	48 c1 e0 08          	shl    $0x8,%rax
    44e0:	48 83 ec 08          	sub    $0x8,%rsp
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    44e4:	49 83 c6 01          	add    $0x1,%r14
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    44e8:	48 03 84 3a 70 01 00 00 	add    0x170(%rdx,%rdi,1),%rax
    44f0:	48 8b 38             	mov    (%rax),%rdi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    44f3:	48 8b b0 80 00 00 00 	mov    0x80(%rax),%rsi
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    44fa:	48 8b 87 00 04 00 00 	mov    0x400(%rdi),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4501:	48 8b 96 80 03 00 00 	mov    0x380(%rsi),%rdx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4508:	48 8b b6 00 04 00 00 	mov    0x400(%rsi),%rsi
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    450f:	48 8b 8f 80 03 00 00 	mov    0x380(%rdi),%rcx
    4516:	bf 01 00 00 00       	mov    $0x1,%edi
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    451b:	48 01 c3             	add    %rax,%rbx
          long temprec = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received + ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    451e:	48 01 f0             	add    %rsi,%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    4521:	49 01 cf             	add    %rcx,%r15
    4524:	4c 8d 0c 11          	lea    (%rcx,%rdx,1),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4528:	48 01 f3             	add    %rsi,%rbx
    452b:	50                   	push   %rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    452c:	49 01 d7             	add    %rdx,%r15
    452f:	8b 54 24 18          	mov    0x18(%rsp),%edx
    4533:	44 89 e1             	mov    %r12d,%ecx
    4536:	48 8d 35 e3 55 00 00 	lea    0x55e3(%rip),%rsi        # 9b20 <_IO_stdin_used+0xb20>
    453d:	31 c0                	xor    %eax,%eax
    453f:	e8 7c df ff ff       	call   24c0 <__printf_chk@plt>
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    4544:	41 5a                	pop    %r10
    4546:	41 5b                	pop    %r11
    4548:	49 83 fe 06          	cmp    $0x6,%r14
    454c:	0f 85 5e ff ff ff    	jne    44b0 <main+0x1df0>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    4552:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    4557:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    455c:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    4561:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4566:	48 83 c2 01          	add    $0x1,%rdx
    456a:	41 39 55 40          	cmp    %edx,0x40(%r13)
    456e:	0f 8f f4 fe ff ff    	jg     4468 <main+0x1da8>
    4574:	48 89 7c 24 30       	mov    %rdi,0x30(%rsp)
    4579:	4d 89 ec             	mov    %r13,%r12
    457c:	44 8b 6c 24 08       	mov    0x8(%rsp),%r13d
    4581:	4c 89 7c 24 28       	mov    %r15,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    4586:	45 31 ff             	xor    %r15d,%r15d
    4589:	4c 8d 35 b0 55 00 00 	lea    0x55b0(%rip),%r14        # 9b40 <_IO_stdin_used+0xb40>
    4590:	49 83 bc 24 a8 00 00 00 00 	cmpq   $0x0,0xa8(%r12)
    4599:	7e 5f                	jle    45fa <main+0x1f3a>
    459b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    45a0:	49 8b 84 24 98 00 00 00 	mov    0x98(%r12),%rax
    45a8:	4b 8d 14 bf          	lea    (%r15,%r15,4),%rdx
    45ac:	48 83 ec 08          	sub    $0x8,%rsp
    45b0:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    45b5:	49 83 c7 01          	add    $0x1,%r15
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    45b9:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    45bd:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    45c1:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    45c5:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    45c8:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    45cc:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    45cf:	48 f7 e5             	mul    %rbp
    45d2:	8b 49 20             	mov    0x20(%rcx),%ecx
    45d5:	56                   	push   %rsi
    45d6:	31 c0                	xor    %eax,%eax
    45d8:	4c 89 f6             	mov    %r14,%rsi
    45db:	48 c1 ea 12          	shr    $0x12,%rdx
    45df:	49 89 d1             	mov    %rdx,%r9
    45e2:	ba 02 00 00 00       	mov    $0x2,%edx
    45e7:	e8 d4 de ff ff       	call   24c0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    45ec:	41 58                	pop    %r8
    45ee:	41 59                	pop    %r9
    45f0:	4d 39 bc 24 a8 00 00 00 	cmp    %r15,0xa8(%r12)
    45f8:	7f a6                	jg     45a0 <main+0x1ee0>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    45fa:	41 8b 94 24 c4 00 00 00 	mov    0xc4(%r12),%edx
    4602:	85 d2                	test   %edx,%edx
    4604:	0f 8e 09 01 00 00    	jle    4713 <main+0x2053>
    460a:	48 89 5c 24 50       	mov    %rbx,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    460f:	49 8b 7c 24 50       	mov    0x50(%r12),%rdi
    4614:	45 31 ff             	xor    %r15d,%r15d
    4617:	44 89 6c 24 58       	mov    %r13d,0x58(%rsp)
    461c:	0f 1f 40 00          	nopl   0x0(%rax)
    4620:	4a 8b 04 ff          	mov    (%rdi,%r15,8),%rax
    4624:	44 89 fb             	mov    %r15d,%ebx
    4627:	4e 8d 2c fd 00 00 00 00 	lea    0x0(,%r15,8),%r13
    462f:	8b 30                	mov    (%rax),%esi
    4631:	85 f6                	test   %esi,%esi
    4633:	0f 8e c3 00 00 00    	jle    46fc <main+0x203c>
    4639:	4c 89 7c 24 10       	mov    %r15,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    463e:	31 d2                	xor    %edx,%edx
    4640:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4644:	49 89 f8             	mov    %rdi,%r8
    4647:	48 89 d7             	mov    %rdx,%rdi
    464a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4650:	49 89 fe             	mov    %rdi,%r14
    4653:	45 31 ff             	xor    %r15d,%r15d
    4656:	49 c1 e6 08          	shl    $0x8,%r14
    465a:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    465e:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    4664:	85 d2                	test   %edx,%edx
    4666:	7e 78                	jle    46e0 <main+0x2020>
    4668:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    466d:	0f 1f 00             	nopl   (%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4670:	4c 89 f9             	mov    %r15,%rcx
    4673:	48 83 ec 08          	sub    $0x8,%rsp
    4677:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    467c:	49 83 c7 01          	add    $0x1,%r15
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4680:	48 c1 e1 05          	shl    $0x5,%rcx
    4684:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    468b:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    468f:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    4693:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4696:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    469a:	4c 2b 01             	sub    (%rcx),%r8
    469d:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    469e:	48 f7 e5             	mul    %rbp
    46a1:	89 d9                	mov    %ebx,%ecx
    46a3:	48 8d 35 e6 54 00 00 	lea    0x54e6(%rip),%rsi        # 9b90 <_IO_stdin_used+0xb90>
    46aa:	31 c0                	xor    %eax,%eax
    46ac:	48 c1 ea 12          	shr    $0x12,%rdx
    46b0:	49 89 d1             	mov    %rdx,%r9
    46b3:	ba 02 00 00 00       	mov    $0x2,%edx
    46b8:	e8 03 de ff ff       	call   24c0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    46bd:	4d 8b 44 24 50       	mov    0x50(%r12),%r8
    46c2:	5e                   	pop    %rsi
    46c3:	5f                   	pop    %rdi
    46c4:	4b 8b 14 28          	mov    (%r8,%r13,1),%rdx
    46c8:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    46cc:	4a 8d 04 31          	lea    (%rcx,%r14,1),%rax
    46d0:	44 39 b8 94 00 00 00 	cmp    %r15d,0x94(%rax)
    46d7:	7f 97                	jg     4670 <main+0x1fb0>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    46d9:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    46de:	8b 32                	mov    (%rdx),%esi
    46e0:	48 83 c7 01          	add    $0x1,%rdi
    46e4:	39 fe                	cmp    %edi,%esi
    46e6:	0f 8f 64 ff ff ff    	jg     4650 <main+0x1f90>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    46ec:	4c 8b 7c 24 10       	mov    0x10(%rsp),%r15
    46f1:	41 8b 94 24 c4 00 00 00 	mov    0xc4(%r12),%edx
    46f9:	4c 89 c7             	mov    %r8,%rdi
    46fc:	49 83 c7 01          	add    $0x1,%r15
    4700:	44 39 fa             	cmp    %r15d,%edx
    4703:	0f 8f 17 ff ff ff    	jg     4620 <main+0x1f60>
    4709:	48 8b 5c 24 50       	mov    0x50(%rsp),%rbx
    470e:	44 8b 6c 24 58       	mov    0x58(%rsp),%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    4713:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    4719:	49 81 c4 20 01 00 00 	add    $0x120,%r12
    4720:	44 39 6c 24 48       	cmp    %r13d,0x48(%rsp)
    4725:	0f 85 08 fc ff ff    	jne    4333 <main+0x1c73>
  for (int k = 0 ; k < group_count ; k++) {
    472b:	48 83 84 24 d8 00 00 00 30 	addq   $0x30,0xd8(%rsp)
    4734:	44 8b 44 24 48       	mov    0x48(%rsp),%r8d
    4739:	48 81 84 24 98 00 00 00 40 02 00 00 	addq   $0x240,0x98(%rsp)
    4745:	41 83 f8 05          	cmp    $0x5,%r8d
    4749:	74 08                	je     4753 <main+0x2093>
    474b:	45 89 c4             	mov    %r8d,%r12d
    474e:	e9 bb fb ff ff       	jmp    430e <main+0x1c4e>
    4753:	4c 8b 74 24 30       	mov    0x30(%rsp),%r14
    4758:	bf 01 00 00 00       	mov    $0x1,%edi
    475d:	31 c0                	xor    %eax,%eax
    475f:	49 89 df             	mov    %rbx,%r15
    4762:	48 8d 35 2f 4f 00 00 	lea    0x4f2f(%rip),%rsi        # 9698 <_IO_stdin_used+0x698>
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    4769:	48 bb 0b d7 a3 70 3d 0a d7 a3 	movabs $0xa3d70a3d70a3d70b,%rbx
    4773:	4c 89 f2             	mov    %r14,%rdx
    4776:	e8 45 dd ff ff       	call   24c0 <__printf_chk@plt>
    477b:	bf 0a 00 00 00       	mov    $0xa,%edi
    4780:	e8 9b db ff ff       	call   2320 <putchar@plt>
    4785:	48 8b bc 24 b0 00 00 00 	mov    0xb0(%rsp),%rdi
    478d:	48 8d 35 54 54 00 00 	lea    0x5454(%rip),%rsi        # 9be8 <_IO_stdin_used+0xbe8>
    4794:	31 c0                	xor    %eax,%eax
    4796:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    479a:	bf 01 00 00 00       	mov    $0x1,%edi
    479f:	e8 1c dd ff ff       	call   24c0 <__printf_chk@plt>
    47a4:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    47a9:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    47ae:	48 8d 35 5b 54 00 00 	lea    0x545b(%rip),%rsi        # 9c10 <_IO_stdin_used+0xc10>
    47b5:	48 f7 eb             	imul   %rbx
    47b8:	31 c0                	xor    %eax,%eax
    47ba:	48 01 fa             	add    %rdi,%rdx
    47bd:	48 c1 ff 3f          	sar    $0x3f,%rdi
    47c1:	48 c1 fa 04          	sar    $0x4,%rdx
    47c5:	48 29 fa             	sub    %rdi,%rdx
    47c8:	bf 01 00 00 00       	mov    $0x1,%edi
    47cd:	e8 ee dc ff ff       	call   24c0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    47d2:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    47d7:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    47dc:	48 8d 35 5d 54 00 00 	lea    0x545d(%rip),%rsi        # 9c40 <_IO_stdin_used+0xc40>
    47e3:	48 f7 eb             	imul   %rbx
    47e6:	31 c0                	xor    %eax,%eax
    47e8:	48 01 fa             	add    %rdi,%rdx
    47eb:	48 c1 ff 3f          	sar    $0x3f,%rdi
    47ef:	48 c1 fa 04          	sar    $0x4,%rdx
    47f3:	48 29 fa             	sub    %rdi,%rdx
    47f6:	bf 01 00 00 00       	mov    $0x1,%edi
    47fb:	e8 c0 dc ff ff       	call   24c0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    4800:	4c 89 f0             	mov    %r14,%rax
    4803:	bf 01 00 00 00       	mov    $0x1,%edi
    4808:	48 8d 35 61 54 00 00 	lea    0x5461(%rip),%rsi        # 9c70 <_IO_stdin_used+0xc70>
    480f:	48 f7 eb             	imul   %rbx
    4812:	4c 89 f0             	mov    %r14,%rax
    4815:	48 c1 f8 3f          	sar    $0x3f,%rax
    4819:	4c 01 f2             	add    %r14,%rdx
    481c:	48 c1 fa 04          	sar    $0x4,%rdx
    4820:	48 29 c2             	sub    %rax,%rdx
    4823:	31 c0                	xor    %eax,%eax
    4825:	e8 96 dc ff ff       	call   24c0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    482a:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    482f:	bf 01 00 00 00       	mov    $0x1,%edi
    4834:	48 8d 35 71 4e 00 00 	lea    0x4e71(%rip),%rsi        # 96ac <_IO_stdin_used+0x6ac>
    483b:	48 f7 eb             	imul   %rbx
    483e:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4843:	48 8d 2c 02          	lea    (%rdx,%rax,1),%rbp
    4847:	48 c1 f8 3f          	sar    $0x3f,%rax
    484b:	48 c1 fd 04          	sar    $0x4,%rbp
    484f:	48 29 c5             	sub    %rax,%rbp
    4852:	31 c0                	xor    %eax,%eax
    4854:	48 89 ea             	mov    %rbp,%rdx
    4857:	e8 64 dc ff ff       	call   24c0 <__printf_chk@plt>
  printf("Total sents per second %ld\n", sentdur);
  long recdur = received / DURATION;
    485c:	4c 89 f8             	mov    %r15,%rax
    485f:	bf 01 00 00 00       	mov    $0x1,%edi
    4864:	48 8d 35 25 54 00 00 	lea    0x5425(%rip),%rsi        # 9c90 <_IO_stdin_used+0xc90>
    486b:	48 f7 eb             	imul   %rbx
    486e:	4c 89 f8             	mov    %r15,%rax
    4871:	48 c1 f8 3f          	sar    $0x3f,%rax
    4875:	48 89 d3             	mov    %rdx,%rbx
    4878:	4c 01 fb             	add    %r15,%rbx
    487b:	48 c1 fb 04          	sar    $0x4,%rbx
    487f:	48 29 c3             	sub    %rax,%rbx
    4882:	31 c0                	xor    %eax,%eax
    4884:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives per second %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    4887:	48 29 eb             	sub    %rbp,%rbx
    488a:	e8 31 dc ff ff       	call   24c0 <__printf_chk@plt>
    488f:	31 c0                	xor    %eax,%eax
    4891:	48 89 da             	mov    %rbx,%rdx
    4894:	bf 01 00 00 00       	mov    $0x1,%edi
    4899:	48 8d 35 28 4e 00 00 	lea    0x4e28(%rip),%rsi        # 96c8 <_IO_stdin_used+0x6c8>
    48a0:	e8 1b dc ff ff       	call   24c0 <__printf_chk@plt>
  return 0;

}
    48a5:	48 8b 84 24 28 01 00 00 	mov    0x128(%rsp),%rax
    48ad:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    48b6:	75 25                	jne    48dd <main+0x221d>
    48b8:	48 81 c4 38 01 00 00 	add    $0x138,%rsp
    48bf:	31 c0                	xor    %eax,%eax
    48c1:	5b                   	pop    %rbx
    48c2:	5d                   	pop    %rbp
    48c3:	41 5c                	pop    %r12
    48c5:	41 5d                	pop    %r13
    48c7:	41 5e                	pop    %r14
    48c9:	41 5f                	pop    %r15
    48cb:	c3                   	ret
      long v = 0;
    48cc:	31 d2                	xor    %edx,%edx
    48ce:	e9 cf fa ff ff       	jmp    43a2 <main+0x1ce2>
            exit(1);
    48d3:	bf 01 00 00 00       	mov    $0x1,%edi
    48d8:	e8 43 dc ff ff       	call   2520 <exit@plt>
}
    48dd:	e8 ae da ff ff       	call   2390 <__stack_chk_fail@plt>
    48e2:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    48ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000048f0 <_start>:
    48f0:	f3 0f 1e fa          	endbr64
    48f4:	31 ed                	xor    %ebp,%ebp
    48f6:	49 89 d1             	mov    %rdx,%r9
    48f9:	5e                   	pop    %rsi
    48fa:	48 89 e2             	mov    %rsp,%rdx
    48fd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4901:	50                   	push   %rax
    4902:	54                   	push   %rsp
    4903:	45 31 c0             	xor    %r8d,%r8d
    4906:	31 c9                	xor    %ecx,%ecx
    4908:	48 8d 3d b1 dd ff ff 	lea    -0x224f(%rip),%rdi        # 26c0 <main>
    490f:	ff 15 c3 76 00 00    	call   *0x76c3(%rip)        # bfd8 <__libc_start_main@GLIBC_2.34>
    4915:	f4                   	hlt
    4916:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004920 <deregister_tm_clones>:
    4920:	48 8d 3d f9 76 00 00 	lea    0x76f9(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4927:	48 8d 05 f2 76 00 00 	lea    0x76f2(%rip),%rax        # c020 <stderr@GLIBC_2.2.5>
    492e:	48 39 f8             	cmp    %rdi,%rax
    4931:	74 15                	je     4948 <deregister_tm_clones+0x28>
    4933:	48 8b 05 a6 76 00 00 	mov    0x76a6(%rip),%rax        # bfe0 <_ITM_deregisterTMCloneTable@Base>
    493a:	48 85 c0             	test   %rax,%rax
    493d:	74 09                	je     4948 <deregister_tm_clones+0x28>
    493f:	ff e0                	jmp    *%rax
    4941:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4948:	c3                   	ret
    4949:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004950 <register_tm_clones>:
    4950:	48 8d 3d c9 76 00 00 	lea    0x76c9(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    4957:	48 8d 35 c2 76 00 00 	lea    0x76c2(%rip),%rsi        # c020 <stderr@GLIBC_2.2.5>
    495e:	48 29 fe             	sub    %rdi,%rsi
    4961:	48 89 f0             	mov    %rsi,%rax
    4964:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4968:	48 c1 f8 03          	sar    $0x3,%rax
    496c:	48 01 c6             	add    %rax,%rsi
    496f:	48 d1 fe             	sar    %rsi
    4972:	74 14                	je     4988 <register_tm_clones+0x38>
    4974:	48 8b 05 75 76 00 00 	mov    0x7675(%rip),%rax        # bff0 <_ITM_registerTMCloneTable@Base>
    497b:	48 85 c0             	test   %rax,%rax
    497e:	74 08                	je     4988 <register_tm_clones+0x38>
    4980:	ff e0                	jmp    *%rax
    4982:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4988:	c3                   	ret
    4989:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004990 <__do_global_dtors_aux>:
    4990:	f3 0f 1e fa          	endbr64
    4994:	80 3d 8d 76 00 00 00 	cmpb   $0x0,0x768d(%rip)        # c028 <completed.0>
    499b:	75 2b                	jne    49c8 <__do_global_dtors_aux+0x38>
    499d:	55                   	push   %rbp
    499e:	48 83 3d 52 76 00 00 00 	cmpq   $0x0,0x7652(%rip)        # bff8 <__cxa_finalize@GLIBC_2.2.5>
    49a6:	48 89 e5             	mov    %rsp,%rbp
    49a9:	74 0c                	je     49b7 <__do_global_dtors_aux+0x27>
    49ab:	48 8b 3d 56 76 00 00 	mov    0x7656(%rip),%rdi        # c008 <__dso_handle>
    49b2:	e8 49 d9 ff ff       	call   2300 <__cxa_finalize@plt>
    49b7:	e8 64 ff ff ff       	call   4920 <deregister_tm_clones>
    49bc:	c6 05 65 76 00 00 01 	movb   $0x1,0x7665(%rip)        # c028 <completed.0>
    49c3:	5d                   	pop    %rbp
    49c4:	c3                   	ret
    49c5:	0f 1f 00             	nopl   (%rax)
    49c8:	c3                   	ret
    49c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000049d0 <frame_dummy>:
    49d0:	f3 0f 1e fa          	endbr64
    49d4:	e9 77 ff ff ff       	jmp    4950 <register_tm_clones>
    49d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000049e0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    49e0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    49e4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    49eb:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    49ef:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    49f7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    49fb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    49ff:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4a06:	48 85 c9             	test   %rcx,%rcx
    4a09:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4a10:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4a14:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4a18:	31 c0                	xor    %eax,%eax
    4a1a:	c3                   	ret
    4a1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004a20 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4a20:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4a24:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    4a2b:	4c 8b 87 28 01 00 00 	mov    0x128(%rdi),%r8
    for (int x = 0 ; x < data->task_count ; x++) {
    4a32:	85 c9                	test   %ecx,%ecx
    4a34:	7e 48                	jle    4a7e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4a36:	48 63 97 30 01 00 00 	movslq 0x130(%rdi),%rdx
    4a3d:	49 8b 40 18          	mov    0x18(%r8),%rax
    4a41:	48 c1 e1 09          	shl    $0x9,%rcx
      data->thread->tasks[x].available = 1; 
    4a45:	49 8b 70 38          	mov    0x38(%r8),%rsi
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4a49:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    4a4d:	48 8b 50 38          	mov    0x38(%rax),%rdx
      data->thread->tasks[x].available = 1; 
    4a51:	31 c0                	xor    %eax,%eax
    4a53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    4a58:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4a60:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4a68:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    4a73:	48 05 00 02 00 00    	add    $0x200,%rax
    4a79:	48 39 c1             	cmp    %rax,%rcx
    4a7c:	75 da                	jne    4a58 <barriered_reset+0x38>
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    4a7e:	49 8b 88 f8 00 00 00 	mov    0xf8(%r8),%rcx
    4a85:	8b 01                	mov    (%rcx),%eax
    4a87:	83 f8 ff             	cmp    $0xffffffff,%eax
    4a8a:	74 0e                	je     4a9a <barriered_reset+0x7a>
    4a8c:	41 8b b8 c8 00 00 00 	mov    0xc8(%r8),%edi
    4a93:	8d 57 ff             	lea    -0x1(%rdi),%edx
    4a96:	39 d0                	cmp    %edx,%eax
    4a98:	74 06                	je     4aa0 <barriered_reset+0x80>
}
    4a9a:	31 c0                	xor    %eax,%eax
    4a9c:	c3                   	ret
    4a9d:	0f 1f 00             	nopl   (%rax)
  if (data->thread->global->request_group_sync != -1 && data->thread->global->request_group_sync == data->thread->group_count - 1 && data->thread->thread_index == 1) {
    4aa0:	41 83 78 04 01       	cmpl   $0x1,0x4(%r8)
    4aa5:	75 f3                	jne    4a9a <barriered_reset+0x7a>
    data->thread->group_data->arrived++;
    4aa7:	49 8b 80 e0 00 00 00 	mov    0xe0(%r8),%rax
    4aae:	83 00 01             	addl   $0x1,(%rax)
    data->thread->global->request_group_sync = -1;
    4ab1:	c7 01 ff ff ff ff    	movl   $0xffffffff,(%rcx)
    4ab7:	eb e1                	jmp    4a9a <barriered_reset+0x7a>
    4ab9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004ac0 <external_thread>:
void * external_thread(void *arg) {
    4ac0:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    4ac4:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4ac8:	0f 85 f8 00 00 00    	jne    4bc6 <external_thread+0x106>
void * external_thread(void *arg) {
    4ace:	41 57                	push   %r15
    4ad0:	4c 8d 3d 2d 45 00 00 	lea    0x452d(%rip),%r15        # 9004 <_IO_stdin_used+0x4>
    4ad7:	41 56                	push   %r14
    4ad9:	49 89 fe             	mov    %rdi,%r14
    4adc:	41 55                	push   %r13
    4ade:	41 54                	push   %r12
    4ae0:	55                   	push   %rbp
    4ae1:	53                   	push   %rbx
    4ae2:	48 83 ec 08          	sub    $0x8,%rsp
    4ae6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    for (int b = 0; b < data->buffers_count; b++) {
    4af0:	41 8b 8e c4 00 00 00 	mov    0xc4(%r14),%ecx
    4af7:	85 c9                	test   %ecx,%ecx
    4af9:	7e 57                	jle    4b52 <external_thread+0x92>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4afb:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4aff:	45 31 ed             	xor    %r13d,%r13d
    4b02:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b08:	4e 8d 24 ed 00 00 00 00 	lea    0x0(,%r13,8),%r12
    4b10:	31 db                	xor    %ebx,%ebx
    4b12:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    4b16:	48 8b 06             	mov    (%rsi),%rax
    4b19:	8b 10                	mov    (%rax),%edx
    4b1b:	85 d2                	test   %edx,%edx
    4b1d:	7e 2a                	jle    4b49 <external_thread+0x89>
    4b1f:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    4b23:	48 89 dd             	mov    %rbx,%rbp
    4b26:	48 c1 e5 08          	shl    $0x8,%rbp
    4b2a:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4b2e:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    4b35:	45 85 c0             	test   %r8d,%r8d
    4b38:	74 36                	je     4b70 <external_thread+0xb0>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4b3a:	48 83 c3 01          	add    $0x1,%rbx
    4b3e:	39 da                	cmp    %ebx,%edx
    4b40:	7f e1                	jg     4b23 <external_thread+0x63>
    for (int b = 0; b < data->buffers_count; b++) {
    4b42:	41 8b 8e c4 00 00 00 	mov    0xc4(%r14),%ecx
    4b49:	49 83 c5 01          	add    $0x1,%r13
    4b4d:	44 39 e9             	cmp    %r13d,%ecx
    4b50:	7f b6                	jg     4b08 <external_thread+0x48>
  while (data->running == 1) {
    4b52:	41 83 7e 44 01       	cmpl   $0x1,0x44(%r14)
    4b57:	74 97                	je     4af0 <external_thread+0x30>
}
    4b59:	48 83 c4 08          	add    $0x8,%rsp
    4b5d:	31 c0                	xor    %eax,%eax
    4b5f:	5b                   	pop    %rbx
    4b60:	5d                   	pop    %rbp
    4b61:	41 5c                	pop    %r12
    4b63:	41 5d                	pop    %r13
    4b65:	41 5e                	pop    %r14
    4b67:	41 5f                	pop    %r15
    4b69:	c3                   	ret
    4b6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
					data->buffers[b]->buffer[x].data = "Hello world";
    4b70:	4c 89 38             	mov    %r15,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    4b73:	48 8b 06             	mov    (%rsi),%rax
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4b76:	48 83 c3 01          	add    $0x1,%rbx
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    4b7a:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4b7e:	48 01 ef             	add    %rbp,%rdi
    4b81:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    4b88:	48 c1 e6 05          	shl    $0x5,%rsi
    4b8c:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4b93:	bf 04 00 00 00       	mov    $0x4,%edi
    4b98:	e8 c3 d7 ff ff       	call   2360 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4b9d:	49 8b 7e 50          	mov    0x50(%r14),%rdi
    4ba1:	4a 8d 34 27          	lea    (%rdi,%r12,1),%rsi
    4ba5:	48 8b 06             	mov    (%rsi),%rax
    4ba8:	48 8b 50 08          	mov    0x8(%rax),%rdx
    4bac:	c7 84 2a 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rdx,%rbp,1)
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4bb7:	8b 10                	mov    (%rax),%edx
    4bb9:	39 da                	cmp    %ebx,%edx
    4bbb:	0f 8f 5e ff ff ff    	jg     4b1f <external_thread+0x5f>
    4bc1:	e9 7c ff ff ff       	jmp    4b42 <external_thread+0x82>
}
    4bc6:	31 c0                	xor    %eax,%eax
    4bc8:	c3                   	ret
    4bc9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004bd0 <timer_thread>:
void* timer_thread(void *arg) {
    4bd0:	f3 0f 1e fa          	endbr64
    4bd4:	41 57                	push   %r15
    4bd6:	48 8d 35 33 44 00 00 	lea    0x4433(%rip),%rsi        # 9010 <_IO_stdin_used+0x10>
    4bdd:	49 89 ff             	mov    %rdi,%r15
    4be0:	41 56                	push   %r14
    4be2:	41 55                	push   %r13
    4be4:	41 54                	push   %r12
    4be6:	55                   	push   %rbp
    4be7:	53                   	push   %rbx
    4be8:	48 83 ec 58          	sub    $0x58,%rsp
    4bec:	8b 57 04             	mov    0x4(%rdi),%edx
    4bef:	bf 01 00 00 00       	mov    $0x1,%edi
    4bf4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4bfd:	48 89 44 24 48       	mov    %rax,0x48(%rsp)
    4c02:	31 c0                	xor    %eax,%eax
    4c04:	e8 b7 d8 ff ff       	call   24c0 <__printf_chk@plt>
  struct timespec preempt = {
    4c09:	66 0f 6f 05 9f 52 00 00 	movdqa 0x529f(%rip),%xmm0        # 9eb0 <_IO_stdin_used+0xeb0>
    4c11:	ba a8 61 00 00       	mov    $0x61a8,%edx
    4c16:	31 c0                	xor    %eax,%eax
    4c18:	48 8d 35 03 44 00 00 	lea    0x4403(%rip),%rsi        # 9022 <_IO_stdin_used+0x22>
    4c1f:	bf 01 00 00 00       	mov    $0x1,%edi
    4c24:	0f 29 44 24 10       	movaps %xmm0,0x10(%rsp)
    4c29:	e8 92 d8 ff ff       	call   24c0 <__printf_chk@plt>
  while (data->running && n < times) {
    4c2e:	41 8b 47 44          	mov    0x44(%r15),%eax
    4c32:	89 c3                	mov    %eax,%ebx
    4c34:	85 c0                	test   %eax,%eax
    4c36:	0f 84 97 00 00 00    	je     4cd3 <timer_thread+0x103>
  int n = 0;
    4c3c:	45 31 f6             	xor    %r14d,%r14d
  int y = 0;
    4c3f:	31 db                	xor    %ebx,%ebx
    4c41:	49 89 e5             	mov    %rsp,%r13
    y++;
    4c44:	31 ed                	xor    %ebp,%ebp
    4c46:	4c 8d 64 24 10       	lea    0x10(%rsp),%r12
    nanosleep(&preempt , &rem2);
    4c4b:	4c 89 e7             	mov    %r12,%rdi
    4c4e:	4c 89 ee             	mov    %r13,%rsi
    n++;
    4c51:	41 83 c6 01          	add    $0x1,%r14d
    nanosleep(&preempt , &rem2);
    4c55:	e8 56 d7 ff ff       	call   23b0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c5a:	49 63 47 30          	movslq 0x30(%r15),%rax
    y++;
    4c5e:	8d 7b 01             	lea    0x1(%rbx),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c61:	85 c0                	test   %eax,%eax
    4c63:	7e 4a                	jle    4caf <timer_thread+0xdf>
    4c65:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4c69:	4c 63 c3             	movslq %ebx,%r8
    4c6c:	49 c1 e0 09          	shl    $0x9,%r8
    4c70:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4c74:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4c78:	48 8b 19             	mov    (%rcx),%rbx
    4c7b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4c7d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4c81:	99                   	cltd
    4c82:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4c85:	48 8b 73 38          	mov    0x38(%rbx),%rsi
        int next = (y + 1) % data->threads[x]->task_count - 1; // ignore reset task
    4c89:	83 ea 01             	sub    $0x1,%edx
        data->threads[x]->tasks[next].scheduled = 1;
    4c8c:	48 63 d2             	movslq %edx,%rdx
    4c8f:	48 c1 e2 09          	shl    $0x9,%rdx
    4c93:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4c9e:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4caa:	49 39 c9             	cmp    %rcx,%r9
    4cad:	75 c9                	jne    4c78 <timer_thread+0xa8>
    if (y >= data->threads[0]->task_count) {
    4caf:	49 8b 47 18          	mov    0x18(%r15),%rax
  while (data->running && n < times) {
    4cb3:	41 8b 4f 44          	mov    0x44(%r15),%ecx
    y++;
    4cb7:	89 fb                	mov    %edi,%ebx
    if (y >= data->threads[0]->task_count) {
    4cb9:	48 8b 00             	mov    (%rax),%rax
    y++;
    4cbc:	39 78 40             	cmp    %edi,0x40(%rax)
    4cbf:	0f 4e dd             	cmovle %ebp,%ebx
  while (data->running && n < times) {
    4cc2:	85 c9                	test   %ecx,%ecx
    4cc4:	74 0d                	je     4cd3 <timer_thread+0x103>
    4cc6:	41 81 fe a8 61 00 00 	cmp    $0x61a8,%r14d
    4ccd:	0f 85 78 ff ff ff    	jne    4c4b <timer_thread+0x7b>
    4cd3:	48 8d 3d 5e 43 00 00 	lea    0x435e(%rip),%rdi        # 9038 <_IO_stdin_used+0x38>
    4cda:	e8 61 d6 ff ff       	call   2340 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    4cdf:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4ce3:	85 d2                	test   %edx,%edx
    4ce5:	7e 6e                	jle    4d55 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    4ce7:	49 63 47 40          	movslq 0x40(%r15),%rax
    4ceb:	85 c0                	test   %eax,%eax
    4ced:	7e 66                	jle    4d55 <timer_thread+0x185>
    4cef:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4cf3:	4d 8b 47 18          	mov    0x18(%r15),%r8
    4cf7:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4cff:	31 c9                	xor    %ecx,%ecx
    4d01:	48 89 c6             	mov    %rax,%rsi
    4d04:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4d08:	48 8b 40 38          	mov    0x38(%rax),%rax
    4d0c:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4d10:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4d16:	74 18                	je     4d30 <timer_thread+0x160>
    4d18:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4d22:	48 05 00 02 00 00    	add    $0x200,%rax
    4d28:	48 39 c2             	cmp    %rax,%rdx
    4d2b:	74 1f                	je     4d4c <timer_thread+0x17c>
    4d2d:	0f 1f 00             	nopl   (%rax)
      data->threads[x]->tasks[y].sending = 0;
    4d30:	c7 80 88 01 00 00 00 00 00 00 	movl   $0x0,0x188(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4d3a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4d40:	c7 40 88 00 00 00 00 	movl   $0x0,-0x78(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4d47:	48 39 c2             	cmp    %rax,%rdx
    4d4a:	75 e4                	jne    4d30 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    4d4c:	48 83 c1 08          	add    $0x8,%rcx
    4d50:	48 39 cf             	cmp    %rcx,%rdi
    4d53:	75 af                	jne    4d04 <timer_thread+0x134>
  struct timespec drain = {
    4d55:	66 0f 6f 05 63 51 00 00 	movdqa 0x5163(%rip),%xmm0        # 9ec0 <_IO_stdin_used+0xec0>
    4d5d:	41 89 dc             	mov    %ebx,%r12d
    4d60:	0f 29 44 24 30       	movaps %xmm0,0x30(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4d65:	49 63 47 28          	movslq 0x28(%r15),%rax
    y++;
    4d69:	41 8d 7c 24 01       	lea    0x1(%r12),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    4d6e:	85 c0                	test   %eax,%eax
    4d70:	7e 49                	jle    4dbb <timer_thread+0x1eb>
    4d72:	49 8b 4f 18          	mov    0x18(%r15),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4d76:	49 63 ec             	movslq %r12d,%rbp
    4d79:	48 c1 e5 09          	shl    $0x9,%rbp
    4d7d:	4c 8d 04 c1          	lea    (%rcx,%rax,8),%r8
    4d81:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4d88:	48 8b 19             	mov    (%rcx),%rbx
    4d8b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    4d8d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4d91:	99                   	cltd
    4d92:	f7 7b 40             	idivl  0x40(%rbx)
        data->threads[x]->tasks[next].scheduled = 1;
    4d95:	48 8b 73 38          	mov    0x38(%rbx),%rsi
    4d99:	48 63 d2             	movslq %edx,%rdx
    4d9c:	48 c1 e2 09          	shl    $0x9,%rdx
    4da0:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4dab:	c7 84 2e 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%rbp,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4db6:	49 39 c8             	cmp    %rcx,%r8
    4db9:	75 cd                	jne    4d88 <timer_thread+0x1b8>
    if (y >= data->threads[0]->task_count) {
    4dbb:	49 8b 77 18          	mov    0x18(%r15),%rsi
    y++;
    4dbf:	45 31 e4             	xor    %r12d,%r12d
    if (y >= data->threads[0]->task_count) {
    4dc2:	48 8b 06             	mov    (%rsi),%rax
    y++;
    4dc5:	39 78 40             	cmp    %edi,0x40(%rax)
    4dc8:	44 0f 4f e7          	cmovg  %edi,%r12d
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4dcc:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4dd0:	85 ff                	test   %edi,%edi
    4dd2:	0f 8e ac 01 00 00    	jle    4f84 <timer_thread+0x3b4>
    4dd8:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    4ddb:	41 ba 01 00 00 00    	mov    $0x1,%r10d
    4de1:	4c 89 f5             	mov    %r14,%rbp
    4de4:	0f 1f 40 00          	nopl   0x0(%rax)
    4de8:	89 eb                	mov    %ebp,%ebx
      for (int y = 0 ; y < 2 ; y++) {
    4dea:	4c 8d 2c ed 00 00 00 00 	lea    0x0(,%rbp,8),%r13
    4df2:	45 31 f6             	xor    %r14d,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4df5:	85 ff                	test   %edi,%edi
    4df7:	7e 7f                	jle    4e78 <timer_thread+0x2a8>
    4df9:	4c 89 f6             	mov    %r14,%rsi
    4dfc:	48 63 cf             	movslq %edi,%rcx
    4dff:	45 31 c0             	xor    %r8d,%r8d
    4e02:	48 c1 e6 09          	shl    $0x9,%rsi
    4e06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          if (x == k) { continue; }
    4e10:	41 39 e8             	cmp    %ebp,%r8d
    4e13:	74 45                	je     4e5a <timer_thread+0x28a>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    4e15:	49 8b 47 18          	mov    0x18(%r15),%rax
    4e19:	4a 8b 04 28          	mov    (%rax,%r13,1),%rax
    4e1d:	48 8b 50 38          	mov    0x38(%rax),%rdx
    4e21:	4c 89 c0             	mov    %r8,%rax
    4e24:	48 c1 e0 08          	shl    $0x8,%rax
    4e28:	48 03 84 32 70 01 00 00 	add    0x170(%rdx,%rsi,1),%rax
    4e30:	48 8b 10             	mov    (%rax),%rdx
    4e33:	48 8b 80 80 00 00 00 	mov    0x80(%rax),%rax
    4e3a:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4e41:	4c 8b 98 80 00 00 00 	mov    0x80(%rax),%r11
    4e48:	4d 85 c9             	test   %r9,%r9
    4e4b:	0f 8f 97 00 00 00    	jg     4ee8 <timer_thread+0x318>
    4e51:	4d 85 db             	test   %r11,%r11
    4e54:	0f 8f 8e 00 00 00    	jg     4ee8 <timer_thread+0x318>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4e5a:	49 83 c0 01          	add    $0x1,%r8
    4e5e:	4c 39 c1             	cmp    %r8,%rcx
    4e61:	75 ad                	jne    4e10 <timer_thread+0x240>
      for (int y = 0 ; y < 2 ; y++) {
    4e63:	49 83 fe 01          	cmp    $0x1,%r14
    4e67:	74 0f                	je     4e78 <timer_thread+0x2a8>
    4e69:	41 be 01 00 00 00    	mov    $0x1,%r14d
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4e6f:	85 ff                	test   %edi,%edi
    4e71:	7f 86                	jg     4df9 <timer_thread+0x229>
    4e73:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4e78:	48 83 c5 01          	add    $0x1,%rbp
    4e7c:	39 ef                	cmp    %ebp,%edi
    4e7e:	0f 8f 64 ff ff ff    	jg     4de8 <timer_thread+0x218>
    4e84:	44 89 d5             	mov    %r10d,%ebp
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4e87:	85 ff                	test   %edi,%edi
    4e89:	7e 3b                	jle    4ec6 <timer_thread+0x2f6>
    4e8b:	31 db                	xor    %ebx,%ebx
    int all_waited = 1;
    4e8d:	bf 01 00 00 00       	mov    $0x1,%edi
    4e92:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4e96:	41 8b 57 40          	mov    0x40(%r15),%edx
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4e9a:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4e9e:	48 8b 40 38          	mov    0x38(%rax),%rax
    4ea2:	8b 88 a4 01 00 00    	mov    0x1a4(%rax),%ecx
    4ea8:	39 d1                	cmp    %edx,%ecx
    4eaa:	0f 8c a8 00 00 00    	jl     4f58 <timer_thread+0x388>
    4eb0:	8b 80 a4 03 00 00    	mov    0x3a4(%rax),%eax
    4eb6:	39 d0                	cmp    %edx,%eax
    4eb8:	7c 6e                	jl     4f28 <timer_thread+0x358>
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4eba:	48 83 c3 01          	add    $0x1,%rbx
    4ebe:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4ec2:	7f d6                	jg     4e9a <timer_thread+0x2ca>
    4ec4:	21 fd                	and    %edi,%ebp
    if (all_empty == 1 && all_waited == 1) {
    4ec6:	85 ed                	test   %ebp,%ebp
    4ec8:	0f 85 b6 00 00 00    	jne    4f84 <timer_thread+0x3b4>
      nanosleep(&drain , &drainrem);
    4ece:	48 8d 74 24 20       	lea    0x20(%rsp),%rsi
    4ed3:	48 8d 7c 24 30       	lea    0x30(%rsp),%rdi
    4ed8:	e8 d3 d4 ff ff       	call   23b0 <nanosleep@plt>
    4edd:	e9 83 fe ff ff       	jmp    4d65 <timer_thread+0x195>
    4ee2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4ee8:	8b 80 18 04 00 00    	mov    0x418(%rax),%eax
    4eee:	48 83 ec 08          	sub    $0x8,%rsp
    4ef2:	bf 01 00 00 00       	mov    $0x1,%edi
    4ef7:	44 89 f1             	mov    %r14d,%ecx
    4efa:	48 8d 35 5c 41 00 00 	lea    0x415c(%rip),%rsi        # 905d <_IO_stdin_used+0x5d>
    4f01:	50                   	push   %rax
    4f02:	8b 82 18 04 00 00    	mov    0x418(%rdx),%eax
    4f08:	89 da                	mov    %ebx,%edx
    4f0a:	50                   	push   %rax
    4f0b:	31 c0                	xor    %eax,%eax
    4f0d:	41 53                	push   %r11
    4f0f:	e8 ac d5 ff ff       	call   24c0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4f14:	41 8b 7f 30          	mov    0x30(%r15),%edi
    4f18:	48 83 c4 20          	add    $0x20,%rsp
            all_empty = 0;
    4f1c:	45 31 d2             	xor    %r10d,%r10d
    4f1f:	e9 3f ff ff ff       	jmp    4e63 <timer_thread+0x293>
    4f24:	0f 1f 40 00          	nopl   0x0(%rax)
    4f28:	89 c2                	mov    %eax,%edx
    4f2a:	bf 01 00 00 00       	mov    $0x1,%edi
    4f2f:	31 c0                	xor    %eax,%eax
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4f31:	48 83 c3 01          	add    $0x1,%rbx
    4f35:	48 8d 35 b9 44 00 00 	lea    0x44b9(%rip),%rsi        # 93f5 <_IO_stdin_used+0x3f5>
    4f3c:	e8 7f d5 ff ff       	call   24c0 <__printf_chk@plt>
          all_waited = 0; 
    4f41:	31 ff                	xor    %edi,%edi
    for (int k = 0 ; k < data->my_thread_count; k++) {
    4f43:	41 39 5f 30          	cmp    %ebx,0x30(%r15)
    4f47:	0f 8f 45 ff ff ff    	jg     4e92 <timer_thread+0x2c2>
    4f4d:	e9 72 ff ff ff       	jmp    4ec4 <timer_thread+0x2f4>
    4f52:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4f58:	89 ca                	mov    %ecx,%edx
    4f5a:	48 8d 35 94 44 00 00 	lea    0x4494(%rip),%rsi        # 93f5 <_IO_stdin_used+0x3f5>
    4f61:	bf 01 00 00 00       	mov    $0x1,%edi
    4f66:	31 c0                	xor    %eax,%eax
    4f68:	e8 53 d5 ff ff       	call   24c0 <__printf_chk@plt>
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4f6d:	49 8b 77 18          	mov    0x18(%r15),%rsi
    4f71:	41 8b 57 40          	mov    0x40(%r15),%edx
          all_waited = 0; 
    4f75:	31 ff                	xor    %edi,%edi
        if (data->threads[k]->tasks[tt].wait < data->task_count) {
    4f77:	48 8b 04 de          	mov    (%rsi,%rbx,8),%rax
    4f7b:	48 8b 40 38          	mov    0x38(%rax),%rax
    4f7f:	e9 2c ff ff ff       	jmp    4eb0 <timer_thread+0x2e0>
    4f84:	48 8d 3d c9 40 00 00 	lea    0x40c9(%rip),%rdi        # 9054 <_IO_stdin_used+0x54>
    4f8b:	e8 b0 d3 ff ff       	call   2340 <puts@plt>
  while (data->running) {
    4f90:	41 8b 57 44          	mov    0x44(%r15),%edx
    4f94:	85 d2                	test   %edx,%edx
    4f96:	0f 84 e8 00 00 00    	je     5084 <timer_thread+0x4b4>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4f9c:	41 8b 47 2c          	mov    0x2c(%r15),%eax
    4fa0:	31 db                	xor    %ebx,%ebx
    4fa2:	48 8d 2d d1 40 00 00 	lea    0x40d1(%rip),%rbp        # 907a <_IO_stdin_used+0x7a>
    4fa9:	4c 8d 25 e5 40 00 00 	lea    0x40e5(%rip),%r12        # 9095 <_IO_stdin_used+0x95>
    4fb0:	85 c0                	test   %eax,%eax
    4fb2:	7e 38                	jle    4fec <timer_thread+0x41c>
    4fb4:	0f 1f 40 00          	nopl   0x0(%rax)
    4fb8:	31 c0                	xor    %eax,%eax
    4fba:	89 da                	mov    %ebx,%edx
    4fbc:	48 89 ee             	mov    %rbp,%rsi
    4fbf:	bf 01 00 00 00       	mov    $0x1,%edi
    4fc4:	e8 f7 d4 ff ff       	call   24c0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4fc9:	49 8b 47 18          	mov    0x18(%r15),%rax
    4fcd:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
      if (data->threads[x]->type == IO) {
    4fd1:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    4fd5:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4fdc:	0f 84 cf 00 00 00    	je     50b1 <timer_thread+0x4e1>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4fe2:	48 83 c3 01          	add    $0x1,%rbx
    4fe6:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    4fea:	7f cc                	jg     4fb8 <timer_thread+0x3e8>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4fec:	49 63 57 30          	movslq 0x30(%r15),%rdx
    4ff0:	85 d2                	test   %edx,%edx
    4ff2:	7e 7c                	jle    5070 <timer_thread+0x4a0>
      for (int y = 0 ; y < data->task_count ; y++) {
    4ff4:	41 8b 47 40          	mov    0x40(%r15),%eax
    4ff8:	85 c0                	test   %eax,%eax
    4ffa:	7e 74                	jle    5070 <timer_thread+0x4a0>
    4ffc:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4fff:	4d 8b 47 18          	mov    0x18(%r15),%r8
    5003:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    500b:	31 c9                	xor    %ecx,%ecx
    500d:	48 c1 e6 09          	shl    $0x9,%rsi
    5011:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5018:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    501c:	48 8b 40 38          	mov    0x38(%rax),%rax
    5020:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    5024:	f7 c6 00 02 00 00    	test   $0x200,%esi
    502a:	74 1c                	je     5048 <timer_thread+0x478>
    502c:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    5036:	48 05 00 02 00 00    	add    $0x200,%rax
    503c:	48 39 d0             	cmp    %rdx,%rax
    503f:	74 26                	je     5067 <timer_thread+0x497>
    5041:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    5048:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    5052:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    5058:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    5062:	48 39 d0             	cmp    %rdx,%rax
    5065:	75 e1                	jne    5048 <timer_thread+0x478>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    5067:	48 83 c1 08          	add    $0x8,%rcx
    506b:	48 39 cf             	cmp    %rcx,%rdi
    506e:	75 a8                	jne    5018 <timer_thread+0x448>
    5070:	48 8d 3d 30 40 00 00 	lea    0x4030(%rip),%rdi        # 90a7 <_IO_stdin_used+0xa7>
    5077:	e8 c4 d2 ff ff       	call   2340 <puts@plt>
    data->running = 0;
    507c:	41 c7 47 44 00 00 00 00 	movl   $0x0,0x44(%r15)
    5084:	48 8d 3d 23 40 00 00 	lea    0x4023(%rip),%rdi        # 90ae <_IO_stdin_used+0xae>
    508b:	e8 b0 d2 ff ff       	call   2340 <puts@plt>
}
    5090:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
    5095:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    509e:	75 41                	jne    50e1 <timer_thread+0x511>
    50a0:	48 83 c4 58          	add    $0x58,%rsp
    50a4:	31 c0                	xor    %eax,%eax
    50a6:	5b                   	pop    %rbx
    50a7:	5d                   	pop    %rbp
    50a8:	41 5c                	pop    %r12
    50aa:	41 5d                	pop    %r13
    50ac:	41 5e                	pop    %r14
    50ae:	41 5f                	pop    %r15
    50b0:	c3                   	ret
    50b1:	4c 89 e7             	mov    %r12,%rdi
    50b4:	e8 87 d2 ff ff       	call   2340 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    50b9:	49 8b 47 18          	mov    0x18(%r15),%rax
    50bd:	be 01 00 00 00       	mov    $0x1,%esi
    50c2:	48 8b 04 d8          	mov    (%rax,%rbx,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    50c6:	48 83 c3 01          	add    $0x1,%rbx
        eventfd_write(data->threads[x]->_eventfd, 1);
    50ca:	8b 78 68             	mov    0x68(%rax),%edi
    50cd:	e8 9e d3 ff ff       	call   2470 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    50d2:	41 39 5f 2c          	cmp    %ebx,0x2c(%r15)
    50d6:	0f 8f dc fe ff ff    	jg     4fb8 <timer_thread+0x3e8>
    50dc:	e9 0b ff ff ff       	jmp    4fec <timer_thread+0x41c>
}
    50e1:	e8 aa d2 ff ff       	call   2390 <__stack_chk_fail@plt>
    50e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000050f0 <minf>:
int minf(int a, int b) {
    50f0:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    50f4:	39 f7                	cmp    %esi,%edi
    50f6:	89 f0                	mov    %esi,%eax
    50f8:	0f 4e c7             	cmovle %edi,%eax
}
    50fb:	c3                   	ret
    50fc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005100 <maxf>:
int maxf(int a, int b) {
    5100:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    5104:	39 f7                	cmp    %esi,%edi
    5106:	89 f0                	mov    %esi,%eax
    5108:	0f 4d c7             	cmovge %edi,%eax
}
    510b:	c3                   	ret
    510c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005110 <strtolower>:
void strtolower(char *str) {
    5110:	f3 0f 1e fa          	endbr64
    5114:	55                   	push   %rbp
    5115:	53                   	push   %rbx
    5116:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    511a:	48 0f be 1f          	movsbq (%rdi),%rbx
    511e:	84 db                	test   %bl,%bl
    5120:	74 24                	je     5146 <strtolower+0x36>
    5122:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    5125:	e8 86 d4 ff ff       	call   25b0 <__ctype_tolower_loc@plt>
    512a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5130:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    5133:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    5137:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    513a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    513d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    5142:	84 db                	test   %bl,%bl
    5144:	75 ea                	jne    5130 <strtolower+0x20>
}
    5146:	48 83 c4 08          	add    $0x8,%rsp
    514a:	5b                   	pop    %rbx
    514b:	5d                   	pop    %rbp
    514c:	c3                   	ret
    514d:	0f 1f 00             	nopl   (%rax)

0000000000005150 <zh_malloc>:
void *zh_malloc(size_t size) {
    5150:	f3 0f 1e fa          	endbr64
    5154:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    5158:	e8 23 d3 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    515d:	48 85 c0             	test   %rax,%rax
    5160:	74 05                	je     5167 <zh_malloc+0x17>
}
    5162:	48 83 c4 08          	add    $0x8,%rsp
    5166:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5167:	48 8b 0d b2 6e 00 00 	mov    0x6eb2(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    516e:	ba 28 00 00 00       	mov    $0x28,%edx
    5173:	be 01 00 00 00       	mov    $0x1,%esi
    5178:	48 8d 3d 59 45 00 00 	lea    0x4559(%rip),%rdi        # 96d8 <_IO_stdin_used+0x6d8>
    517f:	e8 bc d3 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    5184:	bf 01 00 00 00       	mov    $0x1,%edi
    5189:	e8 92 d3 ff ff       	call   2520 <exit@plt>
    518e:	66 90                	xchg   %ax,%ax

0000000000005190 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    5190:	f3 0f 1e fa          	endbr64
    5194:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    5195:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    519a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    519d:	e8 1e d2 ff ff       	call   23c0 <strrchr@plt>
    if (!dot || dot == filename)
    51a2:	48 85 c0             	test   %rax,%rax
    51a5:	74 11                	je     51b8 <get_filename_ext+0x28>
    51a7:	48 39 c3             	cmp    %rax,%rbx
    51aa:	74 0c                	je     51b8 <get_filename_ext+0x28>
    return dot + 1;
    51ac:	48 83 c0 01          	add    $0x1,%rax
}
    51b0:	5b                   	pop    %rbx
    51b1:	c3                   	ret
    51b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    51b8:	48 8d 05 37 3f 00 00 	lea    0x3f37(%rip),%rax        # 90f6 <_IO_stdin_used+0xf6>
}
    51bf:	5b                   	pop    %rbx
    51c0:	c3                   	ret
    51c1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    51cc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000051d0 <send_headers>:
void send_headers(struct KernelThread *data, struct Buffers *buffers, const char *path, off_t len, struct iovec *iov) {
    51d0:	f3 0f 1e fa          	endbr64
    51d4:	41 55                	push   %r13
    51d6:	48 89 d6             	mov    %rdx,%rsi
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    51d9:	ba 00 04 00 00       	mov    $0x400,%edx
    51de:	49 89 cd             	mov    %rcx,%r13
    51e1:	41 54                	push   %r12
    51e3:	55                   	push   %rbp
    51e4:	4c 89 c5             	mov    %r8,%rbp
    51e7:	53                   	push   %rbx
    51e8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    51ef:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    51f8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    5200:	31 c0                	xor    %eax,%eax
    5202:	49 89 e4             	mov    %rsp,%r12
    5205:	4c 89 e7             	mov    %r12,%rdi
    5208:	e8 93 d2 ff ff       	call   24a0 <__strcpy_chk@plt>
    for (; *str; ++str)
    520d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    5212:	84 db                	test   %bl,%bl
    5214:	74 24                	je     523a <send_headers+0x6a>
        *str = (char)tolower(*str);
    5216:	e8 95 d3 ff ff       	call   25b0 <__ctype_tolower_loc@plt>
    521b:	48 8b 08             	mov    (%rax),%rcx
    521e:	4c 89 e0             	mov    %r12,%rax
    5221:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5228:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    522b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    522f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    5232:	48 0f be 18          	movsbq (%rax),%rbx
    5236:	84 db                	test   %bl,%bl
    5238:	75 ee                	jne    5228 <send_headers+0x58>
    void *buf = malloc(size);
    523a:	bf 11 00 00 00       	mov    $0x11,%edi
    523f:	e8 3c d2 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    5244:	48 85 c0             	test   %rax,%rax
    5247:	0f 84 7e 04 00 00    	je     56cb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    524d:	66 0f 6f 05 7b 4c 00 00 	movdqa 0x4c7b(%rip),%xmm0        # 9ed0 <_IO_stdin_used+0xed0>
    iov[0].iov_base = zh_malloc(slen);
    5255:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    5259:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    525e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    5266:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    526a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    526d:	e8 0e d2 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    5272:	48 85 c0             	test   %rax,%rax
    5275:	0f 84 50 04 00 00    	je     56cb <send_headers+0x4fb>
    527b:	66 0f 6f 05 5d 4c 00 00 	movdqa 0x4c5d(%rip),%xmm0        # 9ee0 <_IO_stdin_used+0xee0>
    iov[1].iov_base = zh_malloc(slen);
    5283:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    5287:	4c 89 e7             	mov    %r12,%rdi
    528a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    5294:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    529c:	0f 11 00             	movups %xmm0,(%rax)
    529f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    52a3:	be 2e 00 00 00       	mov    $0x2e,%esi
    52a8:	e8 13 d1 ff ff       	call   23c0 <strrchr@plt>
    if (!dot || dot == filename)
    52ad:	48 85 c0             	test   %rax,%rax
    52b0:	0f 84 ea 02 00 00    	je     55a0 <send_headers+0x3d0>
    52b6:	4c 39 e0             	cmp    %r12,%rax
    52b9:	0f 84 e1 02 00 00    	je     55a0 <send_headers+0x3d0>
    return dot + 1;
    52bf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    52c3:	48 8d 3d fa 3d 00 00 	lea    0x3dfa(%rip),%rdi        # 90c4 <_IO_stdin_used+0xc4>
    52ca:	48 89 de             	mov    %rbx,%rsi
    52cd:	e8 4e d1 ff ff       	call   2420 <strcmp@plt>
    52d2:	85 c0                	test   %eax,%eax
    52d4:	75 20                	jne    52f6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    52d6:	66 0f 6f 05 12 4c 00 00 	movdqa 0x4c12(%rip),%xmm0        # 9ef0 <_IO_stdin_used+0xef0>
    52de:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    52e6:	66 0f 6f 05 12 4c 00 00 	movdqa 0x4c12(%rip),%xmm0        # 9f00 <_IO_stdin_used+0xf00>
    52ee:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    52f6:	48 89 de             	mov    %rbx,%rsi
    52f9:	48 8d 3d c8 3d 00 00 	lea    0x3dc8(%rip),%rdi        # 90c8 <_IO_stdin_used+0xc8>
    5300:	e8 1b d1 ff ff       	call   2420 <strcmp@plt>
    5305:	85 c0                	test   %eax,%eax
    5307:	75 20                	jne    5329 <send_headers+0x159>
    5309:	66 0f 6f 05 df 4b 00 00 	movdqa 0x4bdf(%rip),%xmm0        # 9ef0 <_IO_stdin_used+0xef0>
    5311:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5319:	66 0f 6f 05 df 4b 00 00 	movdqa 0x4bdf(%rip),%xmm0        # 9f00 <_IO_stdin_used+0xf00>
    5321:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    5329:	48 89 de             	mov    %rbx,%rsi
    532c:	48 8d 3d 9a 3d 00 00 	lea    0x3d9a(%rip),%rdi        # 90cd <_IO_stdin_used+0xcd>
    5333:	e8 e8 d0 ff ff       	call   2420 <strcmp@plt>
    5338:	85 c0                	test   %eax,%eax
    533a:	0f 84 10 02 00 00    	je     5550 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    5340:	48 89 de             	mov    %rbx,%rsi
    5343:	48 8d 3d 87 3d 00 00 	lea    0x3d87(%rip),%rdi        # 90d1 <_IO_stdin_used+0xd1>
    534a:	e8 d1 d0 ff ff       	call   2420 <strcmp@plt>
    534f:	85 c0                	test   %eax,%eax
    5351:	0f 84 a9 02 00 00    	je     5600 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    5357:	48 89 de             	mov    %rbx,%rsi
    535a:	48 8d 3d 74 3d 00 00 	lea    0x3d74(%rip),%rdi        # 90d5 <_IO_stdin_used+0xd5>
    5361:	e8 ba d0 ff ff       	call   2420 <strcmp@plt>
    5366:	85 c0                	test   %eax,%eax
    5368:	0f 84 6a 02 00 00    	je     55d8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    536e:	48 89 de             	mov    %rbx,%rsi
    5371:	48 8d 3d ac 3d 00 00 	lea    0x3dac(%rip),%rdi        # 9124 <_IO_stdin_used+0x124>
    5378:	e8 a3 d0 ff ff       	call   2420 <strcmp@plt>
    537d:	85 c0                	test   %eax,%eax
    537f:	0f 84 2b 02 00 00    	je     55b0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    5385:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    5388:	0f 84 52 01 00 00    	je     54e0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    538e:	48 89 de             	mov    %rbx,%rsi
    5391:	48 8d 3d 41 3d 00 00 	lea    0x3d41(%rip),%rdi        # 90d9 <_IO_stdin_used+0xd9>
    5398:	e8 83 d0 ff ff       	call   2420 <strcmp@plt>
    539d:	85 c0                	test   %eax,%eax
    539f:	0f 84 ab 02 00 00    	je     5650 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    53a5:	48 89 de             	mov    %rbx,%rsi
    53a8:	48 8d 3d 2e 3d 00 00 	lea    0x3d2e(%rip),%rdi        # 90dd <_IO_stdin_used+0xdd>
    53af:	e8 6c d0 ff ff       	call   2420 <strcmp@plt>
    53b4:	85 c0                	test   %eax,%eax
    53b6:	0f 84 6c 02 00 00    	je     5628 <send_headers+0x458>
    slen = strlen(send_buffer);
    53bc:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    53c4:	4c 89 e7             	mov    %r12,%rdi
    53c7:	e8 b4 cf ff ff       	call   2380 <strlen@plt>
    void *buf = malloc(size);
    53cc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    53cf:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    53d2:	e8 a9 d0 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    53d7:	48 85 c0             	test   %rax,%rax
    53da:	0f 84 eb 02 00 00    	je     56cb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    53e0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    53e4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    53e8:	83 fb 08             	cmp    $0x8,%ebx
    53eb:	0f 83 3f 01 00 00    	jae    5530 <send_headers+0x360>
    53f1:	f6 c3 04             	test   $0x4,%bl
    53f4:	0f 85 7b 02 00 00    	jne    5675 <send_headers+0x4a5>
    53fa:	85 db                	test   %ebx,%ebx
    53fc:	74 13                	je     5411 <send_headers+0x241>
    53fe:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    5406:	88 10                	mov    %dl,(%rax)
    5408:	f6 c3 02             	test   $0x2,%bl
    540b:	0f 85 96 02 00 00    	jne    56a7 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    5411:	4d 89 e8             	mov    %r13,%r8
    5414:	48 8d 0d c6 3c 00 00 	lea    0x3cc6(%rip),%rcx        # 90e1 <_IO_stdin_used+0xe1>
    541b:	4c 89 e7             	mov    %r12,%rdi
    541e:	31 c0                	xor    %eax,%eax
    5420:	ba 00 04 00 00       	mov    $0x400,%edx
    5425:	be 01 00 00 00       	mov    $0x1,%esi
    542a:	e8 91 d1 ff ff       	call   25c0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    542f:	4c 89 e7             	mov    %r12,%rdi
    5432:	e8 49 cf ff ff       	call   2380 <strlen@plt>
    void *buf = malloc(size);
    5437:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    543a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    543d:	e8 3e d0 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    5442:	48 85 c0             	test   %rax,%rax
    5445:	0f 84 80 02 00 00    	je     56cb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    544b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    544f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    5453:	83 fb 08             	cmp    $0x8,%ebx
    5456:	0f 83 1c 01 00 00    	jae    5578 <send_headers+0x3a8>
    545c:	f6 c3 04             	test   $0x4,%bl
    545f:	0f 85 29 02 00 00    	jne    568e <send_headers+0x4be>
    5465:	85 db                	test   %ebx,%ebx
    5467:	74 13                	je     547c <send_headers+0x2ac>
    5469:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    5471:	88 10                	mov    %dl,(%rax)
    5473:	f6 c3 02             	test   $0x2,%bl
    5476:	0f 85 3d 02 00 00    	jne    56b9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    547c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    5481:	bf 02 00 00 00       	mov    $0x2,%edi
    5486:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    548e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    5496:	e8 e5 cf ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    549b:	48 85 c0             	test   %rax,%rax
    549e:	0f 84 27 02 00 00    	je     56cb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    54a4:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    54ac:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    54b0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    54b8:	66 89 10             	mov    %dx,(%rax)
}
    54bb:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    54c3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    54cc:	0f 85 20 02 00 00    	jne    56f2 <send_headers+0x522>
    54d2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    54d9:	5b                   	pop    %rbx
    54da:	5d                   	pop    %rbp
    54db:	41 5c                	pop    %r12
    54dd:	41 5d                	pop    %r13
    54df:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    54e0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    54e4:	0f 85 a4 fe ff ff    	jne    538e <send_headers+0x1be>
    54ea:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    54ee:	0f 85 9a fe ff ff    	jne    538e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    54f4:	66 0f 6f 05 54 4a 00 00 	movdqa 0x4a54(%rip),%xmm0        # 9f50 <_IO_stdin_used+0xf50>
    54fc:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    5506:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    550e:	66 0f 6f 05 4a 4a 00 00 	movdqa 0x4a4a(%rip),%xmm0        # 9f60 <_IO_stdin_used+0xf60>
    5516:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    551e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    5526:	e9 63 fe ff ff       	jmp    538e <send_headers+0x1be>
    552b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5530:	89 da                	mov    %ebx,%edx
    5532:	48 89 c7             	mov    %rax,%rdi
    5535:	4c 89 e6             	mov    %r12,%rsi
    5538:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    553d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    5542:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    5545:	c1 e9 03             	shr    $0x3,%ecx
    5548:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    554b:	e9 c1 fe ff ff       	jmp    5411 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5550:	66 0f 6f 05 98 49 00 00 	movdqa 0x4998(%rip),%xmm0        # 9ef0 <_IO_stdin_used+0xef0>
    5558:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5560:	66 0f 6f 05 a8 49 00 00 	movdqa 0x49a8(%rip),%xmm0        # 9f10 <_IO_stdin_used+0xf10>
    5568:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5570:	e9 cb fd ff ff       	jmp    5340 <send_headers+0x170>
    5575:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    5578:	89 da                	mov    %ebx,%edx
    557a:	48 89 c7             	mov    %rax,%rdi
    557d:	4c 89 e6             	mov    %r12,%rsi
    5580:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    5585:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    558a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    558d:	c1 e9 03             	shr    $0x3,%ecx
    5590:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    5593:	e9 e4 fe ff ff       	jmp    547c <send_headers+0x2ac>
    5598:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    55a0:	48 8d 1d 4f 3b 00 00 	lea    0x3b4f(%rip),%rbx        # 90f6 <_IO_stdin_used+0xf6>
    55a7:	e9 94 fd ff ff       	jmp    5340 <send_headers+0x170>
    55ac:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55b0:	66 0f 6f 05 78 49 00 00 	movdqa 0x4978(%rip),%xmm0        # 9f30 <_IO_stdin_used+0xf30>
    55b8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    55c0:	66 0f 6f 05 78 49 00 00 	movdqa 0x4978(%rip),%xmm0        # 9f40 <_IO_stdin_used+0xf40>
    55c8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    55d0:	e9 b0 fd ff ff       	jmp    5385 <send_headers+0x1b5>
    55d5:	0f 1f 00             	nopl   (%rax)
    55d8:	66 0f 6f 05 50 49 00 00 	movdqa 0x4950(%rip),%xmm0        # 9f30 <_IO_stdin_used+0xf30>
    55e0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    55e8:	66 0f 6f 05 50 49 00 00 	movdqa 0x4950(%rip),%xmm0        # 9f40 <_IO_stdin_used+0xf40>
    55f0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    55f8:	e9 71 fd ff ff       	jmp    536e <send_headers+0x19e>
    55fd:	0f 1f 00             	nopl   (%rax)
    5600:	66 0f 6f 05 e8 48 00 00 	movdqa 0x48e8(%rip),%xmm0        # 9ef0 <_IO_stdin_used+0xef0>
    5608:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5610:	66 0f 6f 05 08 49 00 00 	movdqa 0x4908(%rip),%xmm0        # 9f20 <_IO_stdin_used+0xf20>
    5618:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5620:	e9 32 fd ff ff       	jmp    5357 <send_headers+0x187>
    5625:	0f 1f 00             	nopl   (%rax)
    5628:	66 0f 6f 05 00 49 00 00 	movdqa 0x4900(%rip),%xmm0        # 9f30 <_IO_stdin_used+0xf30>
    5630:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5638:	66 0f 6f 05 40 49 00 00 	movdqa 0x4940(%rip),%xmm0        # 9f80 <_IO_stdin_used+0xf80>
    5640:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5648:	e9 6f fd ff ff       	jmp    53bc <send_headers+0x1ec>
    564d:	0f 1f 00             	nopl   (%rax)
    5650:	66 0f 6f 05 d8 48 00 00 	movdqa 0x48d8(%rip),%xmm0        # 9f30 <_IO_stdin_used+0xf30>
    5658:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5660:	66 0f 6f 05 08 49 00 00 	movdqa 0x4908(%rip),%xmm0        # 9f70 <_IO_stdin_used+0xf70>
    5668:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5670:	e9 30 fd ff ff       	jmp    53a5 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5675:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    567c:	89 db                	mov    %ebx,%ebx
    567e:	89 10                	mov    %edx,(%rax)
    5680:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5685:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5689:	e9 83 fd ff ff       	jmp    5411 <send_headers+0x241>
    568e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5695:	89 db                	mov    %ebx,%ebx
    5697:	89 10                	mov    %edx,(%rax)
    5699:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    569e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    56a2:	e9 d5 fd ff ff       	jmp    547c <send_headers+0x2ac>
    56a7:	89 db                	mov    %ebx,%ebx
    56a9:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    56af:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    56b4:	e9 58 fd ff ff       	jmp    5411 <send_headers+0x241>
    56b9:	89 db                	mov    %ebx,%ebx
    56bb:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    56c1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    56c6:	e9 b1 fd ff ff       	jmp    547c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    56cb:	48 8b 0d 4e 69 00 00 	mov    0x694e(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    56d2:	ba 28 00 00 00       	mov    $0x28,%edx
    56d7:	be 01 00 00 00       	mov    $0x1,%esi
    56dc:	48 8d 3d f5 3f 00 00 	lea    0x3ff5(%rip),%rdi        # 96d8 <_IO_stdin_used+0x6d8>
    56e3:	e8 58 ce ff ff       	call   2540 <fwrite@plt>
        exit(1);
    56e8:	bf 01 00 00 00       	mov    $0x1,%edi
    56ed:	e8 2e ce ff ff       	call   2520 <exit@plt>
}
    56f2:	e8 99 cc ff ff       	call   2390 <__stack_chk_fail@plt>
    56f7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005700 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5700:	f3 0f 1e fa          	endbr64
    5704:	41 55                	push   %r13
    5706:	49 89 d5             	mov    %rdx,%r13
    5709:	41 54                	push   %r12
    570b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    570e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5711:	55                   	push   %rbp
    5712:	53                   	push   %rbx
    5713:	48 89 f3             	mov    %rsi,%rbx
    5716:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    571a:	e8 61 cd ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    571f:	48 85 c0             	test   %rax,%rax
    5722:	74 6b                	je     578f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    5724:	4c 89 e7             	mov    %r12,%rdi
    5727:	48 89 c5             	mov    %rax,%rbp
    572a:	31 f6                	xor    %esi,%esi
    572c:	31 c0                	xor    %eax,%eax
    572e:	e8 bd cd ff ff       	call   24f0 <open@plt>
    5733:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    5736:	85 c0                	test   %eax,%eax
    5738:	0f 88 b8 ce ff ff    	js     25f6 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    573e:	48 89 da             	mov    %rbx,%rdx
    5741:	48 89 ee             	mov    %rbp,%rsi
    5744:	89 c7                	mov    %eax,%edi
    5746:	e8 b5 cc ff ff       	call   2400 <read@plt>
    if (ret < file_size) {
    574b:	48 98                	cltq
    574d:	48 39 d8             	cmp    %rbx,%rax
    5750:	7c 1e                	jl     5770 <copy_file_contents+0x70>
    close(fd);
    5752:	44 89 e7             	mov    %r12d,%edi
    5755:	e8 86 cc ff ff       	call   23e0 <close@plt>
    iov->iov_base = buf;
    575a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    575e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    5762:	48 83 c4 08          	add    $0x8,%rsp
    5766:	5b                   	pop    %rbx
    5767:	5d                   	pop    %rbp
    5768:	41 5c                	pop    %r12
    576a:	41 5d                	pop    %r13
    576c:	c3                   	ret
    576d:	0f 1f 00             	nopl   (%rax)
    5770:	48 8b 0d a9 68 00 00 	mov    0x68a9(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5777:	ba 1a 00 00 00       	mov    $0x1a,%edx
    577c:	be 01 00 00 00       	mov    $0x1,%esi
    5781:	48 8d 3d 6f 39 00 00 	lea    0x396f(%rip),%rdi        # 90f7 <_IO_stdin_used+0xf7>
    5788:	e8 b3 cd ff ff       	call   2540 <fwrite@plt>
    578d:	eb c3                	jmp    5752 <copy_file_contents+0x52>
    578f:	48 8b 0d 8a 68 00 00 	mov    0x688a(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5796:	ba 28 00 00 00       	mov    $0x28,%edx
    579b:	be 01 00 00 00       	mov    $0x1,%esi
    57a0:	48 8d 3d 31 3f 00 00 	lea    0x3f31(%rip),%rdi        # 96d8 <_IO_stdin_used+0x6d8>
    57a7:	e8 94 cd ff ff       	call   2540 <fwrite@plt>
        exit(1);
    57ac:	bf 01 00 00 00       	mov    $0x1,%edi
    57b1:	e8 6a cd ff ff       	call   2520 <exit@plt>
    57b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000057c0 <add_write_request>:
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    57c0:	f3 0f 1e fa          	endbr64
    57c4:	41 55                	push   %r13
    struct Write *write = calloc(1, sizeof(struct Write));
    57c6:	be 10 00 00 00       	mov    $0x10,%esi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    57cb:	49 89 fd             	mov    %rdi,%r13
    struct Write *write = calloc(1, sizeof(struct Write));
    57ce:	bf 01 00 00 00       	mov    $0x1,%edi
int add_write_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    57d3:	41 54                	push   %r12
    57d5:	55                   	push   %rbp
    57d6:	53                   	push   %rbx
    57d7:	48 89 d3             	mov    %rdx,%rbx
    57da:	48 83 ec 08          	sub    $0x8,%rsp
    struct Write *write = calloc(1, sizeof(struct Write));
    57de:	e8 2d cc ff ff       	call   2410 <calloc@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_WRITE, write);
    57e3:	49 63 ad 10 01 00 00 	movslq 0x110(%r13),%rbp
    req->event_type = EVENT_TYPE_WRITE;
    57ea:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    struct Write *write = calloc(1, sizeof(struct Write));
    57f0:	49 89 c4             	mov    %rax,%r12
    write->client_socket = req->client_socket;
    57f3:	8b 43 08             	mov    0x8(%rbx),%eax
    write->request = req;
    57f6:	49 89 1c 24          	mov    %rbx,(%r12)
    buffersend(data, &data->iomailboxes[data->other_io], IO_WRITE, write);
    57fa:	48 c1 e5 04          	shl    $0x4,%rbp
    57fe:	49 03 ad 08 01 00 00 	add    0x108(%r13),%rbp
    write->client_socket = req->client_socket;
    5805:	41 89 44 24 08       	mov    %eax,0x8(%r12)
  while (data->running == 1) {
    580a:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
    580f:	75 6a                	jne    587b <add_write_request+0xbb>
      for (int x = 0 ; x < buffers->count ; x++) {
    5811:	48 63 45 00          	movslq 0x0(%rbp),%rax
    5815:	85 c0                	test   %eax,%eax
    5817:	7e f1                	jle    580a <add_write_request+0x4a>
        if (buffers->buffer[x].available == 0) {
    5819:	48 8b 55 08          	mov    0x8(%rbp),%rdx
    581d:	48 c1 e0 08          	shl    $0x8,%rax
    5821:	31 db                	xor    %ebx,%ebx
    5823:	eb 0f                	jmp    5834 <add_write_request+0x74>
    5825:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    5828:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    582f:	48 39 c3             	cmp    %rax,%rbx
    5832:	74 d6                	je     580a <add_write_request+0x4a>
        if (buffers->buffer[x].available == 0) {
    5834:	8b 8c 1a 80 00 00 00 	mov    0x80(%rdx,%rbx,1),%ecx
    583b:	85 c9                	test   %ecx,%ecx
    583d:	75 e9                	jne    5828 <add_write_request+0x68>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    583f:	8b 8c 1a 98 00 00 00 	mov    0x98(%rdx,%rbx,1),%ecx
    5846:	49 8b 95 18 01 00 00 	mov    0x118(%r13),%rdx
    584d:	bf 01 00 00 00       	mov    $0x1,%edi
    5852:	31 c0                	xor    %eax,%eax
    5854:	48 8d 35 b7 38 00 00 	lea    0x38b7(%rip),%rsi        # 9112 <_IO_stdin_used+0x112>
    585b:	e8 60 cc ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    5860:	48 03 5d 08          	add    0x8(%rbp),%rbx
    5864:	4c 89 23             	mov    %r12,(%rbx)
          buffers->buffer[x].kind = kind;
    5867:	c7 83 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%rbx)
          buffers->buffer[x].available = 1;
    5871:	c7 83 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbx)
}
    587b:	48 83 c4 08          	add    $0x8,%rsp
    587f:	31 c0                	xor    %eax,%eax
    5881:	5b                   	pop    %rbx
    5882:	5d                   	pop    %rbp
    5883:	41 5c                	pop    %r12
    5885:	41 5d                	pop    %r13
    5887:	c3                   	ret
    5888:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000005890 <add_read_request>:
int add_read_request(struct KernelThread *data, struct Buffers *buffers, int client_socket, struct io_uring *ring) {
    5890:	f3 0f 1e fa          	endbr64
    5894:	41 55                	push   %r13
    5896:	41 89 d5             	mov    %edx,%r13d
    5899:	41 54                	push   %r12
    589b:	55                   	push   %rbp
    589c:	53                   	push   %rbx
    589d:	48 89 cb             	mov    %rcx,%rbx
    58a0:	48 83 ec 08          	sub    $0x8,%rsp
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    58a4:	8b 41 44             	mov    0x44(%rcx),%eax
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    58a7:	48 8b 13             	mov    (%rbx),%rdx
	if (ring->flags & IORING_SETUP_SQE128)
    58aa:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    58b0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    58b3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    58b5:	f6 c1 02             	test   $0x2,%cl
    58b8:	74 00                	je     58ba <add_read_request+0x2a>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    58ba:	89 c2                	mov    %eax,%edx
    58bc:	29 f2                	sub    %esi,%edx
    58be:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    58c1:	0f 82 3b cd ff ff    	jb     2602 <add_read_request.cold>
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58c7:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    58ca:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    58cd:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    58d0:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    58d5:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58d8:	23 6b 58             	and    0x58(%rbx),%ebp
    58db:	d3 e5                	shl    %cl,%ebp
    58dd:	48 c1 e5 06          	shl    $0x6,%rbp
    58e1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    58e5:	e8 96 cb ff ff       	call   2480 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    58ea:	be 01 00 00 00       	mov    $0x1,%esi
    58ef:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    58f4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    58f7:	e8 14 cb ff ff       	call   2410 <calloc@plt>
    req->client_socket = client_socket;
    58fc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5901:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5905:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5908:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    590d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    5912:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    591b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    5923:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    5927:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    592b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    5932:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    593a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    593e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    5946:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    594e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    5952:	e8 49 ca ff ff       	call   23a0 <io_uring_submit@plt>
}
    5957:	48 83 c4 08          	add    $0x8,%rsp
    595b:	31 c0                	xor    %eax,%eax
    595d:	5b                   	pop    %rbx
    595e:	5d                   	pop    %rbp
    595f:	41 5c                	pop    %r12
    5961:	41 5d                	pop    %r13
    5963:	c3                   	ret
    5964:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    596f:	90                   	nop

0000000000005970 <_send_static_string_content>:
void _send_static_string_content(struct KernelThread *data, struct Buffers *buffers, const char *str, int client_socket, struct io_uring *ring) {
    5970:	f3 0f 1e fa          	endbr64
    5974:	41 56                	push   %r14
    5976:	41 89 ce             	mov    %ecx,%r14d
    5979:	41 55                	push   %r13
    597b:	41 54                	push   %r12
    597d:	49 89 d4             	mov    %rdx,%r12
    5980:	55                   	push   %rbp
    5981:	48 89 fd             	mov    %rdi,%rbp
    void *buf = malloc(size);
    5984:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(struct KernelThread *data, struct Buffers *buffers, const char *str, int client_socket, struct io_uring *ring) {
    5989:	53                   	push   %rbx
    void *buf = malloc(size);
    598a:	e8 f1 ca ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    598f:	48 85 c0             	test   %rax,%rax
    5992:	0f 84 f5 00 00 00    	je     5a8d <_send_static_string_content+0x11d>
    5998:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    599b:	4c 89 e7             	mov    %r12,%rdi
    599e:	e8 dd c9 ff ff       	call   2380 <strlen@plt>
    req->iovec_count = 1;
    59a3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    59aa:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    59ae:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    59b1:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    59b4:	e8 c7 ca ff ff       	call   2480 <malloc@plt>
    59b9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    59bc:	48 85 c0             	test   %rax,%rax
    59bf:	0f 84 c8 00 00 00    	je     5a8d <_send_static_string_content+0x11d>
    req->iov[0].iov_len = slen;
    59c5:	4c 89 6b 18          	mov    %r13,0x18(%rbx)
    59c9:	4c 89 ea             	mov    %r13,%rdx
    59cc:	4c 89 e6             	mov    %r12,%rsi
    req->iov[0].iov_base = zh_malloc(slen);
    59cf:	48 89 43 10          	mov    %rax,0x10(%rbx)
    59d3:	e8 78 ca ff ff       	call   2450 <memcpy@plt>
    59d8:	4c 89 e7             	mov    %r12,%rdi
    59db:	e8 60 c9 ff ff       	call   2340 <puts@plt>
    struct Write *write = calloc(1, sizeof(struct Write));
    59e0:	be 10 00 00 00       	mov    $0x10,%esi
    59e5:	bf 01 00 00 00       	mov    $0x1,%edi
    59ea:	e8 21 ca ff ff       	call   2410 <calloc@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_WRITE, write);
    59ef:	4c 63 a5 10 01 00 00 	movslq 0x110(%rbp),%r12
    req->event_type = EVENT_TYPE_WRITE;
    59f6:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    struct Write *write = calloc(1, sizeof(struct Write));
    59fc:	49 89 c5             	mov    %rax,%r13
    write->client_socket = req->client_socket;
    59ff:	8b 43 08             	mov    0x8(%rbx),%eax
    write->request = req;
    5a02:	49 89 5d 00          	mov    %rbx,0x0(%r13)
    buffersend(data, &data->iomailboxes[data->other_io], IO_WRITE, write);
    5a06:	49 c1 e4 04          	shl    $0x4,%r12
    5a0a:	4c 03 a5 08 01 00 00 	add    0x108(%rbp),%r12
    write->client_socket = req->client_socket;
    5a11:	41 89 45 08          	mov    %eax,0x8(%r13)
  while (data->running == 1) {
    5a15:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5a19:	75 69                	jne    5a84 <_send_static_string_content+0x114>
      for (int x = 0 ; x < buffers->count ; x++) {
    5a1b:	49 63 04 24          	movslq (%r12),%rax
    5a1f:	85 c0                	test   %eax,%eax
    5a21:	7e f2                	jle    5a15 <_send_static_string_content+0xa5>
        if (buffers->buffer[x].available == 0) {
    5a23:	49 8b 54 24 08       	mov    0x8(%r12),%rdx
    5a28:	48 c1 e0 08          	shl    $0x8,%rax
    5a2c:	31 db                	xor    %ebx,%ebx
    5a2e:	eb 0c                	jmp    5a3c <_send_static_string_content+0xcc>
      for (int x = 0 ; x < buffers->count ; x++) {
    5a30:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    5a37:	48 39 c3             	cmp    %rax,%rbx
    5a3a:	74 d9                	je     5a15 <_send_static_string_content+0xa5>
        if (buffers->buffer[x].available == 0) {
    5a3c:	8b 8c 1a 80 00 00 00 	mov    0x80(%rdx,%rbx,1),%ecx
    5a43:	85 c9                	test   %ecx,%ecx
    5a45:	75 e9                	jne    5a30 <_send_static_string_content+0xc0>
    5a47:	8b 8c 1a 98 00 00 00 	mov    0x98(%rdx,%rbx,1),%ecx
    5a4e:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    5a55:	bf 01 00 00 00       	mov    $0x1,%edi
    5a5a:	31 c0                	xor    %eax,%eax
    5a5c:	48 8d 35 af 36 00 00 	lea    0x36af(%rip),%rsi        # 9112 <_IO_stdin_used+0x112>
    5a63:	e8 58 ca ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    5a68:	49 03 5c 24 08       	add    0x8(%r12),%rbx
    5a6d:	4c 89 2b             	mov    %r13,(%rbx)
          buffers->buffer[x].kind = kind;
    5a70:	c7 83 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%rbx)
          buffers->buffer[x].available = 1;
    5a7a:	c7 83 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbx)
}
    5a84:	5b                   	pop    %rbx
    5a85:	5d                   	pop    %rbp
    5a86:	41 5c                	pop    %r12
    5a88:	41 5d                	pop    %r13
    5a8a:	41 5e                	pop    %r14
    5a8c:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5a8d:	48 8b 0d 8c 65 00 00 	mov    0x658c(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5a94:	ba 28 00 00 00       	mov    $0x28,%edx
    5a99:	be 01 00 00 00       	mov    $0x1,%esi
    5a9e:	48 8d 3d 33 3c 00 00 	lea    0x3c33(%rip),%rdi        # 96d8 <_IO_stdin_used+0x6d8>
    5aa5:	e8 96 ca ff ff       	call   2540 <fwrite@plt>
        exit(1);
    5aaa:	bf 01 00 00 00       	mov    $0x1,%edi
    5aaf:	e8 6c ca ff ff       	call   2520 <exit@plt>
    5ab4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5abf:	90                   	nop

0000000000005ac0 <handle_unimplemented_method>:
void handle_unimplemented_method(struct KernelThread *data, struct Buffers *buffers, int client_socket, struct io_uring *ring) {
    5ac0:	f3 0f 1e fa          	endbr64
    5ac4:	49 89 c8             	mov    %rcx,%r8
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, ring);
    5ac7:	89 d1                	mov    %edx,%ecx
    5ac9:	48 8b 15 48 65 00 00 	mov    0x6548(%rip),%rdx        # c018 <unimplemented_content>
    5ad0:	e9 9b fe ff ff       	jmp    5970 <_send_static_string_content>
    5ad5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005ae0 <handle_http_404>:
void handle_http_404(struct KernelThread *data, struct Buffers *buffers, int client_socket, struct io_uring *ring) {
    5ae0:	f3 0f 1e fa          	endbr64
    5ae4:	49 89 c8             	mov    %rcx,%r8
    _send_static_string_content(data, buffers, http_404_content, client_socket, ring);
    5ae7:	89 d1                	mov    %edx,%ecx
    5ae9:	48 8b 15 20 65 00 00 	mov    0x6520(%rip),%rdx        # c010 <http_404_content>
    5af0:	e9 7b fe ff ff       	jmp    5970 <_send_static_string_content>
    5af5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005b00 <handle_get_method>:
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, struct io_uring *ring) {
    5b00:	f3 0f 1e fa          	endbr64
    5b04:	41 57                	push   %r15
    5b06:	4d 89 c7             	mov    %r8,%r15
    5b09:	41 56                	push   %r14
    5b0b:	41 55                	push   %r13
    5b0d:	41 89 cd             	mov    %ecx,%r13d
    5b10:	41 54                	push   %r12
    5b12:	49 89 f4             	mov    %rsi,%r12
    5b15:	55                   	push   %rbp
    5b16:	48 89 fd             	mov    %rdi,%rbp
    if (path[strlen(path) - 1] == '/') {
    5b19:	48 89 d7             	mov    %rdx,%rdi
void handle_get_method(struct KernelThread *data, struct Buffers *buffers, char *path, int client_socket, struct io_uring *ring) {
    5b1c:	53                   	push   %rbx
    5b1d:	48 89 d3             	mov    %rdx,%rbx
    5b20:	48 81 ec b8 04 00 00 	sub    $0x4b8,%rsp
    5b27:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5b30:	48 89 84 24 a8 04 00 00 	mov    %rax,0x4a8(%rsp)
    5b38:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    5b3a:	e8 41 c8 ff ff       	call   2380 <strlen@plt>
    5b3f:	80 7c 03 ff 2f       	cmpb   $0x2f,-0x1(%rbx,%rax,1)
    5b44:	48 89 c2             	mov    %rax,%rdx
    5b47:	0f 84 c3 00 00 00    	je     5c10 <handle_get_method+0x110>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5b4d:	be 69 63 00 00       	mov    $0x6369,%esi


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5b52:	48 83 c2 01          	add    $0x1,%rdx
    5b56:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
    5b5e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5b63:	66 89 b4 24 a4 00 00 00 	mov    %si,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5b6b:	48 89 de             	mov    %rbx,%rsi
    5b6e:	4c 8d b4 24 a0 00 00 00 	lea    0xa0(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5b76:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5b81:	e8 aa c8 ff ff       	call   2430 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    5b86:	48 8d 74 24 10       	lea    0x10(%rsp),%rsi
    5b8b:	4c 89 f7             	mov    %r14,%rdi
    5b8e:	e8 ad c8 ff ff       	call   2440 <stat@plt>
    5b93:	83 f8 ff             	cmp    $0xffffffff,%eax
    5b96:	0f 84 f4 01 00 00    	je     5d90 <handle_get_method+0x290>
        if (S_ISREG(path_stat.st_mode)) {
    5b9c:	8b 44 24 28          	mov    0x28(%rsp),%eax
    5ba0:	25 00 f0 00 00       	and    $0xf000,%eax
    5ba5:	3d 00 80 00 00       	cmp    $0x8000,%eax
    5baa:	0f 84 c8 00 00 00    	je     5c78 <handle_get_method+0x178>
    _send_static_string_content(data, buffers, http_404_content, client_socket, ring);
    5bb0:	48 8b 15 59 64 00 00 	mov    0x6459(%rip),%rdx        # c010 <http_404_content>
    5bb7:	4c 89 e6             	mov    %r12,%rsi
    5bba:	48 89 ef             	mov    %rbp,%rdi
    5bbd:	4d 89 f8             	mov    %r15,%r8
    5bc0:	44 89 e9             	mov    %r13d,%ecx
    5bc3:	e8 a8 fd ff ff       	call   5970 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5bc8:	4c 89 f2             	mov    %r14,%rdx
    5bcb:	bf 01 00 00 00       	mov    $0x1,%edi
    5bd0:	31 c0                	xor    %eax,%eax
    5bd2:	48 8d 35 7a 35 00 00 	lea    0x357a(%rip),%rsi        # 9153 <_IO_stdin_used+0x153>
    5bd9:	e8 e2 c8 ff ff       	call   24c0 <__printf_chk@plt>
}
    5bde:	48 8b 84 24 a8 04 00 00 	mov    0x4a8(%rsp),%rax
    5be6:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5bef:	0f 85 d1 01 00 00    	jne    5dc6 <handle_get_method+0x2c6>
    5bf5:	48 81 c4 b8 04 00 00 	add    $0x4b8,%rsp
    5bfc:	5b                   	pop    %rbx
    5bfd:	5d                   	pop    %rbp
    5bfe:	41 5c                	pop    %r12
    5c00:	41 5d                	pop    %r13
    5c02:	41 5e                	pop    %r14
    5c04:	41 5f                	pop    %r15
    5c06:	c3                   	ret
    5c07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5c10:	bf 69 63 00 00       	mov    $0x6369,%edi
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5c15:	48 89 de             	mov    %rbx,%rsi
    5c18:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5c1d:	c7 84 24 a0 00 00 00 70 75 62 6c 	movl   $0x6c627570,0xa0(%rsp)
    5c28:	66 89 bc 24 a4 00 00 00 	mov    %di,0xa4(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5c30:	48 8d bc 24 a6 00 00 00 	lea    0xa6(%rsp),%rdi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5c38:	4c 8d b4 24 a0 00 00 00 	lea    0xa0(%rsp),%r14
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5c40:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5c45:	e8 e6 c7 ff ff       	call   2430 <__memcpy_chk@plt>
    5c4a:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
    5c4f:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5c54:	48 8d 35 c3 34 00 00 	lea    0x34c3(%rip),%rsi        # 911e <_IO_stdin_used+0x11e>
    5c5b:	48 29 d1             	sub    %rdx,%rcx
    5c5e:	49 8d 7c 16 06       	lea    0x6(%r14,%rdx,1),%rdi
    5c63:	ba 0b 00 00 00       	mov    $0xb,%edx
    5c68:	e8 c3 c7 ff ff       	call   2430 <__memcpy_chk@plt>
    5c6d:	e9 14 ff ff ff       	jmp    5b86 <handle_get_method+0x86>
    5c72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5c78:	bf 70 00 00 00       	mov    $0x70,%edi
    5c7d:	e8 fe c7 ff ff       	call   2480 <malloc@plt>
    5c82:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5c85:	48 85 c0             	test   %rax,%rax
    5c88:	0f 84 3d 01 00 00    	je     5dcb <handle_get_method+0x2cb>
            req->client_socket = client_socket;
    5c8e:	44 89 68 08          	mov    %r13d,0x8(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    5c92:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    5c97:	4c 8d 40 10          	lea    0x10(%rax),%r8
    5c9b:	4c 89 e6             	mov    %r12,%rsi
            req->iovec_count = 6;
    5c9e:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(data, buffers, final_path, path_stat.st_size, req->iov);
    5ca5:	4c 89 f2             	mov    %r14,%rdx
    5ca8:	48 89 ef             	mov    %rbp,%rdi
    5cab:	e8 20 f5 ff ff       	call   51d0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5cb0:	48 8b 74 24 40       	mov    0x40(%rsp),%rsi
    5cb5:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    5cb9:	4c 89 f7             	mov    %r14,%rdi
    5cbc:	e8 3f fa ff ff       	call   5700 <copy_file_contents>
    5cc1:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    5cc6:	4c 89 f2             	mov    %r14,%rdx
    5cc9:	31 c0                	xor    %eax,%eax
    5ccb:	48 8d 35 6f 34 00 00 	lea    0x346f(%rip),%rsi        # 9141 <_IO_stdin_used+0x141>
    5cd2:	bf 01 00 00 00       	mov    $0x1,%edi
    5cd7:	e8 e4 c7 ff ff       	call   24c0 <__printf_chk@plt>
    struct Write *write = calloc(1, sizeof(struct Write));
    5cdc:	be 10 00 00 00       	mov    $0x10,%esi
    5ce1:	bf 01 00 00 00       	mov    $0x1,%edi
    5ce6:	e8 25 c7 ff ff       	call   2410 <calloc@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_WRITE, write);
    5ceb:	4c 63 a5 10 01 00 00 	movslq 0x110(%rbp),%r12
    req->event_type = EVENT_TYPE_WRITE;
    5cf2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    struct Write *write = calloc(1, sizeof(struct Write));
    5cf8:	49 89 c5             	mov    %rax,%r13
    write->client_socket = req->client_socket;
    5cfb:	8b 43 08             	mov    0x8(%rbx),%eax
    write->request = req;
    5cfe:	49 89 5d 00          	mov    %rbx,0x0(%r13)
    buffersend(data, &data->iomailboxes[data->other_io], IO_WRITE, write);
    5d02:	49 c1 e4 04          	shl    $0x4,%r12
    5d06:	4c 03 a5 08 01 00 00 	add    0x108(%rbp),%r12
    write->client_socket = req->client_socket;
    5d0d:	41 89 45 08          	mov    %eax,0x8(%r13)
  while (data->running == 1) {
    5d11:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5d15:	0f 85 c3 fe ff ff    	jne    5bde <handle_get_method+0xde>
      for (int x = 0 ; x < buffers->count ; x++) {
    5d1b:	49 63 04 24          	movslq (%r12),%rax
    5d1f:	85 c0                	test   %eax,%eax
    5d21:	7e ee                	jle    5d11 <handle_get_method+0x211>
        if (buffers->buffer[x].available == 0) {
    5d23:	49 8b 54 24 08       	mov    0x8(%r12),%rdx
    5d28:	48 c1 e0 08          	shl    $0x8,%rax
    5d2c:	31 db                	xor    %ebx,%ebx
    5d2e:	eb 0c                	jmp    5d3c <handle_get_method+0x23c>
      for (int x = 0 ; x < buffers->count ; x++) {
    5d30:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    5d37:	48 39 c3             	cmp    %rax,%rbx
    5d3a:	74 d5                	je     5d11 <handle_get_method+0x211>
        if (buffers->buffer[x].available == 0) {
    5d3c:	8b 8c 1a 80 00 00 00 	mov    0x80(%rdx,%rbx,1),%ecx
    5d43:	85 c9                	test   %ecx,%ecx
    5d45:	75 e9                	jne    5d30 <handle_get_method+0x230>
    5d47:	8b 8c 1a 98 00 00 00 	mov    0x98(%rdx,%rbx,1),%ecx
    5d4e:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    5d55:	bf 01 00 00 00       	mov    $0x1,%edi
    5d5a:	31 c0                	xor    %eax,%eax
    5d5c:	48 8d 35 af 33 00 00 	lea    0x33af(%rip),%rsi        # 9112 <_IO_stdin_used+0x112>
    5d63:	e8 58 c7 ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    5d68:	49 03 5c 24 08       	add    0x8(%r12),%rbx
    5d6d:	4c 89 2b             	mov    %r13,(%rbx)
          buffers->buffer[x].kind = kind;
    5d70:	c7 83 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%rbx)
          buffers->buffer[x].available = 1;
    5d7a:	c7 83 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbx)
          return 0;
    5d84:	e9 55 fe ff ff       	jmp    5bde <handle_get_method+0xde>
    5d89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5d90:	48 89 d9             	mov    %rbx,%rcx
    5d93:	4c 89 f2             	mov    %r14,%rdx
    5d96:	48 8d 35 8c 33 00 00 	lea    0x338c(%rip),%rsi        # 9129 <_IO_stdin_used+0x129>
    5d9d:	31 c0                	xor    %eax,%eax
    5d9f:	bf 01 00 00 00       	mov    $0x1,%edi
    5da4:	e8 17 c7 ff ff       	call   24c0 <__printf_chk@plt>
    _send_static_string_content(data, buffers, http_404_content, client_socket, ring);
    5da9:	4d 89 f8             	mov    %r15,%r8
    5dac:	44 89 e9             	mov    %r13d,%ecx
    5daf:	4c 89 e6             	mov    %r12,%rsi
    5db2:	48 8b 15 57 62 00 00 	mov    0x6257(%rip),%rdx        # c010 <http_404_content>
    5db9:	48 89 ef             	mov    %rbp,%rdi
    5dbc:	e8 af fb ff ff       	call   5970 <_send_static_string_content>
}
    5dc1:	e9 18 fe ff ff       	jmp    5bde <handle_get_method+0xde>
}
    5dc6:	e8 c5 c5 ff ff       	call   2390 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5dcb:	48 8b 0d 4e 62 00 00 	mov    0x624e(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5dd2:	ba 28 00 00 00       	mov    $0x28,%edx
    5dd7:	be 01 00 00 00       	mov    $0x1,%esi
    5ddc:	48 8d 3d f5 38 00 00 	lea    0x38f5(%rip),%rdi        # 96d8 <_IO_stdin_used+0x6d8>
    5de3:	e8 58 c7 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    5de8:	bf 01 00 00 00       	mov    $0x1,%edi
    5ded:	e8 2e c7 ff ff       	call   2520 <exit@plt>
    5df2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5dfd:	0f 1f 00             	nopl   (%rax)

0000000000005e00 <handle_http_method>:
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, struct io_uring *ring) {
    5e00:	f3 0f 1e fa          	endbr64
    5e04:	41 57                	push   %r15
    5e06:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5e08:	4c 8d 35 9d 32 00 00 	lea    0x329d(%rip),%r14        # 90ac <_IO_stdin_used+0xac>
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, struct io_uring *ring) {
    5e0f:	41 55                	push   %r13
    5e11:	4d 89 c5             	mov    %r8,%r13
    5e14:	41 54                	push   %r12
    5e16:	41 89 cc             	mov    %ecx,%r12d
    5e19:	55                   	push   %rbp
    5e1a:	48 89 f5             	mov    %rsi,%rbp
    method = strtok_r(method_buffer, " ", &saveptr);
    5e1d:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, struct io_uring *ring) {
    5e20:	53                   	push   %rbx
    5e21:	48 83 ec 28          	sub    $0x28,%rsp
    5e25:	48 89 3c 24          	mov    %rdi,(%rsp)
    method = strtok_r(method_buffer, " ", &saveptr);
    5e29:	4c 8d 7c 24 10       	lea    0x10(%rsp),%r15
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, struct io_uring *ring) {
    5e2e:	48 89 d7             	mov    %rdx,%rdi
    method = strtok_r(method_buffer, " ", &saveptr);
    5e31:	4c 89 fa             	mov    %r15,%rdx
void handle_http_method(struct KernelThread *data, struct Buffers *buffers, char *method_buffer, int client_socket, struct io_uring *ring) {
    5e34:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5e3d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
    5e42:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5e44:	e8 a7 c5 ff ff       	call   23f0 <strtok_r@plt>
    for (; *str; ++str)
    5e49:	0f b6 10             	movzbl (%rax),%edx
    method = strtok_r(method_buffer, " ", &saveptr);
    5e4c:	48 89 c3             	mov    %rax,%rbx
    for (; *str; ++str)
    5e4f:	84 d2                	test   %dl,%dl
    5e51:	88 54 24 0f          	mov    %dl,0xf(%rsp)
    5e55:	74 26                	je     5e7d <handle_http_method+0x7d>
        *str = (char)tolower(*str);
    5e57:	e8 54 c7 ff ff       	call   25b0 <__ctype_tolower_loc@plt>
    5e5c:	48 0f be 54 24 0f    	movsbq 0xf(%rsp),%rdx
    5e62:	48 89 d9             	mov    %rbx,%rcx
    5e65:	0f 1f 00             	nopl   (%rax)
    5e68:	48 8b 30             	mov    (%rax),%rsi
    for (; *str; ++str)
    5e6b:	48 83 c1 01          	add    $0x1,%rcx
        *str = (char)tolower(*str);
    5e6f:	8b 14 96             	mov    (%rsi,%rdx,4),%edx
    5e72:	88 51 ff             	mov    %dl,-0x1(%rcx)
    for (; *str; ++str)
    5e75:	48 0f be 11          	movsbq (%rcx),%rdx
    5e79:	84 d2                	test   %dl,%dl
    5e7b:	75 eb                	jne    5e68 <handle_http_method+0x68>
    path = strtok_r(NULL, " ", &saveptr);
    5e7d:	4c 89 f6             	mov    %r14,%rsi
    5e80:	4c 89 fa             	mov    %r15,%rdx
    5e83:	31 ff                	xor    %edi,%edi
    5e85:	e8 66 c5 ff ff       	call   23f0 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5e8a:	48 8d 35 d5 32 00 00 	lea    0x32d5(%rip),%rsi        # 9166 <_IO_stdin_used+0x166>
    5e91:	48 89 df             	mov    %rbx,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    5e94:	49 89 c6             	mov    %rax,%r14
    if (strcmp(method, "get") == 0) {
    5e97:	e8 84 c5 ff ff       	call   2420 <strcmp@plt>
        handle_get_method(data, buffers, path, client_socket, ring);
    5e9c:	4d 89 e8             	mov    %r13,%r8
    5e9f:	44 89 e1             	mov    %r12d,%ecx
    if (strcmp(method, "get") == 0) {
    5ea2:	85 c0                	test   %eax,%eax
    5ea4:	75 32                	jne    5ed8 <handle_http_method+0xd8>
        handle_get_method(data, buffers, path, client_socket, ring);
    5ea6:	48 8b 3c 24          	mov    (%rsp),%rdi
    5eaa:	4c 89 f2             	mov    %r14,%rdx
    5ead:	48 89 ee             	mov    %rbp,%rsi
    5eb0:	e8 4b fc ff ff       	call   5b00 <handle_get_method>
}
    5eb5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    5eba:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5ec3:	75 28                	jne    5eed <handle_http_method+0xed>
    5ec5:	48 83 c4 28          	add    $0x28,%rsp
    5ec9:	5b                   	pop    %rbx
    5eca:	5d                   	pop    %rbp
    5ecb:	41 5c                	pop    %r12
    5ecd:	41 5d                	pop    %r13
    5ecf:	41 5e                	pop    %r14
    5ed1:	41 5f                	pop    %r15
    5ed3:	c3                   	ret
    5ed4:	0f 1f 40 00          	nopl   0x0(%rax)
    _send_static_string_content(data, buffers, unimplemented_content, client_socket, ring);
    5ed8:	48 8b 15 39 61 00 00 	mov    0x6139(%rip),%rdx        # c018 <unimplemented_content>
    5edf:	48 8b 3c 24          	mov    (%rsp),%rdi
    5ee3:	48 89 ee             	mov    %rbp,%rsi
    5ee6:	e8 85 fa ff ff       	call   5970 <_send_static_string_content>
}
    5eeb:	eb c8                	jmp    5eb5 <handle_http_method+0xb5>
    5eed:	e8 9e c4 ff ff       	call   2390 <__stack_chk_fail@plt>
    5ef2:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    5efd:	0f 1f 00             	nopl   (%rax)

0000000000005f00 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5f00:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5f04:	85 d2                	test   %edx,%edx
    5f06:	7e 38                	jle    5f40 <get_line+0x40>
    5f08:	48 63 d2             	movslq %edx,%rdx
    5f0b:	48 83 c7 01          	add    $0x1,%rdi
    5f0f:	48 01 f2             	add    %rsi,%rdx
    5f12:	eb 11                	jmp    5f25 <get_line+0x25>
    5f14:	0f 1f 40 00          	nopl   0x0(%rax)
    5f18:	48 83 c6 01          	add    $0x1,%rsi
    5f1c:	48 83 c7 01          	add    $0x1,%rdi
    5f20:	48 39 d6             	cmp    %rdx,%rsi
    5f23:	74 1b                	je     5f40 <get_line+0x40>
        dest[i] = src[i];
    5f25:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5f29:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5f2b:	3c 0d                	cmp    $0xd,%al
    5f2d:	75 e9                	jne    5f18 <get_line+0x18>
    5f2f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5f32:	75 e4                	jne    5f18 <get_line+0x18>
            dest[i] = '\0';
    5f34:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5f37:	31 c0                	xor    %eax,%eax
    5f39:	c3                   	ret
    5f3a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5f40:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5f45:	c3                   	ret
    5f46:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005f50 <handle_client_request>:
int handle_client_request(struct KernelThread *data, struct Buffers *buffers, struct Request *req, struct io_uring *ring) {
    5f50:	f3 0f 1e fa          	endbr64
    5f54:	53                   	push   %rbx
    5f55:	49 89 fa             	mov    %rdi,%r10
    5f58:	48 89 f3             	mov    %rsi,%rbx
    5f5b:	48 81 ec 10 04 00 00 	sub    $0x410,%rsp
    5f62:	48 8b 72 10          	mov    0x10(%rdx),%rsi
    5f66:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5f6f:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5f77:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5f79:	49 89 e3             	mov    %rsp,%r11
    5f7c:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    5f84:	4c 89 d8             	mov    %r11,%rax
    5f87:	eb 14                	jmp    5f9d <handle_client_request+0x4d>
    5f89:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    5f90:	48 83 c0 01          	add    $0x1,%rax
    5f94:	48 83 c6 01          	add    $0x1,%rsi
    5f98:	4c 39 c8             	cmp    %r9,%rax
    5f9b:	74 53                	je     5ff0 <handle_client_request+0xa0>
        dest[i] = src[i];
    5f9d:	0f b6 3e             	movzbl (%rsi),%edi
    5fa0:	40 88 38             	mov    %dil,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5fa3:	40 80 ff 0d          	cmp    $0xd,%dil
    5fa7:	75 e7                	jne    5f90 <handle_client_request+0x40>
    5fa9:	80 7e 01 0a          	cmpb   $0xa,0x1(%rsi)
    5fad:	75 e1                	jne    5f90 <handle_client_request+0x40>
            dest[i] = '\0';
    5faf:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(data, buffers, http_request, req->client_socket, ring);
    5fb2:	8b 42 08             	mov    0x8(%rdx),%eax
    5fb5:	49 89 c8             	mov    %rcx,%r8
    5fb8:	4c 89 da             	mov    %r11,%rdx
    5fbb:	48 89 de             	mov    %rbx,%rsi
    5fbe:	4c 89 d7             	mov    %r10,%rdi
    5fc1:	89 c1                	mov    %eax,%ecx
    5fc3:	e8 38 fe ff ff       	call   5e00 <handle_http_method>
}
    5fc8:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5fd0:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5fd9:	75 3c                	jne    6017 <handle_client_request+0xc7>
    5fdb:	48 81 c4 10 04 00 00 	add    $0x410,%rsp
    5fe2:	31 c0                	xor    %eax,%eax
    5fe4:	5b                   	pop    %rbx
    5fe5:	c3                   	ret
    5fe6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5ff0:	48 8b 0d 29 60 00 00 	mov    0x6029(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    5ff7:	ba 12 00 00 00       	mov    $0x12,%edx
    5ffc:	be 01 00 00 00       	mov    $0x1,%esi
    6001:	48 8d 3d 62 31 00 00 	lea    0x3162(%rip),%rdi        # 916a <_IO_stdin_used+0x16a>
    6008:	e8 33 c5 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    600d:	bf 01 00 00 00       	mov    $0x1,%edi
    6012:	e8 09 c5 ff ff       	call   2520 <exit@plt>
}
    6017:	e8 74 c3 ff ff       	call   2390 <__stack_chk_fail@plt>
    601c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006020 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    6020:	f3 0f 1e fa          	endbr64
    6024:	55                   	push   %rbp
    6025:	53                   	push   %rbx
    6026:	48 89 cb             	mov    %rcx,%rbx
    6029:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    602d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    6030:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    6033:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    6039:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    603c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    603f:	f6 c1 02             	test   $0x2,%cl
    6042:	74 00                	je     6044 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    6044:	41 89 c0             	mov    %eax,%r8d
    6047:	45 29 c8             	sub    %r9d,%r8d
    604a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    604e:	0f 82 b8 c5 ff ff    	jb     260c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    6054:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6057:	8b 6b 44             	mov    0x44(%rbx),%ebp
    605a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    605d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    6060:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    6063:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6067:	d3 e5                	shl    %cl,%ebp
    6069:	48 c1 e5 06          	shl    $0x6,%rbp
    606d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    6071:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    6074:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    6079:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    6080:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    6084:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    6088:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    6090:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    6098:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    609c:	e8 df c3 ff ff       	call   2480 <malloc@plt>
  io_uring_submit(ring);
    60a1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    60a4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    60aa:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    60ae:	48 83 c4 08          	add    $0x8,%rsp
    60b2:	5b                   	pop    %rbx
    60b3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    60b4:	e9 e7 c2 ff ff       	jmp    23a0 <io_uring_submit@plt>
    60b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000060c0 <io_thread>:
void* io_thread(void *arg) {
    60c0:	f3 0f 1e fa          	endbr64
    60c4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    60c6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    60c8:	41 56                	push   %r14
    60ca:	41 55                	push   %r13
    60cc:	41 54                	push   %r12
    60ce:	55                   	push   %rbp
    60cf:	48 89 fd             	mov    %rdi,%rbp
    60d2:	53                   	push   %rbx
    60d3:	48 81 ec 88 05 00 00 	sub    $0x588,%rsp
  struct io_uring ring = *data->ring;
    60da:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    60e3:	48 89 84 24 78 05 00 00 	mov    %rax,0x578(%rsp)
    60eb:	48 8b 47 60          	mov    0x60(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    60ef:	bf 00 01 00 00       	mov    $0x100,%edi
  struct io_uring ring = *data->ring;
    60f4:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    60f8:	0f 29 8c 24 90 00 00 00 	movaps %xmm1,0x90(%rsp)
    6100:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    6105:	0f 29 94 24 a0 00 00 00 	movaps %xmm2,0xa0(%rsp)
    610d:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    6112:	0f 29 9c 24 b0 00 00 00 	movaps %xmm3,0xb0(%rsp)
    611a:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    611f:	0f 29 a4 24 c0 00 00 00 	movaps %xmm4,0xc0(%rsp)
    6127:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    612c:	0f 29 ac 24 d0 00 00 00 	movaps %xmm5,0xd0(%rsp)
    6134:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    6139:	0f 29 b4 24 e0 00 00 00 	movaps %xmm6,0xe0(%rsp)
    6141:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    6146:	0f 29 bc 24 f0 00 00 00 	movaps %xmm7,0xf0(%rsp)
    614e:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    6153:	0f 29 8c 24 00 01 00 00 	movaps %xmm1,0x100(%rsp)
    615b:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    6163:	0f 29 94 24 10 01 00 00 	movaps %xmm2,0x110(%rsp)
    616b:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    6173:	0f 29 9c 24 20 01 00 00 	movaps %xmm3,0x120(%rsp)
    617b:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    6183:	0f 29 a4 24 30 01 00 00 	movaps %xmm4,0x130(%rsp)
    618b:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    6193:	0f 29 ac 24 40 01 00 00 	movaps %xmm5,0x140(%rsp)
    619b:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    61a3:	0f 29 b4 24 50 01 00 00 	movaps %xmm6,0x150(%rsp)
    61ab:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    61b2:	48 89 84 24 60 01 00 00 	mov    %rax,0x160(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    61ba:	48 8d 84 24 90 00 00 00 	lea    0x90(%rsp),%rax
    61c2:	48 89 c6             	mov    %rax,%rsi
    61c5:	48 89 04 24          	mov    %rax,(%rsp)
    61c9:	e8 92 c2 ff ff       	call   2460 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    61ce:	48 8b 7d 60          	mov    0x60(%rbp),%rdi
    61d2:	31 f6                	xor    %esi,%esi
    61d4:	e8 87 c3 ff ff       	call   2560 <io_uring_register_eventfd@plt>
  if (data->io_mode == IO_MODE_RECV) {
    61d9:	8b 85 04 01 00 00    	mov    0x104(%rbp),%eax
    61df:	83 f8 01             	cmp    $0x1,%eax
    61e2:	0f 84 cf 09 00 00    	je     6bb7 <io_thread+0xaf7>
  if (data->io_mode == IO_MODE_SEND) {
    61e8:	85 c0                	test   %eax,%eax
    61ea:	0f 85 08 06 00 00    	jne    67f8 <io_thread+0x738>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    61f0:	48 8d 3d a9 35 00 00 	lea    0x35a9(%rip),%rdi        # 97a0 <_IO_stdin_used+0x7a0>
    61f7:	e8 44 c1 ff ff       	call   2340 <puts@plt>
    int epollfd = epoll_create1(0);
    61fc:	31 ff                	xor    %edi,%edi
    61fe:	e8 9d c3 ff ff       	call   25a0 <epoll_create1@plt>
    6203:	89 44 24 10          	mov    %eax,0x10(%rsp)
				if (epollfd == -1) {
    6207:	83 f8 ff             	cmp    $0xffffffff,%eax
    620a:	0f 84 5b c4 ff ff    	je     266b <io_thread.cold+0x55>
    6210:	89 c2                	mov    %eax,%edx
    6212:	48 8d 35 4b 30 00 00 	lea    0x304b(%rip),%rsi        # 9264 <_IO_stdin_used+0x264>
    6219:	31 c0                	xor    %eax,%eax
    621b:	bf 01 00 00 00       	mov    $0x1,%edi
    6220:	e8 9b c2 ff ff       	call   24c0 <__printf_chk@plt>
    6225:	48 8d 3d ac 35 00 00 	lea    0x35ac(%rip),%rdi        # 97d8 <_IO_stdin_used+0x7d8>
    622c:	4c 8d 25 46 30 00 00 	lea    0x3046(%rip),%r12        # 9279 <_IO_stdin_used+0x279>
    6233:	e8 08 c1 ff ff       	call   2340 <puts@plt>
    6238:	8b 8d 14 01 00 00    	mov    0x114(%rbp),%ecx
    623e:	31 c0                	xor    %eax,%eax
    6240:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    6247:	44 8b 85 10 01 00 00 	mov    0x110(%rbp),%r8d
    624e:	48 8d 35 bb 35 00 00 	lea    0x35bb(%rip),%rsi        # 9810 <_IO_stdin_used+0x810>
    6255:	bf 01 00 00 00       	mov    $0x1,%edi
    625a:	e8 61 c2 ff ff       	call   24c0 <__printf_chk@plt>
    void * _reply = bufferrecv("waitsocketreply", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET, &reply, 0); 
    625f:	4c 63 ad 14 01 00 00 	movslq 0x114(%rbp),%r13
    6266:	49 c1 e5 04          	shl    $0x4,%r13
    626a:	4c 03 ad 08 01 00 00 	add    0x108(%rbp),%r13
  while (data->running == 1) {
    6271:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6278:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    627c:	0f 85 09 c4 ff ff    	jne    268b <io_thread.cold+0x75>
      for (int x = 0 ; x < buffers->count ; x++) {
    6282:	49 63 45 00          	movslq 0x0(%r13),%rax
    6286:	85 c0                	test   %eax,%eax
    6288:	0f 8e a1 05 00 00    	jle    682f <io_thread+0x76f>
        if (buffers->buffer[x].available == 1) {
    628e:	49 8b 4d 08          	mov    0x8(%r13),%rcx
    6292:	48 c1 e0 08          	shl    $0x8,%rax
                for (int i = 0; i < req->iovec_count; i++) {
    6296:	31 db                	xor    %ebx,%ebx
    6298:	eb 12                	jmp    62ac <io_thread+0x1ec>
    629a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    62a0:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    62a7:	48 39 c3             	cmp    %rax,%rbx
    62aa:	74 ea                	je     6296 <io_thread+0x1d6>
        if (buffers->buffer[x].available == 1) {
    62ac:	83 bc 19 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx,%rbx,1)
    62b4:	75 ea                	jne    62a0 <io_thread+0x1e0>
    62b6:	44 8b 84 19 98 00 00 00 	mov    0x98(%rcx,%rbx,1),%r8d
    62be:	bf 01 00 00 00       	mov    $0x1,%edi
    62c3:	4c 89 e1             	mov    %r12,%rcx
    62c6:	31 c0                	xor    %eax,%eax
    62c8:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    62cf:	48 8d 35 e3 2e 00 00 	lea    0x2ee3(%rip),%rsi        # 91b9 <_IO_stdin_used+0x1b9>
    62d6:	e8 e5 c1 ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    62db:	49 03 5d 08          	add    0x8(%r13),%rbx
    62df:	8b b3 98 00 00 00    	mov    0x98(%rbx),%esi
    62e5:	85 f6                	test   %esi,%esi
    62e7:	75 8f                	jne    6278 <io_thread+0x1b8>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    62e9:	be 00 01 00 00       	mov    $0x100,%esi
    62ee:	bf 01 00 00 00       	mov    $0x1,%edi
    62f3:	e8 18 c1 ff ff       	call   2410 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    62f8:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    62fb:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
            reply->kind = buffers->buffer[x].kind;
    6305:	c7 80 98 00 00 00 00 00 00 00 	movl   $0x0,0x98(%rax)
            reply->data = buffers->buffer[x].data;
    630f:	48 89 10             	mov    %rdx,(%rax)
    struct NewSocketMessage *msg = bufferreply->data;
    6312:	48 8b 18             	mov    (%rax),%rbx
    6315:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    631c:	48 8d 35 2d 35 00 00 	lea    0x352d(%rip),%rsi        # 9850 <_IO_stdin_used+0x850>
    6323:	31 c0                	xor    %eax,%eax
    6325:	bf 01 00 00 00       	mov    $0x1,%edi
    632a:	8b 0b                	mov    (%rbx),%ecx
    632c:	e8 8f c1 ff ff       	call   24c0 <__printf_chk@plt>
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    6331:	be 04 00 00 00       	mov    $0x4,%esi
    6336:	bf 01 00 00 00       	mov    $0x1,%edi
    633b:	e8 d0 c0 ff ff       	call   2410 <calloc@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    6340:	4c 63 ad 10 01 00 00 	movslq 0x110(%rbp),%r13
    struct NewSocketReply *ourreply = calloc(1, sizeof(struct NewSocketReply));
    6347:	49 89 c4             	mov    %rax,%r12
    ourreply->nothing = msg->socket;
    634a:	8b 03                	mov    (%rbx),%eax
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET_REPLY, ourreply);
    634c:	49 c1 e5 04          	shl    $0x4,%r13
    6350:	4c 03 ad 08 01 00 00 	add    0x108(%rbp),%r13
  while (data->running == 1) {
    6357:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    ourreply->nothing = msg->socket;
    635b:	41 89 04 24          	mov    %eax,(%r12)
  while (data->running == 1) {
    635f:	75 76                	jne    63d7 <io_thread+0x317>
      for (int x = 0 ; x < buffers->count ; x++) {
    6361:	49 63 45 00          	movslq 0x0(%r13),%rax
    6365:	85 c0                	test   %eax,%eax
    6367:	0f 8e cb 07 00 00    	jle    6b38 <io_thread+0xa78>
        if (buffers->buffer[x].available == 0) {
    636d:	49 8b 55 08          	mov    0x8(%r13),%rdx
    6371:	48 c1 e0 08          	shl    $0x8,%rax
    6375:	31 db                	xor    %ebx,%ebx
    6377:	eb 17                	jmp    6390 <io_thread+0x2d0>
    6379:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    6380:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    6387:	48 39 c3             	cmp    %rax,%rbx
    638a:	0f 84 a8 07 00 00    	je     6b38 <io_thread+0xa78>
        if (buffers->buffer[x].available == 0) {
    6390:	8b 8c 1a 80 00 00 00 	mov    0x80(%rdx,%rbx,1),%ecx
    6397:	85 c9                	test   %ecx,%ecx
    6399:	75 e5                	jne    6380 <io_thread+0x2c0>
    639b:	8b 8c 1a 98 00 00 00 	mov    0x98(%rdx,%rbx,1),%ecx
    63a2:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    63a9:	bf 01 00 00 00       	mov    $0x1,%edi
    63ae:	31 c0                	xor    %eax,%eax
    63b0:	48 8d 35 5b 2d 00 00 	lea    0x2d5b(%rip),%rsi        # 9112 <_IO_stdin_used+0x112>
    63b7:	e8 04 c1 ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    63bc:	49 03 5d 08          	add    0x8(%r13),%rbx
    63c0:	4c 89 23             	mov    %r12,(%rbx)
          buffers->buffer[x].kind = kind;
    63c3:	c7 83 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%rbx)
          buffers->buffer[x].available = 1;
    63cd:	c7 83 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbx)
    63d7:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    63de:	48 8d 35 a3 34 00 00 	lea    0x34a3(%rip),%rsi        # 9888 <_IO_stdin_used+0x888>
    63e5:	bf 01 00 00 00       	mov    $0x1,%edi
    63ea:	31 c0                	xor    %eax,%eax
    63ec:	4c 8d 25 b2 2e 00 00 	lea    0x2eb2(%rip),%r12        # 92a5 <_IO_stdin_used+0x2a5>
    63f3:	e8 c8 c0 ff ff       	call   24c0 <__printf_chk@plt>
    63f8:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    63ff:	48 8d 35 83 2e 00 00 	lea    0x2e83(%rip),%rsi        # 9289 <_IO_stdin_used+0x289>
    6406:	31 c0                	xor    %eax,%eax
    6408:	bf 01 00 00 00       	mov    $0x1,%edi
    640d:	e8 ae c0 ff ff       	call   24c0 <__printf_chk@plt>
    struct Buffer* newclient = bufferrecv("clientwait", data, &data->iomailboxes[data->my_io], IO_NEW_CLIENT, &_newclient, 0);
    6412:	4c 63 ad 14 01 00 00 	movslq 0x114(%rbp),%r13
    6419:	49 c1 e5 04          	shl    $0x4,%r13
    641d:	4c 03 ad 08 01 00 00 	add    0x108(%rbp),%r13
  while (data->running == 1) {
    6424:	0f 1f 40 00          	nopl   0x0(%rax)
    6428:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    642c:	0f 85 63 c2 ff ff    	jne    2695 <io_thread.cold+0x7f>
      for (int x = 0 ; x < buffers->count ; x++) {
    6432:	49 63 45 00          	movslq 0x0(%r13),%rax
    6436:	85 c0                	test   %eax,%eax
    6438:	0f 8e f3 03 00 00    	jle    6831 <io_thread+0x771>
        if (buffers->buffer[x].available == 1) {
    643e:	49 8b 4d 08          	mov    0x8(%r13),%rcx
    6442:	48 c1 e0 08          	shl    $0x8,%rax
        if (buffers->buffer[x].available == 0) {
    6446:	31 db                	xor    %ebx,%ebx
    6448:	eb 12                	jmp    645c <io_thread+0x39c>
    644a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    6450:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    6457:	48 39 c3             	cmp    %rax,%rbx
    645a:	74 ea                	je     6446 <io_thread+0x386>
        if (buffers->buffer[x].available == 1) {
    645c:	83 bc 19 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx,%rbx,1)
    6464:	75 ea                	jne    6450 <io_thread+0x390>
    6466:	44 8b 84 19 98 00 00 00 	mov    0x98(%rcx,%rbx,1),%r8d
    646e:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    6475:	31 c0                	xor    %eax,%eax
    6477:	4c 89 e1             	mov    %r12,%rcx
    647a:	48 8d 35 38 2d 00 00 	lea    0x2d38(%rip),%rsi        # 91b9 <_IO_stdin_used+0x1b9>
    6481:	bf 01 00 00 00       	mov    $0x1,%edi
    6486:	e8 35 c0 ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    648b:	49 03 5d 08          	add    0x8(%r13),%rbx
    648f:	83 bb 98 00 00 00 02 	cmpl   $0x2,0x98(%rbx)
    6496:	75 90                	jne    6428 <io_thread+0x368>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6498:	be 00 01 00 00       	mov    $0x100,%esi
    649d:	bf 01 00 00 00       	mov    $0x1,%edi
    64a2:	e8 69 bf ff ff       	call   2410 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    64a7:	48 8b 13             	mov    (%rbx),%rdx
            buffers->buffer[x].available = 0;
    64aa:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
            reply->kind = buffers->buffer[x].kind;
    64b4:	c7 80 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%rax)
            reply->data = buffers->buffer[x].data;
    64be:	48 89 10             	mov    %rdx,(%rax)
    struct NewClientMessage *newclientmsg = newclient->data;
    64c1:	48 8b 18             	mov    (%rax),%rbx
    64c4:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    64cb:	48 8d 35 ee 33 00 00 	lea    0x33ee(%rip),%rsi        # 98c0 <_IO_stdin_used+0x8c0>
    64d2:	31 c0                	xor    %eax,%eax
    64d4:	bf 01 00 00 00       	mov    $0x1,%edi
    64d9:	8b 0b                	mov    (%rbx),%ecx
    64db:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    64e0:	e8 db bf ff ff       	call   24c0 <__printf_chk@plt>
    ev.data.fd = newclientmsg->socket;
    64e5:	8b 03                	mov    (%rbx),%eax
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    64e7:	bf 01 00 00 00       	mov    $0x1,%edi
    64ec:	be 10 00 00 00       	mov    $0x10,%esi
    ev.events = EPOLLOUT;
    64f1:	c7 44 24 64 04 00 00 00 	movl   $0x4,0x64(%rsp)
    ev.data.fd = newclientmsg->socket;
    64f9:	89 44 24 68          	mov    %eax,0x68(%rsp)
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    64fd:	e8 0e bf ff ff       	call   2410 <calloc@plt>
    void *buf = malloc(size);
    6502:	bf 0a 00 00 00       	mov    $0xa,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    6507:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    void *buf = malloc(size);
    650c:	e8 6f bf ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    6511:	48 85 c0             	test   %rax,%rax
    6514:	0f 84 d5 0e 00 00    	je     73ef <io_thread+0x132f>
    iov->iov_base = zh_malloc(10);
    651a:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    651f:	bf 01 00 00 00       	mov    $0x1,%edi
    iov->iov_base = zh_malloc(10);
    6524:	48 89 06             	mov    %rax,(%rsi)
    iov->iov_len = 10;
    6527:	48 c7 46 08 0a 00 00 00 	movq   $0xa,0x8(%rsi)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    652f:	be 10 00 00 00       	mov    $0x10,%esi
    6534:	e8 d7 be ff ff       	call   2410 <calloc@plt>
    struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    6539:	be 10 00 00 00       	mov    $0x10,%esi
    653e:	bf 01 00 00 00       	mov    $0x1,%edi
    eventfdstop->kind = 3; 
    6543:	c7 00 03 00 00 00    	movl   $0x3,(%rax)
    struct SendUserData *eventfdstop = calloc(1, sizeof(struct SendUserData));
    6549:	49 89 c4             	mov    %rax,%r12
    struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    654c:	e8 bf be ff ff       	call   2410 <calloc@plt>
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    6551:	be 10 00 00 00       	mov    $0x10,%esi
    6556:	bf 01 00 00 00       	mov    $0x1,%edi
    readywriting->kind = 4; 
    655b:	c7 00 04 00 00 00    	movl   $0x4,(%rax)
    struct SendUserData *readywriting = calloc(1, sizeof(struct SendUserData));
    6561:	49 89 c5             	mov    %rax,%r13
    struct SendUserData *removed = calloc(1, sizeof(struct SendUserData));
    6564:	e8 a7 be ff ff       	call   2410 <calloc@plt>
	if (ring->flags & IORING_SETUP_SQE128)
    6569:	8b 94 24 50 01 00 00 	mov    0x150(%rsp),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    6570:	48 8b 8c 24 90 00 00 00 	mov    0x90(%rsp),%rcx
    6578:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    removed->kind = 7; 
    657d:	c7 00 07 00 00 00    	movl   $0x7,(%rax)
	unsigned int head, next = sq->sqe_tail + 1;
    6583:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    658a:	8b 31                	mov    (%rcx),%esi
	unsigned int head, next = sq->sqe_tail + 1;
    658c:	83 c0 01             	add    $0x1,%eax
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    658f:	f6 c2 02             	test   $0x2,%dl
    6592:	74 00                	je     6594 <io_thread+0x4d4>
	if (next - head <= sq->ring_entries) {
    6594:	89 c1                	mov    %eax,%ecx
    6596:	29 f1                	sub    %esi,%ecx
    6598:	39 8c 24 ec 00 00 00 	cmp    %ecx,0xec(%rsp)
    659f:	0f 82 fa c0 ff ff    	jb     269f <io_thread.cold+0x89>
	if (ring->flags & IORING_SETUP_SQE128)
    65a5:	c1 ea 0a             	shr    $0xa,%edx
	sqe->fd = fd;
    65a8:	8b 5c 24 10          	mov    0x10(%rsp),%ebx
          io_uring_submit(&ring);
    65ac:	4c 8b 34 24          	mov    (%rsp),%r14
	sqe->addr3 = 0;
    65b0:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    65b4:	8b b4 24 d4 00 00 00 	mov    0xd4(%rsp),%esi
	if (ring->flags & IORING_SETUP_SQE128)
    65bb:	83 e2 01             	and    $0x1,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    65be:	23 b4 24 e8 00 00 00 	and    0xe8(%rsp),%esi
		sq->sqe_tail = next;
    65c5:	89 84 24 d4 00 00 00 	mov    %eax,0xd4(%rsp)
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    65cc:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
	if (ring->flags & IORING_SETUP_SQE128)
    65d1:	89 d1                	mov    %edx,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    65d3:	41 89 f7             	mov    %esi,%r15d
    65d6:	4c 89 f7             	mov    %r14,%rdi
    65d9:	41 d3 e7             	shl    %cl,%r15d
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    65dc:	8b 00                	mov    (%rax),%eax
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    65de:	49 c1 e7 06          	shl    $0x6,%r15
    65e2:	4c 03 bc 24 c8 00 00 00 	add    0xc8(%rsp),%r15
	sqe->opcode = (__u8) op;
    65ea:	41 c7 07 1d 00 00 00 	movl   $0x1d,(%r15)
	sqe->off = offset;
    65f1:	49 89 47 08          	mov    %rax,0x8(%r15)
	sqe->addr = (unsigned long) addr;
    65f5:	48 8d 44 24 64       	lea    0x64(%rsp),%rax
	sqe->fd = fd;
    65fa:	41 89 5f 04          	mov    %ebx,0x4(%r15)
	sqe->addr = (unsigned long) addr;
    65fe:	49 89 47 10          	mov    %rax,0x10(%r15)
	sqe->len = len;
    6602:	49 c7 47 18 01 00 00 00 	movq   $0x1,0x18(%r15)
	sqe->buf_index = 0;
    660a:	49 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%r15)
	sqe->user_data = (unsigned long) data;
    6612:	4d 89 6f 20          	mov    %r13,0x20(%r15)
	sqe->addr3 = 0;
    6616:	41 0f 11 47 30       	movups %xmm0,0x30(%r15)
	sqe->addr = (unsigned long) addr;
    661b:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    6620:	e8 7b bd ff ff       	call   23a0 <io_uring_submit@plt>
	sqe->fd = fd;
    6625:	41 89 5f 04          	mov    %ebx,0x4(%r15)
	sqe->addr3 = 0;
    6629:	66 0f ef c0          	pxor   %xmm0,%xmm0
          io_uring_submit(&ring);
    662d:	4c 89 f7             	mov    %r14,%rdi
	sqe->addr = (unsigned long) addr;
    6630:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
	sqe->opcode = (__u8) op;
    6635:	41 c7 07 01 00 00 00 	movl   $0x1,(%r15)
	sqe->off = offset;
    663c:	49 c7 47 08 00 00 00 00 	movq   $0x0,0x8(%r15)
	sqe->addr = (unsigned long) addr;
    6644:	49 89 47 10          	mov    %rax,0x10(%r15)
	sqe->len = len;
    6648:	49 c7 47 18 01 00 00 00 	movq   $0x1,0x18(%r15)
	sqe->buf_index = 0;
    6650:	49 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%r15)
	sqe->user_data = (unsigned long) data;
    6658:	4d 89 6f 20          	mov    %r13,0x20(%r15)
	sqe->addr3 = 0;
    665c:	41 0f 11 47 30       	movups %xmm0,0x30(%r15)
    6661:	e8 3a bd ff ff       	call   23a0 <io_uring_submit@plt>
    while (data->running == 1) {
    6666:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    666a:	0f 85 88 01 00 00    	jne    67f8 <io_thread+0x738>
	if (ring->flags & IORING_SETUP_CQE32)
    6670:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    6677:	8b bc 24 40 01 00 00 	mov    0x140(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    667e:	c1 e9 0b             	shr    $0xb,%ecx
    6681:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    6684:	48 8b 84 24 00 01 00 00 	mov    0x100(%rsp),%rax
    668c:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    668e:	48 8b b4 24 f8 00 00 00 	mov    0xf8(%rsp),%rsi
    6696:	8b 16                	mov    (%rsi),%edx
		if (!available)
    6698:	39 d0                	cmp    %edx,%eax
    669a:	74 36                	je     66d2 <io_thread+0x612>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    669c:	89 f8                	mov    %edi,%eax
    669e:	21 d0                	and    %edx,%eax
    66a0:	d3 e0                	shl    %cl,%eax
    66a2:	48 c1 e0 04          	shl    $0x4,%rax
    66a6:	48 03 84 24 28 01 00 00 	add    0x128(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    66ae:	f6 84 24 59 01 00 00 01 	testb  $0x1,0x159(%rsp)
    66b6:	0f 85 7c 01 00 00    	jne    6838 <io_thread+0x778>
    66bc:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    66c0:	0f 85 c5 04 00 00    	jne    6b8b <io_thread+0xacb>
			if (cqe->res < 0)
    66c6:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    66c9:	83 c2 01             	add    $0x1,%edx
    66cc:	89 16                	mov    %edx,(%rsi)
			if (!err)
    66ce:	85 c0                	test   %eax,%eax
    66d0:	79 b2                	jns    6684 <io_thread+0x5c4>
	*cqe_ptr = cqe;
    66d2:	48 c7 44 24 58 00 00 00 00 	movq   $0x0,0x58(%rsp)
	return err;
    66db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    66e0:	48 8b 3c 24          	mov    (%rsp),%rdi
    66e4:	48 8d 74 24 58       	lea    0x58(%rsp),%rsi
    66e9:	45 31 c0             	xor    %r8d,%r8d
    66ec:	31 d2                	xor    %edx,%edx
    66ee:	b9 01 00 00 00       	mov    $0x1,%ecx
    66f3:	e8 b8 bd ff ff       	call   24b0 <__io_uring_get_cqe@plt>
    66f8:	89 c3                	mov    %eax,%ebx
        printf("kind %d\n", ((struct SendUserData*) cqe->user_data)->kind);
    66fa:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    66ff:	48 8b 00             	mov    (%rax),%rax
    6702:	48 8d 35 a7 2b 00 00 	lea    0x2ba7(%rip),%rsi        # 92b0 <_IO_stdin_used+0x2b0>
    6709:	bf 01 00 00 00       	mov    $0x1,%edi
    670e:	8b 10                	mov    (%rax),%edx
    6710:	31 c0                	xor    %eax,%eax
    6712:	e8 a9 bd ff ff       	call   24c0 <__printf_chk@plt>
        if (((struct SendUserData*) cqe->user_data)->kind == eventfdstop->kind) {
    6717:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    671c:	48 8b 10             	mov    (%rax),%rdx
    671f:	8b 02                	mov    (%rdx),%eax
    6721:	41 3b 04 24          	cmp    (%r12),%eax
    6725:	0f 84 6c 04 00 00    	je     6b97 <io_thread+0xad7>
        if (((struct SendUserData*) cqe->user_data)->kind == readywriting->kind) {
    672b:	41 3b 45 00          	cmp    0x0(%r13),%eax
    672f:	0f 84 1b 01 00 00    	je     6850 <io_thread+0x790>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
    6735:	83 f8 05             	cmp    $0x5,%eax
    6738:	0f 84 d2 02 00 00    	je     6a10 <io_thread+0x950>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    673e:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
    6746:	8b 02                	mov    (%rdx),%eax
    6748:	83 c0 01             	add    $0x1,%eax
    674b:	89 02                	mov    %eax,(%rdx)
	unsigned int head, next = sq->sqe_tail + 1;
    674d:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6754:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    675b:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    675e:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
    6766:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6768:	f6 c1 02             	test   $0x2,%cl
    676b:	74 00                	je     676d <io_thread+0x6ad>
	if (next - head <= sq->ring_entries) {
    676d:	89 d0                	mov    %edx,%eax
    676f:	29 f0                	sub    %esi,%eax
    6771:	39 84 24 ec 00 00 00 	cmp    %eax,0xec(%rsp)
    6778:	0f 82 d2 be ff ff    	jb     2650 <io_thread.cold+0x3a>
	if (ring->flags & IORING_SETUP_SQE128)
    677e:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->addr = (unsigned long) addr;
    6781:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    6786:	66 0f ef c0          	pxor   %xmm0,%xmm0
          io_uring_submit(&ring);
    678a:	48 8b 3c 24          	mov    (%rsp),%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    678e:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6795:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6798:	23 84 24 e8 00 00 00 	and    0xe8(%rsp),%eax
		sq->sqe_tail = next;
    679f:	89 94 24 d4 00 00 00 	mov    %edx,0xd4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    67a6:	d3 e0                	shl    %cl,%eax
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    67a8:	8b 55 68             	mov    0x68(%rbp),%edx
    67ab:	48 c1 e0 06          	shl    $0x6,%rax
    67af:	48 03 84 24 c8 00 00 00 	add    0xc8(%rsp),%rax
	sqe->opcode = (__u8) op;
    67b7:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    67bd:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    67c0:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    67c8:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    67cc:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    67d4:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    67dc:	4c 89 60 20          	mov    %r12,0x20(%rax)
	sqe->addr3 = 0;
    67e0:	0f 11 40 30          	movups %xmm0,0x30(%rax)
          io_uring_submit(&ring);
    67e4:	e8 b7 bb ff ff       	call   23a0 <io_uring_submit@plt>
    while (data->running == 1) {
    67e9:	8b 45 44             	mov    0x44(%rbp),%eax
    67ec:	83 f8 01             	cmp    $0x1,%eax
    67ef:	0f 84 7b fe ff ff    	je     6670 <io_thread+0x5b0>
    67f5:	0f 1f 00             	nopl   (%rax)
    67f8:	48 8d 3d ec 2a 00 00 	lea    0x2aec(%rip),%rdi        # 92eb <_IO_stdin_used+0x2eb>
    67ff:	e8 3c bb ff ff       	call   2340 <puts@plt>
}
    6804:	48 8b 84 24 78 05 00 00 	mov    0x578(%rsp),%rax
    680c:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    6815:	0f 85 31 0c 00 00    	jne    744c <io_thread+0x138c>
    681b:	48 81 c4 88 05 00 00 	add    $0x588,%rsp
    6822:	31 c0                	xor    %eax,%eax
    6824:	5b                   	pop    %rbx
    6825:	5d                   	pop    %rbp
    6826:	41 5c                	pop    %r12
    6828:	41 5d                	pop    %r13
    682a:	41 5e                	pop    %r14
    682c:	41 5f                	pop    %r15
    682e:	c3                   	ret
      for (int x = 0 ; x < buffers->count ; x++) {
    682f:	eb fe                	jmp    682f <io_thread+0x76f>
    6831:	eb fe                	jmp    6831 <io_thread+0x771>
    6833:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    6838:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    683d:	48 85 c0             	test   %rax,%rax
    6840:	0f 84 9a fe ff ff    	je     66e0 <io_thread+0x620>
		return 0;
    6846:	31 db                	xor    %ebx,%ebx
    6848:	e9 b2 fe ff ff       	jmp    66ff <io_thread+0x63f>
    684d:	0f 1f 00             	nopl   (%rax)
          struct Buffer *send = bufferrecv("write", data, &data->iomailboxes[data->my_io], IO_WRITE, &_send, 1);
    6850:	4c 63 8d 14 01 00 00 	movslq 0x114(%rbp),%r9
    6857:	49 c1 e1 04          	shl    $0x4,%r9
    685b:	4c 03 8d 08 01 00 00 	add    0x108(%rbp),%r9
  while (data->running == 1) {
    6862:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    6866:	75 90                	jne    67f8 <io_thread+0x738>
      for (int x = 0 ; x < buffers->count ; x++) {
    6868:	49 63 01             	movslq (%r9),%rax
    686b:	85 c0                	test   %eax,%eax
    686d:	0f 8e fd fd ff ff    	jle    6670 <io_thread+0x5b0>
        if (buffers->buffer[x].available == 1) {
    6873:	49 8b 49 08          	mov    0x8(%r9),%rcx
    6877:	48 c1 e0 08          	shl    $0x8,%rax
    687b:	45 31 f6             	xor    %r14d,%r14d
    687e:	eb 10                	jmp    6890 <io_thread+0x7d0>
      for (int x = 0 ; x < buffers->count ; x++) {
    6880:	49 81 c6 00 01 00 00 	add    $0x100,%r14
    6887:	49 39 c6             	cmp    %rax,%r14
    688a:	0f 84 e0 fd ff ff    	je     6670 <io_thread+0x5b0>
        if (buffers->buffer[x].available == 1) {
    6890:	42 83 bc 31 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx,%r14,1)
    6899:	75 e5                	jne    6880 <io_thread+0x7c0>
    689b:	46 8b 84 31 98 00 00 00 	mov    0x98(%rcx,%r14,1),%r8d
    68a3:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    68aa:	31 c0                	xor    %eax,%eax
    68ac:	48 8d 0d 10 2a 00 00 	lea    0x2a10(%rip),%rcx        # 92c3 <_IO_stdin_used+0x2c3>
    68b3:	48 8d 35 ff 28 00 00 	lea    0x28ff(%rip),%rsi        # 91b9 <_IO_stdin_used+0x1b9>
    68ba:	bf 01 00 00 00       	mov    $0x1,%edi
    68bf:	4c 89 4c 24 18       	mov    %r9,0x18(%rsp)
    68c4:	e8 f7 bb ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    68c9:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    68ce:	4d 03 71 08          	add    0x8(%r9),%r14
    68d2:	41 83 be 98 00 00 00 02 	cmpl   $0x2,0x98(%r14)
    68da:	0f 85 09 ff ff ff    	jne    67e9 <io_thread+0x729>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    68e0:	be 00 01 00 00       	mov    $0x100,%esi
    68e5:	bf 01 00 00 00       	mov    $0x1,%edi
    68ea:	e8 21 bb ff ff       	call   2410 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    68ef:	49 8b 16             	mov    (%r14),%rdx
            buffers->buffer[x].available = 0;
    68f2:	41 c7 86 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r14)
            reply->kind = buffers->buffer[x].kind;
    68fd:	c7 80 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%rax)
            reply->data = buffers->buffer[x].data;
    6907:	48 89 10             	mov    %rdx,(%rax)
	unsigned int head, next = sq->sqe_tail + 1;
    690a:	8b b4 24 d4 00 00 00 	mov    0xd4(%rsp),%esi
	if (ring->flags & IORING_SETUP_SQE128)
    6911:	8b 94 24 50 01 00 00 	mov    0x150(%rsp),%edx
          struct Write *write = send->data;
    6918:	48 8b 00             	mov    (%rax),%rax
	unsigned int head, next = sq->sqe_tail + 1;
    691b:	83 c6 01             	add    $0x1,%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    691e:	f6 c2 02             	test   $0x2,%dl
    6921:	0f 85 29 02 00 00    	jne    6b50 <io_thread+0xa90>
		head = IO_URING_READ_ONCE(*sq->khead);
    6927:	48 8b 8c 24 90 00 00 00 	mov    0x90(%rsp),%rcx
    692f:	8b 09                	mov    (%rcx),%ecx
          struct Request *req = write->request;
    6931:	4c 8b 00             	mov    (%rax),%r8
	if (next - head <= sq->ring_entries) {
    6934:	89 f0                	mov    %esi,%eax
    6936:	29 c8                	sub    %ecx,%eax
    6938:	39 84 24 ec 00 00 00 	cmp    %eax,0xec(%rsp)
    693f:	0f 82 15 bd ff ff    	jb     265a <io_thread.cold+0x44>
	if (ring->flags & IORING_SETUP_SQE128)
    6945:	c1 ea 0a             	shr    $0xa,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6948:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	sqe->addr3 = 0;
    694f:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6953:	23 84 24 e8 00 00 00 	and    0xe8(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    695a:	83 e2 01             	and    $0x1,%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    695d:	41 89 c6             	mov    %eax,%r14d
          io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    6960:	41 8b 40 04          	mov    0x4(%r8),%eax
          struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    6964:	bf 01 00 00 00       	mov    $0x1,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    6969:	89 d1                	mov    %edx,%ecx
          io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    696b:	41 8b 50 08          	mov    0x8(%r8),%edx
    696f:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6974:	41 d3 e6             	shl    %cl,%r14d
		sq->sqe_tail = next;
    6977:	89 b4 24 d4 00 00 00 	mov    %esi,0xd4(%rsp)
          struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    697e:	be 10 00 00 00       	mov    $0x10,%esi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6983:	49 c1 e6 06          	shl    $0x6,%r14
    6987:	4c 03 b4 24 c8 00 00 00 	add    0xc8(%rsp),%r14
          req->event_type = EVENT_TYPE_WRITE;
    698f:	41 c7 00 02 00 00 00 	movl   $0x2,(%r8)
	sqe->fd = fd;
    6996:	41 89 56 04          	mov    %edx,0x4(%r14)
          io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    699a:	49 8d 50 10          	lea    0x10(%r8),%rdx
    699e:	49 89 56 10          	mov    %rdx,0x10(%r14)
	sqe->opcode = (__u8) op;
    69a2:	41 c7 06 02 00 00 00 	movl   $0x2,(%r14)
	sqe->off = offset;
    69a9:	49 c7 46 08 00 00 00 00 	movq   $0x0,0x8(%r14)
	sqe->len = len;
    69b1:	41 89 46 18          	mov    %eax,0x18(%r14)
	sqe->rw_flags = 0;
    69b5:	41 c7 46 1c 00 00 00 00 	movl   $0x0,0x1c(%r14)
	sqe->buf_index = 0;
    69bd:	49 c7 46 28 00 00 00 00 	movq   $0x0,0x28(%r14)
	sqe->addr3 = 0;
    69c5:	41 0f 11 46 30       	movups %xmm0,0x30(%r14)
          struct SendUserData *finishedwrite = calloc(1, sizeof(struct SendUserData));
    69ca:	e8 41 ba ff ff       	call   2410 <calloc@plt>
          readywriting->data = req;
    69cf:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
          io_uring_submit(&ring);
    69d4:	48 8b 3c 24          	mov    (%rsp),%rdi
          readywriting->kind = 5; 
    69d8:	41 c7 45 00 05 00 00 00 	movl   $0x5,0x0(%r13)
          readywriting->data = req;
    69e0:	4d 89 45 08          	mov    %r8,0x8(%r13)
	sqe->user_data = (unsigned long) data;
    69e4:	49 89 46 20          	mov    %rax,0x20(%r14)
          io_uring_submit(&ring);
    69e8:	e8 b3 b9 ff ff       	call   23a0 <io_uring_submit@plt>
    69ed:	48 8d 3d c5 28 00 00 	lea    0x28c5(%rip),%rdi        # 92b9 <_IO_stdin_used+0x2b9>
    69f4:	e8 47 b9 ff ff       	call   2340 <puts@plt>
        if (((struct SendUserData*) cqe->user_data)->kind == 5) { 
    69f9:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    69fe:	48 8b 10             	mov    (%rax),%rdx
    6a01:	8b 02                	mov    (%rdx),%eax
    6a03:	83 f8 05             	cmp    $0x5,%eax
    6a06:	0f 85 32 fd ff ff    	jne    673e <io_thread+0x67e>
    6a0c:	0f 1f 40 00          	nopl   0x0(%rax)
    6a10:	48 8d 35 b2 28 00 00 	lea    0x28b2(%rip),%rsi        # 92c9 <_IO_stdin_used+0x2c9>
    6a17:	bf 01 00 00 00       	mov    $0x1,%edi
    6a1c:	31 c0                	xor    %eax,%eax
    6a1e:	e8 9d ba ff ff       	call   24c0 <__printf_chk@plt>
    6a23:	48 8d 3d ab 28 00 00 	lea    0x28ab(%rip),%rdi        # 92d5 <_IO_stdin_used+0x2d5>
    6a2a:	e8 11 b9 ff ff       	call   2340 <puts@plt>
          io_uring_cqe_seen(&ring, cqe);
    6a2f:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
	if (cqe)
    6a34:	48 85 c0             	test   %rax,%rax
    6a37:	74 14                	je     6a4d <io_thread+0x98d>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6a39:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
    6a41:	8b 02                	mov    (%rdx),%eax
    6a43:	83 c0 01             	add    $0x1,%eax
    6a46:	89 02                	mov    %eax,(%rdx)
          struct Request *req = ((struct SendUserData *) cqe->user_data)->data;
    6a48:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    6a4d:	48 8b 10             	mov    (%rax),%rdx
    6a50:	4c 8b 72 08          	mov    0x8(%rdx),%r14
          if (ret < 0)
    6a54:	85 db                	test   %ebx,%ebx
    6a56:	0f 88 4d bc ff ff    	js     26a9 <io_thread.cold+0x93>
    6a5c:	8b 50 08             	mov    0x8(%rax),%edx
    6a5f:	48 8d 35 82 28 00 00 	lea    0x2882(%rip),%rsi        # 92e8 <_IO_stdin_used+0x2e8>
    6a66:	bf 01 00 00 00       	mov    $0x1,%edi
    6a6b:	31 c0                	xor    %eax,%eax
    6a6d:	e8 4e ba ff ff       	call   24c0 <__printf_chk@plt>
          if (cqe->res < 0) {
    6a72:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    6a77:	8b 50 08             	mov    0x8(%rax),%edx
    6a7a:	85 d2                	test   %edx,%edx
    6a7c:	0f 88 94 09 00 00    	js     7416 <io_thread+0x1356>
          switch (req->event_type) {
    6a82:	41 8b 06             	mov    (%r14),%eax
    6a85:	83 f8 01             	cmp    $0x1,%eax
    6a88:	0f 84 d1 00 00 00    	je     6b5f <io_thread+0xa9f>
    6a8e:	83 f8 02             	cmp    $0x2,%eax
    6a91:	0f 85 a7 fc ff ff    	jne    673e <io_thread+0x67e>
                  for (int i = 0; i < req->iovec_count; i++) {
    6a97:	41 8b 46 04          	mov    0x4(%r14),%eax
    6a9b:	31 db                	xor    %ebx,%ebx
    6a9d:	85 c0                	test   %eax,%eax
    6a9f:	7e 22                	jle    6ac3 <io_thread+0xa03>
    6aa1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                      free(req->iov[i].iov_base);
    6aa8:	48 89 d8             	mov    %rbx,%rax
                  for (int i = 0; i < req->iovec_count; i++) {
    6aab:	48 83 c3 01          	add    $0x1,%rbx
                      free(req->iov[i].iov_base);
    6aaf:	48 c1 e0 04          	shl    $0x4,%rax
    6ab3:	49 8b 7c 06 10       	mov    0x10(%r14,%rax,1),%rdi
    6ab8:	e8 53 b8 ff ff       	call   2310 <free@plt>
                  for (int i = 0; i < req->iovec_count; i++) {
    6abd:	41 39 5e 04          	cmp    %ebx,0x4(%r14)
    6ac1:	7f e5                	jg     6aa8 <io_thread+0x9e8>
                  close(req->client_socket);
    6ac3:	41 8b 7e 08          	mov    0x8(%r14),%edi
    6ac7:	e8 14 b9 ff ff       	call   23e0 <close@plt>
                  free(req);
    6acc:	4c 89 f7             	mov    %r14,%rdi
    6acf:	e8 3c b8 ff ff       	call   2310 <free@plt>
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6ad4:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
	sqe->fd = fd;
    6ad9:	8b 7c 24 10          	mov    0x10(%rsp),%edi
	sqe->addr3 = 0;
    6add:	66 0f ef c0          	pxor   %xmm0,%xmm0
	io_uring_prep_rw(IORING_OP_EPOLL_CTL, sqe, epfd, ev,
    6ae1:	8b 00                	mov    (%rax),%eax
	sqe->fd = fd;
    6ae3:	41 89 7f 04          	mov    %edi,0x4(%r15)
	sqe->opcode = (__u8) op;
    6ae7:	41 c7 07 1d 00 00 00 	movl   $0x1d,(%r15)
                  io_uring_submit(&ring);
    6aee:	48 8b 3c 24          	mov    (%rsp),%rdi
	sqe->off = offset;
    6af2:	49 89 47 08          	mov    %rax,0x8(%r15)
	sqe->addr = (unsigned long) addr;
    6af6:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
	sqe->len = len;
    6afb:	49 c7 47 18 02 00 00 00 	movq   $0x2,0x18(%r15)
	sqe->addr = (unsigned long) addr;
    6b03:	49 89 47 10          	mov    %rax,0x10(%r15)
	sqe->user_data = (unsigned long) data;
    6b07:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
	sqe->buf_index = 0;
    6b0c:	49 c7 47 28 00 00 00 00 	movq   $0x0,0x28(%r15)
	sqe->user_data = (unsigned long) data;
    6b14:	49 89 47 20          	mov    %rax,0x20(%r15)
	sqe->addr3 = 0;
    6b18:	41 0f 11 47 30       	movups %xmm0,0x30(%r15)
    6b1d:	e8 7e b8 ff ff       	call   23a0 <io_uring_submit@plt>
          io_uring_cqe_seen(&ring, cqe);
    6b22:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
	if (cqe)
    6b27:	48 85 c0             	test   %rax,%rax
    6b2a:	0f 84 1d fc ff ff    	je     674d <io_thread+0x68d>
    6b30:	e9 09 fc ff ff       	jmp    673e <io_thread+0x67e>
    6b35:	0f 1f 00             	nopl   (%rax)
  while (data->running == 1) {
    6b38:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    6b3c:	0f 84 1f f8 ff ff    	je     6361 <io_thread+0x2a1>
    6b42:	e9 90 f8 ff ff       	jmp    63d7 <io_thread+0x317>
    6b47:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    6b50:	48 8b 8c 24 90 00 00 00 	mov    0x90(%rsp),%rcx
    6b58:	8b 09                	mov    (%rcx),%ecx
    6b5a:	e9 d2 fd ff ff       	jmp    6931 <io_thread+0x871>
                  if (!cqe->res) {
    6b5f:	85 d2                	test   %edx,%edx
    6b61:	0f 85 83 06 00 00    	jne    71ea <io_thread+0x112a>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    6b67:	48 8b 0d b2 54 00 00 	mov    0x54b2(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    6b6e:	ba 0f 00 00 00       	mov    $0xf,%edx
    6b73:	be 01 00 00 00       	mov    $0x1,%esi
    6b78:	48 8d 3d bc 26 00 00 	lea    0x26bc(%rip),%rdi        # 923b <_IO_stdin_used+0x23b>
    6b7f:	e8 bc b9 ff ff       	call   2540 <fwrite@plt>
          io_uring_cqe_seen(&ring, cqe);
    6b84:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    6b89:	eb 9c                	jmp    6b27 <io_thread+0xa67>
	*cqe_ptr = cqe;
    6b8b:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
		return 0;
    6b90:	31 db                	xor    %ebx,%ebx
    6b92:	e9 68 fb ff ff       	jmp    66ff <io_thread+0x63f>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6b97:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6b9f:	48 8d 3d 3a 26 00 00 	lea    0x263a(%rip),%rdi        # 91e0 <_IO_stdin_used+0x1e0>
    6ba6:	8b 02                	mov    (%rdx),%eax
    6ba8:	83 c0 01             	add    $0x1,%eax
    6bab:	89 02                	mov    %eax,(%rdx)
    6bad:	e8 8e b7 ff ff       	call   2340 <puts@plt>
    6bb2:	e9 41 fc ff ff       	jmp    67f8 <io_thread+0x738>
    sock = socket(PF_INET, SOCK_STREAM, 0);
    6bb7:	31 d2                	xor    %edx,%edx
    6bb9:	be 01 00 00 00       	mov    $0x1,%esi
    6bbe:	bf 02 00 00 00       	mov    $0x2,%edi
    6bc3:	e8 08 ba ff ff       	call   25d0 <socket@plt>
    6bc8:	89 c3                	mov    %eax,%ebx
    if (sock == -1)
    6bca:	83 f8 ff             	cmp    $0xffffffff,%eax
    6bcd:	0f 84 4d ba ff ff    	je     2620 <io_thread.cold+0xa>
    if (setsockopt(sock,
    6bd3:	48 8d 4c 24 48       	lea    0x48(%rsp),%rcx
    6bd8:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    6bde:	ba 02 00 00 00       	mov    $0x2,%edx
    6be3:	89 c7                	mov    %eax,%edi
    6be5:	be 01 00 00 00       	mov    $0x1,%esi
    int enable = 1;
    6bea:	c7 44 24 48 01 00 00 00 	movl   $0x1,0x48(%rsp)
    if (setsockopt(sock,
    6bf2:	e8 59 b7 ff ff       	call   2350 <setsockopt@plt>
    6bf7:	85 c0                	test   %eax,%eax
    6bf9:	0f 88 2d ba ff ff    	js     262c <io_thread.cold+0x16>
  return __builtin___memset_chk (__dest, __ch, __len,
    6bff:	48 8d 74 24 70       	lea    0x70(%rsp),%rsi
    if (bind(sock,
    6c04:	ba 10 00 00 00       	mov    $0x10,%edx
    6c09:	89 df                	mov    %ebx,%edi
    6c0b:	48 c7 44 24 74 00 00 00 00 	movq   $0x0,0x74(%rsp)
    6c14:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
    srv_addr.sin_family = AF_INET;
    6c1c:	c7 44 24 70 02 00 18 db 	movl   $0xdb180002,0x70(%rsp)
    if (bind(sock,
    6c24:	e8 a7 b8 ff ff       	call   24d0 <bind@plt>
    6c29:	85 c0                	test   %eax,%eax
    6c2b:	0f 88 07 ba ff ff    	js     2638 <io_thread.cold+0x22>
    if (listen(sock, 10) < 0) {
    6c31:	be 0a 00 00 00       	mov    $0xa,%esi
    6c36:	89 df                	mov    %ebx,%edi
    6c38:	e8 53 b8 ff ff       	call   2490 <listen@plt>
    6c3d:	85 c0                	test   %eax,%eax
    6c3f:	0f 88 ff b9 ff ff    	js     2644 <io_thread.cold+0x2e>
    6c45:	89 d9                	mov    %ebx,%ecx
    6c47:	ba db 18 00 00       	mov    $0x18db,%edx
    6c4c:	48 8d 35 b5 2a 00 00 	lea    0x2ab5(%rip),%rsi        # 9708 <_IO_stdin_used+0x708>
    6c53:	31 c0                	xor    %eax,%eax
    6c55:	bf 01 00 00 00       	mov    $0x1,%edi
    6c5a:	e8 61 b8 ff ff       	call   24c0 <__printf_chk@plt>
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    6c5f:	be 04 00 00 00       	mov    $0x4,%esi
    6c64:	bf 01 00 00 00       	mov    $0x1,%edi
    6c69:	e8 a2 b7 ff ff       	call   2410 <calloc@plt>
    6c6e:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    6c75:	bf 01 00 00 00       	mov    $0x1,%edi
    6c7a:	48 8d 35 a7 2a 00 00 	lea    0x2aa7(%rip),%rsi        # 9728 <_IO_stdin_used+0x728>
    msg->socket = sock;
    6c81:	89 18                	mov    %ebx,(%rax)
    struct NewSocketMessage *msg = calloc(1, sizeof(struct NewSocketMessage));
    6c83:	49 89 c5             	mov    %rax,%r13
    6c86:	31 c0                	xor    %eax,%eax
    6c88:	e8 33 b8 ff ff       	call   24c0 <__printf_chk@plt>
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET, msg);
    6c8d:	4c 63 b5 10 01 00 00 	movslq 0x110(%rbp),%r14
    6c94:	4c 8b bd 08 01 00 00 	mov    0x108(%rbp),%r15
  while (data->running == 1) {
    6c9b:	8b 45 44             	mov    0x44(%rbp),%eax
    buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_SOCKET, msg);
    6c9e:	49 c1 e6 04          	shl    $0x4,%r14
    6ca2:	4d 01 fe             	add    %r15,%r14
  while (data->running == 1) {
    6ca5:	83 f8 01             	cmp    $0x1,%eax
    6ca8:	0f 85 8b 00 00 00    	jne    6d39 <io_thread+0xc79>
      for (int x = 0 ; x < buffers->count ; x++) {
    6cae:	49 63 06             	movslq (%r14),%rax
    6cb1:	85 c0                	test   %eax,%eax
    6cb3:	0f 8e 08 06 00 00    	jle    72c1 <io_thread+0x1201>
        if (buffers->buffer[x].available == 0) {
    6cb9:	49 8b 56 08          	mov    0x8(%r14),%rdx
    6cbd:	48 c1 e0 08          	shl    $0x8,%rax
    6cc1:	45 31 e4             	xor    %r12d,%r12d
    6cc4:	eb 1a                	jmp    6ce0 <io_thread+0xc20>
    6cc6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    6cd0:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    6cd7:	4c 39 e0             	cmp    %r12,%rax
    6cda:	0f 84 e1 05 00 00    	je     72c1 <io_thread+0x1201>
        if (buffers->buffer[x].available == 0) {
    6ce0:	46 8b 8c 22 80 00 00 00 	mov    0x80(%rdx,%r12,1),%r9d
    6ce8:	45 85 c9             	test   %r9d,%r9d
    6ceb:	75 e3                	jne    6cd0 <io_thread+0xc10>
    6ced:	42 8b 8c 22 98 00 00 00 	mov    0x98(%rdx,%r12,1),%ecx
    6cf5:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    6cfc:	bf 01 00 00 00       	mov    $0x1,%edi
    6d01:	31 c0                	xor    %eax,%eax
    6d03:	48 8d 35 08 24 00 00 	lea    0x2408(%rip),%rsi        # 9112 <_IO_stdin_used+0x112>
    6d0a:	e8 b1 b7 ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    6d0f:	4d 03 66 08          	add    0x8(%r14),%r12
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
    6d13:	4c 8b bd 08 01 00 00 	mov    0x108(%rbp),%r15
          buffers->buffer[x].data = send;
    6d1a:	4d 89 2c 24          	mov    %r13,(%r12)
  while (data->running == 1) {
    6d1e:	8b 45 44             	mov    0x44(%rbp),%eax
          buffers->buffer[x].kind = kind;
    6d21:	41 c7 84 24 98 00 00 00 00 00 00 00 	movl   $0x0,0x98(%r12)
          buffers->buffer[x].available = 1;
    6d2d:	41 c7 84 24 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r12)
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
    6d39:	48 63 95 14 01 00 00 	movslq 0x114(%rbp),%rdx
    6d40:	4c 8d 35 68 24 00 00 	lea    0x2468(%rip),%r14        # 91af <_IO_stdin_used+0x1af>
    6d47:	4c 8d 2d 6b 24 00 00 	lea    0x246b(%rip),%r13        # 91b9 <_IO_stdin_used+0x1b9>
    6d4e:	48 c1 e2 04          	shl    $0x4,%rdx
    6d52:	49 01 d7             	add    %rdx,%r15
  while (data->running == 1) {
    6d55:	0f 1f 00             	nopl   (%rax)
    6d58:	83 f8 01             	cmp    $0x1,%eax
    6d5b:	0f 85 97 00 00 00    	jne    6df8 <io_thread+0xd38>
      for (int x = 0 ; x < buffers->count ; x++) {
    6d61:	49 63 07             	movslq (%r15),%rax
    6d64:	85 c0                	test   %eax,%eax
    6d66:	7f 08                	jg     6d70 <io_thread+0xcb0>
    6d68:	eb fe                	jmp    6d68 <io_thread+0xca8>
    6d6a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        if (buffers->buffer[x].available == 1) {
    6d70:	49 8b 4f 08          	mov    0x8(%r15),%rcx
    6d74:	48 c1 e0 08          	shl    $0x8,%rax
        if (buffers->buffer[x].available == 0) {
    6d78:	45 31 e4             	xor    %r12d,%r12d
    6d7b:	eb 0f                	jmp    6d8c <io_thread+0xccc>
    6d7d:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    6d80:	49 81 c4 00 01 00 00 	add    $0x100,%r12
    6d87:	4c 39 e0             	cmp    %r12,%rax
    6d8a:	74 ec                	je     6d78 <io_thread+0xcb8>
        if (buffers->buffer[x].available == 1) {
    6d8c:	42 83 bc 21 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx,%r12,1)
    6d95:	75 e9                	jne    6d80 <io_thread+0xcc0>
    6d97:	46 8b 84 21 98 00 00 00 	mov    0x98(%rcx,%r12,1),%r8d
    6d9f:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    6da6:	31 c0                	xor    %eax,%eax
    6da8:	4c 89 f1             	mov    %r14,%rcx
    6dab:	4c 89 ee             	mov    %r13,%rsi
    6dae:	bf 01 00 00 00       	mov    $0x1,%edi
    6db3:	e8 08 b7 ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    6db8:	4d 03 67 08          	add    0x8(%r15),%r12
    6dbc:	41 83 bc 24 98 00 00 00 01 	cmpl   $0x1,0x98(%r12)
    6dc5:	74 05                	je     6dcc <io_thread+0xd0c>
  while (data->running == 1) {
    6dc7:	8b 45 44             	mov    0x44(%rbp),%eax
    6dca:	eb 8c                	jmp    6d58 <io_thread+0xc98>
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    6dcc:	be 00 01 00 00       	mov    $0x100,%esi
    6dd1:	bf 01 00 00 00       	mov    $0x1,%edi
    6dd6:	e8 35 b6 ff ff       	call   2410 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    6ddb:	49 8b 14 24          	mov    (%r12),%rdx
            buffers->buffer[x].available = 0;
    6ddf:	41 c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%r12)
            reply->kind = buffers->buffer[x].kind;
    6deb:	c7 80 98 00 00 00 01 00 00 00 	movl   $0x1,0x98(%rax)
            reply->data = buffers->buffer[x].data;
    6df5:	48 89 10             	mov    %rdx,(%rax)
    6df8:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    6dff:	48 8d 35 4a 29 00 00 	lea    0x294a(%rip),%rsi        # 9750 <_IO_stdin_used+0x750>
    6e06:	bf 01 00 00 00       	mov    $0x1,%edi
    6e0b:	31 c0                	xor    %eax,%eax
    6e0d:	e8 ae b6 ff ff       	call   24c0 <__printf_chk@plt>
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6e12:	48 8b 0c 24          	mov    (%rsp),%rcx
    6e16:	48 8d 54 24 4c       	lea    0x4c(%rsp),%rdx
    6e1b:	89 df                	mov    %ebx,%edi
    6e1d:	48 8d 84 24 80 00 00 00 	lea    0x80(%rsp),%rax
    6e25:	48 89 54 24 28       	mov    %rdx,0x28(%rsp)
    6e2a:	48 89 c6             	mov    %rax,%rsi
    socklen_t client_addr_len = sizeof(client_addr);
    6e2d:	c7 44 24 4c 10 00 00 00 	movl   $0x10,0x4c(%rsp)
    add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    6e35:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    6e3a:	e8 e1 f1 ff ff       	call   6020 <add_accept_request>
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    6e3f:	bf 01 00 00 00       	mov    $0x1,%edi
    6e44:	be 10 00 00 00       	mov    $0x10,%esi
    6e49:	e8 c2 b5 ff ff       	call   2410 <calloc@plt>
    void *buf = malloc(size);
    6e4e:	bf 0a 00 00 00       	mov    $0xa,%edi
    struct iovec *iov = calloc(1, sizeof(struct iovec));
    6e53:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    6e56:	e8 25 b6 ff ff       	call   2480 <malloc@plt>
    if (!buf) {
    6e5b:	48 85 c0             	test   %rax,%rax
    6e5e:	0f 84 ed 05 00 00    	je     7451 <io_thread+0x1391>
    iov->iov_base = zh_malloc(10);
    6e64:	49 89 04 24          	mov    %rax,(%r12)
	unsigned int head, next = sq->sqe_tail + 1;
    6e68:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
    iov->iov_len = 10;
    6e6f:	49 c7 44 24 08 0a 00 00 00 	movq   $0xa,0x8(%r12)
	if (ring->flags & IORING_SETUP_SQE128)
    6e78:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    6e7f:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    6e82:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
    6e8a:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    6e8c:	f6 c1 02             	test   $0x2,%cl
    6e8f:	0f 85 70 03 00 00    	jne    7205 <io_thread+0x1145>
	if (next - head <= sq->ring_entries) {
    6e95:	89 d0                	mov    %edx,%eax
    6e97:	29 f0                	sub    %esi,%eax
    6e99:	39 84 24 ec 00 00 00 	cmp    %eax,0xec(%rsp)
    6ea0:	0f 82 db b7 ff ff    	jb     2681 <io_thread.cold+0x6b>
	if (ring->flags & IORING_SETUP_SQE128)
    6ea6:	c1 e9 0a             	shr    $0xa,%ecx
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
    6ea9:	48 8d 7d 68          	lea    0x68(%rbp),%rdi
    io_uring_submit(&ring);
    6ead:	4c 8b 34 24          	mov    (%rsp),%r14
	sqe->addr3 = 0;
    6eb1:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6eb5:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    6ebc:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6ebf:	23 84 24 e8 00 00 00 	and    0xe8(%rsp),%eax
		sq->sqe_tail = next;
    6ec6:	89 94 24 d4 00 00 00 	mov    %edx,0xd4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    6ecd:	d3 e0                	shl    %cl,%eax
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    6ecf:	8b 55 68             	mov    0x68(%rbp),%edx
          io_uring_sqe_set_data(sqe, &data->_eventfd); 
    6ed2:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    6ed7:	4c 8d 2d eb 22 00 00 	lea    0x22eb(%rip),%r13        # 91c9 <_IO_stdin_used+0x1c9>
    6ede:	48 c1 e0 06          	shl    $0x6,%rax
    6ee2:	48 03 84 24 c8 00 00 00 	add    0xc8(%rsp),%rax
	sqe->user_data = (unsigned long) data;
    6eea:	48 89 78 20          	mov    %rdi,0x20(%rax)
    io_uring_submit(&ring);
    6eee:	4c 89 f7             	mov    %r14,%rdi
	sqe->opcode = (__u8) op;
    6ef1:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    6ef7:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    6efa:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    6f02:	4c 89 60 10          	mov    %r12,0x10(%rax)
	sqe->len = len;
    6f06:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    6f0e:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    6f16:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    6f1a:	e8 81 b4 ff ff       	call   23a0 <io_uring_submit@plt>
    while (data->running == 1) {
    6f1f:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    6f23:	0f 85 b6 02 00 00    	jne    71df <io_thread+0x111f>
    6f29:	89 5c 24 3c          	mov    %ebx,0x3c(%rsp)
    6f2d:	4c 89 ef             	mov    %r13,%rdi
    6f30:	e8 0b b4 ff ff       	call   2340 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    6f35:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    6f3c:	8b bc 24 40 01 00 00 	mov    0x140(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    6f43:	c1 e9 0b             	shr    $0xb,%ecx
    6f46:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    6f49:	48 8b 84 24 00 01 00 00 	mov    0x100(%rsp),%rax
    6f51:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    6f53:	48 8b b4 24 f8 00 00 00 	mov    0xf8(%rsp),%rsi
    6f5b:	8b 16                	mov    (%rsi),%edx
		if (!available)
    6f5d:	39 d0                	cmp    %edx,%eax
    6f5f:	74 36                	je     6f97 <io_thread+0xed7>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    6f61:	89 f8                	mov    %edi,%eax
    6f63:	21 d0                	and    %edx,%eax
    6f65:	d3 e0                	shl    %cl,%eax
    6f67:	48 c1 e0 04          	shl    $0x4,%rax
    6f6b:	48 03 84 24 28 01 00 00 	add    0x128(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    6f73:	f6 84 24 59 01 00 00 01 	testb  $0x1,0x159(%rsp)
    6f7b:	0f 85 8f 02 00 00    	jne    7210 <io_thread+0x1150>
    6f81:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    6f85:	0f 85 24 04 00 00    	jne    73af <io_thread+0x12ef>
			if (cqe->res < 0)
    6f8b:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    6f8e:	83 c2 01             	add    $0x1,%edx
    6f91:	89 16                	mov    %edx,(%rsi)
			if (!err)
    6f93:	85 c0                	test   %eax,%eax
    6f95:	79 b2                	jns    6f49 <io_thread+0xe89>
	*cqe_ptr = cqe;
    6f97:	48 c7 44 24 50 00 00 00 00 	movq   $0x0,0x50(%rsp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    6fa0:	45 31 c0             	xor    %r8d,%r8d
    6fa3:	31 d2                	xor    %edx,%edx
    6fa5:	48 8d 74 24 50       	lea    0x50(%rsp),%rsi
    6faa:	b9 01 00 00 00       	mov    $0x1,%ecx
    6faf:	4c 89 f7             	mov    %r14,%rdi
    6fb2:	e8 f9 b4 ff ff       	call   24b0 <__io_uring_get_cqe@plt>
    6fb7:	89 c3                	mov    %eax,%ebx
        if (cqe->user_data == 1) {
    6fb9:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    6fbe:	48 83 38 01          	cmpq   $0x1,(%rax)
    6fc2:	0f 84 c7 03 00 00    	je     738f <io_thread+0x12cf>
    6fc8:	48 8d 3d 25 22 00 00 	lea    0x2225(%rip),%rdi        # 91f4 <_IO_stdin_used+0x1f4>
    6fcf:	e8 6c b3 ff ff       	call   2340 <puts@plt>
        struct Request *req = (struct Request *) cqe->user_data;
    6fd4:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    6fd9:	4c 8b 38             	mov    (%rax),%r15
        if (ret < 0)
    6fdc:	85 db                	test   %ebx,%ebx
    6fde:	0f 88 c5 b6 ff ff    	js     26a9 <io_thread.cold+0x93>
        if (cqe->res < 0) {
    6fe4:	8b 40 08             	mov    0x8(%rax),%eax
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    6fe7:	41 8b 17             	mov    (%r15),%edx
        if (cqe->res < 0) {
    6fea:	85 c0                	test   %eax,%eax
    6fec:	0f 88 c7 03 00 00    	js     73b9 <io_thread+0x12f9>
        switch (req->event_type) {
    6ff2:	83 fa 01             	cmp    $0x1,%edx
    6ff5:	0f 84 9b 02 00 00    	je     7296 <io_thread+0x11d6>
    6ffb:	83 fa 02             	cmp    $0x2,%edx
    6ffe:	0f 84 51 02 00 00    	je     7255 <io_thread+0x1195>
    7004:	85 d2                	test   %edx,%edx
    7006:	0f 85 35 02 00 00    	jne    7241 <io_thread+0x1181>
                add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    700c:	48 8b 54 24 28       	mov    0x28(%rsp),%rdx
    7011:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    7016:	4c 89 f1             	mov    %r14,%rcx
    7019:	8b 7c 24 3c          	mov    0x3c(%rsp),%edi
    701d:	e8 fe ef ff ff       	call   6020 <add_accept_request>
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
    7022:	be 04 00 00 00       	mov    $0x4,%esi
    7027:	bf 01 00 00 00       	mov    $0x1,%edi
    702c:	e8 df b3 ff ff       	call   2410 <calloc@plt>
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
    7031:	4c 63 9d 10 01 00 00 	movslq 0x110(%rbp),%r11
                struct NewClientMessage *newclientmsg = calloc(1, sizeof(struct NewClientMessage));
    7038:	49 89 c2             	mov    %rax,%r10
                newclientmsg->socket = cqe->res;
    703b:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
                buffersend(data, &data->iomailboxes[data->other_io], IO_NEW_CLIENT, newclientmsg);
    7040:	49 c1 e3 04          	shl    $0x4,%r11
    7044:	4c 03 9d 08 01 00 00 	add    0x108(%rbp),%r11
                newclientmsg->socket = cqe->res;
    704b:	8b 40 08             	mov    0x8(%rax),%eax
    704e:	41 89 02             	mov    %eax,(%r10)
  while (data->running == 1) {
    7051:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    7055:	0f 85 8a 00 00 00    	jne    70e5 <io_thread+0x1025>
      for (int x = 0 ; x < buffers->count ; x++) {
    705b:	49 63 03             	movslq (%r11),%rax
    705e:	85 c0                	test   %eax,%eax
    7060:	7e ef                	jle    7051 <io_thread+0xf91>
        if (buffers->buffer[x].available == 0) {
    7062:	49 8b 53 08          	mov    0x8(%r11),%rdx
    7066:	48 c1 e0 08          	shl    $0x8,%rax
    706a:	45 31 c0             	xor    %r8d,%r8d
    706d:	eb 0d                	jmp    707c <io_thread+0xfbc>
    706f:	90                   	nop
      for (int x = 0 ; x < buffers->count ; x++) {
    7070:	49 81 c0 00 01 00 00 	add    $0x100,%r8
    7077:	49 39 c0             	cmp    %rax,%r8
    707a:	74 d5                	je     7051 <io_thread+0xf91>
        if (buffers->buffer[x].available == 0) {
    707c:	42 8b bc 02 80 00 00 00 	mov    0x80(%rdx,%r8,1),%edi
    7084:	85 ff                	test   %edi,%edi
    7086:	75 e8                	jne    7070 <io_thread+0xfb0>
    7088:	42 8b 8c 02 98 00 00 00 	mov    0x98(%rdx,%r8,1),%ecx
    7090:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    7097:	bf 01 00 00 00       	mov    $0x1,%edi
    709c:	31 c0                	xor    %eax,%eax
    709e:	48 8d 35 6d 20 00 00 	lea    0x206d(%rip),%rsi        # 9112 <_IO_stdin_used+0x112>
    70a5:	4c 89 5c 24 20       	mov    %r11,0x20(%rsp)
    70aa:	4c 89 54 24 18       	mov    %r10,0x18(%rsp)
    70af:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    70b4:	e8 07 b4 ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    70b9:	4c 8b 5c 24 20       	mov    0x20(%rsp),%r11
    70be:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
    70c3:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    70c8:	4d 03 43 08          	add    0x8(%r11),%r8
    70cc:	4d 89 10             	mov    %r10,(%r8)
          buffers->buffer[x].kind = kind;
    70cf:	41 c7 80 98 00 00 00 02 00 00 00 	movl   $0x2,0x98(%r8)
          buffers->buffer[x].available = 1;
    70da:	41 c7 80 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%r8)
    70e5:	48 8b 95 18 01 00 00 	mov    0x118(%rbp),%rdx
    70ec:	48 8d 35 2a 21 00 00 	lea    0x212a(%rip),%rsi        # 921d <_IO_stdin_used+0x21d>
    70f3:	bf 01 00 00 00       	mov    $0x1,%edi
    70f8:	31 c0                	xor    %eax,%eax
    70fa:	e8 c1 b3 ff ff       	call   24c0 <__printf_chk@plt>
                add_read_request(data, &data->iomailboxes[data->other_io], cqe->res, &ring);
    70ff:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    7104:	4c 89 f1             	mov    %r14,%rcx
    7107:	48 89 ef             	mov    %rbp,%rdi
    710a:	48 63 b5 10 01 00 00 	movslq 0x110(%rbp),%rsi
    7111:	8b 50 08             	mov    0x8(%rax),%edx
    7114:	48 c1 e6 04          	shl    $0x4,%rsi
    7118:	48 03 b5 08 01 00 00 	add    0x108(%rbp),%rsi
    711f:	e8 6c e7 ff ff       	call   5890 <add_read_request>
                free(req);
    7124:	4c 89 ff             	mov    %r15,%rdi
    7127:	e8 e4 b1 ff ff       	call   2310 <free@plt>
        io_uring_cqe_seen(&ring, cqe);
    712c:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
	if (cqe)
    7131:	48 85 c0             	test   %rax,%rax
    7134:	0f 85 07 01 00 00    	jne    7241 <io_thread+0x1181>
	unsigned int head, next = sq->sqe_tail + 1;
    713a:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    7141:	8b 8c 24 50 01 00 00 	mov    0x150(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    7148:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    714b:	48 8b 84 24 90 00 00 00 	mov    0x90(%rsp),%rax
    7153:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    7155:	f6 c1 02             	test   $0x2,%cl
    7158:	74 00                	je     715a <io_thread+0x109a>
	if (next - head <= sq->ring_entries) {
    715a:	89 d0                	mov    %edx,%eax
    715c:	29 f0                	sub    %esi,%eax
    715e:	39 84 24 ec 00 00 00 	cmp    %eax,0xec(%rsp)
    7165:	0f 82 ab b4 ff ff    	jb     2616 <io_thread.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    716b:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    716e:	8b 84 24 d4 00 00 00 	mov    0xd4(%rsp),%eax
    7175:	23 84 24 e8 00 00 00 	and    0xe8(%rsp),%eax
	sqe->addr3 = 0;
    717c:	66 0f ef c0          	pxor   %xmm0,%xmm0
	if (ring->flags & IORING_SETUP_SQE128)
    7180:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    7183:	89 94 24 d4 00 00 00 	mov    %edx,0xd4(%rsp)
	sqe->user_data = (unsigned long) data;
    718a:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
          io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    718f:	8b 55 68             	mov    0x68(%rbp),%edx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    7192:	d3 e0                	shl    %cl,%eax
    7194:	48 c1 e0 06          	shl    $0x6,%rax
    7198:	48 03 84 24 c8 00 00 00 	add    0xc8(%rsp),%rax
	sqe->user_data = (unsigned long) data;
    71a0:	48 89 78 20          	mov    %rdi,0x20(%rax)
        io_uring_submit(&ring);
    71a4:	4c 89 f7             	mov    %r14,%rdi
	sqe->opcode = (__u8) op;
    71a7:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    71ad:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    71b0:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    71b8:	4c 89 60 10          	mov    %r12,0x10(%rax)
	sqe->len = len;
    71bc:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    71c4:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->addr3 = 0;
    71cc:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    71d0:	e8 cb b1 ff ff       	call   23a0 <io_uring_submit@plt>
    while (data->running == 1) {
    71d5:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    71d9:	0f 84 4e fd ff ff    	je     6f2d <io_thread+0xe6d>
  if (data->io_mode == IO_MODE_SEND) {
    71df:	8b 85 04 01 00 00    	mov    0x104(%rbp),%eax
    71e5:	e9 fe ef ff ff       	jmp    61e8 <io_thread+0x128>
                  free(req->iov[0].iov_base);
    71ea:	49 8b 7e 10          	mov    0x10(%r14),%rdi
    71ee:	e8 1d b1 ff ff       	call   2310 <free@plt>
                  free(req);
    71f3:	4c 89 f7             	mov    %r14,%rdi
    71f6:	e8 15 b1 ff ff       	call   2310 <free@plt>
          io_uring_cqe_seen(&ring, cqe);
    71fb:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
                  break;
    7200:	e9 22 f9 ff ff       	jmp    6b27 <io_thread+0xa67>
		head = io_uring_smp_load_acquire(sq->khead);
    7205:	e9 8b fc ff ff       	jmp    6e95 <io_thread+0xdd5>
    720a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
	*cqe_ptr = cqe;
    7210:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    7215:	48 85 c0             	test   %rax,%rax
    7218:	0f 84 82 fd ff ff    	je     6fa0 <io_thread+0xee0>
        if (cqe->user_data == 1) {
    721e:	48 83 38 01          	cmpq   $0x1,(%rax)
    7222:	0f 84 67 01 00 00    	je     738f <io_thread+0x12cf>
    7228:	48 8d 3d c5 1f 00 00 	lea    0x1fc5(%rip),%rdi        # 91f4 <_IO_stdin_used+0x1f4>
    722f:	e8 0c b1 ff ff       	call   2340 <puts@plt>
        struct Request *req = (struct Request *) cqe->user_data;
    7234:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    7239:	4c 8b 38             	mov    (%rax),%r15
        if (ret < 0)
    723c:	e9 a3 fd ff ff       	jmp    6fe4 <io_thread+0xf24>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    7241:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
    7249:	8b 02                	mov    (%rdx),%eax
    724b:	83 c0 01             	add    $0x1,%eax
    724e:	89 02                	mov    %eax,(%rdx)
}
    7250:	e9 e5 fe ff ff       	jmp    713a <io_thread+0x107a>
                for (int i = 0; i < req->iovec_count; i++) {
    7255:	45 8b 47 04          	mov    0x4(%r15),%r8d
    7259:	31 db                	xor    %ebx,%ebx
    725b:	45 85 c0             	test   %r8d,%r8d
    725e:	7e 1b                	jle    727b <io_thread+0x11bb>
                    free(req->iov[i].iov_base);
    7260:	48 89 d8             	mov    %rbx,%rax
                for (int i = 0; i < req->iovec_count; i++) {
    7263:	48 83 c3 01          	add    $0x1,%rbx
                    free(req->iov[i].iov_base);
    7267:	48 c1 e0 04          	shl    $0x4,%rax
    726b:	49 8b 7c 07 10       	mov    0x10(%r15,%rax,1),%rdi
    7270:	e8 9b b0 ff ff       	call   2310 <free@plt>
                for (int i = 0; i < req->iovec_count; i++) {
    7275:	41 39 5f 04          	cmp    %ebx,0x4(%r15)
    7279:	7f e5                	jg     7260 <io_thread+0x11a0>
                close(req->client_socket);
    727b:	41 8b 7f 08          	mov    0x8(%r15),%edi
    727f:	e8 5c b1 ff ff       	call   23e0 <close@plt>
                free(req);
    7284:	4c 89 ff             	mov    %r15,%rdi
    7287:	e8 84 b0 ff ff       	call   2310 <free@plt>
        io_uring_cqe_seen(&ring, cqe);
    728c:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
                break;
    7291:	e9 9b fe ff ff       	jmp    7131 <io_thread+0x1071>
                if (!cqe->res) {
    7296:	85 c0                	test   %eax,%eax
    7298:	75 46                	jne    72e0 <io_thread+0x1220>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    729a:	48 8b 0d 7f 4d 00 00 	mov    0x4d7f(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    72a1:	ba 0f 00 00 00       	mov    $0xf,%edx
    72a6:	be 01 00 00 00       	mov    $0x1,%esi
    72ab:	48 8d 3d 89 1f 00 00 	lea    0x1f89(%rip),%rdi        # 923b <_IO_stdin_used+0x23b>
    72b2:	e8 89 b2 ff ff       	call   2540 <fwrite@plt>
        io_uring_cqe_seen(&ring, cqe);
    72b7:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
    72bc:	e9 70 fe ff ff       	jmp    7131 <io_thread+0x1071>
  while (data->running == 1) {
    72c1:	8b 45 44             	mov    0x44(%rbp),%eax
    72c4:	83 f8 01             	cmp    $0x1,%eax
    72c7:	0f 84 e1 f9 ff ff    	je     6cae <io_thread+0xbee>
    bufferrecv("gotsocket", data, &data->iomailboxes[data->my_io], IO_NEW_SOCKET_REPLY, &reply, 0);
    72cd:	4c 8b bd 08 01 00 00 	mov    0x108(%rbp),%r15
    72d4:	e9 60 fa ff ff       	jmp    6d39 <io_thread+0xc79>
    72d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    72e0:	4c 8d 94 24 70 01 00 00 	lea    0x170(%rsp),%r10
    72e8:	4c 8b 85 08 01 00 00 	mov    0x108(%rbp),%r8
    72ef:	49 8b 57 10          	mov    0x10(%r15),%rdx
    72f3:	48 8d b4 24 70 05 00 00 	lea    0x570(%rsp),%rsi
    72fb:	8b bd 10 01 00 00    	mov    0x110(%rbp),%edi
    for (int i = 0; i < dest_sz; i++) {
    7301:	4c 89 d0             	mov    %r10,%rax
    7304:	eb 17                	jmp    731d <io_thread+0x125d>
    7306:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    7310:	48 83 c0 01          	add    $0x1,%rax
    7314:	48 83 c2 01          	add    $0x1,%rdx
    7318:	48 39 f0             	cmp    %rsi,%rax
    731b:	74 4b                	je     7368 <io_thread+0x12a8>
        dest[i] = src[i];
    731d:	0f b6 0a             	movzbl (%rdx),%ecx
    7320:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    7322:	80 f9 0d             	cmp    $0xd,%cl
    7325:	75 e9                	jne    7310 <io_thread+0x1250>
    7327:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    732b:	75 e3                	jne    7310 <io_thread+0x1250>
            dest[i] = '\0';
    732d:	c6 00 00             	movb   $0x0,(%rax)
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    7330:	48 63 c7             	movslq %edi,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, ring);
    7333:	41 8b 4f 08          	mov    0x8(%r15),%ecx
    7337:	4c 89 d2             	mov    %r10,%rdx
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    733a:	48 c1 e0 04          	shl    $0x4,%rax
    handle_http_method(data, buffers, http_request, req->client_socket, ring);
    733e:	48 89 ef             	mov    %rbp,%rdi
                handle_client_request(data, &data->iomailboxes[data->other_io], req, &ring);
    7341:	49 8d 34 00          	lea    (%r8,%rax,1),%rsi
    handle_http_method(data, buffers, http_request, req->client_socket, ring);
    7345:	4d 89 f0             	mov    %r14,%r8
    7348:	e8 b3 ea ff ff       	call   5e00 <handle_http_method>
                free(req->iov[0].iov_base);
    734d:	49 8b 7f 10          	mov    0x10(%r15),%rdi
    7351:	e8 ba af ff ff       	call   2310 <free@plt>
                free(req);
    7356:	4c 89 ff             	mov    %r15,%rdi
    7359:	e8 b2 af ff ff       	call   2310 <free@plt>
        io_uring_cqe_seen(&ring, cqe);
    735e:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
                break;
    7363:	e9 c9 fd ff ff       	jmp    7131 <io_thread+0x1071>
    7368:	48 8b 0d b1 4c 00 00 	mov    0x4cb1(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    736f:	ba 12 00 00 00       	mov    $0x12,%edx
    7374:	be 01 00 00 00       	mov    $0x1,%esi
    7379:	48 8d 3d ea 1d 00 00 	lea    0x1dea(%rip),%rdi        # 916a <_IO_stdin_used+0x16a>
    7380:	e8 bb b1 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    7385:	bf 01 00 00 00       	mov    $0x1,%edi
    738a:	e8 91 b1 ff ff       	call   2520 <exit@plt>
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    738f:	48 8b 94 24 f8 00 00 00 	mov    0xf8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    7397:	48 8d 3d 42 1e 00 00 	lea    0x1e42(%rip),%rdi        # 91e0 <_IO_stdin_used+0x1e0>
    739e:	8b 02                	mov    (%rdx),%eax
    73a0:	83 c0 01             	add    $0x1,%eax
    73a3:	89 02                	mov    %eax,(%rdx)
    73a5:	e8 96 af ff ff       	call   2340 <puts@plt>
    73aa:	e9 30 fe ff ff       	jmp    71df <io_thread+0x111f>
	*cqe_ptr = cqe;
    73af:	48 89 44 24 50       	mov    %rax,0x50(%rsp)
	return err;
    73b4:	e9 65 fe ff ff       	jmp    721e <io_thread+0x115e>
            fprintf(stderr, "Async request failed: %s for event: %d\n",
    73b9:	f7 d8                	neg    %eax
    73bb:	41 89 d7             	mov    %edx,%r15d
    73be:	89 c7                	mov    %eax,%edi
    73c0:	e8 bb b1 ff ff       	call   2580 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    73c5:	48 8b 3d 54 4c 00 00 	mov    0x4c54(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    73cc:	45 89 f8             	mov    %r15d,%r8d
    73cf:	48 8d 15 a2 23 00 00 	lea    0x23a2(%rip),%rdx        # 9778 <_IO_stdin_used+0x778>
    73d6:	48 89 c1             	mov    %rax,%rcx
    73d9:	be 01 00 00 00       	mov    $0x1,%esi
    73de:	31 c0                	xor    %eax,%eax
    73e0:	e8 6b b1 ff ff       	call   2550 <__fprintf_chk@plt>
            exit(1);
    73e5:	bf 01 00 00 00       	mov    $0x1,%edi
    73ea:	e8 31 b1 ff ff       	call   2520 <exit@plt>
    73ef:	48 8b 0d 2a 4c 00 00 	mov    0x4c2a(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    73f6:	ba 28 00 00 00       	mov    $0x28,%edx
    73fb:	be 01 00 00 00       	mov    $0x1,%esi
    7400:	48 8d 3d d1 22 00 00 	lea    0x22d1(%rip),%rdi        # 96d8 <_IO_stdin_used+0x6d8>
    7407:	e8 34 b1 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    740c:	bf 01 00 00 00       	mov    $0x1,%edi
    7411:	e8 0a b1 ff ff       	call   2520 <exit@plt>
              fprintf(stderr, "Async request failed: %s for event: %d\n",
    7416:	89 d7                	mov    %edx,%edi
    7418:	41 8b 1e             	mov    (%r14),%ebx
    741b:	f7 df                	neg    %edi
    741d:	e8 5e b1 ff ff       	call   2580 <strerror@plt>
    7422:	48 8b 3d f7 4b 00 00 	mov    0x4bf7(%rip),%rdi        # c020 <stderr@GLIBC_2.2.5>
    7429:	41 89 d8             	mov    %ebx,%r8d
    742c:	48 8d 15 45 23 00 00 	lea    0x2345(%rip),%rdx        # 9778 <_IO_stdin_used+0x778>
    7433:	48 89 c1             	mov    %rax,%rcx
    7436:	be 01 00 00 00       	mov    $0x1,%esi
    743b:	31 c0                	xor    %eax,%eax
    743d:	e8 0e b1 ff ff       	call   2550 <__fprintf_chk@plt>
              exit(1);
    7442:	bf 01 00 00 00       	mov    $0x1,%edi
    7447:	e8 d4 b0 ff ff       	call   2520 <exit@plt>
}
    744c:	e8 3f af ff ff       	call   2390 <__stack_chk_fail@plt>
    7451:	48 8b 0d c8 4b 00 00 	mov    0x4bc8(%rip),%rcx        # c020 <stderr@GLIBC_2.2.5>
    7458:	ba 28 00 00 00       	mov    $0x28,%edx
    745d:	be 01 00 00 00       	mov    $0x1,%esi
    7462:	48 8d 3d 6f 22 00 00 	lea    0x226f(%rip),%rdi        # 96d8 <_IO_stdin_used+0x6d8>
    7469:	e8 d2 b0 ff ff       	call   2540 <fwrite@plt>
        exit(1);
    746e:	bf 01 00 00 00       	mov    $0x1,%edi
    7473:	e8 a8 b0 ff ff       	call   2520 <exit@plt>
    7478:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000007480 <buffersend>:
int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send) {
    7480:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    7484:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    7488:	0f 85 96 00 00 00    	jne    7524 <buffersend+0xa4>
int buffersend(struct KernelThread *data, struct Buffers *buffers, int kind, void * send) {
    748e:	41 55                	push   %r13
    7490:	49 89 cd             	mov    %rcx,%r13
    7493:	41 54                	push   %r12
    7495:	41 89 d4             	mov    %edx,%r12d
    7498:	55                   	push   %rbp
    7499:	48 89 f5             	mov    %rsi,%rbp
    749c:	53                   	push   %rbx
    749d:	48 83 ec 08          	sub    $0x8,%rsp
      for (int x = 0 ; x < buffers->count ; x++) {
    74a1:	48 63 45 00          	movslq 0x0(%rbp),%rax
    74a5:	85 c0                	test   %eax,%eax
    74a7:	7e 6f                	jle    7518 <buffersend+0x98>
        if (buffers->buffer[x].available == 0) {
    74a9:	48 8b 55 08          	mov    0x8(%rbp),%rdx
    74ad:	48 c1 e0 08          	shl    $0x8,%rax
    74b1:	31 db                	xor    %ebx,%ebx
    74b3:	eb 0f                	jmp    74c4 <buffersend+0x44>
    74b5:	0f 1f 00             	nopl   (%rax)
      for (int x = 0 ; x < buffers->count ; x++) {
    74b8:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    74bf:	48 39 c3             	cmp    %rax,%rbx
    74c2:	74 54                	je     7518 <buffersend+0x98>
        if (buffers->buffer[x].available == 0) {
    74c4:	8b 8c 1a 80 00 00 00 	mov    0x80(%rdx,%rbx,1),%ecx
    74cb:	85 c9                	test   %ecx,%ecx
    74cd:	75 e9                	jne    74b8 <buffersend+0x38>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    74cf:	8b 8c 1a 98 00 00 00 	mov    0x98(%rdx,%rbx,1),%ecx
    74d6:	48 8b 97 18 01 00 00 	mov    0x118(%rdi),%rdx
    74dd:	31 c0                	xor    %eax,%eax
    74df:	bf 01 00 00 00       	mov    $0x1,%edi
    74e4:	48 8d 35 27 1c 00 00 	lea    0x1c27(%rip),%rsi        # 9112 <_IO_stdin_used+0x112>
    74eb:	e8 d0 af ff ff       	call   24c0 <__printf_chk@plt>
          buffers->buffer[x].data = send;
    74f0:	48 03 5d 08          	add    0x8(%rbp),%rbx
    74f4:	4c 89 2b             	mov    %r13,(%rbx)
          buffers->buffer[x].kind = kind;
    74f7:	44 89 a3 98 00 00 00 	mov    %r12d,0x98(%rbx)
          buffers->buffer[x].available = 1;
    74fe:	c7 83 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rbx)
}
    7508:	48 83 c4 08          	add    $0x8,%rsp
    750c:	31 c0                	xor    %eax,%eax
    750e:	5b                   	pop    %rbx
    750f:	5d                   	pop    %rbp
    7510:	41 5c                	pop    %r12
    7512:	41 5d                	pop    %r13
    7514:	c3                   	ret
    7515:	0f 1f 00             	nopl   (%rax)
  while (data->running == 1) {
    7518:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    751c:	0f 84 7f ff ff ff    	je     74a1 <buffersend+0x21>
    7522:	eb e4                	jmp    7508 <buffersend+0x88>
}
    7524:	31 c0                	xor    %eax,%eax
    7526:	c3                   	ret
    7527:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007530 <bufferrecv>:
void * bufferrecv(char * recvkind, struct KernelThread *data, struct Buffers *buffers, int kind, void ** send, int nonblocking) {
    7530:	f3 0f 1e fa          	endbr64
    7534:	41 57                	push   %r15
    7536:	49 89 d7             	mov    %rdx,%r15
    7539:	41 56                	push   %r14
    753b:	4c 8d 35 77 1c 00 00 	lea    0x1c77(%rip),%r14        # 91b9 <_IO_stdin_used+0x1b9>
    7542:	41 55                	push   %r13
    7544:	49 89 f5             	mov    %rsi,%r13
    7547:	41 54                	push   %r12
    7549:	41 89 cc             	mov    %ecx,%r12d
    754c:	55                   	push   %rbp
    754d:	44 89 cd             	mov    %r9d,%ebp
    7550:	53                   	push   %rbx
    7551:	48 83 ec 18          	sub    $0x18,%rsp
    7555:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    755a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  while (data->running == 1) {
    7560:	41 83 7d 44 01       	cmpl   $0x1,0x44(%r13)
    7565:	75 64                	jne    75cb <bufferrecv+0x9b>
      for (int x = 0 ; x < buffers->count ; x++) {
    7567:	49 63 07             	movslq (%r15),%rax
    756a:	85 c0                	test   %eax,%eax
    756c:	7e 6e                	jle    75dc <bufferrecv+0xac>
        if (buffers->buffer[x].available == 1) {
    756e:	49 8b 4f 08          	mov    0x8(%r15),%rcx
    7572:	48 c1 e0 08          	shl    $0x8,%rax
    7576:	31 db                	xor    %ebx,%ebx
    7578:	eb 12                	jmp    758c <bufferrecv+0x5c>
    757a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
      for (int x = 0 ; x < buffers->count ; x++) {
    7580:	48 81 c3 00 01 00 00 	add    $0x100,%rbx
    7587:	48 39 c3             	cmp    %rax,%rbx
    758a:	74 3a                	je     75c6 <bufferrecv+0x96>
        if (buffers->buffer[x].available == 1) {
    758c:	83 bc 19 80 00 00 00 01 	cmpl   $0x1,0x80(%rcx,%rbx,1)
    7594:	75 ea                	jne    7580 <bufferrecv+0x50>
    7596:	44 8b 84 19 98 00 00 00 	mov    0x98(%rcx,%rbx,1),%r8d
    759e:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    75a3:	4c 89 f6             	mov    %r14,%rsi
    75a6:	31 c0                	xor    %eax,%eax
    75a8:	49 8b 95 18 01 00 00 	mov    0x118(%r13),%rdx
    75af:	bf 01 00 00 00       	mov    $0x1,%edi
    75b4:	e8 07 af ff ff       	call   24c0 <__printf_chk@plt>
          if (buffers->buffer[x].kind == kind) {
    75b9:	49 03 5f 08          	add    0x8(%r15),%rbx
    75bd:	44 39 a3 98 00 00 00 	cmp    %r12d,0x98(%rbx)
    75c4:	74 22                	je     75e8 <bufferrecv+0xb8>
     if (nonblocking == 1) { return NULL; }
    75c6:	83 fd 01             	cmp    $0x1,%ebp
    75c9:	75 95                	jne    7560 <bufferrecv+0x30>
}
    75cb:	48 83 c4 18          	add    $0x18,%rsp
     if (nonblocking == 1) { return NULL; }
    75cf:	31 c0                	xor    %eax,%eax
}
    75d1:	5b                   	pop    %rbx
    75d2:	5d                   	pop    %rbp
    75d3:	41 5c                	pop    %r12
    75d5:	41 5d                	pop    %r13
    75d7:	41 5e                	pop    %r14
    75d9:	41 5f                	pop    %r15
    75db:	c3                   	ret
     if (nonblocking == 1) { return NULL; }
    75dc:	83 fd 01             	cmp    $0x1,%ebp
    75df:	74 ea                	je     75cb <bufferrecv+0x9b>
  while (data->running == 1) {
    75e1:	eb fe                	jmp    75e1 <bufferrecv+0xb1>
    75e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            struct Buffer * reply = calloc(1, sizeof(struct Buffer));
    75e8:	be 00 01 00 00       	mov    $0x100,%esi
    75ed:	bf 01 00 00 00       	mov    $0x1,%edi
    75f2:	e8 19 ae ff ff       	call   2410 <calloc@plt>
            reply->data = buffers->buffer[x].data;
    75f7:	48 8b 13             	mov    (%rbx),%rdx
            reply->kind = buffers->buffer[x].kind;
    75fa:	44 89 a0 98 00 00 00 	mov    %r12d,0x98(%rax)
            reply->data = buffers->buffer[x].data;
    7601:	48 89 10             	mov    %rdx,(%rax)
            buffers->buffer[x].available = 0;
    7604:	c7 83 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbx)
}
    760e:	48 83 c4 18          	add    $0x18,%rsp
    7612:	5b                   	pop    %rbx
    7613:	5d                   	pop    %rbp
    7614:	41 5c                	pop    %r12
    7616:	41 5d                	pop    %r13
    7618:	41 5e                	pop    %r14
    761a:	41 5f                	pop    %r15
    761c:	c3                   	ret
    761d:	0f 1f 00             	nopl   (%rax)

0000000000007620 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    7620:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    7624:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    762b:	8b 8e c4 00 00 00    	mov    0xc4(%rsi),%ecx
    7631:	85 c9                	test   %ecx,%ecx
    7633:	0f 8e e7 00 00 00    	jle    7720 <barriered_work_ingest+0x100>
int barriered_work_ingest(struct BarrierTask *data) {
    7639:	41 56                	push   %r14
    763b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    763d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    7640:	41 54                	push   %r12
    7642:	49 89 fc             	mov    %rdi,%r12
    7645:	55                   	push   %rbp
    7646:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    7647:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    764b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7650:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    7654:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    765c:	31 db                	xor    %ebx,%ebx
    765e:	8b 10                	mov    (%rax),%edx
    7660:	85 d2                	test   %edx,%edx
    7662:	7e 26                	jle    768a <barriered_work_ingest+0x6a>
    7664:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    7668:	48 89 dd             	mov    %rbx,%rbp
    766b:	48 c1 e5 08          	shl    $0x8,%rbp
    766f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    7673:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    767a:	74 24                	je     76a0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    767c:	48 83 c3 01          	add    $0x1,%rbx
    7680:	39 da                	cmp    %ebx,%edx
    7682:	7f e4                	jg     7668 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    7684:	8b 8e c4 00 00 00    	mov    0xc4(%rsi),%ecx
    768a:	49 83 c5 01          	add    $0x1,%r13
    768e:	44 39 e9             	cmp    %r13d,%ecx
    7691:	7f bd                	jg     7650 <barriered_work_ingest+0x30>
}
    7693:	5b                   	pop    %rbx
    7694:	31 c0                	xor    %eax,%eax
    7696:	5d                   	pop    %rbp
    7697:	41 5c                	pop    %r12
    7699:	41 5d                	pop    %r13
    769b:	41 5e                	pop    %r14
    769d:	c3                   	ret
    769e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    76a0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    76a9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    76b0:	bf 04 00 00 00       	mov    $0x4,%edi
    76b5:	48 c1 e6 05          	shl    $0x5,%rsi
    76b9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    76c0:	48 83 c6 10          	add    $0x10,%rsi
    76c4:	e8 97 ac ff ff       	call   2360 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    76c9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    76d1:	48 8b 40 50          	mov    0x50(%rax),%rax
    76d5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    76d9:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    76dd:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    76e7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    76ed:	83 c0 01             	add    $0x1,%eax
    76f0:	99                   	cltd
    76f1:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    76f7:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    76fd:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    7705:	48 83 c3 01          	add    $0x1,%rbx
    7709:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    770d:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    7711:	8b 10                	mov    (%rax),%edx
    7713:	39 da                	cmp    %ebx,%edx
    7715:	0f 8f 49 ff ff ff    	jg     7664 <barriered_work_ingest+0x44>
    771b:	e9 64 ff ff ff       	jmp    7684 <barriered_work_ingest+0x64>
}
    7720:	31 c0                	xor    %eax,%eax
    7722:	c3                   	ret
    7723:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    772e:	66 90                	xchg   %ax,%ax

0000000000007730 <barriered_thread>:
void* barriered_thread(void *arg) {
    7730:	f3 0f 1e fa          	endbr64
    7734:	41 56                	push   %r14
    7736:	41 55                	push   %r13
    7738:	41 54                	push   %r12
  int t = 0;
    773a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    773d:	55                   	push   %rbp
  int waiting = 0;
    773e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    7740:	53                   	push   %rbx
    7741:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    7744:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    7748:	0f 85 7c 02 00 00    	jne    79ca <barriered_thread+0x29a>
    if (t >= data->task_count) {
    774e:	8b 43 40             	mov    0x40(%rbx),%eax
    7751:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    7758:	41 39 c4             	cmp    %eax,%r12d
    775b:	0f 8d 6f 01 00 00    	jge    78d0 <barriered_thread+0x1a0>
    7761:	49 63 fc             	movslq %r12d,%rdi
    7764:	48 c1 e7 09          	shl    $0x9,%rdi
    7768:	49 89 fd             	mov    %rdi,%r13
    776b:	eb 32                	jmp    779f <barriered_thread+0x6f>
    776d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    7770:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    7774:	48 8b 43 18          	mov    0x18(%rbx),%rax
    7778:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    777c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7780:	4c 01 ef             	add    %r13,%rdi
    7783:	e8 98 fe ff ff       	call   7620 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    7788:	8b 43 40             	mov    0x40(%rbx),%eax
    778b:	41 83 c4 01          	add    $0x1,%r12d
    778f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    7796:	44 39 e0             	cmp    %r12d,%eax
    7799:	0f 8e 21 02 00 00    	jle    79c0 <barriered_thread+0x290>
      if (data->tasks[t].available == 1) {
    779f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    77a3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    77a7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    77ae:	75 c0                	jne    7770 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    77b0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    77b4:	83 e8 01             	sub    $0x1,%eax
    77b7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    77bc:	45 85 e4             	test   %r12d,%r12d
    77bf:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    77c2:	45 85 c0             	test   %r8d,%r8d
    77c5:	0f 8e 2d 01 00 00    	jle    78f8 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    77cb:	48 63 c8             	movslq %eax,%rcx
    77ce:	48 8b 43 18          	mov    0x18(%rbx),%rax
    77d2:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    77d5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    77db:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    77e2:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    77e6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    77e9:	45 31 f6             	xor    %r14d,%r14d
    77ec:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    77f0:	48 8b 10             	mov    (%rax),%rdx
    77f3:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    77f7:	49 01 cb             	add    %rcx,%r11
    77fa:	4c 89 da             	mov    %r11,%rdx
    77fd:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    7804:	75 04                	jne    780a <barriered_thread+0xda>
            arrived++;
    7806:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    780a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    7810:	75 04                	jne    7816 <barriered_thread+0xe6>
            prearrive++;
    7812:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    7816:	48 83 c0 08          	add    $0x8,%rax
    781a:	48 39 c6             	cmp    %rax,%rsi
    781d:	75 d1                	jne    77f0 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    781f:	45 85 d2             	test   %r10d,%r10d
    7822:	0f 84 c0 00 00 00    	je     78e8 <barriered_thread+0x1b8>
    7828:	45 39 d0             	cmp    %r10d,%r8d
    782b:	0f 84 b7 00 00 00    	je     78e8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    7831:	45 85 f6             	test   %r14d,%r14d
    7834:	74 0a                	je     7840 <barriered_thread+0x110>
    7836:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    783a:	0f 85 b6 01 00 00    	jne    79f6 <barriered_thread+0x2c6>
    7840:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    7844:	4c 01 ea             	add    %r13,%rdx
    7847:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    784e:	45 85 e4             	test   %r12d,%r12d
    7851:	75 14                	jne    7867 <barriered_thread+0x137>
    7853:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    785a:	48 3b b3 90 00 00 00 	cmp    0x90(%rbx),%rsi
    7861:	0f 8c 71 01 00 00    	jl     79d8 <barriered_thread+0x2a8>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    7867:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    786b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    786f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    7879:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    787d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7881:	4c 01 ef             	add    %r13,%rdi
    7884:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    788a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    788e:	4c 01 e8             	add    %r13,%rax
    7891:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7898:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    789b:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    78a3:	83 e8 01             	sub    $0x1,%eax
    78a6:	44 39 e0             	cmp    %r12d,%eax
    78a9:	0f 84 a1 00 00 00    	je     7950 <barriered_thread+0x220>
          if (waiting == 0) {
    78af:	85 ed                	test   %ebp,%ebp
    78b1:	0f 84 d9 00 00 00    	je     7990 <barriered_thread+0x260>
        int arrived = 0; 
    78b7:	bd 01 00 00 00       	mov    $0x1,%ebp
    78bc:	e9 c7 fe ff ff       	jmp    7788 <barriered_thread+0x58>
  while (data->running == 1) {
    78c1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    78c5:	0f 85 ff 00 00 00    	jne    79ca <barriered_thread+0x29a>
    78cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    78d0:	48 83 83 b0 00 00 00 01 	addq   $0x1,0xb0(%rbx)
    for (; t < data->task_count; t++) {
    78d8:	85 c0                	test   %eax,%eax
    78da:	7e e5                	jle    78c1 <barriered_thread+0x191>
    78dc:	45 31 e4             	xor    %r12d,%r12d
    78df:	e9 7d fe ff ff       	jmp    7761 <barriered_thread+0x31>
    78e4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    78e8:	83 fd 01             	cmp    $0x1,%ebp
    78eb:	74 1b                	je     7908 <barriered_thread+0x1d8>
        int arrived = 0; 
    78ed:	31 ed                	xor    %ebp,%ebp
    78ef:	e9 3d ff ff ff       	jmp    7831 <barriered_thread+0x101>
    78f4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    78f8:	83 fd 01             	cmp    $0x1,%ebp
    78fb:	0f 85 43 ff ff ff    	jne    7844 <barriered_thread+0x114>
        int arrived = 0; 
    7901:	45 31 f6             	xor    %r14d,%r14d
    7904:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    7908:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    790f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    7914:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    7916:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    791a:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    7921:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    7926:	e8 35 aa ff ff       	call   2360 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    792b:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
    7932:	48 83 c0 01          	add    $0x1,%rax
    7936:	48 99                	cqto
    7938:	48 f7 bb a8 00 00 00 	idivq  0xa8(%rbx)
    793f:	48 89 93 a0 00 00 00 	mov    %rdx,0xa0(%rbx)
            waiting = 0; 
    7946:	e9 e6 fe ff ff       	jmp    7831 <barriered_thread+0x101>
    794b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    7950:	48 8b b3 88 00 00 00 	mov    0x88(%rbx),%rsi
    7957:	48 3b b3 90 00 00 00 	cmp    0x90(%rbx),%rsi
    795e:	0f 8d 4b ff ff ff    	jge    78af <barriered_thread+0x17f>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    7964:	48 c1 e6 04          	shl    $0x4,%rsi
    7968:	bf 04 00 00 00       	mov    $0x4,%edi
    796d:	48 03 73 78          	add    0x78(%rbx),%rsi
    7971:	e8 ea a9 ff ff       	call   2360 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    7976:	48 83 83 88 00 00 00 01 	addq   $0x1,0x88(%rbx)
          if (waiting == 0) {
    797e:	85 ed                	test   %ebp,%ebp
    7980:	0f 85 31 ff ff ff    	jne    78b7 <barriered_thread+0x187>
    7986:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    7990:	48 8b 83 a0 00 00 00 	mov    0xa0(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    7997:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    799c:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    79a0:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    79a7:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    79ab:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    79af:	e8 ac a9 ff ff       	call   2360 <clock_gettime@plt>
            waiting = 1;
    79b4:	e9 fe fe ff ff       	jmp    78b7 <barriered_thread+0x187>
    79b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    79c0:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    79c4:	0f 84 8e fd ff ff    	je     7758 <barriered_thread+0x28>
}
    79ca:	5b                   	pop    %rbx
    79cb:	31 c0                	xor    %eax,%eax
    79cd:	5d                   	pop    %rbp
    79ce:	41 5c                	pop    %r12
    79d0:	41 5d                	pop    %r13
    79d2:	41 5e                	pop    %r14
    79d4:	c3                   	ret
    79d5:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    79d8:	48 c1 e6 04          	shl    $0x4,%rsi
    79dc:	bf 04 00 00 00       	mov    $0x4,%edi
    79e1:	48 03 73 70          	add    0x70(%rbx),%rsi
    79e5:	e8 76 a9 ff ff       	call   2360 <clock_gettime@plt>
          data->tasks[t].available = 0;
    79ea:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    79ee:	4c 01 ea             	add    %r13,%rdx
    79f1:	e9 71 fe ff ff       	jmp    7867 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    79f6:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    79fa:	48 8b 43 18          	mov    0x18(%rbx),%rax
    79fe:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    7a02:	48 8b 78 38          	mov    0x38(%rax),%rdi
    7a06:	4c 01 ef             	add    %r13,%rdi
    7a09:	e8 12 fc ff ff       	call   7620 <barriered_work_ingest>
          break;
    7a0e:	e9 31 fd ff ff       	jmp    7744 <barriered_thread+0x14>
    7a13:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    7a1e:	66 90                	xchg   %ax,%ax

0000000000007a20 <receive>:
int receive(struct BarrierTask *data) {
    7a20:	f3 0f 1e fa          	endbr64
    7a24:	41 56                	push   %r14
    7a26:	41 55                	push   %r13
    7a28:	41 54                	push   %r12
    7a2a:	55                   	push   %rbp
    7a2b:	53                   	push   %rbx
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7a2c:	4c 63 a7 40 01 00 00 	movslq 0x140(%rdi),%r12
    7a33:	45 85 e4             	test   %r12d,%r12d
    7a36:	0f 8e 27 01 00 00    	jle    7b63 <receive+0x143>
    if (n == data->thread->real_thread_index) { continue; }
    7a3c:	4c 8b b7 28 01 00 00 	mov    0x128(%rdi),%r14
    7a43:	48 89 fe             	mov    %rdi,%rsi
    7a46:	31 db                	xor    %ebx,%ebx
    7a48:	49 63 6e 08          	movslq 0x8(%r14),%rbp
    7a4c:	49 89 ed             	mov    %rbp,%r13
    7a4f:	90                   	nop
    7a50:	41 39 dd             	cmp    %ebx,%r13d
    7a53:	0f 84 fd 00 00 00    	je     7b56 <receive+0x136>
    struct Data *me = data->mailboxes[n].lower;
    7a59:	48 89 d8             	mov    %rbx,%rax
    7a5c:	48 c1 e0 08          	shl    $0x8,%rax
    7a60:	48 03 86 70 01 00 00 	add    0x170(%rsi),%rax
    7a67:	48 8b 10             	mov    (%rax),%rdx
    if (me->available_reading == 1) {
    7a6a:	8b 82 00 02 00 00    	mov    0x200(%rdx),%eax
    7a70:	83 f8 01             	cmp    $0x1,%eax
    7a73:	74 11                	je     7a86 <receive+0x66>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    7a75:	83 ba 08 04 00 00 02 	cmpl   $0x2,0x408(%rdx)
    7a7c:	75 08                	jne    7a86 <receive+0x66>
    7a7e:	85 c0                	test   %eax,%eax
    7a80:	0f 84 d0 00 00 00    	je     7b56 <receive+0x136>
    for (; me->messages_count > 0 ; ) {
    7a86:	48 8b ba 80 00 00 00 	mov    0x80(%rdx),%rdi
    7a8d:	48 85 ff             	test   %rdi,%rdi
    7a90:	0f 8e a2 00 00 00    	jle    7b38 <receive+0x118>
    7a96:	4c 8b 8e 80 01 00 00 	mov    0x180(%rsi),%r9
    7a9d:	4c 8b 86 08 01 00 00 	mov    0x108(%rsi),%r8
    7aa4:	48 8d 47 ff          	lea    -0x1(%rdi),%rax
      if (me->messages[x]->group == data->group) {
    7aa8:	4c 8b 1a             	mov    (%rdx),%r11
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    7aab:	4c 63 56 04          	movslq 0x4(%rsi),%r10
    7aaf:	49 01 f9             	add    %rdi,%r9
    7ab2:	49 01 f8             	add    %rdi,%r8
    7ab5:	48 03 ba 00 04 00 00 	add    0x400(%rdx),%rdi
    7abc:	eb 08                	jmp    7ac6 <receive+0xa6>
    7abe:	66 90                	xchg   %ax,%ax
    for (; me->messages_count > 0 ; ) {
    7ac0:	48 83 e8 01          	sub    $0x1,%rax
    7ac4:	72 72                	jb     7b38 <receive+0x118>
      data->sends++;
    7ac6:	4c 89 c9             	mov    %r9,%rcx
      me->messages_count--;
    7ac9:	48 89 82 80 00 00 00 	mov    %rax,0x80(%rdx)
      data->sends++;
    7ad0:	48 29 c1             	sub    %rax,%rcx
    7ad3:	48 89 8e 80 01 00 00 	mov    %rcx,0x180(%rsi)
      data->n++;
    7ada:	4c 89 c1             	mov    %r8,%rcx
    7add:	48 29 c1             	sub    %rax,%rcx
    7ae0:	48 89 8e 08 01 00 00 	mov    %rcx,0x108(%rsi)
      me->received++;
    7ae7:	48 89 f9             	mov    %rdi,%rcx
    7aea:	48 29 c1             	sub    %rax,%rcx
    7aed:	48 89 8a 00 04 00 00 	mov    %rcx,0x400(%rdx)
      if (me->messages[x]->group == data->group) {
    7af4:	48 63 c8             	movslq %eax,%rcx
    7af7:	49 8b 0c cb          	mov    (%r11,%rcx,8),%rcx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    7afb:	4c 39 51 10          	cmp    %r10,0x10(%rcx)
    7aff:	75 bf                	jne    7ac0 <receive+0xa0>
    7b01:	48 39 69 08          	cmp    %rbp,0x8(%rcx)
    7b05:	75 b9                	jne    7ac0 <receive+0xa0>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    7b07:	49 63 46 04          	movslq 0x4(%r14),%rax
    7b0b:	31 c9                	xor    %ecx,%ecx
    7b0d:	bf 01 00 00 00       	mov    $0x1,%edi
    7b12:	ba 01 00 00 00       	mov    $0x1,%edx
    7b17:	48 8d 35 ca 1d 00 00 	lea    0x1dca(%rip),%rsi        # 98e8 <_IO_stdin_used+0x8e8>
    7b1e:	48 39 e8             	cmp    %rbp,%rax
    7b21:	0f 94 c1             	sete   %cl
    7b24:	31 c0                	xor    %eax,%eax
    7b26:	e8 95 a9 ff ff       	call   24c0 <__printf_chk@plt>
        exit(1);
    7b2b:	bf 01 00 00 00       	mov    $0x1,%edi
    7b30:	e8 eb a9 ff ff       	call   2520 <exit@plt>
    7b35:	0f 1f 00             	nopl   (%rax)
      me->available_reading = 0;
    7b38:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
      me->finished_reading = 1;
    7b42:	c7 82 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rdx)
      me->available_sending = 1;
    7b4c:	c7 82 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rdx)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7b56:	48 83 c3 01          	add    $0x1,%rbx
    7b5a:	49 39 dc             	cmp    %rbx,%r12
    7b5d:	0f 85 ed fe ff ff    	jne    7a50 <receive+0x30>
}
    7b63:	31 c0                	xor    %eax,%eax
    7b65:	5b                   	pop    %rbx
    7b66:	5d                   	pop    %rbp
    7b67:	41 5c                	pop    %r12
    7b69:	41 5d                	pop    %r13
    7b6b:	41 5e                	pop    %r14
    7b6d:	c3                   	ret
    7b6e:	66 90                	xchg   %ax,%ax

0000000000007b70 <sendm>:
int sendm(struct BarrierTask *data) {
    7b70:	f3 0f 1e fa          	endbr64
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7b74:	8b 87 40 01 00 00    	mov    0x140(%rdi),%eax
    7b7a:	85 c0                	test   %eax,%eax
    7b7c:	0f 8e 96 02 00 00    	jle    7e18 <sendm+0x2a8>
int sendm(struct BarrierTask *data) {
    7b82:	41 57                	push   %r15
    7b84:	41 56                	push   %r14
    7b86:	41 55                	push   %r13
        if (n == data->thread->real_thread_index) { continue; }
    7b88:	45 31 ed             	xor    %r13d,%r13d
int sendm(struct BarrierTask *data) {
    7b8b:	41 54                	push   %r12
    7b8d:	4c 63 e0             	movslq %eax,%r12
    7b90:	55                   	push   %rbp
    7b91:	48 89 fd             	mov    %rdi,%rbp
    7b94:	53                   	push   %rbx
        if (n == data->thread->real_thread_index) { continue; }
    7b95:	48 8b 9f 28 01 00 00 	mov    0x128(%rdi),%rbx
    7b9c:	44 8b 7b 08          	mov    0x8(%rbx),%r15d
    7ba0:	48 89 5c 24 c8       	mov    %rbx,-0x38(%rsp)
    7ba5:	0f 1f 00             	nopl   (%rax)
    7ba8:	45 39 ef             	cmp    %r13d,%r15d
    7bab:	0f 84 97 00 00 00    	je     7c48 <sendm+0xd8>
        struct Data *them = data->mailboxes[n].higher;
    7bb1:	4c 89 e8             	mov    %r13,%rax
    7bb4:	48 c1 e0 08          	shl    $0x8,%rax
    7bb8:	48 03 85 70 01 00 00 	add    0x170(%rbp),%rax
        data->mailboxes[n].counter++;
    7bbf:	48 8b 98 b8 00 00 00 	mov    0xb8(%rax),%rbx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7bc6:	83 b8 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax)
        struct Data *them = data->mailboxes[n].higher;
    7bcd:	48 8b 88 80 00 00 00 	mov    0x80(%rax),%rcx
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7bd4:	40 0f 94 c7          	sete   %dil
        data->mailboxes[n].counter++;
    7bd8:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    7bdc:	48 89 90 b8 00 00 00 	mov    %rdx,0xb8(%rax)
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter < limit) {
    7be3:	48 85 d2             	test   %rdx,%rdx
    7be6:	7f 05                	jg     7bed <sendm+0x7d>
    7be8:	40 84 ff             	test   %dil,%dil
    7beb:	75 5b                	jne    7c48 <sendm+0xd8>
        if (them->messages_count > 0) {
    7bed:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    7bf4:	48 85 f6             	test   %rsi,%rsi
    7bf7:	7f 4f                	jg     7c48 <sendm+0xd8>
        if (them->available_sending == 1) {
    7bf9:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    7c00:	41 83 f8 01          	cmp    $0x1,%r8d
    7c04:	74 0e                	je     7c14 <sendm+0xa4>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    7c06:	83 b9 08 04 00 00 02 	cmpl   $0x2,0x408(%rcx)
    7c0d:	75 05                	jne    7c14 <sendm+0xa4>
    7c0f:	45 85 c0             	test   %r8d,%r8d
    7c12:	74 34                	je     7c48 <sendm+0xd8>
        if (data->sending == 1) {
    7c14:	83 bd 88 01 00 00 01 	cmpl   $0x1,0x188(%rbp)
    7c1b:	74 4b                	je     7c68 <sendm+0xf8>
        if (data->mailboxes[n].kind == MAILBOX_FOREIGN && data->mailboxes[n].counter >= limit) {
    7c1d:	48 85 d2             	test   %rdx,%rdx
    7c20:	7e 26                	jle    7c48 <sendm+0xd8>
    7c22:	40 84 ff             	test   %dil,%dil
    7c25:	74 21                	je     7c48 <sendm+0xd8>
          data->mailboxes[n].counter = 0;
    7c27:	48 c7 80 b8 00 00 00 00 00 00 00 	movq   $0x0,0xb8(%rax)
          data->thread->have_foreign = 1;
    7c32:	48 8b 44 24 c8       	mov    -0x38(%rsp),%rax
    7c37:	c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rax)
    7c41:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    7c48:	49 83 c5 01          	add    $0x1,%r13
    7c4c:	4d 39 ec             	cmp    %r13,%r12
    7c4f:	0f 85 53 ff ff ff    	jne    7ba8 <sendm+0x38>
}
    7c55:	31 c0                	xor    %eax,%eax
    7c57:	5b                   	pop    %rbx
    7c58:	5d                   	pop    %rbp
    7c59:	41 5c                	pop    %r12
    7c5b:	41 5d                	pop    %r13
    7c5d:	41 5e                	pop    %r14
    7c5f:	41 5f                	pop    %r15
    7c61:	c3                   	ret
    7c62:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (; them->messages_count < min;) {
    7c68:	4c 63 99 88 00 00 00 	movslq 0x88(%rcx),%r11
    7c6f:	4c 39 de             	cmp    %r11,%rsi
    7c72:	0f 8d c2 00 00 00    	jge    7d3a <sendm+0x1ca>
    7c78:	48 8b 9d 08 01 00 00 	mov    0x108(%rbp),%rbx
    7c7f:	4d 89 de             	mov    %r11,%r14
            them->messages[them->messages_count++] = data->message; 
    7c82:	4c 8b 11             	mov    (%rcx),%r10
    7c85:	49 29 f6             	sub    %rsi,%r14
    7c88:	48 89 5c 24 d8       	mov    %rbx,-0x28(%rsp)
    7c8d:	48 8b 99 80 03 00 00 	mov    0x380(%rcx),%rbx
    7c94:	4d 8d 46 ff          	lea    -0x1(%r14),%r8
    7c98:	48 89 5c 24 e0       	mov    %rbx,-0x20(%rsp)
    7c9d:	49 83 f8 02          	cmp    $0x2,%r8
    7ca1:	0f 86 51 01 00 00    	jbe    7df8 <sendm+0x288>
    7ca7:	48 8d 1c f5 00 00 00 00 	lea    0x0(,%rsi,8),%rbx
    7caf:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    7cb7:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    7cbc:	4c 01 d3             	add    %r10,%rbx
    7cbf:	4c 8d 85 90 01 00 00 	lea    0x190(%rbp),%r8
    7cc6:	48 89 5c 24 d0       	mov    %rbx,-0x30(%rsp)
    7ccb:	4b 8d 1c 0a          	lea    (%r10,%r9,1),%rbx
    7ccf:	49 39 d8             	cmp    %rbx,%r8
    7cd2:	0f 83 88 00 00 00    	jae    7d60 <sendm+0x1f0>
    7cd8:	48 8d 9d 98 01 00 00 	lea    0x198(%rbp),%rbx
    7cdf:	48 39 5c 24 d0       	cmp    %rbx,-0x30(%rsp)
    7ce4:	73 7a                	jae    7d60 <sendm+0x1f0>
    7ce6:	4c 8b 44 24 e8       	mov    -0x18(%rsp),%r8
    7ceb:	4b 8d 34 0a          	lea    (%r10,%r9,1),%rsi
    7cef:	4d 01 d0             	add    %r10,%r8
    7cf2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    7cf8:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
          for (; them->messages_count < min;) {
    7cff:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    7d03:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    7d07:	4c 39 c6             	cmp    %r8,%rsi
    7d0a:	75 ec                	jne    7cf8 <sendm+0x188>
    7d0c:	0f 1f 40 00          	nopl   0x0(%rax)
    7d10:	48 8b 74 24 d8       	mov    -0x28(%rsp),%rsi
    7d15:	4c 01 f6             	add    %r14,%rsi
    7d18:	48 89 b5 08 01 00 00 	mov    %rsi,0x108(%rbp)
    7d1f:	48 8b 74 24 e0       	mov    -0x20(%rsp),%rsi
    7d24:	4c 89 99 80 00 00 00 	mov    %r11,0x80(%rcx)
    7d2b:	4c 01 f6             	add    %r14,%rsi
    7d2e:	48 89 b1 80 03 00 00 	mov    %rsi,0x380(%rcx)
    7d35:	4f 89 4c da f8       	mov    %r9,-0x8(%r10,%r11,8)
          them->available_sending = 0;
    7d3a:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
          them->available_reading = 1;
    7d44:	c7 81 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rcx)
          them->available_receiving = 1;
    7d4e:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
    7d58:	e9 c0 fe ff ff       	jmp    7c1d <sendm+0xad>
    7d5d:	0f 1f 00             	nopl   (%rax)
    7d60:	4c 89 f3             	mov    %r14,%rbx
    7d63:	4c 8b 44 24 d0       	mov    -0x30(%rsp),%r8
    7d68:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    7d6f:	48 d1 eb             	shr    %rbx
    7d72:	48 c1 e3 04          	shl    $0x4,%rbx
    7d76:	66 49 0f 6e c1       	movq   %r9,%xmm0
    7d7b:	48 89 5c 24 e8       	mov    %rbx,-0x18(%rsp)
    7d80:	4c 01 c3             	add    %r8,%rbx
    7d83:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    7d87:	48 89 5c 24 f0       	mov    %rbx,-0x10(%rsp)
    7d8c:	48 8b 5c 24 e8       	mov    -0x18(%rsp),%rbx
    7d91:	83 e3 10             	and    $0x10,%ebx
    7d94:	75 4a                	jne    7de0 <sendm+0x270>
    7d96:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    7d9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    7da0:	41 0f 11 00          	movups %xmm0,(%r8)
    7da4:	49 83 c0 20          	add    $0x20,%r8
    7da8:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    7dad:	49 39 d8             	cmp    %rbx,%r8
    7db0:	75 ee                	jne    7da0 <sendm+0x230>
    7db2:	4d 89 f0             	mov    %r14,%r8
    7db5:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    7db9:	49 01 f0             	add    %rsi,%r8
    7dbc:	41 f6 c6 01          	test   $0x1,%r14b
    7dc0:	0f 84 4a ff ff ff    	je     7d10 <sendm+0x1a0>
            them->messages[them->messages_count++] = data->message; 
    7dc6:	4c 8b 8d 90 01 00 00 	mov    0x190(%rbp),%r9
    7dcd:	4f 89 0c c2          	mov    %r9,(%r10,%r8,8)
          for (; them->messages_count < min;) {
    7dd1:	e9 3a ff ff ff       	jmp    7d10 <sendm+0x1a0>
    7dd6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
            them->messages[them->messages_count++] = data->message; 
    7de0:	48 8b 5c 24 f0       	mov    -0x10(%rsp),%rbx
    7de5:	41 0f 11 00          	movups %xmm0,(%r8)
          for (; them->messages_count < min;) {
    7de9:	49 83 c0 10          	add    $0x10,%r8
    7ded:	49 39 d8             	cmp    %rbx,%r8
    7df0:	75 ae                	jne    7da0 <sendm+0x230>
    7df2:	eb be                	jmp    7db2 <sendm+0x242>
    7df4:	0f 1f 40 00          	nopl   0x0(%rax)
    7df8:	48 8d 34 f5 00 00 00 00 	lea    0x0(,%rsi,8),%rsi
    7e00:	4e 8d 0c dd 00 00 00 00 	lea    0x0(,%r11,8),%r9
    7e08:	48 89 74 24 e8       	mov    %rsi,-0x18(%rsp)
    7e0d:	e9 d4 fe ff ff       	jmp    7ce6 <sendm+0x176>
    7e12:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
}
    7e18:	31 c0                	xor    %eax,%eax
    7e1a:	c3                   	ret
    7e1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000007e20 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    7e20:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    7e24:	85 f6                	test   %esi,%esi
    7e26:	74 18                	je     7e40 <mailboxkind+0x20>
  return NULL;
    7e28:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    7e2a:	83 fe 01             	cmp    $0x1,%esi
    7e2d:	74 01                	je     7e30 <mailboxkind+0x10>
}
    7e2f:	c3                   	ret
    return mailbox->higher;
    7e30:	48 8b 87 80 00 00 00 	mov    0x80(%rdi),%rax
}
    7e37:	c3                   	ret
    7e38:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    return mailbox->lower;
    7e40:	48 8b 07             	mov    (%rdi),%rax
    7e43:	c3                   	ret
    7e44:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    7e4f:	90                   	nop

0000000000007e50 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    7e50:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    7e54:	85 d2                	test   %edx,%edx
    7e56:	75 08                	jne    7e60 <setmailboxkind+0x10>
    mailbox->lower = data;
    7e58:	48 89 37             	mov    %rsi,(%rdi)
}
    7e5b:	31 c0                	xor    %eax,%eax
    7e5d:	c3                   	ret
    7e5e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    7e60:	83 fa 01             	cmp    $0x1,%edx
    7e63:	74 13                	je     7e78 <setmailboxkind+0x28>
  if (kind == 2) {
    7e65:	83 fa 02             	cmp    $0x2,%edx
    7e68:	75 1e                	jne    7e88 <setmailboxkind+0x38>
    mailbox->pending_lower = data;
    7e6a:	48 89 b7 88 00 00 00 	mov    %rsi,0x88(%rdi)
}
    7e71:	31 c0                	xor    %eax,%eax
    7e73:	c3                   	ret
    7e74:	0f 1f 40 00          	nopl   0x0(%rax)
    mailbox->higher = data;
    7e78:	48 89 b7 80 00 00 00 	mov    %rsi,0x80(%rdi)
}
    7e7f:	31 c0                	xor    %eax,%eax
    7e81:	c3                   	ret
    7e82:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  if (kind == 3) {
    7e88:	83 fa 03             	cmp    $0x3,%edx
    7e8b:	75 ce                	jne    7e5b <setmailboxkind+0xb>
    mailbox->pending_higher = data;
    7e8d:	48 89 b7 90 00 00 00 	mov    %rsi,0x90(%rdi)
}
    7e94:	31 c0                	xor    %eax,%eax
    7e96:	c3                   	ret
    7e97:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000007ea0 <fswap>:
int fswap(struct BarrierTask *data) {
    7ea0:	f3 0f 1e fa          	endbr64
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    7ea4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    7eab:	8b 97 9c 01 00 00    	mov    0x19c(%rdi),%edx
    7eb1:	44 8b 97 30 01 00 00 	mov    0x130(%rdi),%r10d
  int t = data->task_index;
    7eb8:	48 63 4f 04          	movslq 0x4(%rdi),%rcx
      int y = (k * data->thread->threads_per_group) + data->thread_index;
    7ebc:	8b 86 cc 00 00 00    	mov    0xcc(%rsi),%eax
    7ec2:	0f af d0             	imul   %eax,%edx
    7ec5:	41 01 d2             	add    %edx,%r10d
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    7ec8:	85 c0                	test   %eax,%eax
    7eca:	0f 8e 1b 01 00 00    	jle    7feb <fswap+0x14b>
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7ed0:	4d 63 d2             	movslq %r10d,%r10
int fswap(struct BarrierTask *data) {
    7ed3:	41 56                	push   %r14
    7ed5:	48 63 d2             	movslq %edx,%rdx
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7ed8:	48 c1 e1 09          	shl    $0x9,%rcx
int fswap(struct BarrierTask *data) {
    7edc:	41 55                	push   %r13
    7ede:	4c 63 d8             	movslq %eax,%r11
    7ee1:	41 54                	push   %r12
    7ee3:	49 01 d3             	add    %rdx,%r11
    7ee6:	55                   	push   %rbp
    7ee7:	49 c1 e3 08          	shl    $0x8,%r11
    7eeb:	53                   	push   %rbx
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7eec:	48 8b 76 20          	mov    0x20(%rsi),%rsi
        int next_task = abs((t + 1) % (data->thread_count));
    7ef0:	44 8b 87 34 01 00 00 	mov    0x134(%rdi),%r8d
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7ef7:	4b 8d 3c d2          	lea    (%r10,%r10,8),%rdi
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    7efb:	49 c1 e2 08          	shl    $0x8,%r10
        int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    7eff:	48 c1 e7 05          	shl    $0x5,%rdi
    7f03:	48 8b 5c 3e 38       	mov    0x38(%rsi,%rdi,1),%rbx
    7f08:	48 8b ac 0b 70 01 00 00 	mov    0x170(%rbx,%rcx,1),%rbp
    7f10:	48 8d 0c d2          	lea    (%rdx,%rdx,8),%rcx
    7f14:	48 c1 e1 05          	shl    $0x5,%rcx
    7f18:	4c 8d 4c 0e 38       	lea    0x38(%rsi,%rcx,1),%r9
    7f1d:	48 89 d6             	mov    %rdx,%rsi
    7f20:	48 c1 e6 08          	shl    $0x8,%rsi
    7f24:	eb 21                	jmp    7f47 <fswap+0xa7>
    7f26:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
      for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    7f30:	48 81 c6 00 01 00 00 	add    $0x100,%rsi
    7f37:	49 81 c1 20 01 00 00 	add    $0x120,%r9
    7f3e:	49 39 f3             	cmp    %rsi,%r11
    7f41:	0f 84 99 00 00 00    	je     7fe0 <fswap+0x140>
        if (kind == MAILBOX_FRIEND) {
    7f47:	83 bc 35 b0 00 00 00 01 	cmpl   $0x1,0xb0(%rbp,%rsi,1)
    7f4f:	75 df                	jne    7f30 <fswap+0x90>
            int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    7f51:	49 8b 39             	mov    (%r9),%rdi
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    7f54:	45 85 c0             	test   %r8d,%r8d
    7f57:	7e d7                	jle    7f30 <fswap+0x90>
    7f59:	48 81 c7 70 01 00 00 	add    $0x170,%rdi
    7f60:	31 c9                	xor    %ecx,%ecx
    7f62:	eb 59                	jmp    7fbd <fswap+0x11d>
    7f64:	0f 1f 40 00          	nopl   0x0(%rax)
              struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    7f68:	48 63 d2             	movslq %edx,%rdx
    7f6b:	48 c1 e2 09          	shl    $0x9,%rdx
    7f6f:	4c 8b ac 13 70 01 00 00 	mov    0x170(%rbx,%rdx,1),%r13
    7f77:	49 01 f5             	add    %rsi,%r13
    7f7a:	4c 89 ea             	mov    %r13,%rdx
    return mailbox->lower;
    7f7d:	4d 8b 6d 00          	mov    0x0(%r13),%r13
                if (dest->messages_count != 0) { 
    7f81:	49 83 bd 80 00 00 00 00 	cmpq   $0x0,0x80(%r13)
    7f89:	75 22                	jne    7fad <fswap+0x10d>
    mailbox->lower = data;
    7f8b:	4c 8b b0 80 00 00 00 	mov    0x80(%rax),%r14
    7f92:	4c 89 32             	mov    %r14,(%rdx)
    7f95:	4c 8b b2 80 00 00 00 	mov    0x80(%rdx),%r14
    mailbox->higher = data;
    7f9c:	4c 89 a8 80 00 00 00 	mov    %r13,0x80(%rax)
    mailbox->lower = data;
    7fa3:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    7fa6:	4c 89 a2 80 00 00 00 	mov    %r12,0x80(%rdx)
             for (int nn = 0 ; nn < data->thread_count; nn++) {
    7fad:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    7fb4:	41 39 c8             	cmp    %ecx,%r8d
    7fb7:	0f 84 73 ff ff ff    	je     7f30 <fswap+0x90>
              int next_task = abs((nn + 1) % (data->thread_count));
    7fbd:	83 c1 01             	add    $0x1,%ecx
    7fc0:	89 c8                	mov    %ecx,%eax
    7fc2:	99                   	cltd
    7fc3:	41 f7 f8             	idiv   %r8d
              struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    7fc6:	48 8b 07             	mov    (%rdi),%rax
    7fc9:	4c 01 d0             	add    %r10,%rax
    return mailbox->lower;
    7fcc:	4c 8b 20             	mov    (%rax),%r12
                if (source2->messages_count != 0) { 
    7fcf:	49 83 bc 24 80 00 00 00 00 	cmpq   $0x0,0x80(%r12)
    7fd8:	74 8e                	je     7f68 <fswap+0xc8>
    7fda:	e9 51 ff ff ff       	jmp    7f30 <fswap+0x90>
    7fdf:	90                   	nop
}
    7fe0:	5b                   	pop    %rbx
    7fe1:	31 c0                	xor    %eax,%eax
    7fe3:	5d                   	pop    %rbp
    7fe4:	41 5c                	pop    %r12
    7fe6:	41 5d                	pop    %r13
    7fe8:	41 5e                	pop    %r14
    7fea:	c3                   	ret
    7feb:	31 c0                	xor    %eax,%eax
    7fed:	c3                   	ret
    7fee:	66 90                	xchg   %ax,%ax

0000000000007ff0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    7ff0:	f3 0f 1e fa          	endbr64
    7ff4:	41 57                	push   %r15
    7ff6:	41 56                	push   %r14
    7ff8:	41 55                	push   %r13
    7ffa:	41 54                	push   %r12
    7ffc:	55                   	push   %rbp
    7ffd:	53                   	push   %rbx
    7ffe:	48 89 fb             	mov    %rdi,%rbx
    8001:	48 81 ec 88 00 00 00 	sub    $0x88,%rsp
  struct timespec preempt = {
    8008:	66 0f 6f 05 a0 1e 00 00 	movdqa 0x1ea0(%rip),%xmm0        # 9eb0 <_IO_stdin_used+0xeb0>
int barriered_work(struct BarrierTask *data) {
    8010:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    8019:	48 89 44 24 78       	mov    %rax,0x78(%rsp)
    801e:	31 c0                	xor    %eax,%eax
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    8020:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
  struct timespec preempt = {
    8027:	0f 29 44 24 50       	movaps %xmm0,0x50(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    802c:	48 8b 88 f8 00 00 00 	mov    0xf8(%rax),%rcx
  struct timespec rem = {
    8033:	0f 29 44 24 60       	movaps %xmm0,0x60(%rsp)
  if (data->thread->global->request_group_sync == -1 || data->thread->global->request_group_sync == data->thread->group) {
    8038:	8b 11                	mov    (%rcx),%edx
    803a:	83 fa ff             	cmp    $0xffffffff,%edx
    803d:	0f 84 cd 02 00 00    	je     8310 <barriered_work+0x320>
    8043:	3b 90 f0 00 00 00    	cmp    0xf0(%rax),%edx
    8049:	74 2d                	je     8078 <barriered_work+0x88>
}
    804b:	48 8b 44 24 78       	mov    0x78(%rsp),%rax
    8050:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    8059:	0f 85 20 05 00 00    	jne    857f <barriered_work+0x58f>
    805f:	48 81 c4 88 00 00 00 	add    $0x88,%rsp
    8066:	31 c0                	xor    %eax,%eax
    8068:	5b                   	pop    %rbx
    8069:	5d                   	pop    %rbp
    806a:	41 5c                	pop    %r12
    806c:	41 5d                	pop    %r13
    806e:	41 5e                	pop    %r14
    8070:	41 5f                	pop    %r15
    8072:	c3                   	ret
    8073:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    8078:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    807f:	8b 41 04             	mov    0x4(%rcx),%eax
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    8082:	85 ed                	test   %ebp,%ebp
    8084:	0f 85 76 04 00 00    	jne    8500 <barriered_work+0x510>
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    808a:	85 c0                	test   %eax,%eax
    808c:	0f 84 76 04 00 00    	je     8508 <barriered_work+0x518>
    8092:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          int t = data->task_index;
    8098:	44 8b 63 04          	mov    0x4(%rbx),%r12d
      receive(data);
    809c:	48 89 df             	mov    %rbx,%rdi
    if (data->thread_index == data->task_index) {
    809f:	41 39 ec             	cmp    %ebp,%r12d
    80a2:	0f 85 b0 03 00 00    	jne    8458 <barriered_work+0x468>
      receive(data);
    80a8:	e8 73 f9 ff ff       	call   7a20 <receive>
        if (data->thread->have_foreign == 1) {
    80ad:	4c 8b b3 28 01 00 00 	mov    0x128(%rbx),%r14
    80b4:	41 83 be 00 01 00 00 01 	cmpl   $0x1,0x100(%r14)
    80bc:	0f 85 a1 02 00 00    	jne    8363 <barriered_work+0x373>
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    80c2:	48 63 93 40 01 00 00 	movslq 0x140(%rbx),%rdx
    80c9:	85 d2                	test   %edx,%edx
    80cb:	0f 8e 92 02 00 00    	jle    8363 <barriered_work+0x373>
                int next_task = abs((t + 1) % (data->thread_count));
    80d1:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    80d7:	48 c1 e5 09          	shl    $0x9,%rbp
    80db:	31 f6                	xor    %esi,%esi
    80dd:	49 89 d2             	mov    %rdx,%r10
    80e0:	49 89 ed             	mov    %rbp,%r13
    80e3:	48 c7 04 24 00 00 00 00 	movq   $0x0,(%rsp)
                int next_task = abs((t + 1) % (data->thread_count));
    80eb:	89 44 24 1c          	mov    %eax,0x1c(%rsp)
          int b = data->thread->real_thread_index;
    80ef:	49 63 46 08          	movslq 0x8(%r14),%rax
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    80f3:	48 8d 0c c0          	lea    (%rax,%rax,8),%rcx
          int b = data->thread->real_thread_index;
    80f7:	49 89 c7             	mov    %rax,%r15
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    80fa:	48 c1 e0 08          	shl    $0x8,%rax
    80fe:	48 c1 e1 05          	shl    $0x5,%rcx
    8102:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    8107:	48 89 cd             	mov    %rcx,%rbp
    810a:	44 89 e1             	mov    %r12d,%ecx
    810d:	eb 1a                	jmp    8129 <barriered_work+0x139>
    810f:	90                   	nop
          for (int y = 0; y < data->mailbox_thread_count ; y++) {
    8110:	48 83 04 24 01       	addq   $0x1,(%rsp)
    8115:	48 8b 04 24          	mov    (%rsp),%rax
    8119:	48 81 c6 20 01 00 00 	add    $0x120,%rsi
    8120:	49 39 c2             	cmp    %rax,%r10
    8123:	0f 84 37 02 00 00    	je     8360 <barriered_work+0x370>
                if (y == b) { continue; }
    8129:	8b 04 24             	mov    (%rsp),%eax
    812c:	41 39 c7             	cmp    %eax,%r15d
    812f:	74 df                	je     8110 <barriered_work+0x120>
                    if (data->thread->all_threads[y].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].swap == 0 && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN && data->thread->all_threads[y].tasks[t].mailboxes[b].kind == MAILBOX_FOREIGN) {
    8131:	49 8b 56 20          	mov    0x20(%r14),%rdx
    8135:	48 8b 7c 32 38       	mov    0x38(%rdx,%rsi,1),%rdi
    813a:	4a 8d 04 2f          	lea    (%rdi,%r13,1),%rax
    813e:	44 8b 80 a0 01 00 00 	mov    0x1a0(%rax),%r8d
    8145:	45 85 c0             	test   %r8d,%r8d
    8148:	75 c6                	jne    8110 <barriered_work+0x120>
    814a:	4c 8b 44 2a 38       	mov    0x38(%rdx,%rbp,1),%r8
    814f:	4b 8d 14 28          	lea    (%r8,%r13,1),%rdx
    8153:	44 8b 8a a0 01 00 00 	mov    0x1a0(%rdx),%r9d
    815a:	45 85 c9             	test   %r9d,%r9d
    815d:	75 b1                	jne    8110 <barriered_work+0x120>
    815f:	4c 8b 24 24          	mov    (%rsp),%r12
    8163:	48 8b 92 70 01 00 00 	mov    0x170(%rdx),%rdx
    816a:	49 c1 e4 08          	shl    $0x8,%r12
    816e:	42 83 bc 22 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rdx,%r12,1)
    8177:	75 97                	jne    8110 <barriered_work+0x120>
    8179:	48 8b 80 70 01 00 00 	mov    0x170(%rax),%rax
    8180:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    8185:	83 bc 10 b0 00 00 00 02 	cmpl   $0x2,0xb0(%rax,%rdx,1)
    818d:	75 81                	jne    8110 <barriered_work+0x120>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    818f:	48 63 44 24 1c       	movslq 0x1c(%rsp),%rax
    8194:	85 c0                	test   %eax,%eax
    8196:	0f 8e 74 ff ff ff    	jle    8110 <barriered_work+0x120>
    819c:	48 89 c2             	mov    %rax,%rdx
    819f:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    81a4:	b8 70 01 00 00       	mov    $0x170,%eax
    81a9:	48 c1 e2 09          	shl    $0x9,%rdx
    81ad:	89 4c 24 30          	mov    %ecx,0x30(%rsp)
    81b1:	44 89 7c 24 34       	mov    %r15d,0x34(%rsp)
    81b6:	4c 8d 9a a0 01 00 00 	lea    0x1a0(%rdx),%r11
    81bd:	48 89 54 24 38       	mov    %rdx,0x38(%rsp)
    81c2:	4c 89 6c 24 28       	mov    %r13,0x28(%rsp)
    81c7:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    81cc:	4c 89 54 24 40       	mov    %r10,0x40(%rsp)
    81d1:	44 8b 54 24 1c       	mov    0x1c(%rsp),%r10d
    81d6:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
    81db:	48 89 c6             	mov    %rax,%rsi
    81de:	66 90                	xchg   %ax,%ax
                        int next_task = abs((nn + 1) % data->thread_count);
    81e0:	41 83 c1 01          	add    $0x1,%r9d
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    81e4:	49 8b 0c 30          	mov    (%r8,%rsi,1),%rcx
                        int next_task = abs((nn + 1) % data->thread_count);
    81e8:	44 89 c8             	mov    %r9d,%eax
    81eb:	99                   	cltd
                        struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    81ec:	4c 01 e1             	add    %r12,%rcx
                        int next_task = abs((nn + 1) % data->thread_count);
    81ef:	41 f7 fa             	idiv   %r10d
    return mailbox->lower;
    81f2:	4c 8b 31             	mov    (%rcx),%r14
    81f5:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    mailbox->lower = data;
    81fa:	4c 8b b1 80 00 00 00 	mov    0x80(%rcx),%r14
                        struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    8201:	48 63 d2             	movslq %edx,%rdx
    8204:	48 c1 e2 09          	shl    $0x9,%rdx
    8208:	48 8b 84 17 70 01 00 00 	mov    0x170(%rdi,%rdx,1),%rax
    8210:	4c 01 e8             	add    %r13,%rax
    return mailbox->lower;
    8213:	4c 8b 38             	mov    (%rax),%r15
    return mailbox->higher;
    8216:	48 8b 90 80 00 00 00 	mov    0x80(%rax),%rdx
    mailbox->lower = data;
    821d:	4c 89 30             	mov    %r14,(%rax)
    mailbox->higher = data;
    8220:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    8225:	4c 89 b0 80 00 00 00 	mov    %r14,0x80(%rax)
    mailbox->lower = data;
    822c:	48 89 11             	mov    %rdx,(%rcx)
    mailbox->higher = data;
    822f:	4c 89 b9 80 00 00 00 	mov    %r15,0x80(%rcx)
    8236:	b9 a0 01 00 00       	mov    $0x1a0,%ecx
    823b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                          data->thread->all_threads[l2].tasks[jj].swap = 1;
    8240:	41 c7 04 08 01 00 00 00 	movl   $0x1,(%r8,%rcx,1)
                          data->thread->all_threads[t2].tasks[jj].swap = 1;
    8248:	c7 04 0f 01 00 00 00 	movl   $0x1,(%rdi,%rcx,1)
                        for (int jj = 0 ; jj < data->thread_count; jj++) {
    824f:	48 81 c1 00 02 00 00 	add    $0x200,%rcx
    8256:	4c 39 d9             	cmp    %r11,%rcx
    8259:	75 e5                	jne    8240 <barriered_work+0x250>
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    825b:	48 8b 0c 37          	mov    (%rdi,%rsi,1),%rcx
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    825f:	48 8b 00             	mov    (%rax),%rax
                             ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    8262:	41 c7 87 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%r15)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    826d:	48 81 c6 00 02 00 00 	add    $0x200,%rsi
                             ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    8274:	4a 8b 8c 29 80 00 00 00 	mov    0x80(%rcx,%r13,1),%rcx
    827c:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
                            ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    8286:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                            ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    8290:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                      for (int nn = 0; nn < data->thread_count; nn++) {
    829a:	45 39 ca             	cmp    %r9d,%r10d
    829d:	0f 85 3d ff ff ff    	jne    81e0 <barriered_work+0x1f0>
    82a3:	4c 8b 74 24 20       	mov    0x20(%rsp),%r14
    82a8:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    82ad:	b8 70 01 00 00       	mov    $0x170,%eax
    82b2:	4c 8b 6c 24 28       	mov    0x28(%rsp),%r13
    82b7:	8b 4c 24 30          	mov    0x30(%rsp),%ecx
    82bb:	44 8b 7c 24 34       	mov    0x34(%rsp),%r15d
    82c0:	4c 8b 54 24 40       	mov    0x40(%rsp),%r10
    82c5:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    82ca:	4c 8d 9a 70 01 00 00 	lea    0x170(%rdx),%r11
    82d1:	48 8b 74 24 48       	mov    0x48(%rsp),%rsi
    82d6:	4c 8b 74 24 10       	mov    0x10(%rsp),%r14
    82db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                          if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    82e0:	48 8b 14 07          	mov    (%rdi,%rax,1),%rdx
    82e4:	4d 8b 0c 00          	mov    (%r8,%rax,1),%r9
    82e8:	4a 8b 14 32          	mov    (%rdx,%r14,1),%rdx
    82ec:	4b 39 14 21          	cmp    %rdx,(%r9,%r12,1)
    82f0:	0f 84 8e 02 00 00    	je     8584 <barriered_work+0x594>
                        for (int nn = 0; nn < data->thread_count; nn++) {
    82f6:	48 05 00 02 00 00    	add    $0x200,%rax
    82fc:	4c 39 d8             	cmp    %r11,%rax
    82ff:	75 df                	jne    82e0 <barriered_work+0x2f0>
    8301:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    8306:	e9 05 fe ff ff       	jmp    8110 <barriered_work+0x120>
    830b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (data->thread_index == 0 && data->thread->global->request_group_sync == -1 && data->thread->group == 0 && data->arrived % 100000 == 0) {
    8310:	48 63 af 30 01 00 00 	movslq 0x130(%rdi),%rbp
    8317:	85 ed                	test   %ebp,%ebp
    8319:	0f 85 79 fd ff ff    	jne    8098 <barriered_work+0xa8>
    831f:	44 8b 88 f0 00 00 00 	mov    0xf0(%rax),%r9d
    8326:	45 85 c9             	test   %r9d,%r9d
    8329:	0f 85 69 fd ff ff    	jne    8098 <barriered_work+0xa8>
    832f:	69 87 80 00 00 00 1d e6 cb 0b 	imul   $0xbcbe61d,0x80(%rdi),%eax
    8339:	05 40 7c 0a 00       	add    $0xa7c40,%eax
    833e:	c1 c8 05             	ror    $0x5,%eax
    8341:	3d c4 a7 00 00       	cmp    $0xa7c4,%eax
    8346:	0f 87 4c fd ff ff    	ja     8098 <barriered_work+0xa8>
      data->thread->global->request_group_sync = 0;
    834c:	48 c7 01 00 00 00 00 	movq   $0x0,(%rcx)
    8353:	e9 40 fd ff ff       	jmp    8098 <barriered_work+0xa8>
    8358:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    8360:	41 89 cc             	mov    %ecx,%r12d
        fswap(data); 
    8363:	48 89 df             	mov    %rbx,%rdi
    8366:	e8 35 fb ff ff       	call   7ea0 <fswap>
        receive(data);
    836b:	48 89 df             	mov    %rbx,%rdi
    836e:	e8 ad f6 ff ff       	call   7a20 <receive>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    8373:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    837a:	31 ff                	xor    %edi,%edi
    837c:	48 c1 e6 05          	shl    $0x5,%rsi
    8380:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    8387:	e8 d4 9f ff ff       	call   2360 <clock_gettime@plt>
      int modcount = ++data->thread->protected_state->modcount;
    838c:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    8393:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      int modcount = ++data->thread->protected_state->modcount;
    839a:	48 8b 50 48          	mov    0x48(%rax),%rdx
    839e:	8b 72 10             	mov    0x10(%rdx),%esi
    83a1:	8d 6e 01             	lea    0x1(%rsi),%ebp
    83a4:	89 6a 10             	mov    %ebp,0x10(%rdx)
      while (data->scheduled == 1) {
    83a7:	75 55                	jne    83fe <barriered_work+0x40e>
    83a9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    83b0:	48 63 93 30 01 00 00 	movslq 0x130(%rbx),%rdx
    83b7:	48 8b 40 18          	mov    0x18(%rax),%rax
    83bb:	48 63 7b 04          	movslq 0x4(%rbx),%rdi
        data->n++;
    83bf:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
        data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    83c7:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    83cb:	48 c1 e7 09          	shl    $0x9,%rdi
    83cf:	48 03 78 38          	add    0x38(%rax),%rdi
    83d3:	ff 93 20 01 00 00    	call   *0x120(%rbx)
      while (data->scheduled == 1) {
    83d9:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
      if (modcount != data->thread->protected_state->modcount) {
    83e0:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
      while (data->scheduled == 1) {
    83e7:	74 c7                	je     83b0 <barriered_work+0x3c0>
      if (modcount != data->thread->protected_state->modcount) {
    83e9:	48 8b 40 48          	mov    0x48(%rax),%rax
    83ed:	3b 68 10             	cmp    0x10(%rax),%ebp
    83f0:	74 0c                	je     83fe <barriered_work+0x40e>
    83f2:	48 8d 3d 3d 0f 00 00 	lea    0xf3d(%rip),%rdi        # 9336 <_IO_stdin_used+0x336>
    83f9:	e8 42 9f ff ff       	call   2340 <puts@plt>
      clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    83fe:	48 8b b3 60 01 00 00 	mov    0x160(%rbx),%rsi
    8405:	31 ff                	xor    %edi,%edi
    8407:	48 c1 e6 05          	shl    $0x5,%rsi
    840b:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    8412:	48 83 c6 10          	add    $0x10,%rsi
    8416:	e8 45 9f ff ff       	call   2360 <clock_gettime@plt>
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    841b:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    8422:	48 83 c0 01          	add    $0x1,%rax
    8426:	48 99                	cqto
    8428:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    if (t == data->thread_count - 1) {
    842f:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    8435:	83 e8 01             	sub    $0x1,%eax
      data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    8438:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    if (t == data->thread_count - 1) {
    843f:	44 39 e0             	cmp    %r12d,%eax
    8442:	74 53                	je     8497 <barriered_work+0x4a7>
    data->swap = 0;
    8444:	c7 83 a0 01 00 00 00 00 00 00 	movl   $0x0,0x1a0(%rbx)
    return 0;
    844e:	e9 f8 fb ff ff       	jmp    804b <barriered_work+0x5b>
    8453:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      receive(data);
    8458:	e8 c3 f5 ff ff       	call   7a20 <receive>
      while (data->scheduled == 1) {
    845d:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    8464:	75 1b                	jne    8481 <barriered_work+0x491>
    8466:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        data->n++;
    8470:	48 83 83 08 01 00 00 01 	addq   $0x1,0x108(%rbx)
      while (data->scheduled == 1) {
    8478:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    847f:	74 ef                	je     8470 <barriered_work+0x480>
      sendm(data);
    8481:	48 89 df             	mov    %rbx,%rdi
    8484:	e8 e7 f6 ff ff       	call   7b70 <sendm>
    if (t == data->thread_count - 1) {
    8489:	8b 83 34 01 00 00    	mov    0x134(%rbx),%eax
    848f:	83 e8 01             	sub    $0x1,%eax
    8492:	44 39 e0             	cmp    %r12d,%eax
    8495:	75 ad                	jne    8444 <barriered_work+0x454>
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    8497:	48 63 93 48 01 00 00 	movslq 0x148(%rbx),%rdx
    849e:	85 d2                	test   %edx,%edx
    84a0:	7e a2                	jle    8444 <barriered_work+0x454>
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    84a2:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    84a9:	48 c1 e2 09          	shl    $0x9,%rdx
    84ad:	48 63 41 08          	movslq 0x8(%rcx),%rax
    84b1:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    84b5:	48 c1 e0 05          	shl    $0x5,%rax
    84b9:	48 03 41 20          	add    0x20(%rcx),%rax
    84bd:	48 8b 40 38          	mov    0x38(%rax),%rax
    84c1:	48 8d 0c 02          	lea    (%rdx,%rax,1),%rcx
    84c5:	80 e6 02             	and    $0x2,%dh
    84c8:	74 16                	je     84e0 <barriered_work+0x4f0>
    84ca:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    84d1:	48 05 00 02 00 00    	add    $0x200,%rax
    84d7:	48 39 c8             	cmp    %rcx,%rax
    84da:	0f 84 64 ff ff ff    	je     8444 <barriered_work+0x454>
          data->thread->all_threads[data->thread->real_thread_index].tasks[tt].wait++;
    84e0:	83 80 a4 01 00 00 01 	addl   $0x1,0x1a4(%rax)
    84e7:	83 80 a4 03 00 00 01 	addl   $0x1,0x3a4(%rax)
        for (int tt = 0 ; tt < data->task_count ; tt++) {
    84ee:	48 05 00 04 00 00    	add    $0x400,%rax
    84f4:	48 39 c8             	cmp    %rcx,%rax
    84f7:	75 e7                	jne    84e0 <barriered_work+0x4f0>
    84f9:	e9 46 ff ff ff       	jmp    8444 <barriered_work+0x454>
    84fe:	66 90                	xchg   %ax,%ax
    if (data->thread_index == data->thread->global->request_thread_sync && data->thread->global->request_group_sync == data->thread->group && data->thread->global->request_group_sync != -1) {
    8500:	39 c5                	cmp    %eax,%ebp
    8502:	0f 85 90 fb ff ff    	jne    8098 <barriered_work+0xa8>
      struct ProtectedState *protected = data->thread->global->protected_state;
    8508:	48 8b 69 08          	mov    0x8(%rcx),%rbp
      nanosleep(&preempt , &rem);
    850c:	48 8d 74 24 60       	lea    0x60(%rsp),%rsi
    8511:	48 8d 7c 24 50       	lea    0x50(%rsp),%rdi
      int modcount = ++protected->modcount;
    8516:	8b 45 10             	mov    0x10(%rbp),%eax
      protected->protected++;
    8519:	48 83 45 00 01       	addq   $0x1,0x0(%rbp)
      int modcount = ++protected->modcount;
    851e:	44 8d 60 01          	lea    0x1(%rax),%r12d
    8522:	44 89 65 10          	mov    %r12d,0x10(%rbp)
      nanosleep(&preempt , &rem);
    8526:	e8 85 9e ff ff       	call   23b0 <nanosleep@plt>
      if (protected->modcount != modcount) {
    852b:	44 3b 65 10          	cmp    0x10(%rbp),%r12d
    852f:	74 0c                	je     853d <barriered_work+0x54d>
    8531:	48 8d 3d c6 0d 00 00 	lea    0xdc6(%rip),%rdi        # 92fe <_IO_stdin_used+0x2fe>
    8538:	e8 03 9e ff ff       	call   2340 <puts@plt>
      data->thread->global->request_thread_sync = (data->thread_index + 1) % data->thread_count;
    853d:	48 63 ab 30 01 00 00 	movslq 0x130(%rbx),%rbp
    8544:	48 8b 8b 28 01 00 00 	mov    0x128(%rbx),%rcx
    854b:	8d 45 01             	lea    0x1(%rbp),%eax
    854e:	48 8b b1 f8 00 00 00 	mov    0xf8(%rcx),%rsi
    8555:	99                   	cltd
    8556:	f7 bb 34 01 00 00    	idivl  0x134(%rbx)
    855c:	89 56 04             	mov    %edx,0x4(%rsi)
      if (data->thread_index == 1) {
    855f:	83 fd 01             	cmp    $0x1,%ebp
    8562:	0f 85 30 fb ff ff    	jne    8098 <barriered_work+0xa8>
        data->thread->global->request_group_sync = (data->thread->group + 1) % data->thread->group_count;
    8568:	8b 81 f0 00 00 00    	mov    0xf0(%rcx),%eax
    856e:	83 c0 01             	add    $0x1,%eax
    8571:	99                   	cltd
    8572:	f7 b9 c8 00 00 00    	idivl  0xc8(%rcx)
    8578:	89 16                	mov    %edx,(%rsi)
    857a:	e9 19 fb ff ff       	jmp    8098 <barriered_work+0xa8>
}
    857f:	e8 0c 9e ff ff       	call   2390 <__stack_chk_fail@plt>
    8584:	bf 01 00 00 00       	mov    $0x1,%edi
    8589:	48 8d 35 8b 0d 00 00 	lea    0xd8b(%rip),%rsi        # 931b <_IO_stdin_used+0x31b>
    8590:	31 c0                	xor    %eax,%eax
    8592:	e8 29 9f ff ff       	call   24c0 <__printf_chk@plt>
                            exit(1);
    8597:	bf 01 00 00 00       	mov    $0x1,%edi
    859c:	e8 7f 9f ff ff       	call   2520 <exit@plt>
    85a1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    85ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000085b0 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    85b0:	f3 0f 1e fa          	endbr64
    85b4:	53                   	push   %rbx
    85b5:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    85b8:	e8 63 f0 ff ff       	call   7620 <barriered_work_ingest>
  barriered_work(data);
    85bd:	48 89 df             	mov    %rbx,%rdi
}
    85c0:	5b                   	pop    %rbx
  barriered_work(data);
    85c1:	e9 2a fa ff ff       	jmp    7ff0 <barriered_work>
    85c6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000085d0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    85d0:	f3 0f 1e fa          	endbr64
}
    85d4:	31 c0                	xor    %eax,%eax
    85d6:	c3                   	ret
    85d7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000085e0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    85e0:	f3 0f 1e fa          	endbr64
    85e4:	31 c0                	xor    %eax,%eax
    85e6:	c3                   	ret
    85e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000085f0 <after>:
int after(struct timespec left, struct timespec right) {
    85f0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    85f4:	31 c0                	xor    %eax,%eax
    85f6:	48 39 d7             	cmp    %rdx,%rdi
    85f9:	7e 08                	jle    8603 <after+0x13>
    85fb:	31 c0                	xor    %eax,%eax
    85fd:	48 39 ce             	cmp    %rcx,%rsi
    8600:	0f 9f c0             	setg   %al
}
    8603:	c3                   	ret
    8604:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    860f:	90                   	nop

0000000000008610 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    8610:	f3 0f 1e fa          	endbr64
    8614:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    8619:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    861e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8620:	48 39 d7             	cmp    %rdx,%rdi
    8623:	7f 18                	jg     863d <within+0x2d>
    8625:	4d 39 d8             	cmp    %r11,%r8
    8628:	0f 9e c2             	setle  %dl
    862b:	48 39 ce             	cmp    %rcx,%rsi
    862e:	0f 9e c0             	setle  %al
    8631:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8633:	31 c0                	xor    %eax,%eax
    8635:	4d 39 d1             	cmp    %r10,%r9
    8638:	0f 9e c0             	setle  %al
    863b:	21 d0                	and    %edx,%eax
}
    863d:	c3                   	ret
    863e:	66 90                	xchg   %ax,%ax

0000000000008640 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    8640:	f3 0f 1e fa          	endbr64
    8644:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    8649:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    864e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    8653:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    8658:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    865d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    8662:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    8667:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    866c:	48 39 fe             	cmp    %rdi,%rsi
    866f:	7d 2f                	jge    86a0 <overlap+0x60>
    8671:	48 39 ca             	cmp    %rcx,%rdx
    8674:	7d 62                	jge    86d8 <overlap+0x98>
    8676:	4d 39 da             	cmp    %r11,%r10
    8679:	7d 0e                	jge    8689 <overlap+0x49>
    return 1;
    867b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    8680:	4d 39 c1             	cmp    %r8,%r9
    8683:	0f 8c 7f 00 00 00    	jl     8708 <overlap+0xc8>
  return 0;
    8689:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    868b:	4d 39 c1             	cmp    %r8,%r9
    868e:	7f 4c                	jg     86dc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8690:	31 c0                	xor    %eax,%eax
    8692:	4d 39 da             	cmp    %r11,%r10
    8695:	0f 9e c0             	setle  %al
    8698:	c3                   	ret
    8699:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    86a0:	7e 4e                	jle    86f0 <overlap+0xb0>
    86a2:	48 39 ca             	cmp    %rcx,%rdx
    86a5:	7f 39                	jg     86e0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    86a7:	75 31                	jne    86da <overlap+0x9a>
    86a9:	4d 39 c1             	cmp    %r8,%r9
    86ac:	7c 2c                	jl     86da <overlap+0x9a>
    return 1;
    86ae:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    86b3:	4d 39 da             	cmp    %r11,%r10
    86b6:	7d 24                	jge    86dc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    86b8:	48 39 ca             	cmp    %rcx,%rdx
    86bb:	0f 94 c2             	sete   %dl
    86be:	48 39 fe             	cmp    %rdi,%rsi
    86c1:	0f 94 c0             	sete   %al
    86c4:	21 c2                	and    %eax,%edx
    86c6:	31 c0                	xor    %eax,%eax
    86c8:	4d 39 c1             	cmp    %r8,%r9
    86cb:	0f 94 c0             	sete   %al
    86ce:	21 d0                	and    %edx,%eax
    86d0:	c3                   	ret
    86d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    86d8:	74 af                	je     8689 <overlap+0x49>
  return 0;
    86da:	31 c0                	xor    %eax,%eax
}
    86dc:	c3                   	ret
    86dd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    86e0:	4d 39 da             	cmp    %r11,%r10
    86e3:	7e c4                	jle    86a9 <overlap+0x69>
    return 1;
    86e5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    86ea:	4d 39 c1             	cmp    %r8,%r9
    86ed:	7e ba                	jle    86a9 <overlap+0x69>
    86ef:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    86f0:	48 39 ca             	cmp    %rcx,%rdx
    86f3:	7c 94                	jl     8689 <overlap+0x49>
    86f5:	4d 39 c1             	cmp    %r8,%r9
    86f8:	7d b4                	jge    86ae <overlap+0x6e>
    86fa:	48 39 ca             	cmp    %rcx,%rdx
    86fd:	74 91                	je     8690 <overlap+0x50>
    86ff:	eb d9                	jmp    86da <overlap+0x9a>
    8701:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    8708:	c3                   	ret
    8709:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000008710 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    8710:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    8714:	85 f6                	test   %esi,%esi
    8716:	0f 8e 44 03 00 00    	jle    8a60 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    871c:	41 57                	push   %r15
    871e:	41 89 f7             	mov    %esi,%r15d
    8721:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    8723:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    8726:	41 55                	push   %r13
    8728:	41 54                	push   %r12
    872a:	55                   	push   %rbp
    872b:	53                   	push   %rbx
    872c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    8730:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    8734:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    8739:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    873e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    8741:	45 39 e6             	cmp    %r12d,%r14d
    8744:	0f 84 4e 02 00 00    	je     8998 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    874a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    874f:	8b 50 08             	mov    0x8(%rax),%edx
    8752:	85 d2                	test   %edx,%edx
    8754:	0f 8e 3e 02 00 00    	jle    8998 <verify+0x288>
    875a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    875f:	31 c9                	xor    %ecx,%ecx
    8761:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    8766:	31 c0                	xor    %eax,%eax
    8768:	44 89 f2             	mov    %r14d,%edx
    876b:	bf 01 00 00 00       	mov    $0x1,%edi
    8770:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    8775:	48 8d 35 ca 0b 00 00 	lea    0xbca(%rip),%rsi        # 9346 <_IO_stdin_used+0x346>
    877c:	e8 3f 9d ff ff       	call   24c0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    8781:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    8786:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    878b:	8b 40 08             	mov    0x8(%rax),%eax
    878e:	85 c0                	test   %eax,%eax
    8790:	0f 8e e6 01 00 00    	jle    897c <verify+0x26c>
    8796:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    8799:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    879e:	31 db                	xor    %ebx,%ebx
    87a0:	48 c1 e0 09          	shl    $0x9,%rax
    87a4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    87a9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    87ae:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    87b3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    87b8:	4c 8b 20             	mov    (%rax),%r12
    87bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    87c0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    87c5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    87ca:	49 89 de             	mov    %rbx,%r14
    87cd:	48 8d 35 87 0b 00 00 	lea    0xb87(%rip),%rsi        # 935b <_IO_stdin_used+0x35b>
    87d4:	49 c1 e6 09          	shl    $0x9,%r14
    87d8:	bf 01 00 00 00       	mov    $0x1,%edi
    87dd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    87e1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    87e9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    87ee:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    87f6:	31 c0                	xor    %eax,%eax
    87f8:	e8 c3 9c ff ff       	call   24c0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    87fd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8802:	4c 8b 20             	mov    (%rax),%r12
    8805:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    880e:	0f 8e 47 01 00 00    	jle    895b <verify+0x24b>
    8814:	4c 03 75 00          	add    0x0(%rbp),%r14
    8818:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    881d:	ba 01 00 00 00       	mov    $0x1,%edx
    8822:	4d 89 f5             	mov    %r14,%r13
    8825:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    882c:	4d 85 f6             	test   %r14,%r14
    882f:	0f 8e 21 01 00 00    	jle    8956 <verify+0x246>
    8835:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    8838:	48 89 d5             	mov    %rdx,%rbp
    883b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8840:	31 db                	xor    %ebx,%ebx
    8842:	4d 89 f2             	mov    %r14,%r10
    8845:	48 c1 e5 05          	shl    $0x5,%rbp
    8849:	48 83 ed 20          	sub    $0x20,%rbp
    884d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    8851:	49 89 ee             	mov    %rbp,%r14
    8854:	48 89 dd             	mov    %rbx,%rbp
    8857:	48 89 d3             	mov    %rdx,%rbx
    885a:	eb 31                	jmp    888d <verify+0x17d>
    885c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    8860:	4c 39 c2             	cmp    %r8,%rdx
    8863:	0f 8d 57 01 00 00    	jge    89c0 <verify+0x2b0>
    8869:	4c 39 df             	cmp    %r11,%rdi
    886c:	7e 05                	jle    8873 <verify+0x163>
    886e:	49 39 c1             	cmp    %rax,%r9
    8871:	7c 75                	jl     88e8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    8873:	4c 39 df             	cmp    %r11,%rdi
    8876:	0f 8d ab 01 00 00    	jge    8a27 <verify+0x317>
    887c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8880:	48 83 c5 01          	add    $0x1,%rbp
    8884:	49 39 ea             	cmp    %rbp,%r10
    8887:	0f 8e a9 00 00 00    	jle    8936 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    888d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    8894:	48 89 e8             	mov    %rbp,%rax
    8897:	48 c1 e0 05          	shl    $0x5,%rax
    889b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    88a2:	4c 01 f2             	add    %r14,%rdx
    88a5:	48 8b 08             	mov    (%rax),%rcx
    88a8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    88ac:	48 8b 32             	mov    (%rdx),%rsi
    88af:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    88b3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    88b7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    88bb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    88bf:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    88c3:	48 39 f1             	cmp    %rsi,%rcx
    88c6:	7c 98                	jl     8860 <verify+0x150>
    88c8:	0f 8e 42 01 00 00    	jle    8a10 <verify+0x300>
    88ce:	4c 39 c2             	cmp    %r8,%rdx
    88d1:	0f 8f f9 00 00 00    	jg     89d0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    88d7:	75 a7                	jne    8880 <verify+0x170>
    88d9:	4c 39 df             	cmp    %r11,%rdi
    88dc:	7f a2                	jg     8880 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    88de:	49 39 c1             	cmp    %rax,%r9
    88e1:	7c 9d                	jl     8880 <verify+0x170>
    88e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    88e8:	49 89 c1             	mov    %rax,%r9
    88eb:	48 89 f9             	mov    %rdi,%rcx
    88ee:	48 89 f2             	mov    %rsi,%rdx
    88f1:	bf 01 00 00 00       	mov    $0x1,%edi
    88f6:	48 8d 35 13 10 00 00 	lea    0x1013(%rip),%rsi        # 9910 <_IO_stdin_used+0x910>
    88fd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    88ff:	48 83 c5 01          	add    $0x1,%rbp
    8903:	e8 b8 9b ff ff       	call   24c0 <__printf_chk@plt>
    8908:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    890d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    8912:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8915:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    891a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8921:	4c 8b 20             	mov    (%rax),%r12
    8924:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    8929:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    892d:	49 39 ea             	cmp    %rbp,%r10
    8930:	0f 8f 57 ff ff ff    	jg     888d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    8936:	48 89 da             	mov    %rbx,%rdx
    8939:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    8940:	7d 14                	jge    8956 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    8942:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    8949:	48 83 c2 01          	add    $0x1,%rdx
    894d:	4d 85 f6             	test   %r14,%r14
    8950:	0f 8f e2 fe ff ff    	jg     8838 <verify+0x128>
    8956:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    895b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    8960:	48 83 c3 01          	add    $0x1,%rbx
    8964:	39 58 08             	cmp    %ebx,0x8(%rax)
    8967:	0f 8f 53 fe ff ff    	jg     87c0 <verify+0xb0>
    896d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    8972:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    8977:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    897c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    8981:	48 83 c1 01          	add    $0x1,%rcx
    8985:	39 48 08             	cmp    %ecx,0x8(%rax)
    8988:	0f 8f d8 fd ff ff    	jg     8766 <verify+0x56>
    898e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    8993:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    8998:	48 81 44 24 10 20 01 00 00 	addq   $0x120,0x10(%rsp)
    89a1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    89a6:	41 39 c7             	cmp    %eax,%r15d
    89a9:	0f 84 86 00 00 00    	je     8a35 <verify+0x325>
    89af:	41 89 c4             	mov    %eax,%r12d
    89b2:	e9 8a fd ff ff       	jmp    8741 <verify+0x31>
    89b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    89c0:	0f 85 ba fe ff ff    	jne    8880 <verify+0x170>
    89c6:	e9 a8 fe ff ff       	jmp    8873 <verify+0x163>
    89cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    89d0:	49 39 c1             	cmp    %rax,%r9
    89d3:	7e 09                	jle    89de <verify+0x2ce>
    89d5:	4c 39 df             	cmp    %r11,%rdi
    89d8:	0f 8c 0a ff ff ff    	jl     88e8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    89de:	4c 39 df             	cmp    %r11,%rdi
    89e1:	0f 8f 99 fe ff ff    	jg     8880 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    89e7:	49 39 c1             	cmp    %rax,%r9
    89ea:	0f 8d f8 fe ff ff    	jge    88e8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    89f0:	48 39 f1             	cmp    %rsi,%rcx
    89f3:	0f 85 87 fe ff ff    	jne    8880 <verify+0x170>
    89f9:	4c 39 c2             	cmp    %r8,%rdx
    89fc:	0f 85 7e fe ff ff    	jne    8880 <verify+0x170>
    8a02:	4c 39 df             	cmp    %r11,%rdi
    8a05:	0f 84 dd fe ff ff    	je     88e8 <verify+0x1d8>
    8a0b:	e9 70 fe ff ff       	jmp    8880 <verify+0x170>
    8a10:	4c 39 c2             	cmp    %r8,%rdx
    8a13:	0f 8c 5a fe ff ff    	jl     8873 <verify+0x163>
    8a19:	4c 39 df             	cmp    %r11,%rdi
    8a1c:	7e c9                	jle    89e7 <verify+0x2d7>
    8a1e:	4c 39 c2             	cmp    %r8,%rdx
    8a21:	0f 85 59 fe ff ff    	jne    8880 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    8a27:	49 39 c1             	cmp    %rax,%r9
    8a2a:	0f 8f 50 fe ff ff    	jg     8880 <verify+0x170>
    8a30:	e9 b3 fe ff ff       	jmp    88e8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    8a35:	48 81 44 24 18 20 01 00 00 	addq   $0x120,0x18(%rsp)
    8a3e:	41 8d 46 01          	lea    0x1(%r14),%eax
    8a42:	45 39 e6             	cmp    %r12d,%r14d
    8a45:	74 08                	je     8a4f <verify+0x33f>
    8a47:	41 89 c6             	mov    %eax,%r14d
    8a4a:	e9 ea fc ff ff       	jmp    8739 <verify+0x29>
}
    8a4f:	48 83 c4 58          	add    $0x58,%rsp
    8a53:	31 c0                	xor    %eax,%eax
    8a55:	5b                   	pop    %rbx
    8a56:	5d                   	pop    %rbp
    8a57:	41 5c                	pop    %r12
    8a59:	41 5d                	pop    %r13
    8a5b:	41 5e                	pop    %r14
    8a5d:	41 5f                	pop    %r15
    8a5f:	c3                   	ret
    8a60:	31 c0                	xor    %eax,%eax
    8a62:	c3                   	ret

Disassembly of section .fini:

0000000000008a64 <_fini>:
    8a64:	f3 0f 1e fa          	endbr64
    8a68:	48 83 ec 08          	sub    $0x8,%rsp
    8a6c:	48 83 c4 08          	add    $0x8,%rsp
    8a70:	c3                   	ret
