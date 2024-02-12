
multibarrier-evented:     file format elf64-x86-64


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
    2020:	ff 35 32 8e 00 00    	push   0x8e32(%rip)        # ae58 <_GLOBAL_OFFSET_TABLE_+0x8>
    2026:	ff 25 34 8e 00 00    	jmp    *0x8e34(%rip)        # ae60 <_GLOBAL_OFFSET_TABLE_+0x10>
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
    2314:	ff 25 de 8c 00 00    	jmp    *0x8cde(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    231a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .plt.sec:

0000000000002320 <free@plt>:
    2320:	f3 0f 1e fa          	endbr64
    2324:	ff 25 3e 8b 00 00    	jmp    *0x8b3e(%rip)        # ae68 <free@GLIBC_2.2.5>
    232a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002330 <putchar@plt>:
    2330:	f3 0f 1e fa          	endbr64
    2334:	ff 25 36 8b 00 00    	jmp    *0x8b36(%rip)        # ae70 <putchar@GLIBC_2.2.5>
    233a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002340 <pthread_setaffinity_np@plt>:
    2340:	f3 0f 1e fa          	endbr64
    2344:	ff 25 2e 8b 00 00    	jmp    *0x8b2e(%rip)        # ae78 <pthread_setaffinity_np@GLIBC_2.34>
    234a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002350 <puts@plt>:
    2350:	f3 0f 1e fa          	endbr64
    2354:	ff 25 26 8b 00 00    	jmp    *0x8b26(%rip)        # ae80 <puts@GLIBC_2.2.5>
    235a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002360 <setsockopt@plt>:
    2360:	f3 0f 1e fa          	endbr64
    2364:	ff 25 1e 8b 00 00    	jmp    *0x8b1e(%rip)        # ae88 <setsockopt@GLIBC_2.2.5>
    236a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002370 <clock_gettime@plt>:
    2370:	f3 0f 1e fa          	endbr64
    2374:	ff 25 16 8b 00 00    	jmp    *0x8b16(%rip)        # ae90 <clock_gettime@GLIBC_2.17>
    237a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002380 <fclose@plt>:
    2380:	f3 0f 1e fa          	endbr64
    2384:	ff 25 0e 8b 00 00    	jmp    *0x8b0e(%rip)        # ae98 <fclose@GLIBC_2.2.5>
    238a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002390 <strlen@plt>:
    2390:	f3 0f 1e fa          	endbr64
    2394:	ff 25 06 8b 00 00    	jmp    *0x8b06(%rip)        # aea0 <strlen@GLIBC_2.2.5>
    239a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023a0 <__stack_chk_fail@plt>:
    23a0:	f3 0f 1e fa          	endbr64
    23a4:	ff 25 fe 8a 00 00    	jmp    *0x8afe(%rip)        # aea8 <__stack_chk_fail@GLIBC_2.4>
    23aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023b0 <io_uring_submit@plt>:
    23b0:	f3 0f 1e fa          	endbr64
    23b4:	ff 25 f6 8a 00 00    	jmp    *0x8af6(%rip)        # aeb0 <io_uring_submit@LIBURING_2.0>
    23ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023c0 <nanosleep@plt>:
    23c0:	f3 0f 1e fa          	endbr64
    23c4:	ff 25 ee 8a 00 00    	jmp    *0x8aee(%rip)        # aeb8 <nanosleep@GLIBC_2.2.5>
    23ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023d0 <strrchr@plt>:
    23d0:	f3 0f 1e fa          	endbr64
    23d4:	ff 25 e6 8a 00 00    	jmp    *0x8ae6(%rip)        # aec0 <strrchr@GLIBC_2.2.5>
    23da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023e0 <fputs@plt>:
    23e0:	f3 0f 1e fa          	endbr64
    23e4:	ff 25 de 8a 00 00    	jmp    *0x8ade(%rip)        # aec8 <fputs@GLIBC_2.2.5>
    23ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000023f0 <close@plt>:
    23f0:	f3 0f 1e fa          	endbr64
    23f4:	ff 25 d6 8a 00 00    	jmp    *0x8ad6(%rip)        # aed0 <close@GLIBC_2.2.5>
    23fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002400 <strtok_r@plt>:
    2400:	f3 0f 1e fa          	endbr64
    2404:	ff 25 ce 8a 00 00    	jmp    *0x8ace(%rip)        # aed8 <strtok_r@GLIBC_2.2.5>
    240a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002410 <read@plt>:
    2410:	f3 0f 1e fa          	endbr64
    2414:	ff 25 c6 8a 00 00    	jmp    *0x8ac6(%rip)        # aee0 <read@GLIBC_2.2.5>
    241a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002420 <calloc@plt>:
    2420:	f3 0f 1e fa          	endbr64
    2424:	ff 25 be 8a 00 00    	jmp    *0x8abe(%rip)        # aee8 <calloc@GLIBC_2.2.5>
    242a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002430 <strcmp@plt>:
    2430:	f3 0f 1e fa          	endbr64
    2434:	ff 25 b6 8a 00 00    	jmp    *0x8ab6(%rip)        # aef0 <strcmp@GLIBC_2.2.5>
    243a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002440 <__memcpy_chk@plt>:
    2440:	f3 0f 1e fa          	endbr64
    2444:	ff 25 ae 8a 00 00    	jmp    *0x8aae(%rip)        # aef8 <__memcpy_chk@GLIBC_2.3.4>
    244a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002450 <stat@plt>:
    2450:	f3 0f 1e fa          	endbr64
    2454:	ff 25 a6 8a 00 00    	jmp    *0x8aa6(%rip)        # af00 <stat@GLIBC_2.33>
    245a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002460 <memcpy@plt>:
    2460:	f3 0f 1e fa          	endbr64
    2464:	ff 25 9e 8a 00 00    	jmp    *0x8a9e(%rip)        # af08 <memcpy@GLIBC_2.14>
    246a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002470 <io_uring_queue_init@plt>:
    2470:	f3 0f 1e fa          	endbr64
    2474:	ff 25 96 8a 00 00    	jmp    *0x8a96(%rip)        # af10 <io_uring_queue_init@LIBURING_2.0>
    247a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002480 <eventfd_write@plt>:
    2480:	f3 0f 1e fa          	endbr64
    2484:	ff 25 8e 8a 00 00    	jmp    *0x8a8e(%rip)        # af18 <eventfd_write@GLIBC_2.7>
    248a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002490 <pthread_mutex_unlock@plt>:
    2490:	f3 0f 1e fa          	endbr64
    2494:	ff 25 86 8a 00 00    	jmp    *0x8a86(%rip)        # af20 <pthread_mutex_unlock@GLIBC_2.2.5>
    249a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024a0 <malloc@plt>:
    24a0:	f3 0f 1e fa          	endbr64
    24a4:	ff 25 7e 8a 00 00    	jmp    *0x8a7e(%rip)        # af28 <malloc@GLIBC_2.2.5>
    24aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024b0 <listen@plt>:
    24b0:	f3 0f 1e fa          	endbr64
    24b4:	ff 25 76 8a 00 00    	jmp    *0x8a76(%rip)        # af30 <listen@GLIBC_2.2.5>
    24ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024c0 <__strcpy_chk@plt>:
    24c0:	f3 0f 1e fa          	endbr64
    24c4:	ff 25 6e 8a 00 00    	jmp    *0x8a6e(%rip)        # af38 <__strcpy_chk@GLIBC_2.3.4>
    24ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024d0 <__io_uring_get_cqe@plt>:
    24d0:	f3 0f 1e fa          	endbr64
    24d4:	ff 25 66 8a 00 00    	jmp    *0x8a66(%rip)        # af40 <__io_uring_get_cqe@LIBURING_2.0>
    24da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024e0 <__printf_chk@plt>:
    24e0:	f3 0f 1e fa          	endbr64
    24e4:	ff 25 5e 8a 00 00    	jmp    *0x8a5e(%rip)        # af48 <__printf_chk@GLIBC_2.3.4>
    24ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000024f0 <bind@plt>:
    24f0:	f3 0f 1e fa          	endbr64
    24f4:	ff 25 56 8a 00 00    	jmp    *0x8a56(%rip)        # af50 <bind@GLIBC_2.2.5>
    24fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002500 <pthread_create@plt>:
    2500:	f3 0f 1e fa          	endbr64
    2504:	ff 25 4e 8a 00 00    	jmp    *0x8a4e(%rip)        # af58 <pthread_create@GLIBC_2.34>
    250a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002510 <open@plt>:
    2510:	f3 0f 1e fa          	endbr64
    2514:	ff 25 46 8a 00 00    	jmp    *0x8a46(%rip)        # af60 <open@GLIBC_2.2.5>
    251a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002520 <fopen@plt>:
    2520:	f3 0f 1e fa          	endbr64
    2524:	ff 25 3e 8a 00 00    	jmp    *0x8a3e(%rip)        # af68 <fopen@GLIBC_2.2.5>
    252a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002530 <perror@plt>:
    2530:	f3 0f 1e fa          	endbr64
    2534:	ff 25 36 8a 00 00    	jmp    *0x8a36(%rip)        # af70 <perror@GLIBC_2.2.5>
    253a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002540 <exit@plt>:
    2540:	f3 0f 1e fa          	endbr64
    2544:	ff 25 2e 8a 00 00    	jmp    *0x8a2e(%rip)        # af78 <exit@GLIBC_2.2.5>
    254a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002550 <eventfd@plt>:
    2550:	f3 0f 1e fa          	endbr64
    2554:	ff 25 26 8a 00 00    	jmp    *0x8a26(%rip)        # af80 <eventfd@GLIBC_2.7>
    255a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002560 <fwrite@plt>:
    2560:	f3 0f 1e fa          	endbr64
    2564:	ff 25 1e 8a 00 00    	jmp    *0x8a1e(%rip)        # af88 <fwrite@GLIBC_2.2.5>
    256a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002570 <__fprintf_chk@plt>:
    2570:	f3 0f 1e fa          	endbr64
    2574:	ff 25 16 8a 00 00    	jmp    *0x8a16(%rip)        # af90 <__fprintf_chk@GLIBC_2.3.4>
    257a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002580 <io_uring_register_eventfd@plt>:
    2580:	f3 0f 1e fa          	endbr64
    2584:	ff 25 0e 8a 00 00    	jmp    *0x8a0e(%rip)        # af98 <io_uring_register_eventfd@LIBURING_2.0>
    258a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000002590 <pthread_join@plt>:
    2590:	f3 0f 1e fa          	endbr64
    2594:	ff 25 06 8a 00 00    	jmp    *0x8a06(%rip)        # afa0 <pthread_join@GLIBC_2.34>
    259a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025a0 <strerror@plt>:
    25a0:	f3 0f 1e fa          	endbr64
    25a4:	ff 25 fe 89 00 00    	jmp    *0x89fe(%rip)        # afa8 <strerror@GLIBC_2.2.5>
    25aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025b0 <pthread_mutex_init@plt>:
    25b0:	f3 0f 1e fa          	endbr64
    25b4:	ff 25 f6 89 00 00    	jmp    *0x89f6(%rip)        # afb0 <pthread_mutex_init@GLIBC_2.2.5>
    25ba:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025c0 <pthread_mutex_lock@plt>:
    25c0:	f3 0f 1e fa          	endbr64
    25c4:	ff 25 ee 89 00 00    	jmp    *0x89ee(%rip)        # afb8 <pthread_mutex_lock@GLIBC_2.2.5>
    25ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025d0 <__ctype_tolower_loc@plt>:
    25d0:	f3 0f 1e fa          	endbr64
    25d4:	ff 25 e6 89 00 00    	jmp    *0x89e6(%rip)        # afc0 <__ctype_tolower_loc@GLIBC_2.3>
    25da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025e0 <__sprintf_chk@plt>:
    25e0:	f3 0f 1e fa          	endbr64
    25e4:	ff 25 de 89 00 00    	jmp    *0x89de(%rip)        # afc8 <__sprintf_chk@GLIBC_2.3.4>
    25ea:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000000025f0 <socket@plt>:
    25f0:	f3 0f 1e fa          	endbr64
    25f4:	ff 25 d6 89 00 00    	jmp    *0x89d6(%rip)        # afd0 <socket@GLIBC_2.2.5>
    25fa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

Disassembly of section .text:

0000000000002600 <fatal_error>:
  if (a > b) { return a; }
  if (b > a) { return b; }
  return a;
}

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
    2616:	48 8d 3d 09 5c 00 00 	lea    0x5c09(%rip),%rdi        # 8226 <_IO_stdin_used+0x226>
    261d:	e8 de ff ff ff       	call   2600 <fatal_error>

0000000000002622 <add_write_request.cold>:
    iov->iov_base = buf;
    iov->iov_len = file_size;
}
int add_write_request(struct Request *req, struct io_uring *ring) {
    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    req->event_type = EVENT_TYPE_WRITE;
    2622:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)

IOURINGINLINE void io_uring_prep_rw(int op, struct io_uring_sqe *sqe, int fd,
				    const void *addr, unsigned len,
				    __u64 offset)
{
	sqe->opcode = (__u8) op;
    2628:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2630:	0f 0b                	ud2

0000000000002632 <add_read_request.cold>:
    2632:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    263a:	0f 0b                	ud2

000000000000263c <_send_static_string_content.cold>:
    263c:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
    2642:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    264a:	0f 0b                	ud2

000000000000264c <add_accept_request.cold>:
    264c:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2654:	0f 0b                	ud2

0000000000002656 <io_thread.cold>:
        break;
      }
      printf("Received wait finished\n");
      struct Request *req = (struct Request *) cqe->user_data;
      if (ret < 0)
          fatal_error("io_uring_wait_cqe");
    2656:	48 8d 3d 99 5b 00 00 	lea    0x5b99(%rip),%rdi        # 81f6 <_IO_stdin_used+0x1f6>
    265d:	e8 9e ff ff ff       	call   2600 <fatal_error>
      fatal_error("setsockopt(SO_REUSEADDR)");
    2662:	48 8d 3d 11 5b 00 00 	lea    0x5b11(%rip),%rdi        # 817a <_IO_stdin_used+0x17a>
    2669:	e8 92 ff ff ff       	call   2600 <fatal_error>
    fatal_error("listen()");
    266e:	48 8d 3d 25 5b 00 00 	lea    0x5b25(%rip),%rdi        # 819a <_IO_stdin_used+0x19a>
    2675:	e8 86 ff ff ff       	call   2600 <fatal_error>
    267a:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    2682:	0f 0b                	ud2
    2684:	c6 04 25 00 00 00 00 00 	movb   $0x0,0x0
    268c:	0f 0b                	ud2
      fatal_error("socket()");
    268e:	48 8d 3d dc 5a 00 00 	lea    0x5adc(%rip),%rdi        # 8171 <_IO_stdin_used+0x171>
    2695:	e8 66 ff ff ff       	call   2600 <fatal_error>
      fatal_error("bind()");
    269a:	48 8d 3d f2 5a 00 00 	lea    0x5af2(%rip),%rdi        # 8193 <_IO_stdin_used+0x193>
    26a1:	e8 5a ff ff ff       	call   2600 <fatal_error>
    26a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000026b0 <main>:
    }


  return 0;
}
int main() {
    26b0:	f3 0f 1e fa          	endbr64
    26b4:	41 57                	push   %r15
}

__fortify_function int
printf (const char *__restrict __fmt, ...)
{
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    26b6:	48 8d 3d ab 5f 00 00 	lea    0x5fab(%rip),%rdi        # 8668 <_IO_stdin_used+0x668>
    26bd:	41 56                	push   %r14
    26bf:	41 55                	push   %r13
    26c1:	41 54                	push   %r12
    26c3:	55                   	push   %rbp
    26c4:	48 8d 2d b1 5c 00 00 	lea    0x5cb1(%rip),%rbp        # 837c <_IO_stdin_used+0x37c>
    26cb:	53                   	push   %rbx
    26cc:	48 81 ec 08 01 00 00 	sub    $0x108,%rsp
    26d3:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    26dc:	48 89 84 24 f8 00 00 00 	mov    %rax,0xf8(%rsp)
    26e4:	48 8d 05 b5 1d 00 00 	lea    0x1db5(%rip),%rax        # 44a0 <barriered_reset>
    26eb:	66 48 0f 6e f0       	movq   %rax,%xmm6
    26f0:	0f 16 35 51 85 00 00 	movhps 0x8551(%rip),%xmm6        # ac48 <__do_global_dtors_aux_fini_array_entry+0x8>
    26f7:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    26ff:	e8 4c fc ff ff       	call   2350 <puts@plt>
    2704:	bf 0a 00 00 00       	mov    $0xa,%edi
    2709:	e8 22 fc ff ff       	call   2330 <putchar@plt>
    270e:	ba 01 00 00 00       	mov    $0x1,%edx
    2713:	48 8d 35 5a 5b 00 00 	lea    0x5b5a(%rip),%rsi        # 8274 <_IO_stdin_used+0x274>
    271a:	31 c0                	xor    %eax,%eax
    271c:	bf 01 00 00 00       	mov    $0x1,%edi
    2721:	e8 ba fd ff ff       	call   24e0 <__printf_chk@plt>
    2726:	ba 06 00 00 00       	mov    $0x6,%edx
    272b:	48 8d 35 52 5b 00 00 	lea    0x5b52(%rip),%rsi        # 8284 <_IO_stdin_used+0x284>
    2732:	31 c0                	xor    %eax,%eax
    2734:	bf 01 00 00 00       	mov    $0x1,%edi
    2739:	e8 a2 fd ff ff       	call   24e0 <__printf_chk@plt>
    273e:	ba 03 00 00 00       	mov    $0x3,%edx
    2743:	48 8d 35 4f 5b 00 00 	lea    0x5b4f(%rip),%rsi        # 8299 <_IO_stdin_used+0x299>
    274a:	31 c0                	xor    %eax,%eax
    274c:	bf 01 00 00 00       	mov    $0x1,%edi
    2751:	e8 8a fd ff ff       	call   24e0 <__printf_chk@plt>
    2756:	ba 02 00 00 00       	mov    $0x2,%edx
    275b:	48 8d 35 47 5b 00 00 	lea    0x5b47(%rip),%rsi        # 82a9 <_IO_stdin_used+0x2a9>
    2762:	31 c0                	xor    %eax,%eax
    2764:	bf 01 00 00 00       	mov    $0x1,%edi
    2769:	e8 72 fd ff ff       	call   24e0 <__printf_chk@plt>
    276e:	48 8d 3d 4a 5b 00 00 	lea    0x5b4a(%rip),%rdi        # 82bf <_IO_stdin_used+0x2bf>
    2775:	e8 d6 fb ff ff       	call   2350 <puts@plt>
    277a:	ba 02 00 00 00       	mov    $0x2,%edx
    277f:	48 8d 35 55 5b 00 00 	lea    0x5b55(%rip),%rsi        # 82db <_IO_stdin_used+0x2db>
    2786:	31 c0                	xor    %eax,%eax
    2788:	bf 01 00 00 00       	mov    $0x1,%edi
    278d:	e8 4e fd ff ff       	call   24e0 <__printf_chk@plt>
    2792:	ba 0a 00 00 00       	mov    $0xa,%edx
    2797:	48 8d 35 57 5b 00 00 	lea    0x5b57(%rip),%rsi        # 82f5 <_IO_stdin_used+0x2f5>
    279e:	31 c0                	xor    %eax,%eax
    27a0:	bf 01 00 00 00       	mov    $0x1,%edi
    27a5:	e8 36 fd ff ff       	call   24e0 <__printf_chk@plt>
    27aa:	ba 01 00 00 00       	mov    $0x1,%edx
    27af:	48 8d 35 53 5b 00 00 	lea    0x5b53(%rip),%rsi        # 8309 <_IO_stdin_used+0x309>
    27b6:	31 c0                	xor    %eax,%eax
    27b8:	bf 01 00 00 00       	mov    $0x1,%edi
    27bd:	e8 1e fd ff ff       	call   24e0 <__printf_chk@plt>
    27c2:	ba 01 00 00 00       	mov    $0x1,%edx
    27c7:	48 8d 35 4c 5b 00 00 	lea    0x5b4c(%rip),%rsi        # 831a <_IO_stdin_used+0x31a>
    27ce:	31 c0                	xor    %eax,%eax
    27d0:	bf 01 00 00 00       	mov    $0x1,%edi
    27d5:	e8 06 fd ff ff       	call   24e0 <__printf_chk@plt>
    27da:	ba 02 00 00 00       	mov    $0x2,%edx
    27df:	48 8d 35 4c 5b 00 00 	lea    0x5b4c(%rip),%rsi        # 8332 <_IO_stdin_used+0x332>
    27e6:	31 c0                	xor    %eax,%eax
    27e8:	bf 01 00 00 00       	mov    $0x1,%edi
    27ed:	e8 ee fc ff ff       	call   24e0 <__printf_chk@plt>
    27f2:	ba 01 00 00 00       	mov    $0x1,%edx
    27f7:	48 8d 35 d2 5e 00 00 	lea    0x5ed2(%rip),%rsi        # 86d0 <_IO_stdin_used+0x6d0>
    27fe:	31 c0                	xor    %eax,%eax
    2800:	bf 01 00 00 00       	mov    $0x1,%edi
    2805:	e8 d6 fc ff ff       	call   24e0 <__printf_chk@plt>
    280a:	ba 01 00 00 00       	mov    $0x1,%edx
    280f:	48 8d 35 ea 5e 00 00 	lea    0x5eea(%rip),%rsi        # 8700 <_IO_stdin_used+0x700>
    2816:	31 c0                	xor    %eax,%eax
    2818:	bf 01 00 00 00       	mov    $0x1,%edi
    281d:	e8 be fc ff ff       	call   24e0 <__printf_chk@plt>
    2822:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2827:	48 8d 35 20 5b 00 00 	lea    0x5b20(%rip),%rsi        # 834e <_IO_stdin_used+0x34e>
    282e:	31 c0                	xor    %eax,%eax
    2830:	bf 01 00 00 00       	mov    $0x1,%edi
    2835:	e8 a6 fc ff ff       	call   24e0 <__printf_chk@plt>
    283a:	ba 05 00 00 00       	mov    $0x5,%edx
    283f:	48 8d 35 22 5b 00 00 	lea    0x5b22(%rip),%rsi        # 8368 <_IO_stdin_used+0x368>
    2846:	31 c0                	xor    %eax,%eax
    2848:	bf 01 00 00 00       	mov    $0x1,%edi
    284d:	e8 8e fc ff ff       	call   24e0 <__printf_chk@plt>
    2852:	48 8d 3d 9c 58 00 00 	lea    0x589c(%rip),%rdi        # 80f5 <_IO_stdin_used+0xf5>
    2859:	e8 f2 fa ff ff       	call   2350 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    285e:	be 18 00 00 00       	mov    $0x18,%esi
    2863:	bf 03 00 00 00       	mov    $0x3,%edi
    2868:	e8 b3 fb ff ff       	call   2420 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    286d:	be d8 00 00 00       	mov    $0xd8,%esi
  
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
  int cc = 0; 
  for (int x = 0 ; x < total_threads; x++) {
    2872:	45 31 f6             	xor    %r14d,%r14d
  int cc = 0; 
    2875:	45 31 ed             	xor    %r13d,%r13d
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2878:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    287d:	48 89 84 24 a0 00 00 00 	mov    %rax,0xa0(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2885:	e8 96 fb ff ff       	call   2420 <calloc@plt>
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    288a:	be 28 00 00 00       	mov    $0x28,%esi
    288f:	bf 01 00 00 00       	mov    $0x1,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2894:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    2899:	e8 82 fb ff ff       	call   2420 <calloc@plt>
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    289e:	be 28 00 00 00       	mov    $0x28,%esi
    28a3:	bf 64 00 00 00       	mov    $0x64,%edi
  pthread_mutex_t * mswapmutex = calloc(1, sizeof(pthread_mutex_t));
    28a8:	48 89 84 24 d0 00 00 00 	mov    %rax,0xd0(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads * total_threads, sizeof(pthread_mutex_t));
    28b0:	e8 6b fb ff ff       	call   2420 <calloc@plt>
    28b5:	48 89 84 24 d8 00 00 00 	mov    %rax,0xd8(%rsp)
  for (int x = 0 ; x < total_threads; x++) {
    28bd:	49 89 c7             	mov    %rax,%r15
int main() {
    28c0:	4d 89 fc             	mov    %r15,%r12
    for (int y = 0 ; y < total_threads; y++) {
    28c3:	31 db                	xor    %ebx,%ebx
    28c5:	0f 1f 00             	nopl   (%rax)
    28c8:	41 8d 54 1d 00       	lea    0x0(%r13,%rbx,1),%edx
    28cd:	41 89 d8             	mov    %ebx,%r8d
    28d0:	44 89 f1             	mov    %r14d,%ecx
    28d3:	48 89 ee             	mov    %rbp,%rsi
    28d6:	bf 01 00 00 00       	mov    $0x1,%edi
    28db:	31 c0                	xor    %eax,%eax
    28dd:	83 c3 01             	add    $0x1,%ebx
    28e0:	e8 fb fb ff ff       	call   24e0 <__printf_chk@plt>
      printf("c %d x %d y %d\n", cc, x, y);
      pthread_mutex_init(&swapmutex[cc++], NULL);
    28e5:	4c 89 e7             	mov    %r12,%rdi
    28e8:	31 f6                	xor    %esi,%esi
    for (int y = 0 ; y < total_threads; y++) {
    28ea:	49 83 c4 28          	add    $0x28,%r12
      pthread_mutex_init(&swapmutex[cc++], NULL);
    28ee:	e8 bd fc ff ff       	call   25b0 <pthread_mutex_init@plt>
    for (int y = 0 ; y < total_threads; y++) {
    28f3:	83 fb 0a             	cmp    $0xa,%ebx
    28f6:	75 d0                	jne    28c8 <main+0x218>
    28f8:	41 83 c5 0a          	add    $0xa,%r13d
  for (int x = 0 ; x < total_threads; x++) {
    28fc:	41 83 c6 01          	add    $0x1,%r14d
    2900:	49 81 c7 90 01 00 00 	add    $0x190,%r15
    2907:	41 83 fd 64          	cmp    $0x64,%r13d
    290b:	75 b3                	jne    28c0 <main+0x210>
    290d:	ba 06 00 00 00       	mov    $0x6,%edx
    2912:	48 8d 35 73 5a 00 00 	lea    0x5a73(%rip),%rsi        # 838c <_IO_stdin_used+0x38c>
    2919:	bf 01 00 00 00       	mov    $0x1,%edi
    291e:	31 c0                	xor    %eax,%eax
    2920:	e8 bb fb ff ff       	call   24e0 <__printf_chk@plt>
    2925:	ba 0c 00 00 00       	mov    $0xc,%edx
    292a:	48 8d 35 71 5a 00 00 	lea    0x5a71(%rip),%rsi        # 83a2 <_IO_stdin_used+0x3a2>
    2931:	31 c0                	xor    %eax,%eax
    2933:	bf 01 00 00 00       	mov    $0x1,%edi
    2938:	e8 a3 fb ff ff       	call   24e0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    293d:	be 10 00 00 00       	mov    $0x10,%esi
    2942:	bf 0c 00 00 00       	mov    $0xc,%edi
    2947:	e8 d4 fa ff ff       	call   2420 <calloc@plt>
    294c:	48 89 84 24 c0 00 00 00 	mov    %rax,0xc0(%rsp)
    2954:	48 89 c5             	mov    %rax,%rbp
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2957:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    295e:	49 89 c6             	mov    %rax,%r14
    buffers[x].count = buffer_size;
    2961:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2968:	be 00 01 00 00       	mov    $0x100,%esi
    296d:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    2972:	49 83 c6 10          	add    $0x10,%r14
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2976:	e8 a5 fa ff ff       	call   2420 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    297b:	be 20 00 00 00       	mov    $0x20,%esi
    2980:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2985:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    2989:	49 89 c4             	mov    %rax,%r12
      buffers[x].buffer[y].available = 0;
    298c:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    2996:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    29a0:	e8 7b fa ff ff       	call   2420 <calloc@plt>
    29a5:	49 89 84 24 88 00 00 00 	mov    %rax,0x88(%r12)
  for (int x = 0 ; x < buffers_required; x++) {
    29ad:	4c 39 f3             	cmp    %r14,%rbx
    29b0:	75 af                	jne    2961 <main+0x2b1>
    29b2:	48 8b b4 24 a0 00 00 00 	mov    0xa0(%rsp),%rsi
    29ba:	48 8b 5c 24 38       	mov    0x38(%rsp),%rbx
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  int swap = 0;
    29bf:	c7 44 24 28 00 00 00 00 	movl   $0x0,0x28(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    29c7:	45 31 f6             	xor    %r14d,%r14d
  int curcpu = 0;
    29ca:	c7 44 24 7c 00 00 00 00 	movl   $0x0,0x7c(%rsp)
  int dataid = 0;
    29d2:	45 31 e4             	xor    %r12d,%r12d
    29d5:	45 89 f7             	mov    %r14d,%r15d
    29d8:	48 89 b4 24 90 00 00 00 	mov    %rsi,0x90(%rsp)
    29e0:	48 89 9c 24 a8 00 00 00 	mov    %rbx,0xa8(%rsp)
  int cur_buffer = 0;
    29e8:	c7 84 24 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rsp)
    for (int d = 0 ; d < threads_per_group ; d++) {
    29f3:	48 63 84 24 80 00 00 00 	movslq 0x80(%rsp),%rax
    29fb:	44 89 bc 24 84 00 00 00 	mov    %r15d,0x84(%rsp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2a03:	49 89 d9             	mov    %rbx,%r9
    2a06:	48 89 9c 24 e0 00 00 00 	mov    %rbx,0xe0(%rsp)
    2a0e:	48 c1 e0 04          	shl    $0x4,%rax
    2a12:	48 89 b4 24 c8 00 00 00 	mov    %rsi,0xc8(%rsp)
    2a1a:	48 01 e8             	add    %rbp,%rax
    2a1d:	48 89 ac 24 e8 00 00 00 	mov    %rbp,0xe8(%rsp)
    2a25:	48 89 44 24 68       	mov    %rax,0x68(%rsp)
    2a2a:	43 8d 04 3f          	lea    (%r15,%r15,1),%eax
    2a2e:	8d 78 01             	lea    0x1(%rax),%edi
    2a31:	83 c0 03             	add    $0x3,%eax
    2a34:	89 7c 24 20          	mov    %edi,0x20(%rsp)
    2a38:	89 84 24 9c 00 00 00 	mov    %eax,0x9c(%rsp)
    2a3f:	44 8b 74 24 20       	mov    0x20(%rsp),%r14d
    2a44:	8b 94 24 84 00 00 00 	mov    0x84(%rsp),%edx
    2a4b:	48 8d 35 d6 5c 00 00 	lea    0x5cd6(%rip),%rsi        # 8728 <_IO_stdin_used+0x728>
    2a52:	31 c0                	xor    %eax,%eax
    2a54:	bf 01 00 00 00       	mov    $0x1,%edi
    2a59:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      int x = (k * threads_per_group) + d;
    2a5e:	45 8d 7e ff          	lea    -0x1(%r14),%r15d
    2a62:	44 89 f9             	mov    %r15d,%ecx
    2a65:	e8 76 fa ff ff       	call   24e0 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a6a:	be 08 00 00 00       	mov    $0x8,%esi
    2a6f:	bf 02 00 00 00       	mov    $0x2,%edi
    2a74:	e8 a7 f9 ff ff       	call   2420 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a79:	be 80 00 00 00       	mov    $0x80,%esi
    2a7e:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a83:	48 89 c3             	mov    %rax,%rbx
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a86:	e8 95 f9 ff ff       	call   2420 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2a8b:	45 89 f8             	mov    %r15d,%r8d
    2a8e:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2a93:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a97:	48 89 c5             	mov    %rax,%rbp
      if (x % 2 == 1) {
    2a9a:	44 89 44 24 58       	mov    %r8d,0x58(%rsp)
    2a9f:	0f 84 00 11 00 00    	je     3ba5 <main+0x14f5>
        other = abs(x - 1) % total_threads;
    2aa5:	45 89 f5             	mov    %r14d,%r13d
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    2aa8:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
        my_thread_data[1] = &thread_data[x]; 
    2aad:	4c 89 ca             	mov    %r9,%rdx
        other = abs(x - 1) % total_threads;
    2ab0:	41 8d 45 fe          	lea    -0x2(%r13),%eax
    2ab4:	49 89 c6             	mov    %rax,%r14
        my_thread_data[0] = &thread_data[other]; 
    2ab7:	48 8d 04 40          	lea    (%rax,%rax,2),%rax
    2abb:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    2abf:	48 8d 04 c6          	lea    (%rsi,%rax,8),%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2ac3:	48 8d 73 08          	lea    0x8(%rbx),%rsi
    2ac7:	48 89 74 24 48       	mov    %rsi,0x48(%rsp)
        thread_data[x].protected_state = &protected_state[k];
    2acc:	48 8b bc 24 c8 00 00 00 	mov    0xc8(%rsp),%rdi
    2ad4:	48 89 03             	mov    %rax,(%rbx)
    2ad7:	44 89 f1             	mov    %r14d,%ecx
    2ada:	48 8d 35 77 5c 00 00 	lea    0x5c77(%rip),%rsi        # 8758 <_IO_stdin_used+0x758>
        thread_data[x].thread_index = 1;
    2ae1:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2ae5:	31 c0                	xor    %eax,%eax
        thread_data[x].protected_state = &protected_state[k];
    2ae7:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2aeb:	bf 01 00 00 00       	mov    $0x1,%edi
    2af0:	48 89 53 08          	mov    %rdx,0x8(%rbx)
    2af4:	44 89 fa             	mov    %r15d,%edx
    2af7:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2afc:	e8 df f9 ff ff       	call   24e0 <__printf_chk@plt>
      thread_data[x].other = other;
    2b01:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2b06:	8b 4c 24 7c          	mov    0x7c(%rsp),%ecx
    2b0a:	31 c0                	xor    %eax,%eax
    2b0c:	44 89 fa             	mov    %r15d,%edx
    2b0f:	48 8d 35 72 5c 00 00 	lea    0x5c72(%rip),%rsi        # 8788 <_IO_stdin_used+0x788>
    2b16:	bf 01 00 00 00       	mov    $0x1,%edi
    2b1b:	45 89 b1 b8 00 00 00 	mov    %r14d,0xb8(%r9)
    2b22:	e8 b9 f9 ff ff       	call   24e0 <__printf_chk@plt>
        if (x < thread_count) {
    2b27:	41 83 ff 01          	cmp    $0x1,%r15d
    2b2b:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2b30:	0f 87 99 10 00 00    	ja     3bcf <main+0x151f>
          CPU_SET(curcpu, sendercpu);
    2b36:	48 63 44 24 7c       	movslq 0x7c(%rsp),%rax
    2b3b:	48 89 c7             	mov    %rax,%rdi
    2b3e:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2b44:	77 13                	ja     2b59 <main+0x4a9>
    2b46:	48 c1 e8 06          	shr    $0x6,%rax
    2b4a:	ba 01 00 00 00       	mov    $0x1,%edx
    2b4f:	89 f9                	mov    %edi,%ecx
    2b51:	48 d3 e2             	shl    %cl,%rdx
    2b54:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
          curcpu += 2;
    2b59:	83 44 24 7c 02       	addl   $0x2,0x7c(%rsp)
      thread_data[x].real_thread_index = x;
    2b5e:	45 89 79 08          	mov    %r15d,0x8(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b62:	be 10 00 00 00       	mov    $0x10,%esi
    2b67:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].swapmutex = swapmutex;
    2b6c:	48 8b 84 24 d8 00 00 00 	mov    0xd8(%rsp),%rax
      thread_data[x].cpu_set = sendercpu;
    2b74:	49 89 a9 b0 00 00 00 	mov    %rbp,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2b7b:	31 ed                	xor    %ebp,%ebp
      thread_data[x].swapmutex = swapmutex;
    2b7d:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].mswapmutex = mswapmutex;
    2b84:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
      thread_data[x].threads = my_thread_data;
    2b8c:	49 89 59 18          	mov    %rbx,0x18(%r9)
            data[0].messages_count = 0;
    2b90:	44 89 fb             	mov    %r15d,%ebx
      thread_data[x].mswapmutex = mswapmutex;
    2b93:	49 89 81 d0 00 00 00 	mov    %rax,0xd0(%r9)
      thread_data[x].all_threads = thread_data;
    2b9a:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
      thread_data[x].kind = KERNEL_THREAD;
    2b9f:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].all_threads = thread_data;
    2ba6:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2baa:	48 8b 05 ff 60 00 00 	mov    0x60ff(%rip),%rax        # 8cb0 <_IO_stdin_used+0xcb0>
      thread_data[x].task_count = total_barrier_count;
    2bb1:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].group_count = group_count;
    2bb9:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2bc0:	48 8b 05 f1 60 00 00 	mov    0x60f1(%rip),%rax        # 8cb8 <_IO_stdin_used+0xcb8>
      thread_data[x].task_count = total_barrier_count;
    2bc7:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
      thread_data[x].thread_count = 2;
    2bcc:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2bd0:	e8 4b f8 ff ff       	call   2420 <calloc@plt>
    2bd5:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2bda:	be 10 00 00 00       	mov    $0x10,%esi
    2bdf:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2be4:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2be8:	e8 33 f8 ff ff       	call   2420 <calloc@plt>
    2bed:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bf2:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2bf7:	66 0f 6f 3d 81 60 00 00 	movdqa 0x6081(%rip),%xmm7        # 8c80 <_IO_stdin_used+0xc80>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bff:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2c04:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2c08:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c10:	e8 0b f8 ff ff       	call   2420 <calloc@plt>
    2c15:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c1a:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2c1f:	66 0f 6f 35 59 60 00 00 	movdqa 0x6059(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c27:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2c2c:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2c33:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c3b:	e8 e0 f7 ff ff       	call   2420 <calloc@plt>
        thread_data[x].tasks = barriers;
    2c40:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c45:	4c 89 ef             	mov    %r13,%rdi
            data[0].messages_count = 0;
    2c48:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2c50:	49 89 c6             	mov    %rax,%r14
        thread_data[x].tasks = barriers;
    2c53:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c57:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
            data[0].messages_count = 0;
    2c5c:	4c 89 f1             	mov    %r14,%rcx
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c5f:	48 0f af f8          	imul   %rax,%rdi
            data[0].messages_count = 0;
    2c63:	4c 89 4c 24 50       	mov    %r9,0x50(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c68:	48 c1 ef 22          	shr    $0x22,%rdi
    2c6c:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2c6f:	8b 7c 24 20          	mov    0x20(%rsp),%edi
    2c73:	01 c0                	add    %eax,%eax
    2c75:	29 c7                	sub    %eax,%edi
            data[0].messages_count = 0;
    2c77:	89 bc 24 98 00 00 00 	mov    %edi,0x98(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c7e:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c81:	be 38 00 00 00       	mov    $0x38,%esi
    2c86:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c8b:	45 31 f6             	xor    %r14d,%r14d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c8e:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    2c93:	48 c1 e0 09          	shl    $0x9,%rax
    2c97:	4c 8d 2c 01          	lea    (%rcx,%rax,1),%r13
    2c9b:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
    2ca0:	48 8d 05 b9 17 00 00 	lea    0x17b9(%rip),%rax        # 4460 <do_protected_write>
    2ca7:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2cae:	e8 6d f7 ff ff       	call   2420 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2cb3:	49 89 85 70 01 00 00 	mov    %rax,0x170(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2cba:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cbd:	8b 44 24 58          	mov    0x58(%rsp),%eax
    2cc1:	85 c0                	test   %eax,%eax
    2cc3:	0f 84 76 06 00 00    	je     333f <main+0xc8f>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2cc9:	8b 44 24 20          	mov    0x20(%rsp),%eax
    2ccd:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    2cd1:	49 89 cd             	mov    %rcx,%r13
    2cd4:	48 89 8c 24 88 00 00 00 	mov    %rcx,0x88(%rsp)
    2cdc:	83 e8 02             	sub    $0x2,%eax
    2cdf:	89 44 24 70          	mov    %eax,0x70(%rsp)
    2ce3:	eb 15                	jmp    2cfa <main+0x64a>
    2ce5:	0f 1f 00             	nopl   (%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2ce8:	41 83 c6 01          	add    $0x1,%r14d
    2cec:	49 83 c5 38          	add    $0x38,%r13
    2cf0:	41 83 fe 06          	cmp    $0x6,%r14d
    2cf4:	0f 84 51 01 00 00    	je     2e4b <main+0x79b>
            int group_of = b / threads_per_group;
    2cfa:	44 89 f3             	mov    %r14d,%ebx
    2cfd:	31 c0                	xor    %eax,%eax
    2cff:	44 89 f2             	mov    %r14d,%edx
    2d02:	bf 01 00 00 00       	mov    $0x1,%edi
    2d07:	d1 fb                	sar    %ebx
    2d09:	48 8d 35 ac 56 00 00 	lea    0x56ac(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2d10:	89 d9                	mov    %ebx,%ecx
    2d12:	e8 c9 f7 ff ff       	call   24e0 <__printf_chk@plt>
            if (k == group_of) {
    2d17:	41 39 df             	cmp    %ebx,%r15d
    2d1a:	75 cc                	jne    2ce8 <main+0x638>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d1c:	be 08 00 00 00       	mov    $0x8,%esi
    2d21:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d26:	49 83 c5 38          	add    $0x38,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d2a:	e8 f1 f6 ff ff       	call   2420 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d2f:	be 08 00 00 00       	mov    $0x8,%esi
    2d34:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2d39:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d3e:	e8 dd f6 ff ff       	call   2420 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2d43:	be 80 03 00 00       	mov    $0x380,%esi
    2d48:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2d4d:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2d52:	e8 c9 f6 ff ff       	call   2420 <calloc@plt>
              data[0].a = x;
    2d57:	8b 7c 24 08          	mov    0x8(%rsp),%edi
              mailboxes[b].pending = NULL;
    2d5b:	49 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%r13)
    2d63:	44 89 f2             	mov    %r14d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    2d66:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    2d69:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
    2d70:	48 8d 35 31 5a 00 00 	lea    0x5a31(%rip),%rsi        # 87a8 <_IO_stdin_used+0x7a8>
              data[0].a = x;
    2d77:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].kind = MAILBOX_LOWER;
    2d7d:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
    2d87:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    2d8d:	41 8d 44 24 01       	lea    0x1(%r12),%eax
              data[1].id = dataid++;
    2d92:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2d99:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2da0:	49 89 45 d0          	mov    %rax,-0x30(%r13)
    2da4:	8b 44 24 70          	mov    0x70(%rsp),%eax
              data[0].id = dataid++;
    2da8:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
              data[1].id = dataid++;
    2daf:	41 83 c4 02          	add    $0x2,%r12d
              data[1].a = x;
    2db3:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    2dba:	89 c1                	mov    %eax,%ecx
    2dbc:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].c = b;
    2dc1:	45 89 b1 a4 06 00 00 	mov    %r14d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2dc8:	41 83 c6 01          	add    $0x1,%r14d
              mailboxes[b].lower = &data[0];
    2dcc:	4d 89 4d c8          	mov    %r9,-0x38(%r13)
    2dd0:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    2dd4:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    2dd6:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].b = y;
    2de1:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    2de8:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    2df3:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2dfe:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    2e06:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    2e0b:	e8 d0 f6 ff ff       	call   24e0 <__printf_chk@plt>
              data[0].messages = messages;
    2e10:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    2e15:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
              data[0].messages_count = 0;
    2e1a:	66 0f 6f 35 6e 5e 00 00 	movdqa 0x5e6e(%rip),%xmm6        # 8c90 <_IO_stdin_used+0xc90>
              data[1].messages = messages2;
    2e22:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
              data[0].messages = messages;
    2e27:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2e2a:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2e31:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2e39:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e41:	41 83 fe 06          	cmp    $0x6,%r14d
    2e45:	0f 85 af fe ff ff    	jne    2cfa <main+0x64a>
    2e4b:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    2e4f:	48 8b 8c 24 88 00 00 00 	mov    0x88(%rsp),%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2e57:	45 31 ed             	xor    %r13d,%r13d
    2e5a:	44 89 7c 24 08       	mov    %r15d,0x8(%rsp)
    2e5f:	41 89 e8             	mov    %ebp,%r8d
    2e62:	41 89 df             	mov    %ebx,%r15d
    2e65:	44 89 eb             	mov    %r13d,%ebx
    2e68:	49 89 cd             	mov    %rcx,%r13
    2e6b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            int group_of = b / threads_per_group;
    2e70:	89 d8                	mov    %ebx,%eax
    2e72:	d1 f8                	sar    %eax
            if (k == group_of) {
    2e74:	39 44 24 08          	cmp    %eax,0x8(%rsp)
    2e78:	0f 84 58 01 00 00    	je     2fd6 <main+0x926>
    2e7e:	89 da                	mov    %ebx,%edx
    2e80:	48 8d 35 45 55 00 00 	lea    0x5545(%rip),%rsi        # 83cc <_IO_stdin_used+0x3cc>
    2e87:	bf 01 00 00 00       	mov    $0x1,%edi
    2e8c:	31 c0                	xor    %eax,%eax
    2e8e:	44 89 44 24 18       	mov    %r8d,0x18(%rsp)
    2e93:	e8 48 f6 ff ff       	call   24e0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e98:	be 08 00 00 00       	mov    $0x8,%esi
    2e9d:	bf 01 00 00 00       	mov    $0x1,%edi
    2ea2:	e8 79 f5 ff ff       	call   2420 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ea7:	be 08 00 00 00       	mov    $0x8,%esi
    2eac:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2eb1:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2eb6:	e8 65 f5 ff ff       	call   2420 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2ebb:	be 80 03 00 00       	mov    $0x380,%esi
    2ec0:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2ec5:	48 89 c5             	mov    %rax,%rbp
            struct Data *data = calloc(3, sizeof(struct Data));
    2ec8:	e8 53 f5 ff ff       	call   2420 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2ecd:	be 80 03 00 00       	mov    $0x380,%esi
    2ed2:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2ed7:	49 89 c6             	mov    %rax,%r14
            struct Data **stack = calloc(3, sizeof(struct Data));
    2eda:	e8 41 f5 ff ff       	call   2420 <calloc@plt>
            data[0].id = dataid++;
    2edf:	41 8d 74 24 01       	lea    0x1(%r12),%esi
            data[0].b = y;
    2ee4:	44 8b 44 24 18       	mov    0x18(%rsp),%r8d
            data[0].messages = messages;
    2ee9:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
            data[1].id = dataid++;
    2eee:	41 89 b6 a8 06 00 00 	mov    %esi,0x6a8(%r14)
            mailboxes[b].higher = &data[1];
    2ef5:	49 8d b6 80 03 00 00 	lea    0x380(%r14),%rsi
            data[0].messages_count = 0;
    2efc:	66 0f 6f 35 8c 5d 00 00 	movdqa 0x5d8c(%rip),%xmm6        # 8c90 <_IO_stdin_used+0xc90>
            data[0].kind = MAILBOX_LOWER;
    2f04:	41 c7 86 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r14)
            data[0].a = x;
    2f0f:	45 89 be 1c 03 00 00 	mov    %r15d,0x31c(%r14)
            data[0].b = y;
    2f16:	45 89 86 20 03 00 00 	mov    %r8d,0x320(%r14)
            data[0].c = b;
    2f1d:	41 89 9e 24 03 00 00 	mov    %ebx,0x324(%r14)
            data[1].kind = MAILBOX_HIGHER;
    2f24:	41 c7 86 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r14)
            data[1].a = x;
    2f2f:	45 89 be 9c 06 00 00 	mov    %r15d,0x69c(%r14)
            data[1].b = y;
    2f36:	45 89 86 a0 06 00 00 	mov    %r8d,0x6a0(%r14)
            data[1].c = b;
    2f3d:	41 89 9e a4 06 00 00 	mov    %ebx,0x6a4(%r14)
            mailboxes[b].lower = &data[0];
    2f44:	4d 89 75 00          	mov    %r14,0x0(%r13)
            mailboxes[b].my_lower = &data[0];
    2f48:	4d 89 75 20          	mov    %r14,0x20(%r13)
            mailboxes[b].higher = &data[1];
    2f4c:	49 89 75 08          	mov    %rsi,0x8(%r13)
            mailboxes[b].pending = NULL;
    2f50:	49 c7 45 10 00 00 00 00 	movq   $0x0,0x10(%r13)
            data[0].finished_reading = 1;
    2f58:	41 c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r14)
            data[1].finished_reading = 1;
    2f63:	41 c7 86 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r14)
            mailboxes[b].my_higher = &data[1];
    2f6e:	49 89 75 28          	mov    %rsi,0x28(%r13)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2f72:	41 c7 45 30 02 00 00 00 	movl   $0x2,0x30(%r13)
            stack[0] = mailboxes[b].lower;
    2f7a:	4c 89 30             	mov    %r14,(%rax)
            stack[1] = mailboxes[b].higher;
    2f7d:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2f81:	49 89 45 18          	mov    %rax,0x18(%r13)
            data[0].available_sending = 0;
    2f85:	41 c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r14)
            data[0].available_receiving = 0;
    2f90:	41 c7 86 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r14)
            data[0].messages = messages;
    2f9b:	49 89 16             	mov    %rdx,(%r14)
            data[1].messages = messages2;
    2f9e:	49 89 ae 80 03 00 00 	mov    %rbp,0x380(%r14)
            data[1].available_sending = 1;
    2fa5:	41 c7 86 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r14)
            data[1].available_receiving = 0;
    2fb0:	41 c7 86 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r14)
            data[0].id = dataid++;
    2fbb:	45 89 a6 28 03 00 00 	mov    %r12d,0x328(%r14)
            data[1].id = dataid++;
    2fc2:	41 83 c4 02          	add    $0x2,%r12d
            data[0].messages_count = 0;
    2fc6:	41 0f 29 b6 80 00 00 00 	movaps %xmm6,0x80(%r14)
            data[1].messages_count = 0;
    2fce:	41 0f 29 b6 00 04 00 00 	movaps %xmm6,0x400(%r14)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2fd6:	83 c3 01             	add    $0x1,%ebx
    2fd9:	49 83 c5 38          	add    $0x38,%r13
    2fdd:	83 fb 06             	cmp    $0x6,%ebx
    2fe0:	0f 85 8a fe ff ff    	jne    2e70 <main+0x7c0>
          char *message = malloc(sizeof(char) * 256);
    2fe6:	be 01 00 00 00       	mov    $0x1,%esi
    2feb:	bf 00 01 00 00       	mov    $0x100,%edi
    2ff0:	44 89 c5             	mov    %r8d,%ebp
    2ff3:	44 89 fb             	mov    %r15d,%ebx
    2ff6:	44 8b 7c 24 08       	mov    0x8(%rsp),%r15d
    2ffb:	e8 20 f4 ff ff       	call   2420 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    3000:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    3005:	49 89 c5             	mov    %rax,%r13
          struct Message *messaged = malloc(sizeof(struct Message));
    3008:	e8 93 f4 ff ff       	call   24a0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    300d:	48 83 ec 08          	sub    $0x8,%rsp
    3011:	4c 89 ef             	mov    %r13,%rdi
    3014:	41 89 e9             	mov    %ebp,%r9d
    3017:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    301c:	41 89 d8             	mov    %ebx,%r8d
    301f:	ba 00 01 00 00       	mov    $0x100,%edx
    3024:	31 c0                	xor    %eax,%eax
    3026:	41 57                	push   %r15
    3028:	48 8d 0d a1 57 00 00 	lea    0x57a1(%rip),%rcx        # 87d0 <_IO_stdin_used+0x7d0>
    302f:	be 01 00 00 00       	mov    $0x1,%esi
    3034:	e8 a7 f5 ff ff       	call   25e0 <__sprintf_chk@plt>
          messaged->message = message;
    3039:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
          messaged->thread_index = thread_data[x].real_thread_index;
    303e:	4c 8b 74 24 60       	mov    0x60(%rsp),%r14
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3043:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->task_index = y;
    3048:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
          thread_data[x].tasks[y].swap = swap;
    304d:	48 8b 54 24 40       	mov    0x40(%rsp),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    3052:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].swap = swap;
    3057:	49 8b 4e 38          	mov    0x38(%r14),%rcx
          messaged->message = message;
    305b:	4d 89 2a             	mov    %r13,(%r10)
          messaged->task_index = y;
    305e:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    3062:	49 63 46 08          	movslq 0x8(%r14),%rax
          thread_data[x].tasks[y].swap = swap;
    3066:	48 01 ca             	add    %rcx,%rdx
          messaged->group = k;
    3069:	45 89 7a 18          	mov    %r15d,0x18(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    306d:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].swap = swap;
    3071:	8b 44 24 38          	mov    0x38(%rsp),%eax
          thread_data[x].tasks[y].group = k;
    3075:	44 89 ba 94 01 00 00 	mov    %r15d,0x194(%rdx)
          thread_data[x].tasks[y].swap = swap;
    307c:	89 82 98 01 00 00    	mov    %eax,0x198(%rdx)
          swap += 1;
    3082:	83 c0 01             	add    $0x1,%eax
    3085:	89 44 24 38          	mov    %eax,0x38(%rsp)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3089:	8d 45 01             	lea    0x1(%rbp),%eax
    308c:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    308f:	c7 02 41 00 00 00    	movl   $0x41,(%rdx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3095:	89 82 90 01 00 00    	mov    %eax,0x190(%rdx)
          thread_data[x].tasks[y].message = messaged;
    309b:	4c 89 92 88 01 00 00 	mov    %r10,0x188(%rdx)
          thread_data[x].tasks[y].sending = 1;
    30a2:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
          thread_data[x].tasks[y].snapshot_count = 99;
    30ac:	48 c7 82 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rdx)
          thread_data[x].tasks[y].swap = swap;
    30b7:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
          thread_data[x].tasks[y].snapshot_count = 99;
    30bc:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    30c1:	e8 5a f3 ff ff       	call   2420 <calloc@plt>
    30c6:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    30cb:	48 89 82 50 01 00 00 	mov    %rax,0x150(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    30d2:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    30d7:	48 c7 82 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    30e2:	48 8b 00             	mov    (%rax),%rax
    30e5:	8b 70 04             	mov    0x4(%rax),%esi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    30e8:	4c 39 f0             	cmp    %r14,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    30eb:	48 89 82 28 01 00 00 	mov    %rax,0x128(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    30f2:	89 b2 30 01 00 00    	mov    %esi,0x130(%rdx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    30f8:	41 5b                	pop    %r11
    30fa:	41 5d                	pop    %r13
    30fc:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    3101:	0f 85 52 12 00 00    	jne    4359 <main+0x1ca9>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    3107:	66 0f 6f 05 91 5b 00 00 	movdqa 0x5b91(%rip),%xmm0        # 8ca0 <_IO_stdin_used+0xca0>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    310f:	89 6a 04             	mov    %ebp,0x4(%rdx)
          thread_data[x].tasks[y].available = 1;
    3112:	4c 8b 2d a7 5b 00 00 	mov    0x5ba7(%rip),%r13        # 8cc0 <_IO_stdin_used+0xcc0>
          thread_data[x].tasks[y].arrived = 0;
    3119:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
          thread_data[x].tasks[y].worker_count = thread_count;
    3123:	c7 82 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rdx)
          thread_data[x].tasks[y].available = 1;
    312d:	4c 89 aa 44 01 00 00 	mov    %r13,0x144(%rdx)
          thread_data[x].tasks[y].thread_count = 2;
    3134:	0f 11 82 34 01 00 00 	movups %xmm0,0x134(%rdx)
          if (y == barrier_count - 1) {
    313b:	83 fd 01             	cmp    $0x1,%ebp
    313e:	0f 84 98 03 00 00    	je     34dc <main+0xe2c>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    3144:	85 ed                	test   %ebp,%ebp
    3146:	0f 84 78 03 00 00    	je     34c4 <main+0xe14>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    314c:	4c 8b 4c 24 50       	mov    0x50(%rsp),%r9
    3151:	48 8d 05 88 36 00 00 	lea    0x3688(%rip),%rax        # 67e0 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3158:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    315d:	49 89 ce             	mov    %rcx,%r14
    3160:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3167:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers_count = buffers_per_thread;
    316c:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    3177:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    317c:	e8 9f f2 ff ff       	call   2420 <calloc@plt>
    3181:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3186:	48 8b 7c 24 68       	mov    0x68(%rsp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    318b:	66 0f 6f bc 24 b0 00 00 00 	movdqa 0xb0(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    3194:	83 44 24 20 01       	addl   $0x1,0x20(%rsp)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3199:	48 89 38             	mov    %rdi,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    319c:	48 83 c7 10          	add    $0x10,%rdi
    31a0:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    31a7:	49 89 81 78 ff ff ff 	mov    %rax,-0x88(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    31ae:	48 8b 44 24 48       	mov    0x48(%rsp),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    31b3:	83 84 24 80 00 00 00 01 	addl   $0x1,0x80(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    31bb:	48 8b 00             	mov    (%rax),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    31be:	48 89 7c 24 68       	mov    %rdi,0x68(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    31c3:	41 c7 86 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r14)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    31ce:	49 89 86 28 05 00 00 	mov    %rax,0x528(%r14)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    31d5:	41 c7 86 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r14)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    31e0:	41 c7 86 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    31eb:	41 8b 81 2c ff ff ff 	mov    -0xd4(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    31f2:	41 0f 11 be 18 05 00 00 	movups %xmm7,0x518(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    31fa:	41 89 86 30 05 00 00 	mov    %eax,0x530(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3201:	8b 44 24 20          	mov    0x20(%rsp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    3205:	41 c7 86 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r14)
        thread_data[x].tasks[barrier_count].available = 1; 
    3210:	4d 89 ae 44 05 00 00 	mov    %r13,0x544(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3217:	39 84 24 9c 00 00 00 	cmp    %eax,0x9c(%rsp)
    321e:	0f 85 1b f8 ff ff    	jne    2a3f <main+0x38f>
    3224:	44 8b bc 24 84 00 00 00 	mov    0x84(%rsp),%r15d
    322c:	48 8b 9c 24 e0 00 00 00 	mov    0xe0(%rsp),%rbx
    3234:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    323c:	48 8b ac 24 e8 00 00 00 	mov    0xe8(%rsp),%rbp
  for (int k = 0 ; k < group_count ; k++) {
    3244:	41 83 c7 01          	add    $0x1,%r15d
    3248:	48 81 c3 b0 01 00 00 	add    $0x1b0,%rbx
    324f:	48 83 c6 18          	add    $0x18,%rsi
    3253:	41 83 ff 03          	cmp    $0x3,%r15d
    3257:	0f 85 96 f7 ff ff    	jne    29f3 <main+0x343>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    325d:	be 08 00 00 00       	mov    $0x8,%esi
    3262:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    3267:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    326a:	e8 b1 f1 ff ff       	call   2420 <calloc@plt>
    326f:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3274:	48 89 c5             	mov    %rax,%rbp
    3277:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3279:	49 89 d1             	mov    %rdx,%r9
    327c:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    327e:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3282:	45 85 d2             	test   %r10d,%r10d
    3285:	0f 8e 9b 00 00 00    	jle    3326 <main+0xc76>
    328b:	49 8b 79 38          	mov    0x38(%r9),%rdi
    328f:	4d 63 c2             	movslq %r10d,%r8
    3292:	49 63 cc             	movslq %r12d,%rcx
    3295:	49 c1 e0 09          	shl    $0x9,%r8
    3299:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    329e:	49 01 f8             	add    %rdi,%r8
    32a1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32a8:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    32af:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    32b6:	48 83 c6 60          	add    $0x60,%rsi
    32ba:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    32bf:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    32c4:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32cc:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    32d0:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    32d8:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    32dc:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    32e0:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    32e8:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    32ef:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    32f3:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    32f7:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    32fe:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3305:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3309:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    330d:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3311:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3315:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3319:	49 39 f8             	cmp    %rdi,%r8
    331c:	75 8a                	jne    32a8 <main+0xbf8>
    331e:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3322:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    3326:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    332d:	85 db                	test   %ebx,%ebx
    332f:	0f 85 b5 01 00 00    	jne    34ea <main+0xe3a>
    3335:	bb 01 00 00 00       	mov    $0x1,%ebx
    333a:	e9 3f ff ff ff       	jmp    327e <main+0xbce>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    333f:	89 5c 24 08          	mov    %ebx,0x8(%rsp)
    3343:	49 89 cd             	mov    %rcx,%r13
    3346:	48 89 4c 24 70       	mov    %rcx,0x70(%rsp)
    334b:	eb 15                	jmp    3362 <main+0xcb2>
    334d:	0f 1f 00             	nopl   (%rax)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3350:	41 83 c6 01          	add    $0x1,%r14d
    3354:	49 83 c5 38          	add    $0x38,%r13
    3358:	41 83 fe 06          	cmp    $0x6,%r14d
    335c:	0f 84 54 01 00 00    	je     34b6 <main+0xe06>
            int group_of = b / threads_per_group;
    3362:	44 89 f3             	mov    %r14d,%ebx
    3365:	31 c0                	xor    %eax,%eax
    3367:	44 89 f2             	mov    %r14d,%edx
    336a:	bf 01 00 00 00       	mov    $0x1,%edi
    336f:	d1 fb                	sar    %ebx
    3371:	48 8d 35 44 50 00 00 	lea    0x5044(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    3378:	89 d9                	mov    %ebx,%ecx
    337a:	e8 61 f1 ff ff       	call   24e0 <__printf_chk@plt>
            if (k == group_of) {
    337f:	41 39 df             	cmp    %ebx,%r15d
    3382:	75 cc                	jne    3350 <main+0xca0>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3384:	be 08 00 00 00       	mov    $0x8,%esi
    3389:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    338e:	49 83 c5 38          	add    $0x38,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3392:	e8 89 f0 ff ff       	call   2420 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3397:	be 08 00 00 00       	mov    $0x8,%esi
    339c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    33a1:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    33a6:	e8 75 f0 ff ff       	call   2420 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    33ab:	be 80 03 00 00       	mov    $0x380,%esi
    33b0:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    33b5:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    33ba:	e8 61 f0 ff ff       	call   2420 <calloc@plt>
              data[0].a = x;
    33bf:	8b 7c 24 08          	mov    0x8(%rsp),%edi
              mailboxes[b].pending = NULL;
    33c3:	49 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%r13)
    33cb:	44 89 f2             	mov    %r14d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    33ce:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    33d1:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
    33d8:	48 8d 35 c9 53 00 00 	lea    0x53c9(%rip),%rsi        # 87a8 <_IO_stdin_used+0x7a8>
              data[0].a = x;
    33df:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].kind = MAILBOX_LOWER;
    33e5:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
    33ef:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    33f5:	41 8d 44 24 01       	lea    0x1(%r12),%eax
              data[1].id = dataid++;
    33fa:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    3401:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    3408:	49 89 45 d0          	mov    %rax,-0x30(%r13)
    340c:	8b 84 24 98 00 00 00 	mov    0x98(%rsp),%eax
              data[0].id = dataid++;
    3413:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
              data[1].id = dataid++;
    341a:	41 83 c4 02          	add    $0x2,%r12d
              data[1].a = x;
    341e:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    3425:	89 c1                	mov    %eax,%ecx
    3427:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].c = b;
    342c:	45 89 b1 a4 06 00 00 	mov    %r14d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    3433:	41 83 c6 01          	add    $0x1,%r14d
              mailboxes[b].lower = &data[0];
    3437:	4d 89 4d c8          	mov    %r9,-0x38(%r13)
    343b:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    343f:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    3441:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].b = y;
    344c:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    3453:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    345e:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    3469:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    3471:	4c 89 4c 24 10       	mov    %r9,0x10(%rsp)
    3476:	e8 65 f0 ff ff       	call   24e0 <__printf_chk@plt>
              data[0].messages = messages;
    347b:	4c 8b 4c 24 10       	mov    0x10(%rsp),%r9
    3480:	4c 8b 5c 24 60       	mov    0x60(%rsp),%r11
              data[0].messages_count = 0;
    3485:	66 0f 6f 35 03 58 00 00 	movdqa 0x5803(%rip),%xmm6        # 8c90 <_IO_stdin_used+0xc90>
              data[1].messages = messages2;
    348d:	4c 8b 54 24 18       	mov    0x18(%rsp),%r10
              data[0].messages = messages;
    3492:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    3495:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    349c:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    34a4:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    34ac:	41 83 fe 06          	cmp    $0x6,%r14d
    34b0:	0f 85 ac fe ff ff    	jne    3362 <main+0xcb2>
    34b6:	8b 5c 24 08          	mov    0x8(%rsp),%ebx
    34ba:	48 8b 4c 24 70       	mov    0x70(%rsp),%rcx
    34bf:	e9 93 f9 ff ff       	jmp    2e57 <main+0x7a7>
    34c4:	48 8d 05 35 39 00 00 	lea    0x3935(%rip),%rax        # 6e00 <barriered_work_ingest_andwork>
    34cb:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    34d0:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    34d7:	e9 a2 f7 ff ff       	jmp    2c7e <main+0x5ce>
    34dc:	48 8d 05 fd 32 00 00 	lea    0x32fd(%rip),%rax        # 67e0 <barriered_work>
    34e3:	bd 02 00 00 00       	mov    $0x2,%ebp
    34e8:	eb e6                	jmp    34d0 <main+0xe20>
  for (int k = 0 ; k < group_count ; k++) {
    34ea:	83 c0 02             	add    $0x2,%eax
    34ed:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    34f4:	83 f8 06             	cmp    $0x6,%eax
    34f7:	0f 85 7c fd ff ff    	jne    3279 <main+0xbc9>
    34fd:	48 8d 3d e6 4e 00 00 	lea    0x4ee6(%rip),%rdi        # 83ea <_IO_stdin_used+0x3ea>
    3504:	e8 47 ee ff ff       	call   2350 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    3509:	48 8d 35 ef 4e 00 00 	lea    0x4eef(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3510:	48 8d 3d ea 4e 00 00 	lea    0x4eea(%rip),%rdi        # 8401 <_IO_stdin_used+0x401>
    3517:	e8 04 f0 ff ff       	call   2520 <fopen@plt>
    351c:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas_size; x++) {
    351f:	45 85 e4             	test   %r12d,%r12d
    3522:	7e 77                	jle    359b <main+0xeeb>
    3524:	4d 63 e4             	movslq %r12d,%r12
    3527:	4c 8d 35 b0 4e 00 00 	lea    0x4eb0(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    352e:	4c 8d 2d ed 4e 00 00 	lea    0x4eed(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    3535:	4a 8d 44 e5 00       	lea    0x0(%rbp,%r12,8),%rax
    353a:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    char * c = calloc(250, sizeof(char));
    353f:	be 01 00 00 00       	mov    $0x1,%esi
    3544:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    3549:	48 83 c5 08          	add    $0x8,%rbp
    char * c = calloc(250, sizeof(char));
    354d:	e8 ce ee ff ff       	call   2420 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3552:	4c 89 f1             	mov    %r14,%rcx
    3555:	ba fa 00 00 00       	mov    $0xfa,%edx
    355a:	be 01 00 00 00       	mov    $0x1,%esi
    355f:	49 89 c4             	mov    %rax,%r12
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    3562:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
    3566:	4c 89 e7             	mov    %r12,%rdi
    3569:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3570:	31 c0                	xor    %eax,%eax
    3572:	e8 69 f0 ff ff       	call   25e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3577:	4c 89 e2             	mov    %r12,%rdx
    357a:	4c 89 ee             	mov    %r13,%rsi
    357d:	bf 01 00 00 00       	mov    $0x1,%edi
    3582:	31 c0                	xor    %eax,%eax
    3584:	e8 57 ef ff ff       	call   24e0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3589:	4c 89 fe             	mov    %r15,%rsi
    358c:	4c 89 e7             	mov    %r12,%rdi
    358f:	e8 4c ee ff ff       	call   23e0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    3594:	48 39 6c 24 08       	cmp    %rbp,0x8(%rsp)
    3599:	75 a4                	jne    353f <main+0xe8f>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    359b:	4c 89 ff             	mov    %r15,%rdi

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    359e:	31 ed                	xor    %ebp,%ebp
    35a0:	4c 8d 35 a5 4e 00 00 	lea    0x4ea5(%rip),%r14        # 844c <_IO_stdin_used+0x44c>
  fclose(m1);
    35a7:	e8 d4 ed ff ff       	call   2380 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    35ac:	48 8d 3d 57 4e 00 00 	lea    0x4e57(%rip),%rdi        # 840a <_IO_stdin_used+0x40a>
    35b3:	41 89 ec             	mov    %ebp,%r12d
    35b6:	e8 95 ed ff ff       	call   2350 <puts@plt>
    35bb:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    35c0:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    35c5:	44 89 e2             	mov    %r12d,%edx
    35c8:	48 8d 35 56 4e 00 00 	lea    0x4e56(%rip),%rsi        # 8425 <_IO_stdin_used+0x425>
    35cf:	31 c0                	xor    %eax,%eax
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    35d1:	45 31 ed             	xor    %r13d,%r13d
    35d4:	bf 01 00 00 00       	mov    $0x1,%edi
    35d9:	47 8d 3c 24          	lea    (%r12,%r12,1),%r15d
    35dd:	e8 fe ee ff ff       	call   24e0 <__printf_chk@plt>
    35e2:	48 8b 6c 24 08       	mov    0x8(%rsp),%rbp
    35e7:	44 89 7c 24 10       	mov    %r15d,0x10(%rsp)
    35ec:	48 89 e8             	mov    %rbp,%rax
    35ef:	89 dd                	mov    %ebx,%ebp
    35f1:	44 89 eb             	mov    %r13d,%ebx
    35f4:	49 89 c5             	mov    %rax,%r13
      int x = (k * threads_per_group) + d;
    35f7:	8b 44 24 10          	mov    0x10(%rsp),%eax
    35fb:	89 da                	mov    %ebx,%edx
    35fd:	48 8d 35 2b 4e 00 00 	lea    0x4e2b(%rip),%rsi        # 842f <_IO_stdin_used+0x42f>
    3604:	45 31 ff             	xor    %r15d,%r15d
    3607:	bf 01 00 00 00       	mov    $0x1,%edi
    360c:	8d 0c 03             	lea    (%rbx,%rax,1),%ecx
    360f:	31 c0                	xor    %eax,%eax
    3611:	e8 ca ee ff ff       	call   24e0 <__printf_chk@plt>
    3616:	89 5c 24 18          	mov    %ebx,0x18(%rsp)
    361a:	89 6c 24 20          	mov    %ebp,0x20(%rsp)
    361e:	44 89 64 24 28       	mov    %r12d,0x28(%rsp)
    3623:	44 89 fa             	mov    %r15d,%edx
    3626:	48 8d 35 14 4e 00 00 	lea    0x4e14(%rip),%rsi        # 8441 <_IO_stdin_used+0x441>
    362d:	31 c0                	xor    %eax,%eax
    362f:	4d 89 fc             	mov    %r15,%r12
    3632:	bf 01 00 00 00       	mov    $0x1,%edi
    3637:	49 c1 e4 09          	shl    $0x9,%r12
    363b:	31 ed                	xor    %ebp,%ebp
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    363d:	31 db                	xor    %ebx,%ebx
    363f:	e8 9c ee ff ff       	call   24e0 <__printf_chk@plt>
    3644:	eb 34                	jmp    367a <main+0xfca>
    3646:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    3650:	83 fa 01             	cmp    $0x1,%edx
    3653:	0f 84 91 00 00 00    	je     36ea <main+0x103a>
    3659:	44 8b 40 34          	mov    0x34(%rax),%r8d
    365d:	89 da                	mov    %ebx,%edx
    365f:	4c 89 f6             	mov    %r14,%rsi
    3662:	bf 01 00 00 00       	mov    $0x1,%edi
    3667:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3669:	83 c3 01             	add    $0x1,%ebx
    366c:	48 83 c5 38          	add    $0x38,%rbp
    3670:	e8 6b ee ff ff       	call   24e0 <__printf_chk@plt>
    3675:	83 fb 06             	cmp    $0x6,%ebx
    3678:	74 43                	je     36bd <main+0x100d>
          char * mailbox_kind = calloc(100, sizeof(char));
    367a:	be 01 00 00 00       	mov    $0x1,%esi
    367f:	bf 64 00 00 00       	mov    $0x64,%edi
    3684:	e8 97 ed ff ff       	call   2420 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3689:	49 8b 75 38          	mov    0x38(%r13),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    368d:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3690:	4a 8b 84 26 70 01 00 00 	mov    0x170(%rsi,%r12,1),%rax
    3698:	48 01 e8             	add    %rbp,%rax
    369b:	8b 50 30             	mov    0x30(%rax),%edx
    369e:	83 fa 02             	cmp    $0x2,%edx
    36a1:	75 ad                	jne    3650 <main+0xfa0>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    36a3:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    36ad:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    36b0:	4a 8b 84 26 70 01 00 00 	mov    0x170(%rsi,%r12,1),%rax
    36b8:	48 01 e8             	add    %rbp,%rax
    36bb:	eb 9c                	jmp    3659 <main+0xfa9>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    36bd:	49 83 c7 01          	add    $0x1,%r15
    36c1:	49 83 ff 03          	cmp    $0x3,%r15
    36c5:	0f 85 58 ff ff ff    	jne    3623 <main+0xf73>
    for (int d = 0 ; d < threads_per_group ; d++) {
    36cb:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    36cf:	8b 6c 24 20          	mov    0x20(%rsp),%ebp
    36d3:	49 81 c5 d8 00 00 00 	add    $0xd8,%r13
    36da:	44 8b 64 24 28       	mov    0x28(%rsp),%r12d
    36df:	85 db                	test   %ebx,%ebx
    36e1:	75 24                	jne    3707 <main+0x1057>
    36e3:	89 eb                	mov    %ebp,%ebx
    36e5:	e9 0d ff ff ff       	jmp    35f7 <main+0xf47>
    36ea:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    36f0:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    36f7:	4a 8b 84 26 70 01 00 00 	mov    0x170(%rsi,%r12,1),%rax
    36ff:	48 01 e8             	add    %rbp,%rax
    3702:	e9 52 ff ff ff       	jmp    3659 <main+0xfa9>
  for (int k = 0 ; k < group_count ; k++) {
    3707:	48 81 44 24 08 b0 01 00 00 	addq   $0x1b0,0x8(%rsp)
    3710:	41 83 c4 01          	add    $0x1,%r12d
    3714:	41 89 dd             	mov    %ebx,%r13d
    3717:	89 eb                	mov    %ebp,%ebx
    3719:	41 83 fc 03          	cmp    $0x3,%r12d
    371d:	0f 85 a2 fe ff ff    	jne    35c5 <main+0xf15>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3723:	ba 07 00 00 00       	mov    $0x7,%edx
    3728:	bf 01 00 00 00       	mov    $0x1,%edi
    372d:	31 c0                	xor    %eax,%eax
    372f:	45 89 ec             	mov    %r13d,%r12d
    3732:	48 8d 35 2e 4d 00 00 	lea    0x4d2e(%rip),%rsi        # 8467 <_IO_stdin_used+0x467>
    3739:	e8 a2 ed ff ff       	call   24e0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    373e:	be 08 00 00 00       	mov    $0x8,%esi
    3743:	bf 02 00 00 00       	mov    $0x2,%edi
    3748:	e8 d3 ec ff ff       	call   2420 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    374d:	48 8b 6c 24 38       	mov    0x38(%rsp),%rbp
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3752:	be 38 00 00 00       	mov    $0x38,%esi
    3757:	bf 0a 00 00 00       	mov    $0xa,%edi
    my_thread_data[0] = &thread_data[x]; 
    375c:	4c 8d b5 e8 05 00 00 	lea    0x5e8(%rbp),%r14
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    3763:	48 89 68 08          	mov    %rbp,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3767:	4c 8d ad d8 00 00 00 	lea    0xd8(%rbp),%r13
    thread_data[x].threads = my_thread_data;
    376e:	48 89 85 00 06 00 00 	mov    %rax,0x600(%rbp)
    my_thread_data[0] = &thread_data[x]; 
    3775:	4c 89 30             	mov    %r14,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    3778:	48 8b 45 38          	mov    0x38(%rbp),%rax
    thread_data[x].thread_count = 2;
    377c:	c7 85 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%rbp)
    thread_data[x].thread_index = 0;
    3786:	c7 85 ec 05 00 00 00 00 00 00 	movl   $0x0,0x5ec(%rbp)
    thread_data[x].task_count = total_barrier_count;
    3790:	c7 85 28 06 00 00 03 00 00 00 	movl   $0x3,0x628(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    379a:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    37a4:	48 8b 85 10 01 00 00 	mov    0x110(%rbp),%rax
    37ab:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37b5:	e8 66 ec ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37ba:	be 38 00 00 00       	mov    $0x38,%esi
    37bf:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37c4:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37c9:	e8 52 ec ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37ce:	be 38 00 00 00       	mov    $0x38,%esi
    37d3:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37d8:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37db:	e8 40 ec ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37e0:	be 38 00 00 00       	mov    $0x38,%esi
    37e5:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37ea:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37ef:	e8 2c ec ff ff       	call   2420 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    37f4:	be 08 00 00 00       	mov    $0x8,%esi
    37f9:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    37fe:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3803:	e8 18 ec ff ff       	call   2420 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    3808:	be 08 00 00 00       	mov    $0x8,%esi
    380d:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
    3812:	c7 85 1c 05 00 00 00 00 00 00 	movl   $0x0,0x51c(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    381c:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    381f:	48 8b 05 a2 54 00 00 	mov    0x54a2(%rip),%rax        # 8cc8 <_IO_stdin_used+0xcc8>
    3826:	48 89 85 50 05 00 00 	mov    %rax,0x550(%rbp)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    382d:	e8 ee eb ff ff       	call   2420 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    3832:	48 8d 95 b0 01 00 00 	lea    0x1b0(%rbp),%rdx
    3839:	48 89 ef             	mov    %rbp,%rdi
    383c:	48 8d 8d 10 05 00 00 	lea    0x510(%rbp),%rcx
    3843:	48 89 50 10          	mov    %rdx,0x10(%rax)
    3847:	48 8d 95 88 02 00 00 	lea    0x288(%rbp),%rdx
    384e:	48 8d 35 21 4c 00 00 	lea    0x4c21(%rip),%rsi        # 8476 <_IO_stdin_used+0x476>
    3855:	48 89 50 18          	mov    %rdx,0x18(%rax)
    3859:	48 8d 95 60 03 00 00 	lea    0x360(%rbp),%rdx
    3860:	48 89 50 20          	mov    %rdx,0x20(%rax)
    3864:	48 8d 95 38 04 00 00 	lea    0x438(%rbp),%rdx
    386b:	48 89 28             	mov    %rbp,(%rax)
    386e:	48 8d ad c0 06 00 00 	lea    0x6c0(%rbp),%rbp
    3875:	48 89 50 28          	mov    %rdx,0x28(%rax)
    3879:	48 8d 97 98 07 00 00 	lea    0x798(%rdi),%rdx
    3880:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3884:	48 89 48 30          	mov    %rcx,0x30(%rax)
    3888:	4c 89 70 38          	mov    %r14,0x38(%rax)
    388c:	48 89 50 48          	mov    %rdx,0x48(%rax)
    3890:	ba 06 00 00 00       	mov    $0x6,%edx
  }
  thread_data[timer_threadi].threads = my_thread_data;
    3895:	48 89 87 28 05 00 00 	mov    %rax,0x528(%rdi)
    my_thread_data[n] = &thread_data[n]; 
    389c:	48 89 68 40          	mov    %rbp,0x40(%rax)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    38a0:	48 8b 05 29 54 00 00 	mov    0x5429(%rip),%rax        # 8cd0 <_IO_stdin_used+0xcd0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    38a7:	c7 87 40 05 00 00 06 00 00 00 	movl   $0x6,0x540(%rdi)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    38b1:	48 89 87 38 05 00 00 	mov    %rax,0x538(%rdi)
    38b8:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    38ba:	c7 87 14 05 00 00 00 00 00 00 	movl   $0x0,0x514(%rdi)
    38c4:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
    38c9:	bf 01 00 00 00       	mov    $0x1,%edi
    my_thread_data[n] = &thread_data[n]; 
    38ce:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    38d3:	e8 08 ec ff ff       	call   24e0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38d8:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    38dd:	49 8d b7 50 01 00 00 	lea    0x150(%r15),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    38e4:	45 31 ff             	xor    %r15d,%r15d
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    38e7:	48 8d 15 32 0d 00 00 	lea    0xd32(%rip),%rdx        # 4620 <timer_thread>
    38ee:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    38f2:	e8 09 ec ff ff       	call   2500 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    38f7:	44 89 64 24 20       	mov    %r12d,0x20(%rsp)
    38fc:	4c 89 f6             	mov    %r14,%rsi
    38ff:	48 89 d9             	mov    %rbx,%rcx
    3902:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3907:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    390c:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
    3911:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3917:	48 89 6c 24 40       	mov    %rbp,0x40(%rsp)
    391c:	4c 89 6c 24 30       	mov    %r13,0x30(%rsp)
    3921:	49 89 c6             	mov    %rax,%r14
    3924:	45 89 d5             	mov    %r10d,%r13d
    for (int d = 0 ; d < threads_per_group ; d++) {
    3927:	48 89 4c 24 50       	mov    %rcx,0x50(%rsp)
    392c:	47 8d 24 3f          	lea    (%r15,%r15,1),%r12d
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    3930:	48 89 cd             	mov    %rcx,%rbp
    3933:	48 89 d3             	mov    %rdx,%rbx
    3936:	48 89 54 24 58       	mov    %rdx,0x58(%rsp)
    393b:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    3940:	4c 89 74 24 48       	mov    %r14,0x48(%rsp)
    3945:	49 89 f6             	mov    %rsi,%r14
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    3948:	c7 43 0c 01 00 00 00 	movl   $0x1,0xc(%rbx)
    394f:	44 89 e2             	mov    %r12d,%edx
    3952:	44 89 f9             	mov    %r15d,%ecx
    3955:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    3957:	c7 43 44 01 00 00 00 	movl   $0x1,0x44(%rbx)
    395e:	48 8d 35 9b 4e 00 00 	lea    0x4e9b(%rip),%rsi        # 8800 <_IO_stdin_used+0x800>
    3965:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    396a:	41 83 c4 01          	add    $0x1,%r12d
    396e:	e8 6d eb ff ff       	call   24e0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3973:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3978:	48 89 d9             	mov    %rbx,%rcx
    397b:	48 89 ef             	mov    %rbp,%rdi
    397e:	48 8d 15 bb 27 00 00 	lea    0x27bb(%rip),%rdx        # 6140 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3985:	48 81 c3 d8 00 00 00 	add    $0xd8,%rbx
    398c:	48 83 c5 08          	add    $0x8,%rbp
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3990:	e8 6b eb ff ff       	call   2500 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3995:	48 8b 53 d8          	mov    -0x28(%rbx),%rdx
    3999:	48 8b 7d f8          	mov    -0x8(%rbp),%rdi
    399d:	be 08 00 00 00       	mov    $0x8,%esi
    39a2:	e8 99 e9 ff ff       	call   2340 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    39a7:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    39ad:	45 39 e5             	cmp    %r12d,%r13d
    39b0:	75 96                	jne    3948 <main+0x1298>
  for (int k = 0 ; k < group_count ; k++) {
    39b2:	48 8b 4c 24 50       	mov    0x50(%rsp),%rcx
    39b7:	4c 89 f6             	mov    %r14,%rsi
    39ba:	41 83 c7 01          	add    $0x1,%r15d
    39be:	41 83 c5 02          	add    $0x2,%r13d
    39c2:	4c 8b 74 24 48       	mov    0x48(%rsp),%r14
    39c7:	48 8b 54 24 58       	mov    0x58(%rsp),%rdx
    39cc:	48 83 c1 10          	add    $0x10,%rcx
    39d0:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    39d7:	49 83 c6 70          	add    $0x70,%r14
    39db:	41 83 ff 03          	cmp    $0x3,%r15d
    39df:	0f 85 42 ff ff ff    	jne    3927 <main+0x1277>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    39e5:	4c 8b 7c 24 38       	mov    0x38(%rsp),%r15
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    39ea:	48 8b 05 e7 52 00 00 	mov    0x52e7(%rip),%rax        # 8cd8 <_IO_stdin_used+0xcd8>
    thread_data[x].type = IO;
    39f1:	49 89 f6             	mov    %rsi,%r14

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    39f4:	bf 01 00 00 00       	mov    $0x1,%edi
    39f9:	be d8 00 00 00       	mov    $0xd8,%esi
    thread_data[x].type = IO;
    39fe:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
    3a03:	4c 8b 6c 24 30       	mov    0x30(%rsp),%r13
    3a08:	41 c7 87 f4 05 00 00 02 00 00 00 	movl   $0x2,0x5f4(%r15)
    3a13:	44 8b 64 24 20       	mov    0x20(%rsp),%r12d
    thread_data[x].task_count = 0;
    3a18:	49 89 87 28 06 00 00 	mov    %rax,0x628(%r15)
    thread_data[x].type = IO;
    3a1f:	48 8b 6c 24 40       	mov    0x40(%rsp),%rbp
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a24:	e8 f7 e9 ff ff       	call   2420 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a29:	be 00 08 00 00       	mov    $0x800,%esi
    3a2e:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3a30:	49 89 87 40 06 00 00 	mov    %rax,0x640(%r15)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a37:	e8 14 eb ff ff       	call   2550 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a3c:	be 08 00 00 00       	mov    $0x8,%esi
    3a41:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    3a46:	41 89 87 48 06 00 00 	mov    %eax,0x648(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a4d:	e8 ce e9 ff ff       	call   2420 <calloc@plt>
    3a52:	ba 07 00 00 00       	mov    $0x7,%edx
    3a57:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    3a5c:	41 c7 87 10 06 00 00 02 00 00 00 	movl   $0x2,0x610(%r15)
      my_thread_data[n] = &thread_data[n]; 
    3a67:	4c 89 38             	mov    %r15,(%rax)
    3a6a:	48 8d 35 23 4a 00 00 	lea    0x4a23(%rip),%rsi        # 8494 <_IO_stdin_used+0x494>
    thread_data[x].threads = my_thread_data;
    3a71:	49 89 87 00 06 00 00 	mov    %rax,0x600(%r15)
      my_thread_data[n] = &thread_data[n]; 
    3a78:	4c 89 68 08          	mov    %r13,0x8(%rax)
    3a7c:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    3a7e:	41 c7 87 ec 05 00 00 07 00 00 00 	movl   $0x7,0x5ec(%r15)
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a89:	41 bf 08 00 00 00    	mov    $0x8,%r15d
    3a8f:	e8 4c ea ff ff       	call   24e0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    3a94:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    3a99:	4c 89 f1             	mov    %r14,%rcx
    3a9c:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3aa0:	48 8d 15 a9 1e 00 00 	lea    0x1ea9(%rip),%rdx        # 5950 <io_thread>
    3aa7:	4c 8d 73 40          	lea    0x40(%rbx),%r14
    3aab:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3ab2:	e8 49 ea ff ff       	call   2500 <pthread_create@plt>
    3ab7:	ba 08 00 00 00       	mov    $0x8,%edx
    3abc:	48 8d 35 e8 49 00 00 	lea    0x49e8(%rip),%rsi        # 84ab <_IO_stdin_used+0x4ab>
    3ac3:	31 c0                	xor    %eax,%eax
    3ac5:	bf 01 00 00 00       	mov    $0x1,%edi
    3aca:	e8 11 ea ff ff       	call   24e0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3acf:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    3ad4:	48 05 c0 01 00 00    	add    $0x1c0,%rax
    3ada:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    3adf:	44 89 fa             	mov    %r15d,%edx
    3ae2:	48 8d 35 d8 49 00 00 	lea    0x49d8(%rip),%rsi        # 84c1 <_IO_stdin_used+0x4c1>
    3ae9:	bf 01 00 00 00       	mov    $0x1,%edi
    3aee:	31 c0                	xor    %eax,%eax
    3af0:	e8 eb e9 ff ff       	call   24e0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3af5:	be 08 00 00 00       	mov    $0x8,%esi
    3afa:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3aff:	48 8b 05 d2 51 00 00 	mov    0x51d2(%rip),%rax        # 8cd8 <_IO_stdin_used+0xcd8>
    thread_data[x].type = EXTERNAL;
    3b06:	c7 45 0c 03 00 00 00 	movl   $0x3,0xc(%rbp)
    thread_data[x].task_count = 0;
    3b0d:	48 89 45 40          	mov    %rax,0x40(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3b11:	e8 0a e9 ff ff       	call   2420 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3b16:	48 8b bc 24 c0 00 00 00 	mov    0xc0(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3b1e:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3b23:	c7 85 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%rbp)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3b2d:	48 89 45 50          	mov    %rax,0x50(%rbp)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3b31:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3b34:	bf 02 00 00 00       	mov    $0x2,%edi
    3b39:	e8 e2 e8 ff ff       	call   2420 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3b3e:	48 8b 74 24 38       	mov    0x38(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b43:	48 89 e9             	mov    %rbp,%rcx
    3b46:	4c 89 f7             	mov    %r14,%rdi
    thread_data[x].threads = my_thread_data;
    3b49:	48 89 45 18          	mov    %rax,0x18(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b4d:	48 8d 15 bc 09 00 00 	lea    0x9bc(%rip),%rdx        # 4510 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b54:	49 83 c6 08          	add    $0x8,%r14
    3b58:	48 81 c5 d8 00 00 00 	add    $0xd8,%rbp
      my_thread_data[n] = &thread_data[n]; 
    3b5f:	48 89 30             	mov    %rsi,(%rax)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b62:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
      my_thread_data[n] = &thread_data[n]; 
    3b67:	4c 89 68 08          	mov    %r13,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3b6b:	48 8b 05 46 51 00 00 	mov    0x5146(%rip),%rax        # 8cb8 <_IO_stdin_used+0xcb8>
    thread_data[x].thread_index = x;
    3b72:	44 89 bd 2c ff ff ff 	mov    %r15d,-0xd4(%rbp)
    thread_data[x].thread_count = thread_count;
    3b79:	48 89 85 50 ff ff ff 	mov    %rax,-0xb0(%rbp)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3b80:	e8 7b e9 ff ff       	call   2500 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3b85:	48 83 44 24 08 38    	addq   $0x38,0x8(%rsp)
    3b8b:	48 83 84 24 c0 00 00 00 10 	addq   $0x10,0xc0(%rsp)
    3b94:	41 83 ff 08          	cmp    $0x8,%r15d
    3b98:	75 42                	jne    3bdc <main+0x152c>
    3b9a:	41 bf 09 00 00 00    	mov    $0x9,%r15d
    3ba0:	e9 3a ff ff ff       	jmp    3adf <main+0x142f>
        other = (x + 1) % total_threads;
    3ba5:	44 8b 6c 24 20       	mov    0x20(%rsp),%r13d
        my_thread_data[1] = &thread_data[other]; 
    3baa:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3baf:	48 89 5c 24 48       	mov    %rbx,0x48(%rsp)
    3bb4:	45 31 c0             	xor    %r8d,%r8d
    3bb7:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
        other = (x + 1) % total_threads;
    3bbc:	45 89 ee             	mov    %r13d,%r14d
        my_thread_data[1] = &thread_data[other]; 
    3bbf:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3bc3:	48 8d 14 c7          	lea    (%rdi,%rax,8),%rdx
        my_thread_data[0] = &thread_data[x]; 
    3bc7:	4c 89 c8             	mov    %r9,%rax
    3bca:	e9 fd ee ff ff       	jmp    2acc <main+0x41c>
            CPU_SET(j, sendercpu);
    3bcf:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
    3bd7:	e9 82 ef ff ff       	jmp    2b5e <main+0x4ae>
    3bdc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3be1:	48 8d 2d f6 48 00 00 	lea    0x48f6(%rip),%rbp        # 84de <_IO_stdin_used+0x4de>
    3be8:	4c 8d 70 04          	lea    0x4(%rax),%r14
    3bec:	4c 8d a8 74 08 00 00 	lea    0x874(%rax),%r13
    3bf3:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3bf7:	41 8b 16             	mov    (%r14),%edx
    3bfa:	48 89 ee             	mov    %rbp,%rsi
    3bfd:	bf 01 00 00 00       	mov    $0x1,%edi
    3c02:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3c04:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    3c0b:	e8 d0 e8 ff ff       	call   24e0 <__printf_chk@plt>
    3c10:	4d 39 f5             	cmp    %r14,%r13
    3c13:	75 de                	jne    3bf3 <main+0x1543>
    3c15:	48 8d 3d d5 48 00 00 	lea    0x48d5(%rip),%rdi        # 84f1 <_IO_stdin_used+0x4f1>
    3c1c:	45 31 f6             	xor    %r14d,%r14d
    3c1f:	4c 8d ac 24 f0 00 00 00 	lea    0xf0(%rsp),%r13
    3c27:	e8 24 e7 ff ff       	call   2350 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3c2c:	48 8d 2d dc 48 00 00 	lea    0x48dc(%rip),%rbp        # 850f <_IO_stdin_used+0x50f>
    void * result; 
    pthread_join(thread[x], &result);
    3c33:	4a 8b 3c f3          	mov    (%rbx,%r14,8),%rdi
    3c37:	4c 89 ee             	mov    %r13,%rsi
    3c3a:	e8 51 e9 ff ff       	call   2590 <pthread_join@plt>
    3c3f:	44 89 f2             	mov    %r14d,%edx
    3c42:	48 89 ee             	mov    %rbp,%rsi
    3c45:	bf 01 00 00 00       	mov    $0x1,%edi
    3c4a:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3c4c:	49 83 c6 01          	add    $0x1,%r14
    3c50:	e8 8b e8 ff ff       	call   24e0 <__printf_chk@plt>
    3c55:	49 83 fe 0a          	cmp    $0xa,%r14
    3c59:	75 d8                	jne    3c33 <main+0x1583>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c5b:	be 08 00 00 00       	mov    $0x8,%esi
    3c60:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3c65:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3c67:	e8 b4 e7 ff ff       	call   2420 <calloc@plt>
    3c6c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    3c71:	49 89 c7             	mov    %rax,%r15
    3c74:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c76:	49 89 d1             	mov    %rdx,%r9
    3c79:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c7c:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3c80:	45 85 d2             	test   %r10d,%r10d
    3c83:	0f 8e 94 00 00 00    	jle    3d1d <main+0x166d>
    3c89:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3c8d:	4d 63 c2             	movslq %r10d,%r8
    3c90:	48 63 cb             	movslq %ebx,%rcx
    3c93:	49 c1 e0 09          	shl    $0x9,%r8
    3c97:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    3c9b:	49 01 f8             	add    %rdi,%r8
    3c9e:	66 90                	xchg   %ax,%ax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3ca0:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3ca7:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3cae:	48 83 c6 60          	add    $0x60,%rsi
    3cb2:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    3cb7:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    3cbc:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3cc4:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3cc8:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3cd0:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3cd4:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    3cd8:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    3ce0:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3ce7:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    3ceb:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3cef:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3cf6:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3cfd:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3d01:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3d05:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3d09:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3d0d:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3d11:	4c 39 c7             	cmp    %r8,%rdi
    3d14:	75 8a                	jne    3ca0 <main+0x15f0>
    3d16:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3d1a:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3d1d:	49 81 c1 d8 00 00 00 	add    $0xd8,%r9
    3d24:	45 85 db             	test   %r11d,%r11d
    3d27:	75 08                	jne    3d31 <main+0x1681>
    3d29:	45 89 e3             	mov    %r12d,%r11d
    3d2c:	e9 4b ff ff ff       	jmp    3c7c <main+0x15cc>
  for (int k = 0 ; k < group_count ; k++) {
    3d31:	83 c0 02             	add    $0x2,%eax
    3d34:	48 81 c2 b0 01 00 00 	add    $0x1b0,%rdx
    3d3b:	83 f8 06             	cmp    $0x6,%eax
    3d3e:	0f 85 32 ff ff ff    	jne    3c76 <main+0x15c6>
    3d44:	48 8d 3d d8 47 00 00 	lea    0x47d8(%rip),%rdi        # 8523 <_IO_stdin_used+0x523>
    3d4b:	e8 00 e6 ff ff       	call   2350 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3d50:	48 8d 35 a8 46 00 00 	lea    0x46a8(%rip),%rsi        # 83ff <_IO_stdin_used+0x3ff>
    3d57:	48 8d 3d dd 47 00 00 	lea    0x47dd(%rip),%rdi        # 853b <_IO_stdin_used+0x53b>
    3d5e:	e8 bd e7 ff ff       	call   2520 <fopen@plt>
    3d63:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas2_size; x++) {
    3d66:	85 db                	test   %ebx,%ebx
    3d68:	7e 6f                	jle    3dd9 <main+0x1729>
    3d6a:	48 63 db             	movslq %ebx,%rbx
    3d6d:	4c 8d 35 6a 46 00 00 	lea    0x466a(%rip),%r14        # 83de <_IO_stdin_used+0x3de>
    3d74:	4c 8d 2d a7 46 00 00 	lea    0x46a7(%rip),%r13        # 8422 <_IO_stdin_used+0x422>
    3d7b:	49 8d 2c df          	lea    (%r15,%rbx,8),%rbp
    char * c = calloc(250, sizeof(char));
    3d7f:	be 01 00 00 00       	mov    $0x1,%esi
    3d84:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3d89:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    3d8d:	e8 8e e6 ff ff       	call   2420 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3d92:	4c 89 f1             	mov    %r14,%rcx
    3d95:	ba fa 00 00 00       	mov    $0xfa,%edx
    3d9a:	be 01 00 00 00       	mov    $0x1,%esi
    3d9f:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3da2:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3da6:	48 89 df             	mov    %rbx,%rdi
    3da9:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3db0:	31 c0                	xor    %eax,%eax
    3db2:	e8 29 e8 ff ff       	call   25e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3db7:	48 89 da             	mov    %rbx,%rdx
    3dba:	4c 89 ee             	mov    %r13,%rsi
    3dbd:	bf 01 00 00 00       	mov    $0x1,%edi
    3dc2:	31 c0                	xor    %eax,%eax
    3dc4:	e8 17 e7 ff ff       	call   24e0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3dc9:	4c 89 e6             	mov    %r12,%rsi
    3dcc:	48 89 df             	mov    %rbx,%rdi
    3dcf:	e8 0c e6 ff ff       	call   23e0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3dd4:	49 39 ef             	cmp    %rbp,%r15
    3dd7:	75 a6                	jne    3d7f <main+0x16cf>
    printf("%s", c);
    fprintf(m2, "%s", c);
  } 
  fclose(m2);
    3dd9:	4c 89 e7             	mov    %r12,%rdi
  long total = 0;
  long ingests = 0;
  long sends = 0;
  long sents = 0;
  long received = 0;
    3ddc:	45 31 f6             	xor    %r14d,%r14d
  long sents = 0;
    3ddf:	45 31 ed             	xor    %r13d,%r13d
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3de2:	49 bc db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r12
  fclose(m2);
    3dec:	e8 8f e5 ff ff       	call   2380 <fclose@plt>
    3df1:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  long sends = 0;
    3df6:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  long ingests = 0;
    3dff:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long total = 0;
    3e08:	48 c7 44 24 30 00 00 00 00 	movq   $0x0,0x30(%rsp)
  int datas2_size = 0; 
    3e11:	48 8b bc 24 90 00 00 00 	mov    0x90(%rsp),%rdi
    3e19:	8d 48 02             	lea    0x2(%rax),%ecx
    3e1c:	89 44 24 10          	mov    %eax,0x10(%rsp)
    3e20:	89 4c 24 48          	mov    %ecx,0x48(%rsp)
    3e24:	4c 8b bc 24 a8 00 00 00 	mov    0xa8(%rsp),%r15
    3e2c:	48 89 7c 24 40       	mov    %rdi,0x40(%rsp)
      int x = (k * threads_per_group) + d;
    3e31:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    3e35:	89 f8                	mov    %edi,%eax
    3e37:	83 c7 01             	add    $0x1,%edi
        other = abs(x - 1) % total_threads;
    3e3a:	8d 50 02             	lea    0x2(%rax),%edx
    3e3d:	89 7c 24 10          	mov    %edi,0x10(%rsp)
    3e41:	83 e7 01             	and    $0x1,%edi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3e44:	bf 0a 00 00 00       	mov    $0xa,%edi
    3e49:	0f 44 c2             	cmove  %edx,%eax
    3e4c:	48 63 d8             	movslq %eax,%rbx
    3e4f:	e8 dc e4 ff ff       	call   2330 <putchar@plt>
    3e54:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3e59:	bf 01 00 00 00       	mov    $0x1,%edi
    3e5e:	48 8d 35 df 46 00 00 	lea    0x46df(%rip),%rsi        # 8544 <_IO_stdin_used+0x544>
    3e65:	48 8b 10             	mov    (%rax),%rdx
    3e68:	31 c0                	xor    %eax,%eax
    3e6a:	e8 71 e6 ff ff       	call   24e0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e6f:	41 8b 57 40          	mov    0x40(%r15),%edx
    3e73:	85 d2                	test   %edx,%edx
    3e75:	0f 8e d7 04 00 00    	jle    4352 <main+0x1ca2>
    3e7b:	48 63 ca             	movslq %edx,%rcx
    3e7e:	49 8b 47 38          	mov    0x38(%r15),%rax
      long v = 0;
    3e82:	31 d2                	xor    %edx,%edx
    3e84:	48 c1 e1 09          	shl    $0x9,%rcx
    3e88:	48 01 c1             	add    %rax,%rcx
    3e8b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
        v += thread_data[me].tasks[n].v;
    3e90:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e97:	48 05 00 02 00 00    	add    $0x200,%rax
    3e9d:	48 39 c8             	cmp    %rcx,%rax
    3ea0:	75 ee                	jne    3e90 <main+0x17e0>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3ea2:	48 8b 7c 24 38       	mov    0x38(%rsp),%rdi
    3ea7:	48 8d 04 5b          	lea    (%rbx,%rbx,2),%rax
    3eab:	48 8d 04 c0          	lea    (%rax,%rax,8),%rax
    3eaf:	48 8d 04 c7          	lea    (%rdi,%rax,8),%rax
    3eb3:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3eb7:	85 c9                	test   %ecx,%ecx
    3eb9:	7e 27                	jle    3ee2 <main+0x1832>
    3ebb:	48 8b 40 38          	mov    0x38(%rax),%rax
    3ebf:	48 c1 e1 09          	shl    $0x9,%rcx
    3ec3:	48 01 c1             	add    %rax,%rcx
    3ec6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        v += thread_data[other].tasks[n].v;
    3ed0:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3ed7:	48 05 00 02 00 00    	add    $0x200,%rax
    3edd:	48 39 c8             	cmp    %rcx,%rax
    3ee0:	75 ee                	jne    3ed0 <main+0x1820>
    3ee2:	48 8d 35 70 46 00 00 	lea    0x4670(%rip),%rsi        # 8559 <_IO_stdin_used+0x559>
    3ee9:	bf 01 00 00 00       	mov    $0x1,%edi
    3eee:	31 c0                	xor    %eax,%eax
    3ef0:	e8 eb e5 ff ff       	call   24e0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3ef5:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3efa:	bf 01 00 00 00       	mov    $0x1,%edi
    3eff:	48 8d 35 2a 49 00 00 	lea    0x492a(%rip),%rsi        # 8830 <_IO_stdin_used+0x830>
    3f06:	48 8b 08             	mov    (%rax),%rcx
    3f09:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3f13:	48 f7 e9             	imul   %rcx
    3f16:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3f1a:	31 c0                	xor    %eax,%eax
    3f1c:	48 d1 fa             	sar    %rdx
    3f1f:	48 29 ca             	sub    %rcx,%rdx
    3f22:	e8 b9 e5 ff ff       	call   24e0 <__printf_chk@plt>
    3f27:	bf 0a 00 00 00       	mov    $0xa,%edi
    3f2c:	e8 ff e3 ff ff       	call   2330 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3f31:	45 8b 57 40          	mov    0x40(%r15),%r10d
    3f35:	45 85 d2             	test   %r10d,%r10d
    3f38:	0f 8e 01 01 00 00    	jle    403f <main+0x198f>
        total += thread_data[x].tasks[n].n;
    3f3e:	49 8b 4f 38          	mov    0x38(%r15),%rcx
    3f42:	4c 8b 44 24 30       	mov    0x30(%rsp),%r8
    3f47:	31 d2                	xor    %edx,%edx
    3f49:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    3f4e:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    3f53:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3f58:	48 89 d5             	mov    %rdx,%rbp
    3f5b:	89 54 24 08          	mov    %edx,0x8(%rsp)
        sends += thread_data[x].tasks[n].sends;
    3f5f:	31 db                	xor    %ebx,%ebx
    3f61:	48 c1 e5 09          	shl    $0x9,%rbp
    3f65:	48 89 54 24 30       	mov    %rdx,0x30(%rsp)
        total += thread_data[x].tasks[n].n;
    3f6a:	48 01 e9             	add    %rbp,%rcx
        sends += thread_data[x].tasks[n].sends;
    3f6d:	48 89 e8             	mov    %rbp,%rax
    3f70:	4c 89 ed             	mov    %r13,%rbp
    3f73:	4d 89 f5             	mov    %r14,%r13
        total += thread_data[x].tasks[n].n;
    3f76:	4c 03 81 08 01 00 00 	add    0x108(%rcx),%r8
        ingests += thread_data[x].tasks[n].ingest_count;
    3f7d:	48 03 b1 68 01 00 00 	add    0x168(%rcx),%rsi
        sends += thread_data[x].tasks[n].sends;
    3f84:	49 89 c6             	mov    %rax,%r14
    3f87:	48 03 b9 78 01 00 00 	add    0x178(%rcx),%rdi
    3f8e:	4c 89 44 24 18       	mov    %r8,0x18(%rsp)
    3f93:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
    3f98:	48 89 7c 24 28       	mov    %rdi,0x28(%rsp)
    3f9d:	0f 1f 00             	nopl   (%rax)
    3fa0:	8b 4c 24 08          	mov    0x8(%rsp),%ecx
    3fa4:	8b 54 24 10          	mov    0x10(%rsp),%edx
    3fa8:	41 89 d8             	mov    %ebx,%r8d
    3fab:	bf 01 00 00 00       	mov    $0x1,%edi
    3fb0:	48 8d 35 af 45 00 00 	lea    0x45af(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    3fb7:	31 c0                	xor    %eax,%eax
    3fb9:	e8 22 e5 ff ff       	call   24e0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fbe:	49 8b 4f 38          	mov    0x38(%r15),%rcx
    3fc2:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    3fca:	48 29 d8             	sub    %rbx,%rax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3fcd:	48 83 c3 01          	add    $0x1,%rbx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fd1:	4a 8b 94 31 70 01 00 00 	mov    0x170(%rcx,%r14,1),%rdx
    3fd9:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    3fdd:	48 8b 10             	mov    (%rax),%rdx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3fe0:	48 8b 40 08          	mov    0x8(%rax),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3fe4:	4c 8b 8a 08 03 00 00 	mov    0x308(%rdx),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3feb:	4c 8b 92 10 03 00 00 	mov    0x310(%rdx),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3ff2:	49 01 e9             	add    %rbp,%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3ff5:	4d 01 ea             	add    %r13,%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3ff8:	4c 03 88 08 03 00 00 	add    0x308(%rax),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3fff:	4c 03 90 10 03 00 00 	add    0x310(%rax),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    4006:	4c 89 cd             	mov    %r9,%rbp
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    4009:	4d 89 d5             	mov    %r10,%r13
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    400c:	48 83 fb 06          	cmp    $0x6,%rbx
    4010:	75 8e                	jne    3fa0 <main+0x18f0>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    4012:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    4017:	4c 8b 44 24 18       	mov    0x18(%rsp),%r8
    401c:	4d 89 d6             	mov    %r10,%r14
    401f:	4d 89 cd             	mov    %r9,%r13
    4022:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
    4027:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    402c:	48 83 c2 01          	add    $0x1,%rdx
    4030:	41 39 57 40          	cmp    %edx,0x40(%r15)
    4034:	0f 8f 1e ff ff ff    	jg     3f58 <main+0x18a8>
    403a:	4c 89 44 24 30       	mov    %r8,0x30(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    403f:	31 ed                	xor    %ebp,%ebp
    4041:	49 83 bf a0 00 00 00 00 	cmpq   $0x0,0xa0(%r15)
    4049:	48 8d 1d 00 48 00 00 	lea    0x4800(%rip),%rbx        # 8850 <_IO_stdin_used+0x850>
    4050:	7e 5f                	jle    40b1 <main+0x1a01>
    4052:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4058:	49 8b 87 90 00 00 00 	mov    0x90(%r15),%rax
    405f:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    4064:	48 83 ec 08          	sub    $0x8,%rsp
    4068:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    406d:	48 83 c5 01          	add    $0x1,%rbp
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    4071:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    4075:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    4079:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    407d:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4080:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    4084:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    4087:	49 f7 e4             	mul    %r12
    408a:	8b 49 20             	mov    0x20(%rcx),%ecx
    408d:	56                   	push   %rsi
    408e:	31 c0                	xor    %eax,%eax
    4090:	48 89 de             	mov    %rbx,%rsi
    4093:	48 c1 ea 12          	shr    $0x12,%rdx
    4097:	49 89 d1             	mov    %rdx,%r9
    409a:	ba 02 00 00 00       	mov    $0x2,%edx
    409f:	e8 3c e4 ff ff       	call   24e0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    40a4:	41 58                	pop    %r8
    40a6:	41 59                	pop    %r9
    40a8:	49 39 af a0 00 00 00 	cmp    %rbp,0xa0(%r15)
    40af:	7f a7                	jg     4058 <main+0x19a8>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    40b1:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    40b8:	85 c9                	test   %ecx,%ecx
    40ba:	0f 8e f5 00 00 00    	jle    41b5 <main+0x1b05>
    40c0:	4c 89 6c 24 50       	mov    %r13,0x50(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    40c5:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    40c9:	31 db                	xor    %ebx,%ebx
    40cb:	4c 89 74 24 58       	mov    %r14,0x58(%rsp)
    40d0:	49 8b 04 d9          	mov    (%r9,%rbx,8),%rax
    40d4:	41 89 dd             	mov    %ebx,%r13d
    40d7:	4c 8d 34 dd 00 00 00 00 	lea    0x0(,%rbx,8),%r14
    40df:	8b 30                	mov    (%rax),%esi
    40e1:	85 f6                	test   %esi,%esi
    40e3:	0f 8e b6 00 00 00    	jle    419f <main+0x1aef>
    40e9:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    40ee:	48 8b 48 08          	mov    0x8(%rax),%rcx
    40f2:	31 ff                	xor    %edi,%edi
    40f4:	0f 1f 40 00          	nopl   0x0(%rax)
    40f8:	48 89 fb             	mov    %rdi,%rbx
    40fb:	31 ed                	xor    %ebp,%ebp
    40fd:	48 c1 e3 08          	shl    $0x8,%rbx
    4101:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    4105:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    410b:	85 d2                	test   %edx,%edx
    410d:	7e 78                	jle    4187 <main+0x1ad7>
    410f:	48 89 7c 24 08       	mov    %rdi,0x8(%rsp)
    4114:	0f 1f 40 00          	nopl   0x0(%rax)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4118:	48 89 e9             	mov    %rbp,%rcx
    411b:	48 83 ec 08          	sub    $0x8,%rsp
    411f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    4124:	48 83 c5 01          	add    $0x1,%rbp
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4128:	48 c1 e1 05          	shl    $0x5,%rcx
    412c:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    4133:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    4137:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    413b:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    413e:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    4142:	4c 2b 01             	sub    (%rcx),%r8
    4145:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    4146:	49 f7 e4             	mul    %r12
    4149:	44 89 e9             	mov    %r13d,%ecx
    414c:	48 8d 35 4d 47 00 00 	lea    0x474d(%rip),%rsi        # 88a0 <_IO_stdin_used+0x8a0>
    4153:	31 c0                	xor    %eax,%eax
    4155:	48 c1 ea 12          	shr    $0x12,%rdx
    4159:	49 89 d1             	mov    %rdx,%r9
    415c:	ba 02 00 00 00       	mov    $0x2,%edx
    4161:	e8 7a e3 ff ff       	call   24e0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    4166:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    416a:	5e                   	pop    %rsi
    416b:	5f                   	pop    %rdi
    416c:	4b 8b 14 31          	mov    (%r9,%r14,1),%rdx
    4170:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    4174:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    4178:	39 a8 94 00 00 00    	cmp    %ebp,0x94(%rax)
    417e:	7f 98                	jg     4118 <main+0x1a68>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4180:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    4185:	8b 32                	mov    (%rdx),%esi
    4187:	48 83 c7 01          	add    $0x1,%rdi
    418b:	39 fe                	cmp    %edi,%esi
    418d:	0f 8f 65 ff ff ff    	jg     40f8 <main+0x1a48>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4193:	48 8b 5c 24 18       	mov    0x18(%rsp),%rbx
    4198:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    419f:	48 83 c3 01          	add    $0x1,%rbx
    41a3:	39 d9                	cmp    %ebx,%ecx
    41a5:	0f 8f 25 ff ff ff    	jg     40d0 <main+0x1a20>
    41ab:	4c 8b 6c 24 50       	mov    0x50(%rsp),%r13
    41b0:	4c 8b 74 24 58       	mov    0x58(%rsp),%r14
    for (int d = 0 ; d < threads_per_group ; d++) {
    41b5:	48 83 44 24 40 18    	addq   $0x18,0x40(%rsp)
    41bb:	8b 7c 24 10          	mov    0x10(%rsp),%edi
    41bf:	49 81 c7 d8 00 00 00 	add    $0xd8,%r15
    41c6:	39 7c 24 48          	cmp    %edi,0x48(%rsp)
    41ca:	0f 85 61 fc ff ff    	jne    3e31 <main+0x1781>
  for (int k = 0 ; k < group_count ; k++) {
    41d0:	48 81 84 24 a8 00 00 00 b0 01 00 00 	addq   $0x1b0,0xa8(%rsp)
    41dc:	8b 4c 24 48          	mov    0x48(%rsp),%ecx
    41e0:	48 83 84 24 90 00 00 00 30 	addq   $0x30,0x90(%rsp)
    41e9:	83 f9 05             	cmp    $0x5,%ecx
    41ec:	74 07                	je     41f5 <main+0x1b45>
    41ee:	89 c8                	mov    %ecx,%eax
    41f0:	e9 1c fc ff ff       	jmp    3e11 <main+0x1761>
    41f5:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
    41fa:	48 8d 35 75 43 00 00 	lea    0x4375(%rip),%rsi        # 8576 <_IO_stdin_used+0x576>
    4201:	bf 01 00 00 00       	mov    $0x1,%edi
    4206:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    4208:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4212:	4c 89 fa             	mov    %r15,%rdx
    4215:	e8 c6 e2 ff ff       	call   24e0 <__printf_chk@plt>
    421a:	bf 0a 00 00 00       	mov    $0xa,%edi
    421f:	e8 0c e1 ff ff       	call   2330 <putchar@plt>
    4224:	48 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%rdi
    422c:	48 8d 35 c5 46 00 00 	lea    0x46c5(%rip),%rsi        # 88f8 <_IO_stdin_used+0x8f8>
    4233:	31 c0                	xor    %eax,%eax
    4235:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    4239:	bf 01 00 00 00       	mov    $0x1,%edi
    423e:	e8 9d e2 ff ff       	call   24e0 <__printf_chk@plt>
    4243:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    4248:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    424d:	48 8d 35 cc 46 00 00 	lea    0x46cc(%rip),%rsi        # 8920 <_IO_stdin_used+0x920>
    4254:	48 f7 eb             	imul   %rbx
    4257:	48 c1 ff 3f          	sar    $0x3f,%rdi
    425b:	31 c0                	xor    %eax,%eax
    425d:	48 d1 fa             	sar    %rdx
    4260:	48 29 fa             	sub    %rdi,%rdx
    4263:	bf 01 00 00 00       	mov    $0x1,%edi
    4268:	e8 73 e2 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    426d:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    4272:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    4277:	48 8d 35 d2 46 00 00 	lea    0x46d2(%rip),%rsi        # 8950 <_IO_stdin_used+0x950>
    427e:	48 f7 eb             	imul   %rbx
    4281:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4285:	31 c0                	xor    %eax,%eax
    4287:	48 d1 fa             	sar    %rdx
    428a:	48 29 fa             	sub    %rdi,%rdx
    428d:	bf 01 00 00 00       	mov    $0x1,%edi
    4292:	e8 49 e2 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    4297:	4c 89 f8             	mov    %r15,%rax
    429a:	4c 89 ff             	mov    %r15,%rdi
    429d:	48 8d 35 dc 46 00 00 	lea    0x46dc(%rip),%rsi        # 8980 <_IO_stdin_used+0x980>
    42a4:	48 f7 eb             	imul   %rbx
    42a7:	48 c1 ff 3f          	sar    $0x3f,%rdi
    42ab:	31 c0                	xor    %eax,%eax
    42ad:	48 d1 fa             	sar    %rdx
    42b0:	48 29 fa             	sub    %rdi,%rdx
    42b3:	bf 01 00 00 00       	mov    $0x1,%edi
    42b8:	e8 23 e2 ff ff       	call   24e0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    42bd:	4c 89 e8             	mov    %r13,%rax
    42c0:	bf 01 00 00 00       	mov    $0x1,%edi
    42c5:	48 8d 35 be 42 00 00 	lea    0x42be(%rip),%rsi        # 858a <_IO_stdin_used+0x58a>
    42cc:	48 f7 eb             	imul   %rbx
    42cf:	4c 89 e8             	mov    %r13,%rax
    42d2:	48 c1 f8 3f          	sar    $0x3f,%rax
    42d6:	48 d1 fa             	sar    %rdx
    42d9:	48 29 c2             	sub    %rax,%rdx
    42dc:	31 c0                	xor    %eax,%eax
    42de:	48 89 d5             	mov    %rdx,%rbp
    42e1:	e8 fa e1 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total sents %ld\n", sentdur);
  long recdur = received / DURATION;
    42e6:	4c 89 f0             	mov    %r14,%rax
    42e9:	bf 01 00 00 00       	mov    $0x1,%edi
    42ee:	48 8d 35 a6 42 00 00 	lea    0x42a6(%rip),%rsi        # 859b <_IO_stdin_used+0x59b>
    42f5:	48 f7 eb             	imul   %rbx
    42f8:	4c 89 f0             	mov    %r14,%rax
    42fb:	48 c1 f8 3f          	sar    $0x3f,%rax
    42ff:	48 89 d3             	mov    %rdx,%rbx
    4302:	48 d1 fb             	sar    %rbx
    4305:	48 29 c3             	sub    %rax,%rbx
    4308:	31 c0                	xor    %eax,%eax
    430a:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    430d:	48 29 eb             	sub    %rbp,%rbx
    4310:	e8 cb e1 ff ff       	call   24e0 <__printf_chk@plt>
    4315:	31 c0                	xor    %eax,%eax
    4317:	48 89 da             	mov    %rbx,%rdx
    431a:	bf 01 00 00 00       	mov    $0x1,%edi
    431f:	48 8d 35 89 42 00 00 	lea    0x4289(%rip),%rsi        # 85af <_IO_stdin_used+0x5af>
    4326:	e8 b5 e1 ff ff       	call   24e0 <__printf_chk@plt>
  return 0;

}
    432b:	48 8b 84 24 f8 00 00 00 	mov    0xf8(%rsp),%rax
    4333:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    433c:	75 25                	jne    4363 <main+0x1cb3>
    433e:	48 81 c4 08 01 00 00 	add    $0x108,%rsp
    4345:	31 c0                	xor    %eax,%eax
    4347:	5b                   	pop    %rbx
    4348:	5d                   	pop    %rbp
    4349:	41 5c                	pop    %r12
    434b:	41 5d                	pop    %r13
    434d:	41 5e                	pop    %r14
    434f:	41 5f                	pop    %r15
    4351:	c3                   	ret
      long v = 0;
    4352:	31 d2                	xor    %edx,%edx
    4354:	e9 49 fb ff ff       	jmp    3ea2 <main+0x17f2>
            exit(1);
    4359:	bf 01 00 00 00       	mov    $0x1,%edi
    435e:	e8 dd e1 ff ff       	call   2540 <exit@plt>
}
    4363:	e8 38 e0 ff ff       	call   23a0 <__stack_chk_fail@plt>
    4368:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)

0000000000004370 <_start>:
    4370:	f3 0f 1e fa          	endbr64
    4374:	31 ed                	xor    %ebp,%ebp
    4376:	49 89 d1             	mov    %rdx,%r9
    4379:	5e                   	pop    %rsi
    437a:	48 89 e2             	mov    %rsp,%rdx
    437d:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4381:	50                   	push   %rax
    4382:	54                   	push   %rsp
    4383:	45 31 c0             	xor    %r8d,%r8d
    4386:	31 c9                	xor    %ecx,%ecx
    4388:	48 8d 3d 21 e3 ff ff 	lea    -0x1cdf(%rip),%rdi        # 26b0 <main>
    438f:	ff 15 43 6c 00 00    	call   *0x6c43(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    4395:	f4                   	hlt
    4396:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000043a0 <deregister_tm_clones>:
    43a0:	48 8d 3d 79 6c 00 00 	lea    0x6c79(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    43a7:	48 8d 05 72 6c 00 00 	lea    0x6c72(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    43ae:	48 39 f8             	cmp    %rdi,%rax
    43b1:	74 15                	je     43c8 <deregister_tm_clones+0x28>
    43b3:	48 8b 05 26 6c 00 00 	mov    0x6c26(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    43ba:	48 85 c0             	test   %rax,%rax
    43bd:	74 09                	je     43c8 <deregister_tm_clones+0x28>
    43bf:	ff e0                	jmp    *%rax
    43c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    43c8:	c3                   	ret
    43c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000043d0 <register_tm_clones>:
    43d0:	48 8d 3d 49 6c 00 00 	lea    0x6c49(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    43d7:	48 8d 35 42 6c 00 00 	lea    0x6c42(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    43de:	48 29 fe             	sub    %rdi,%rsi
    43e1:	48 89 f0             	mov    %rsi,%rax
    43e4:	48 c1 ee 3f          	shr    $0x3f,%rsi
    43e8:	48 c1 f8 03          	sar    $0x3,%rax
    43ec:	48 01 c6             	add    %rax,%rsi
    43ef:	48 d1 fe             	sar    %rsi
    43f2:	74 14                	je     4408 <register_tm_clones+0x38>
    43f4:	48 8b 05 f5 6b 00 00 	mov    0x6bf5(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    43fb:	48 85 c0             	test   %rax,%rax
    43fe:	74 08                	je     4408 <register_tm_clones+0x38>
    4400:	ff e0                	jmp    *%rax
    4402:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4408:	c3                   	ret
    4409:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004410 <__do_global_dtors_aux>:
    4410:	f3 0f 1e fa          	endbr64
    4414:	80 3d 0d 6c 00 00 00 	cmpb   $0x0,0x6c0d(%rip)        # b028 <completed.0>
    441b:	75 2b                	jne    4448 <__do_global_dtors_aux+0x38>
    441d:	55                   	push   %rbp
    441e:	48 83 3d d2 6b 00 00 00 	cmpq   $0x0,0x6bd2(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    4426:	48 89 e5             	mov    %rsp,%rbp
    4429:	74 0c                	je     4437 <__do_global_dtors_aux+0x27>
    442b:	48 8b 3d d6 6b 00 00 	mov    0x6bd6(%rip),%rdi        # b008 <__dso_handle>
    4432:	e8 d9 de ff ff       	call   2310 <__cxa_finalize@plt>
    4437:	e8 64 ff ff ff       	call   43a0 <deregister_tm_clones>
    443c:	c6 05 e5 6b 00 00 01 	movb   $0x1,0x6be5(%rip)        # b028 <completed.0>
    4443:	5d                   	pop    %rbp
    4444:	c3                   	ret
    4445:	0f 1f 00             	nopl   (%rax)
    4448:	c3                   	ret
    4449:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004450 <frame_dummy>:
    4450:	f3 0f 1e fa          	endbr64
    4454:	e9 77 ff ff ff       	jmp    43d0 <register_tm_clones>
    4459:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004460 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    4460:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    4464:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    446b:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    446f:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    4477:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    447b:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    447f:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4486:	48 85 c9             	test   %rcx,%rcx
    4489:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4490:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4494:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4498:	31 c0                	xor    %eax,%eax
    449a:	c3                   	ret
    449b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000044a0 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    44a0:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    44a4:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    44ab:	85 c9                	test   %ecx,%ecx
    44ad:	7e 4f                	jle    44fe <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    44af:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    44b6:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    44bd:	48 c1 e1 09          	shl    $0x9,%rcx
    44c1:	48 8b 50 18          	mov    0x18(%rax),%rdx
    44c5:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    44c9:	48 8b 70 38          	mov    0x38(%rax),%rsi
    44cd:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    44cf:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    44d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    44d8:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    44e0:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    44e8:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    44f3:	48 05 00 02 00 00    	add    $0x200,%rax
    44f9:	48 39 c1             	cmp    %rax,%rcx
    44fc:	75 da                	jne    44d8 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    44fe:	0f ae f8             	sfence
}
    4501:	31 c0                	xor    %eax,%eax
    4503:	c3                   	ret
    4504:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    450f:	90                   	nop

0000000000004510 <external_thread>:
void * external_thread(void *arg) {
    4510:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    4514:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4518:	0f 85 fb 00 00 00    	jne    4619 <external_thread+0x109>
void * external_thread(void *arg) {
    451e:	41 57                	push   %r15
    4520:	49 89 ff             	mov    %rdi,%r15
    4523:	41 56                	push   %r14
    4525:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    4527:	4c 8d 2d d6 3a 00 00 	lea    0x3ad6(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    452e:	41 54                	push   %r12
    4530:	55                   	push   %rbp
    4531:	53                   	push   %rbx
    4532:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    4536:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    453c:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    4540:	85 c9                	test   %ecx,%ecx
    4542:	7e 6e                	jle    45b2 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4544:	45 31 e4             	xor    %r12d,%r12d
    4547:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4550:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    4558:	31 db                	xor    %ebx,%ebx
    455a:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    455e:	48 8b 06             	mov    (%rsi),%rax
    4561:	8b 10                	mov    (%rax),%edx
    4563:	85 d2                	test   %edx,%edx
    4565:	7e 2a                	jle    4591 <external_thread+0x81>
    4567:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    456b:	48 89 dd             	mov    %rbx,%rbp
    456e:	48 c1 e5 08          	shl    $0x8,%rbp
    4572:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    4576:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    457d:	45 85 c0             	test   %r8d,%r8d
    4580:	74 36                	je     45b8 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4582:	48 83 c3 01          	add    $0x1,%rbx
    4586:	39 da                	cmp    %ebx,%edx
    4588:	7f e1                	jg     456b <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    458a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4591:	49 83 c4 01          	add    $0x1,%r12
    4595:	44 39 e1             	cmp    %r12d,%ecx
    4598:	7f b6                	jg     4550 <external_thread+0x40>
  while (data->running == 1) {
    459a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    459f:	74 9f                	je     4540 <external_thread+0x30>
}
    45a1:	48 83 c4 08          	add    $0x8,%rsp
    45a5:	31 c0                	xor    %eax,%eax
    45a7:	5b                   	pop    %rbx
    45a8:	5d                   	pop    %rbp
    45a9:	41 5c                	pop    %r12
    45ab:	41 5d                	pop    %r13
    45ad:	41 5e                	pop    %r14
    45af:	41 5f                	pop    %r15
    45b1:	c3                   	ret
  while (data->running == 1) {
    45b2:	eb fe                	jmp    45b2 <external_thread+0xa2>
    45b4:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    45b8:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    45bb:	48 8b 06             	mov    (%rsi),%rax
    45be:	48 8b 78 08          	mov    0x8(%rax),%rdi
    45c2:	48 01 ef             	add    %rbp,%rdi
    45c5:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    45cc:	48 c1 e6 05          	shl    $0x5,%rsi
    45d0:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    45d7:	bf 04 00 00 00       	mov    $0x4,%edi
    45dc:	e8 8f dd ff ff       	call   2370 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    45e1:	49 8b 47 50          	mov    0x50(%r15),%rax
    45e5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    45e9:	48 8b 40 08          	mov    0x8(%rax),%rax
    45ed:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    45f8:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    45fb:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    45ff:	48 83 c3 01          	add    $0x1,%rbx
    4603:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4607:	48 8b 06             	mov    (%rsi),%rax
    460a:	8b 10                	mov    (%rax),%edx
    460c:	39 da                	cmp    %ebx,%edx
    460e:	0f 8f 53 ff ff ff    	jg     4567 <external_thread+0x57>
    4614:	e9 71 ff ff ff       	jmp    458a <external_thread+0x7a>
}
    4619:	31 c0                	xor    %eax,%eax
    461b:	c3                   	ret
    461c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004620 <timer_thread>:
void* timer_thread(void *arg) {
    4620:	f3 0f 1e fa          	endbr64
    4624:	41 57                	push   %r15
    4626:	48 8d 35 e3 39 00 00 	lea    0x39e3(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    462d:	41 56                	push   %r14
    462f:	41 55                	push   %r13
    4631:	41 54                	push   %r12
    4633:	55                   	push   %rbp
    4634:	53                   	push   %rbx
    4635:	48 89 fb             	mov    %rdi,%rbx
    4638:	48 83 ec 68          	sub    $0x68,%rsp
    463c:	8b 57 04             	mov    0x4(%rdi),%edx
    463f:	bf 01 00 00 00       	mov    $0x1,%edi
    4644:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    464d:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    4652:	31 c0                	xor    %eax,%eax
    4654:	e8 87 de ff ff       	call   24e0 <__printf_chk@plt>
  struct timespec preempt = {
    4659:	66 0f 6f 05 3f 45 00 00 	movdqa 0x453f(%rip),%xmm0        # 8ba0 <_IO_stdin_used+0xba0>
    4661:	ba 88 13 00 00       	mov    $0x1388,%edx
    4666:	31 c0                	xor    %eax,%eax
    4668:	48 8d 35 b3 39 00 00 	lea    0x39b3(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    466f:	bf 01 00 00 00       	mov    $0x1,%edi
    4674:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    4679:	e8 62 de ff ff       	call   24e0 <__printf_chk@plt>
  while (data->running && n < times) {
    467e:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4681:	85 ed                	test   %ebp,%ebp
    4683:	0f 84 9b 00 00 00    	je     4724 <timer_thread+0x104>
  int n = 0;
    4689:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    468c:	31 ed                	xor    %ebp,%ebp
    468e:	4c 8d 74 24 10       	lea    0x10(%rsp),%r14
    y++;
    4693:	45 31 e4             	xor    %r12d,%r12d
    4696:	4c 8d 6c 24 20       	lea    0x20(%rsp),%r13
    nanosleep(&preempt , &rem2);
    469b:	4c 89 ef             	mov    %r13,%rdi
    469e:	4c 89 f6             	mov    %r14,%rsi
    n++;
    46a1:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    46a5:	e8 16 dd ff ff       	call   23c0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46aa:	48 63 43 30          	movslq 0x30(%rbx),%rax
    y++;
    46ae:	8d 7d 01             	lea    0x1(%rbp),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46b1:	85 c0                	test   %eax,%eax
    46b3:	7e 48                	jle    46fd <timer_thread+0xdd>
    46b5:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    46b9:	4c 63 c5             	movslq %ebp,%r8
    46bc:	49 c1 e0 09          	shl    $0x9,%r8
    46c0:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    46c4:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    46c8:	4c 8b 19             	mov    (%rcx),%r11
    46cb:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46cd:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    46d1:	99                   	cltd
    46d2:	41 f7 7b 40          	idivl  0x40(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    46d6:	49 8b 73 38          	mov    0x38(%r11),%rsi
    46da:	48 63 d2             	movslq %edx,%rdx
    46dd:	48 c1 e2 09          	shl    $0x9,%rdx
    46e1:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    46ec:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    46f8:	49 39 c9             	cmp    %rcx,%r9
    46fb:	75 cb                	jne    46c8 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    46fd:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4700:	48 8b 43 18          	mov    0x18(%rbx),%rax
  while (data->running && n < times) {
    4704:	8b 4b 44             	mov    0x44(%rbx),%ecx
    if (y >= data->threads[0]->task_count) {
    4707:	48 8b 00             	mov    (%rax),%rax
    y++;
    470a:	39 78 40             	cmp    %edi,0x40(%rax)
    470d:	41 0f 4e fc          	cmovle %r12d,%edi
    4711:	89 fd                	mov    %edi,%ebp
  while (data->running && n < times) {
    4713:	85 c9                	test   %ecx,%ecx
    4715:	74 0d                	je     4724 <timer_thread+0x104>
    4717:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    471e:	0f 85 77 ff ff ff    	jne    469b <timer_thread+0x7b>
    4724:	48 8d 3d 0d 39 00 00 	lea    0x390d(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    472b:	e8 20 dc ff ff       	call   2350 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    4730:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    4734:	85 d2                	test   %edx,%edx
    4736:	7e 6d                	jle    47a5 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    4738:	48 63 43 40          	movslq 0x40(%rbx),%rax
    473c:	85 c0                	test   %eax,%eax
    473e:	7e 65                	jle    47a5 <timer_thread+0x185>
    4740:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    4744:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    4748:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4750:	31 c9                	xor    %ecx,%ecx
    4752:	48 89 c6             	mov    %rax,%rsi
    4755:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4759:	48 8b 40 38          	mov    0x38(%rax),%rax
    475d:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    4761:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4767:	74 17                	je     4780 <timer_thread+0x160>
    4769:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4773:	48 05 00 02 00 00    	add    $0x200,%rax
    4779:	48 39 c2             	cmp    %rax,%rdx
    477c:	74 1e                	je     479c <timer_thread+0x17c>
    477e:	66 90                	xchg   %ax,%ax
      data->threads[x]->tasks[y].sending = 0;
    4780:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    478a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4790:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4797:	48 39 c2             	cmp    %rax,%rdx
    479a:	75 e4                	jne    4780 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    479c:	48 83 c1 08          	add    $0x8,%rcx
    47a0:	48 39 cf             	cmp    %rcx,%rdi
    47a3:	75 b0                	jne    4755 <timer_thread+0x135>
  asm volatile ("mfence" ::: "memory");
    47a5:	0f ae f0             	mfence
  struct timespec drain = {
    47a8:	66 0f 6f 05 00 44 00 00 	movdqa 0x4400(%rip),%xmm0        # 8bb0 <_IO_stdin_used+0xbb0>
    47b0:	4c 8d 3d a6 38 00 00 	lea    0x38a6(%rip),%r15        # 805d <_IO_stdin_used+0x5d>
    47b7:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    47bc:	48 63 43 28          	movslq 0x28(%rbx),%rax
    y++;
    47c0:	8d 7d 01             	lea    0x1(%rbp),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    47c3:	85 c0                	test   %eax,%eax
    47c5:	7e 4e                	jle    4815 <timer_thread+0x1f5>
    47c7:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    47cb:	4c 63 c5             	movslq %ebp,%r8
    47ce:	49 c1 e0 09          	shl    $0x9,%r8
    47d2:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    47d6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    47e0:	4c 8b 11             	mov    (%rcx),%r10
    47e3:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    47e5:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    47e9:	99                   	cltd
    47ea:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    47ee:	49 8b 72 38          	mov    0x38(%r10),%rsi
    47f2:	48 63 d2             	movslq %edx,%rdx
    47f5:	48 c1 e2 09          	shl    $0x9,%rdx
    47f9:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4804:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4810:	4c 39 c9             	cmp    %r9,%rcx
    4813:	75 cb                	jne    47e0 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    4815:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4818:	48 8b 43 18          	mov    0x18(%rbx),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    481c:	44 8b 53 30          	mov    0x30(%rbx),%r10d
    if (y >= data->threads[0]->task_count) {
    4820:	48 8b 00             	mov    (%rax),%rax
    y++;
    4823:	39 78 40             	cmp    %edi,0x40(%rax)
    4826:	b8 00 00 00 00       	mov    $0x0,%eax
    482b:	0f 4f c7             	cmovg  %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    482e:	45 85 d2             	test   %r10d,%r10d
    4831:	0f 8e 45 01 00 00    	jle    497c <timer_thread+0x35c>
    int all_empty = 1;
    4837:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    483b:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    483e:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    4844:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int y = 0 ; y < 2 ; y++) {
    4848:	45 31 ed             	xor    %r13d,%r13d
    484b:	44 89 f5             	mov    %r14d,%ebp
    484e:	4e 8d 24 f5 00 00 00 00 	lea    0x0(,%r14,8),%r12
    4856:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4859:	45 85 d2             	test   %r10d,%r10d
    485c:	0f 8e bd 00 00 00    	jle    491f <timer_thread+0x2ff>
    4862:	44 89 5c 24 08       	mov    %r11d,0x8(%rsp)
    4867:	4d 89 eb             	mov    %r13,%r11
      y = 0;
    486a:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    486c:	45 31 c0             	xor    %r8d,%r8d
    486f:	49 c1 e3 09          	shl    $0x9,%r11
    4873:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (x == k) { continue; }
    4878:	45 39 f0             	cmp    %r14d,%r8d
    487b:	74 36                	je     48b3 <timer_thread+0x293>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    487d:	48 8b 53 18          	mov    0x18(%rbx),%rdx
    4881:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    4885:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4889:	4a 8b 8c 1a 70 01 00 00 	mov    0x170(%rdx,%r11,1),%rcx
    4891:	48 01 c1             	add    %rax,%rcx
    4894:	48 8b 11             	mov    (%rcx),%rdx
    4897:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    489b:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    48a2:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    48a9:	4d 85 c9             	test   %r9,%r9
    48ac:	7f 2a                	jg     48d8 <timer_thread+0x2b8>
    48ae:	48 85 f6             	test   %rsi,%rsi
    48b1:	7f 25                	jg     48d8 <timer_thread+0x2b8>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    48b3:	41 83 c0 01          	add    $0x1,%r8d
    48b7:	48 83 c0 38          	add    $0x38,%rax
    48bb:	45 39 d0             	cmp    %r10d,%r8d
    48be:	75 b8                	jne    4878 <timer_thread+0x258>
      for (int y = 0 ; y < 2 ; y++) {
    48c0:	49 83 fd 01          	cmp    $0x1,%r13
    48c4:	0f 84 9e 00 00 00    	je     4968 <timer_thread+0x348>
    48ca:	49 83 c5 01          	add    $0x1,%r13
    48ce:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    48d1:	eb 94                	jmp    4867 <timer_thread+0x247>
    48d3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    48d8:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    48de:	48 83 ec 08          	sub    $0x8,%rsp
    48e2:	89 f9                	mov    %edi,%ecx
    48e4:	bf 01 00 00 00       	mov    $0x1,%edi
    48e9:	50                   	push   %rax
    48ea:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    48f0:	89 ea                	mov    %ebp,%edx
    48f2:	50                   	push   %rax
    48f3:	31 c0                	xor    %eax,%eax
    48f5:	56                   	push   %rsi
    48f6:	4c 89 fe             	mov    %r15,%rsi
    48f9:	e8 e2 db ff ff       	call   24e0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48fe:	44 8b 53 30          	mov    0x30(%rbx),%r10d
      for (int y = 0 ; y < 2 ; y++) {
    4902:	48 83 c4 20          	add    $0x20,%rsp
    4906:	49 83 fd 01          	cmp    $0x1,%r13
    490a:	74 44                	je     4950 <timer_thread+0x330>
    490c:	49 83 c5 01          	add    $0x1,%r13
    4910:	45 31 db             	xor    %r11d,%r11d
    4913:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4916:	45 85 d2             	test   %r10d,%r10d
    4919:	0f 8f 43 ff ff ff    	jg     4862 <timer_thread+0x242>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    491f:	49 83 c6 01          	add    $0x1,%r14
    4923:	45 39 f2             	cmp    %r14d,%r10d
    4926:	0f 8f 1c ff ff ff    	jg     4848 <timer_thread+0x228>
    492c:	8b 6c 24 0c          	mov    0xc(%rsp),%ebp
    if (all_empty == 1) {
    4930:	41 83 fb 01          	cmp    $0x1,%r11d
    4934:	74 46                	je     497c <timer_thread+0x35c>
      nanosleep(&drain , &drainrem);
    4936:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    493b:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    4940:	e8 7b da ff ff       	call   23c0 <nanosleep@plt>
    4945:	e9 72 fe ff ff       	jmp    47bc <timer_thread+0x19c>
    494a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4950:	49 83 c6 01          	add    $0x1,%r14
    4954:	45 31 db             	xor    %r11d,%r11d
    4957:	45 39 f2             	cmp    %r14d,%r10d
    495a:	0f 8f e8 fe ff ff    	jg     4848 <timer_thread+0x228>
    4960:	eb ca                	jmp    492c <timer_thread+0x30c>
    4962:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4968:	49 83 c6 01          	add    $0x1,%r14
    496c:	44 8b 5c 24 08       	mov    0x8(%rsp),%r11d
    4971:	45 39 f2             	cmp    %r14d,%r10d
    4974:	0f 8f ce fe ff ff    	jg     4848 <timer_thread+0x228>
    497a:	eb b0                	jmp    492c <timer_thread+0x30c>
    497c:	48 8d 3d d1 36 00 00 	lea    0x36d1(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4983:	e8 c8 d9 ff ff       	call   2350 <puts@plt>
  while (data->running) {
    4988:	8b 53 44             	mov    0x44(%rbx),%edx
    498b:	85 d2                	test   %edx,%edx
    498d:	0f 84 eb 00 00 00    	je     4a7e <timer_thread+0x45e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4993:	8b 43 2c             	mov    0x2c(%rbx),%eax
    4996:	31 ed                	xor    %ebp,%ebp
    4998:	4c 8d 25 db 36 00 00 	lea    0x36db(%rip),%r12        # 807a <_IO_stdin_used+0x7a>
    499f:	4c 8d 2d ef 36 00 00 	lea    0x36ef(%rip),%r13        # 8095 <_IO_stdin_used+0x95>
    49a6:	85 c0                	test   %eax,%eax
    49a8:	7e 39                	jle    49e3 <timer_thread+0x3c3>
    49aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    49b0:	31 c0                	xor    %eax,%eax
    49b2:	89 ea                	mov    %ebp,%edx
    49b4:	4c 89 e6             	mov    %r12,%rsi
    49b7:	bf 01 00 00 00       	mov    $0x1,%edi
    49bc:	e8 1f db ff ff       	call   24e0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    49c1:	48 8b 43 18          	mov    0x18(%rbx),%rax
    49c5:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
      if (data->threads[x]->type == IO) {
    49c9:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    49cd:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    49d4:	0f 84 d1 00 00 00    	je     4aab <timer_thread+0x48b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    49da:	48 83 c5 01          	add    $0x1,%rbp
    49de:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
    49e1:	7f cd                	jg     49b0 <timer_thread+0x390>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    49e3:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    49e7:	85 d2                	test   %edx,%edx
    49e9:	7e 7d                	jle    4a68 <timer_thread+0x448>
      for (int y = 0 ; y < data->task_count ; y++) {
    49eb:	8b 43 40             	mov    0x40(%rbx),%eax
    49ee:	85 c0                	test   %eax,%eax
    49f0:	7e 76                	jle    4a68 <timer_thread+0x448>
    49f2:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    49f5:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    49f9:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4a01:	31 c9                	xor    %ecx,%ecx
    4a03:	48 c1 e6 09          	shl    $0x9,%rsi
    4a07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4a10:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4a14:	48 8b 40 38          	mov    0x38(%rax),%rax
    4a18:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    4a1c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    4a22:	74 1c                	je     4a40 <timer_thread+0x420>
    4a24:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4a2e:	48 05 00 02 00 00    	add    $0x200,%rax
    4a34:	48 39 d0             	cmp    %rdx,%rax
    4a37:	74 26                	je     4a5f <timer_thread+0x43f>
    4a39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    4a40:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4a4a:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    4a50:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    4a5a:	48 39 d0             	cmp    %rdx,%rax
    4a5d:	75 e1                	jne    4a40 <timer_thread+0x420>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4a5f:	48 83 c1 08          	add    $0x8,%rcx
    4a63:	48 39 f9             	cmp    %rdi,%rcx
    4a66:	75 a8                	jne    4a10 <timer_thread+0x3f0>
    asm volatile ("mfence" ::: "memory");
    4a68:	0f ae f0             	mfence
    4a6b:	48 8d 3d 35 36 00 00 	lea    0x3635(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    4a72:	e8 d9 d8 ff ff       	call   2350 <puts@plt>
    data->running = 0;
    4a77:	c7 43 44 00 00 00 00 	movl   $0x0,0x44(%rbx)
    4a7e:	48 8d 3d 29 36 00 00 	lea    0x3629(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4a85:	e8 c6 d8 ff ff       	call   2350 <puts@plt>
}
    4a8a:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    4a8f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4a98:	75 40                	jne    4ada <timer_thread+0x4ba>
    4a9a:	48 83 c4 68          	add    $0x68,%rsp
    4a9e:	31 c0                	xor    %eax,%eax
    4aa0:	5b                   	pop    %rbx
    4aa1:	5d                   	pop    %rbp
    4aa2:	41 5c                	pop    %r12
    4aa4:	41 5d                	pop    %r13
    4aa6:	41 5e                	pop    %r14
    4aa8:	41 5f                	pop    %r15
    4aaa:	c3                   	ret
    4aab:	4c 89 ef             	mov    %r13,%rdi
    4aae:	e8 9d d8 ff ff       	call   2350 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4ab3:	48 8b 43 18          	mov    0x18(%rbx),%rax
    4ab7:	be 01 00 00 00       	mov    $0x1,%esi
    4abc:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4ac0:	48 83 c5 01          	add    $0x1,%rbp
        eventfd_write(data->threads[x]->_eventfd, 1);
    4ac4:	8b 78 60             	mov    0x60(%rax),%edi
    4ac7:	e8 b4 d9 ff ff       	call   2480 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4acc:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
    4acf:	0f 8f db fe ff ff    	jg     49b0 <timer_thread+0x390>
    4ad5:	e9 09 ff ff ff       	jmp    49e3 <timer_thread+0x3c3>
}
    4ada:	e8 c1 d8 ff ff       	call   23a0 <__stack_chk_fail@plt>
    4adf:	90                   	nop

0000000000004ae0 <minf>:
int minf(int a, int b) {
    4ae0:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    4ae4:	39 f7                	cmp    %esi,%edi
    4ae6:	89 f0                	mov    %esi,%eax
    4ae8:	0f 4e c7             	cmovle %edi,%eax
}
    4aeb:	c3                   	ret
    4aec:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004af0 <maxf>:
int maxf(int a, int b) {
    4af0:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    4af4:	39 f7                	cmp    %esi,%edi
    4af6:	89 f0                	mov    %esi,%eax
    4af8:	0f 4d c7             	cmovge %edi,%eax
}
    4afb:	c3                   	ret
    4afc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b00 <strtolower>:
void strtolower(char *str) {
    4b00:	f3 0f 1e fa          	endbr64
    4b04:	55                   	push   %rbp
    4b05:	53                   	push   %rbx
    4b06:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    4b0a:	48 0f be 1f          	movsbq (%rdi),%rbx
    4b0e:	84 db                	test   %bl,%bl
    4b10:	74 24                	je     4b36 <strtolower+0x36>
    4b12:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4b15:	e8 b6 da ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    4b1a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4b20:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4b23:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4b27:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4b2a:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    4b2d:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4b32:	84 db                	test   %bl,%bl
    4b34:	75 ea                	jne    4b20 <strtolower+0x20>
}
    4b36:	48 83 c4 08          	add    $0x8,%rsp
    4b3a:	5b                   	pop    %rbx
    4b3b:	5d                   	pop    %rbp
    4b3c:	c3                   	ret
    4b3d:	0f 1f 00             	nopl   (%rax)

0000000000004b40 <zh_malloc>:
void *zh_malloc(size_t size) {
    4b40:	f3 0f 1e fa          	endbr64
    4b44:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4b48:	e8 53 d9 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4b4d:	48 85 c0             	test   %rax,%rax
    4b50:	74 05                	je     4b57 <zh_malloc+0x17>
}
    4b52:	48 83 c4 08          	add    $0x8,%rsp
    4b56:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4b57:	48 8b 0d c2 64 00 00 	mov    0x64c2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4b5e:	ba 28 00 00 00       	mov    $0x28,%edx
    4b63:	be 01 00 00 00       	mov    $0x1,%esi
    4b68:	48 8d 3d 51 3a 00 00 	lea    0x3a51(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    4b6f:	e8 ec d9 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    4b74:	bf 01 00 00 00       	mov    $0x1,%edi
    4b79:	e8 c2 d9 ff ff       	call   2540 <exit@plt>
    4b7e:	66 90                	xchg   %ax,%ax

0000000000004b80 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4b80:	f3 0f 1e fa          	endbr64
    4b84:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4b85:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4b8a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4b8d:	e8 3e d8 ff ff       	call   23d0 <strrchr@plt>
    if (!dot || dot == filename)
    4b92:	48 85 c0             	test   %rax,%rax
    4b95:	74 11                	je     4ba8 <get_filename_ext+0x28>
    4b97:	48 39 c3             	cmp    %rax,%rbx
    4b9a:	74 0c                	je     4ba8 <get_filename_ext+0x28>
    return dot + 1;
    4b9c:	48 83 c0 01          	add    $0x1,%rax
}
    4ba0:	5b                   	pop    %rbx
    4ba1:	c3                   	ret
    4ba2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4ba8:	48 8d 05 47 35 00 00 	lea    0x3547(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4baf:	5b                   	pop    %rbx
    4bb0:	c3                   	ret
    4bb1:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4bbc:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004bc0 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4bc0:	f3 0f 1e fa          	endbr64
    4bc4:	41 55                	push   %r13
    4bc6:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4bc9:	48 89 fe             	mov    %rdi,%rsi
    4bcc:	41 54                	push   %r12
    4bce:	55                   	push   %rbp
    4bcf:	48 89 d5             	mov    %rdx,%rbp
    4bd2:	ba 00 04 00 00       	mov    $0x400,%edx
    4bd7:	53                   	push   %rbx
    4bd8:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4bdf:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4be8:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4bf0:	31 c0                	xor    %eax,%eax
    4bf2:	49 89 e4             	mov    %rsp,%r12
    4bf5:	4c 89 e7             	mov    %r12,%rdi
    4bf8:	e8 c3 d8 ff ff       	call   24c0 <__strcpy_chk@plt>
    for (; *str; ++str)
    4bfd:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4c02:	84 db                	test   %bl,%bl
    4c04:	74 24                	je     4c2a <send_headers+0x6a>
        *str = (char)tolower(*str);
    4c06:	e8 c5 d9 ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    4c0b:	48 8b 08             	mov    (%rax),%rcx
    4c0e:	4c 89 e0             	mov    %r12,%rax
    4c11:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4c18:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4c1b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4c1f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4c22:	48 0f be 18          	movsbq (%rax),%rbx
    4c26:	84 db                	test   %bl,%bl
    4c28:	75 ee                	jne    4c18 <send_headers+0x58>
    void *buf = malloc(size);
    4c2a:	bf 11 00 00 00       	mov    $0x11,%edi
    4c2f:	e8 6c d8 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4c34:	48 85 c0             	test   %rax,%rax
    4c37:	0f 84 7e 04 00 00    	je     50bb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4c3d:	66 0f 6f 05 7b 3f 00 00 	movdqa 0x3f7b(%rip),%xmm0        # 8bc0 <_IO_stdin_used+0xbc0>
    iov[0].iov_base = zh_malloc(slen);
    4c45:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4c49:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4c4e:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4c56:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4c5a:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4c5d:	e8 3e d8 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4c62:	48 85 c0             	test   %rax,%rax
    4c65:	0f 84 50 04 00 00    	je     50bb <send_headers+0x4fb>
    4c6b:	66 0f 6f 05 5d 3f 00 00 	movdqa 0x3f5d(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    iov[1].iov_base = zh_malloc(slen);
    4c73:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4c77:	4c 89 e7             	mov    %r12,%rdi
    4c7a:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4c84:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4c8c:	0f 11 00             	movups %xmm0,(%rax)
    4c8f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4c93:	be 2e 00 00 00       	mov    $0x2e,%esi
    4c98:	e8 33 d7 ff ff       	call   23d0 <strrchr@plt>
    if (!dot || dot == filename)
    4c9d:	48 85 c0             	test   %rax,%rax
    4ca0:	0f 84 ea 02 00 00    	je     4f90 <send_headers+0x3d0>
    4ca6:	4c 39 e0             	cmp    %r12,%rax
    4ca9:	0f 84 e1 02 00 00    	je     4f90 <send_headers+0x3d0>
    return dot + 1;
    4caf:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4cb3:	48 8d 3d 0a 34 00 00 	lea    0x340a(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4cba:	48 89 de             	mov    %rbx,%rsi
    4cbd:	e8 6e d7 ff ff       	call   2430 <strcmp@plt>
    4cc2:	85 c0                	test   %eax,%eax
    4cc4:	75 20                	jne    4ce6 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4cc6:	66 0f 6f 05 12 3f 00 00 	movdqa 0x3f12(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4cce:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4cd6:	66 0f 6f 05 12 3f 00 00 	movdqa 0x3f12(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4cde:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4ce6:	48 89 de             	mov    %rbx,%rsi
    4ce9:	48 8d 3d d8 33 00 00 	lea    0x33d8(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4cf0:	e8 3b d7 ff ff       	call   2430 <strcmp@plt>
    4cf5:	85 c0                	test   %eax,%eax
    4cf7:	75 20                	jne    4d19 <send_headers+0x159>
    4cf9:	66 0f 6f 05 df 3e 00 00 	movdqa 0x3edf(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4d01:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4d09:	66 0f 6f 05 df 3e 00 00 	movdqa 0x3edf(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4d11:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4d19:	48 89 de             	mov    %rbx,%rsi
    4d1c:	48 8d 3d aa 33 00 00 	lea    0x33aa(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4d23:	e8 08 d7 ff ff       	call   2430 <strcmp@plt>
    4d28:	85 c0                	test   %eax,%eax
    4d2a:	0f 84 10 02 00 00    	je     4f40 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4d30:	48 89 de             	mov    %rbx,%rsi
    4d33:	48 8d 3d 97 33 00 00 	lea    0x3397(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4d3a:	e8 f1 d6 ff ff       	call   2430 <strcmp@plt>
    4d3f:	85 c0                	test   %eax,%eax
    4d41:	0f 84 a9 02 00 00    	je     4ff0 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4d47:	48 89 de             	mov    %rbx,%rsi
    4d4a:	48 8d 3d 84 33 00 00 	lea    0x3384(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4d51:	e8 da d6 ff ff       	call   2430 <strcmp@plt>
    4d56:	85 c0                	test   %eax,%eax
    4d58:	0f 84 6a 02 00 00    	je     4fc8 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4d5e:	48 89 de             	mov    %rbx,%rsi
    4d61:	48 8d 3d b0 33 00 00 	lea    0x33b0(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4d68:	e8 c3 d6 ff ff       	call   2430 <strcmp@plt>
    4d6d:	85 c0                	test   %eax,%eax
    4d6f:	0f 84 2b 02 00 00    	je     4fa0 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4d75:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4d78:	0f 84 52 01 00 00    	je     4ed0 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4d7e:	48 89 de             	mov    %rbx,%rsi
    4d81:	48 8d 3d 51 33 00 00 	lea    0x3351(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4d88:	e8 a3 d6 ff ff       	call   2430 <strcmp@plt>
    4d8d:	85 c0                	test   %eax,%eax
    4d8f:	0f 84 ab 02 00 00    	je     5040 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4d95:	48 89 de             	mov    %rbx,%rsi
    4d98:	48 8d 3d 3e 33 00 00 	lea    0x333e(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4d9f:	e8 8c d6 ff ff       	call   2430 <strcmp@plt>
    4da4:	85 c0                	test   %eax,%eax
    4da6:	0f 84 6c 02 00 00    	je     5018 <send_headers+0x458>
    slen = strlen(send_buffer);
    4dac:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4db4:	4c 89 e7             	mov    %r12,%rdi
    4db7:	e8 d4 d5 ff ff       	call   2390 <strlen@plt>
    void *buf = malloc(size);
    4dbc:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4dbf:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4dc2:	e8 d9 d6 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4dc7:	48 85 c0             	test   %rax,%rax
    4dca:	0f 84 eb 02 00 00    	je     50bb <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4dd0:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4dd4:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4dd8:	83 fb 08             	cmp    $0x8,%ebx
    4ddb:	0f 83 3f 01 00 00    	jae    4f20 <send_headers+0x360>
    4de1:	f6 c3 04             	test   $0x4,%bl
    4de4:	0f 85 7b 02 00 00    	jne    5065 <send_headers+0x4a5>
    4dea:	85 db                	test   %ebx,%ebx
    4dec:	74 13                	je     4e01 <send_headers+0x241>
    4dee:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4df6:	88 10                	mov    %dl,(%rax)
    4df8:	f6 c3 02             	test   $0x2,%bl
    4dfb:	0f 85 96 02 00 00    	jne    5097 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4e01:	4d 89 e8             	mov    %r13,%r8
    4e04:	48 8d 0d d6 32 00 00 	lea    0x32d6(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4e0b:	4c 89 e7             	mov    %r12,%rdi
    4e0e:	31 c0                	xor    %eax,%eax
    4e10:	ba 00 04 00 00       	mov    $0x400,%edx
    4e15:	be 01 00 00 00       	mov    $0x1,%esi
    4e1a:	e8 c1 d7 ff ff       	call   25e0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4e1f:	4c 89 e7             	mov    %r12,%rdi
    4e22:	e8 69 d5 ff ff       	call   2390 <strlen@plt>
    void *buf = malloc(size);
    4e27:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4e2a:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4e2d:	e8 6e d6 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4e32:	48 85 c0             	test   %rax,%rax
    4e35:	0f 84 80 02 00 00    	je     50bb <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4e3b:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4e3f:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4e43:	83 fb 08             	cmp    $0x8,%ebx
    4e46:	0f 83 1c 01 00 00    	jae    4f68 <send_headers+0x3a8>
    4e4c:	f6 c3 04             	test   $0x4,%bl
    4e4f:	0f 85 29 02 00 00    	jne    507e <send_headers+0x4be>
    4e55:	85 db                	test   %ebx,%ebx
    4e57:	74 13                	je     4e6c <send_headers+0x2ac>
    4e59:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4e61:	88 10                	mov    %dl,(%rax)
    4e63:	f6 c3 02             	test   $0x2,%bl
    4e66:	0f 85 3d 02 00 00    	jne    50a9 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4e6c:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4e71:	bf 02 00 00 00       	mov    $0x2,%edi
    4e76:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4e7e:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4e86:	e8 15 d6 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4e8b:	48 85 c0             	test   %rax,%rax
    4e8e:	0f 84 27 02 00 00    	je     50bb <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4e94:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4e9c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4ea0:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4ea8:	66 89 10             	mov    %dx,(%rax)
}
    4eab:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4eb3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4ebc:	0f 85 20 02 00 00    	jne    50e2 <send_headers+0x522>
    4ec2:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4ec9:	5b                   	pop    %rbx
    4eca:	5d                   	pop    %rbp
    4ecb:	41 5c                	pop    %r12
    4ecd:	41 5d                	pop    %r13
    4ecf:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4ed0:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4ed4:	0f 85 a4 fe ff ff    	jne    4d7e <send_headers+0x1be>
    4eda:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4ede:	0f 85 9a fe ff ff    	jne    4d7e <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ee4:	66 0f 6f 05 54 3d 00 00 	movdqa 0x3d54(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4eec:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4ef6:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4efe:	66 0f 6f 05 4a 3d 00 00 	movdqa 0x3d4a(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4f06:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4f0e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4f16:	e9 63 fe ff ff       	jmp    4d7e <send_headers+0x1be>
    4f1b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f20:	89 da                	mov    %ebx,%edx
    4f22:	48 89 c7             	mov    %rax,%rdi
    4f25:	4c 89 e6             	mov    %r12,%rsi
    4f28:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4f2d:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4f32:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4f35:	c1 e9 03             	shr    $0x3,%ecx
    4f38:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4f3b:	e9 c1 fe ff ff       	jmp    4e01 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f40:	66 0f 6f 05 98 3c 00 00 	movdqa 0x3c98(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4f48:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f50:	66 0f 6f 05 a8 3c 00 00 	movdqa 0x3ca8(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4f58:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4f60:	e9 cb fd ff ff       	jmp    4d30 <send_headers+0x170>
    4f65:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4f68:	89 da                	mov    %ebx,%edx
    4f6a:	48 89 c7             	mov    %rax,%rdi
    4f6d:	4c 89 e6             	mov    %r12,%rsi
    4f70:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4f75:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4f7a:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4f7d:	c1 e9 03             	shr    $0x3,%ecx
    4f80:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4f83:	e9 e4 fe ff ff       	jmp    4e6c <send_headers+0x2ac>
    4f88:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4f90:	48 8d 1d 5f 31 00 00 	lea    0x315f(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    4f97:	e9 94 fd ff ff       	jmp    4d30 <send_headers+0x170>
    4f9c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4fa0:	66 0f 6f 05 78 3c 00 00 	movdqa 0x3c78(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4fa8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fb0:	66 0f 6f 05 78 3c 00 00 	movdqa 0x3c78(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4fb8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4fc0:	e9 b0 fd ff ff       	jmp    4d75 <send_headers+0x1b5>
    4fc5:	0f 1f 00             	nopl   (%rax)
    4fc8:	66 0f 6f 05 50 3c 00 00 	movdqa 0x3c50(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4fd0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fd8:	66 0f 6f 05 50 3c 00 00 	movdqa 0x3c50(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4fe0:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4fe8:	e9 71 fd ff ff       	jmp    4d5e <send_headers+0x19e>
    4fed:	0f 1f 00             	nopl   (%rax)
    4ff0:	66 0f 6f 05 e8 3b 00 00 	movdqa 0x3be8(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4ff8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5000:	66 0f 6f 05 08 3c 00 00 	movdqa 0x3c08(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    5008:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    5010:	e9 32 fd ff ff       	jmp    4d47 <send_headers+0x187>
    5015:	0f 1f 00             	nopl   (%rax)
    5018:	66 0f 6f 05 00 3c 00 00 	movdqa 0x3c00(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    5020:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5028:	66 0f 6f 05 40 3c 00 00 	movdqa 0x3c40(%rip),%xmm0        # 8c70 <_IO_stdin_used+0xc70>
    5030:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    5038:	e9 6f fd ff ff       	jmp    4dac <send_headers+0x1ec>
    503d:	0f 1f 00             	nopl   (%rax)
    5040:	66 0f 6f 05 d8 3b 00 00 	movdqa 0x3bd8(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    5048:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    5050:	66 0f 6f 05 08 3c 00 00 	movdqa 0x3c08(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    5058:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    5060:	e9 30 fd ff ff       	jmp    4d95 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    5065:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    506c:	89 db                	mov    %ebx,%ebx
    506e:	89 10                	mov    %edx,(%rax)
    5070:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    5075:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5079:	e9 83 fd ff ff       	jmp    4e01 <send_headers+0x241>
    507e:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5085:	89 db                	mov    %ebx,%ebx
    5087:	89 10                	mov    %edx,(%rax)
    5089:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    508e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5092:	e9 d5 fd ff ff       	jmp    4e6c <send_headers+0x2ac>
    5097:	89 db                	mov    %ebx,%ebx
    5099:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    509f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    50a4:	e9 58 fd ff ff       	jmp    4e01 <send_headers+0x241>
    50a9:	89 db                	mov    %ebx,%ebx
    50ab:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    50b1:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    50b6:	e9 b1 fd ff ff       	jmp    4e6c <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    50bb:	48 8b 0d 5e 5f 00 00 	mov    0x5f5e(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    50c2:	ba 28 00 00 00       	mov    $0x28,%edx
    50c7:	be 01 00 00 00       	mov    $0x1,%esi
    50cc:	48 8d 3d ed 34 00 00 	lea    0x34ed(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    50d3:	e8 88 d4 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    50d8:	bf 01 00 00 00       	mov    $0x1,%edi
    50dd:	e8 5e d4 ff ff       	call   2540 <exit@plt>
}
    50e2:	e8 b9 d2 ff ff       	call   23a0 <__stack_chk_fail@plt>
    50e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000050f0 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    50f0:	f3 0f 1e fa          	endbr64
    50f4:	41 55                	push   %r13
    50f6:	49 89 d5             	mov    %rdx,%r13
    50f9:	41 54                	push   %r12
    50fb:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    50fe:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5101:	55                   	push   %rbp
    5102:	53                   	push   %rbx
    5103:	48 89 f3             	mov    %rsi,%rbx
    5106:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    510a:	e8 91 d3 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    510f:	48 85 c0             	test   %rax,%rax
    5112:	74 6b                	je     517f <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    5114:	4c 89 e7             	mov    %r12,%rdi
    5117:	48 89 c5             	mov    %rax,%rbp
    511a:	31 f6                	xor    %esi,%esi
    511c:	31 c0                	xor    %eax,%eax
    511e:	e8 ed d3 ff ff       	call   2510 <open@plt>
    5123:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    5126:	85 c0                	test   %eax,%eax
    5128:	0f 88 e8 d4 ff ff    	js     2616 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    512e:	48 89 da             	mov    %rbx,%rdx
    5131:	48 89 ee             	mov    %rbp,%rsi
    5134:	89 c7                	mov    %eax,%edi
    5136:	e8 d5 d2 ff ff       	call   2410 <read@plt>
    if (ret < file_size) {
    513b:	48 98                	cltq
    513d:	48 39 d8             	cmp    %rbx,%rax
    5140:	7c 1e                	jl     5160 <copy_file_contents+0x70>
    close(fd);
    5142:	44 89 e7             	mov    %r12d,%edi
    5145:	e8 a6 d2 ff ff       	call   23f0 <close@plt>
    iov->iov_base = buf;
    514a:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    514e:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    5152:	48 83 c4 08          	add    $0x8,%rsp
    5156:	5b                   	pop    %rbx
    5157:	5d                   	pop    %rbp
    5158:	41 5c                	pop    %r12
    515a:	41 5d                	pop    %r13
    515c:	c3                   	ret
    515d:	0f 1f 00             	nopl   (%rax)
    5160:	48 8b 0d b9 5e 00 00 	mov    0x5eb9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5167:	ba 1a 00 00 00       	mov    $0x1a,%edx
    516c:	be 01 00 00 00       	mov    $0x1,%esi
    5171:	48 8d 3d 7f 2f 00 00 	lea    0x2f7f(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    5178:	e8 e3 d3 ff ff       	call   2560 <fwrite@plt>
    517d:	eb c3                	jmp    5142 <copy_file_contents+0x52>
    517f:	48 8b 0d 9a 5e 00 00 	mov    0x5e9a(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5186:	ba 28 00 00 00       	mov    $0x28,%edx
    518b:	be 01 00 00 00       	mov    $0x1,%esi
    5190:	48 8d 3d 29 34 00 00 	lea    0x3429(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    5197:	e8 c4 d3 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    519c:	bf 01 00 00 00       	mov    $0x1,%edi
    51a1:	e8 9a d3 ff ff       	call   2540 <exit@plt>
    51a6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000051b0 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    51b0:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    51b4:	8b 46 44             	mov    0x44(%rsi),%eax
    51b7:	48 89 fa             	mov    %rdi,%rdx
    51ba:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    51bd:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    51c3:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    51c6:	48 8b 07             	mov    (%rdi),%rax
    51c9:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    51cc:	f6 c1 02             	test   $0x2,%cl
    51cf:	74 00                	je     51d1 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    51d1:	89 f0                	mov    %esi,%eax
    51d3:	44 29 c0             	sub    %r8d,%eax
    51d6:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    51d9:	0f 82 43 d4 ff ff    	jb     2622 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    51df:	c1 e9 0a             	shr    $0xa,%ecx
    51e2:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    51e6:	8b 47 44             	mov    0x44(%rdi),%eax
    51e9:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    51ec:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    51ef:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    51f2:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    51f5:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    51f9:	d3 e0                	shl    %cl,%eax
    51fb:	8b 4a 04             	mov    0x4(%rdx),%ecx
    51fe:	48 c1 e0 06          	shl    $0x6,%rax
    5202:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    5206:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    520c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    520f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    5213:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5219:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5221:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    5225:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    5228:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    522f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5237:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    523b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    523f:	e8 6c d1 ff ff       	call   23b0 <io_uring_submit@plt>
}
    5244:	31 c0                	xor    %eax,%eax
    5246:	48 83 c4 08          	add    $0x8,%rsp
    524a:	c3                   	ret
    524b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005250 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    5250:	f3 0f 1e fa          	endbr64
    5254:	41 55                	push   %r13
    5256:	41 89 fd             	mov    %edi,%r13d
    5259:	41 54                	push   %r12
    525b:	55                   	push   %rbp
    525c:	53                   	push   %rbx
    525d:	48 89 f3             	mov    %rsi,%rbx
    5260:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    5264:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5267:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    526d:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    5270:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5273:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5275:	f6 c1 02             	test   $0x2,%cl
    5278:	74 00                	je     527a <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    527a:	89 c2                	mov    %eax,%edx
    527c:	29 f2                	sub    %esi,%edx
    527e:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5281:	0f 82 ab d3 ff ff    	jb     2632 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5287:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    528a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    528d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5290:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    5295:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5298:	23 6b 58             	and    0x58(%rbx),%ebp
    529b:	d3 e5                	shl    %cl,%ebp
    529d:	48 c1 e5 06          	shl    $0x6,%rbp
    52a1:	48 03 6b 38          	add    0x38(%rbx),%rbp
    52a5:	e8 f6 d1 ff ff       	call   24a0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    52aa:	be 01 00 00 00       	mov    $0x1,%esi
    52af:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    52b4:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    52b7:	e8 64 d1 ff ff       	call   2420 <calloc@plt>
    req->client_socket = client_socket;
    52bc:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    52c1:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    52c5:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    52c8:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    52cd:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    52d2:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    52db:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    52e3:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    52e7:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    52eb:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    52f2:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    52fa:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    52fe:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    5306:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    530e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    5312:	e8 99 d0 ff ff       	call   23b0 <io_uring_submit@plt>
}
    5317:	48 83 c4 08          	add    $0x8,%rsp
    531b:	31 c0                	xor    %eax,%eax
    531d:	5b                   	pop    %rbx
    531e:	5d                   	pop    %rbp
    531f:	41 5c                	pop    %r12
    5321:	41 5d                	pop    %r13
    5323:	c3                   	ret
    5324:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    532f:	90                   	nop

0000000000005330 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5330:	f3 0f 1e fa          	endbr64
    5334:	41 56                	push   %r14
    5336:	41 89 f6             	mov    %esi,%r14d
    5339:	41 55                	push   %r13
    533b:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    533e:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    5343:	41 54                	push   %r12
    5345:	55                   	push   %rbp
    5346:	48 89 d5             	mov    %rdx,%rbp
    5349:	53                   	push   %rbx
    void *buf = malloc(size);
    534a:	e8 51 d1 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    534f:	48 85 c0             	test   %rax,%rax
    5352:	0f 84 dd 00 00 00    	je     5435 <_send_static_string_content+0x105>
    5358:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    535b:	4c 89 ef             	mov    %r13,%rdi
    535e:	e8 2d d0 ff ff       	call   2390 <strlen@plt>
    req->iovec_count = 1;
    5363:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    536a:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    536e:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    5371:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    5374:	e8 27 d1 ff ff       	call   24a0 <malloc@plt>
    5379:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    537c:	48 85 c0             	test   %rax,%rax
    537f:	0f 84 b0 00 00 00    	je     5435 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    5385:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5389:	4c 89 e2             	mov    %r12,%rdx
    538c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    538f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5393:	e8 c8 d0 ff ff       	call   2460 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5398:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    539b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    53a1:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    53a4:	48 8b 45 00          	mov    0x0(%rbp),%rax
    53a8:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    53aa:	f6 c1 02             	test   $0x2,%cl
    53ad:	0f 85 7d 00 00 00    	jne    5430 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    53b3:	89 d0                	mov    %edx,%eax
    53b5:	29 f0                	sub    %esi,%eax
    53b7:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    53ba:	0f 82 7c d2 ff ff    	jb     263c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    53c0:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53c3:	8b 45 44             	mov    0x44(%rbp),%eax
    53c6:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    53c9:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    53cc:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    53cf:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    53d2:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    53d8:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    53dc:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    53de:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    53e1:	48 89 ef             	mov    %rbp,%rdi
    53e4:	48 c1 e0 06          	shl    $0x6,%rax
    53e8:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    53ec:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    53ef:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    53f3:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    53f9:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5401:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5405:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5408:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    540f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5417:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    541b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    541f:	5b                   	pop    %rbx
    5420:	5d                   	pop    %rbp
    5421:	41 5c                	pop    %r12
    5423:	41 5d                	pop    %r13
    5425:	41 5e                	pop    %r14
    io_uring_submit(ring);
    5427:	e9 84 cf ff ff       	jmp    23b0 <io_uring_submit@plt>
    542c:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    5430:	e9 7e ff ff ff       	jmp    53b3 <_send_static_string_content+0x83>
    5435:	48 8b 0d e4 5b 00 00 	mov    0x5be4(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    543c:	ba 28 00 00 00       	mov    $0x28,%edx
    5441:	be 01 00 00 00       	mov    $0x1,%esi
    5446:	48 8d 3d 73 31 00 00 	lea    0x3173(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    544d:	e8 0e d1 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    5452:	bf 01 00 00 00       	mov    $0x1,%edi
    5457:	e8 e4 d0 ff ff       	call   2540 <exit@plt>
    545c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005460 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    5460:	f3 0f 1e fa          	endbr64
    5464:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5467:	89 fe                	mov    %edi,%esi
    5469:	48 8b 3d a8 5b 00 00 	mov    0x5ba8(%rip),%rdi        # b018 <unimplemented_content>
    5470:	e9 bb fe ff ff       	jmp    5330 <_send_static_string_content>
    5475:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005480 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5480:	f3 0f 1e fa          	endbr64
    5484:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5487:	89 fe                	mov    %edi,%esi
    5489:	48 8b 3d 80 5b 00 00 	mov    0x5b80(%rip),%rdi        # b010 <http_404_content>
    5490:	e9 9b fe ff ff       	jmp    5330 <_send_static_string_content>
    5495:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000054a0 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    54a0:	f3 0f 1e fa          	endbr64
    54a4:	41 56                	push   %r14
    54a6:	41 55                	push   %r13
    54a8:	49 89 d5             	mov    %rdx,%r13
    54ab:	41 54                	push   %r12
    54ad:	41 89 f4             	mov    %esi,%r12d
    54b0:	55                   	push   %rbp
    54b1:	48 89 fd             	mov    %rdi,%rbp
    54b4:	53                   	push   %rbx
    54b5:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    54bc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    54c5:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    54cd:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    54cf:	e8 bc ce ff ff       	call   2390 <strlen@plt>
    54d4:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    54d9:	48 89 c3             	mov    %rax,%rbx
    54dc:	0f 84 b6 00 00 00    	je     5598 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    54e2:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    54e7:	48 89 ee             	mov    %rbp,%rsi
    54ea:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    54ee:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    54f3:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    54fb:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5503:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    550e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5516:	e8 25 cf ff ff       	call   2440 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    551b:	48 89 e6             	mov    %rsp,%rsi
    551e:	4c 89 f7             	mov    %r14,%rdi
    5521:	e8 2a cf ff ff       	call   2450 <stat@plt>
    5526:	83 f8 ff             	cmp    $0xffffffff,%eax
    5529:	0f 84 d3 00 00 00    	je     5602 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    552f:	8b 44 24 18          	mov    0x18(%rsp),%eax
    5533:	25 00 f0 00 00       	and    $0xf000,%eax
    5538:	3d 00 80 00 00       	cmp    $0x8000,%eax
    553d:	0f 84 f5 00 00 00    	je     5638 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    5543:	48 8b 3d c6 5a 00 00 	mov    0x5ac6(%rip),%rdi        # b010 <http_404_content>
    554a:	4c 89 ea             	mov    %r13,%rdx
    554d:	44 89 e6             	mov    %r12d,%esi
    5550:	e8 db fd ff ff       	call   5330 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5555:	4c 89 f2             	mov    %r14,%rdx
    5558:	bf 01 00 00 00       	mov    $0x1,%edi
    555d:	31 c0                	xor    %eax,%eax
    555f:	48 8d 35 e1 2b 00 00 	lea    0x2be1(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    5566:	e8 75 cf ff ff       	call   24e0 <__printf_chk@plt>
}
    556b:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    5573:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    557c:	0f 85 20 01 00 00    	jne    56a2 <handle_get_method+0x202>
    5582:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5589:	5b                   	pop    %rbx
    558a:	5d                   	pop    %rbp
    558b:	41 5c                	pop    %r12
    558d:	41 5d                	pop    %r13
    558f:	41 5e                	pop    %r14
    5591:	c3                   	ret
    5592:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5598:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    559d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    55a5:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    55aa:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55ad:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55b5:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    55b8:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    55c0:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    55cb:	e8 70 ce ff ff       	call   2440 <__memcpy_chk@plt>
    55d0:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    55d5:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    55da:	48 8d 35 31 2b 00 00 	lea    0x2b31(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    55e1:	48 29 d9             	sub    %rbx,%rcx
    55e4:	ba 0b 00 00 00       	mov    $0xb,%edx
    55e9:	e8 52 ce ff ff       	call   2440 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    55ee:	48 89 e6             	mov    %rsp,%rsi
    55f1:	4c 89 f7             	mov    %r14,%rdi
    55f4:	e8 57 ce ff ff       	call   2450 <stat@plt>
    55f9:	83 f8 ff             	cmp    $0xffffffff,%eax
    55fc:	0f 85 2d ff ff ff    	jne    552f <handle_get_method+0x8f>
    5602:	4c 89 f2             	mov    %r14,%rdx
    5605:	48 89 e9             	mov    %rbp,%rcx
    5608:	48 8d 35 0e 2b 00 00 	lea    0x2b0e(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    560f:	31 c0                	xor    %eax,%eax
    5611:	bf 01 00 00 00       	mov    $0x1,%edi
    5616:	e8 c5 ce ff ff       	call   24e0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    561b:	48 8b 3d ee 59 00 00 	mov    0x59ee(%rip),%rdi        # b010 <http_404_content>
    5622:	4c 89 ea             	mov    %r13,%rdx
    5625:	44 89 e6             	mov    %r12d,%esi
    5628:	e8 03 fd ff ff       	call   5330 <_send_static_string_content>
}
    562d:	e9 39 ff ff ff       	jmp    556b <handle_get_method+0xcb>
    5632:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    5638:	bf 70 00 00 00       	mov    $0x70,%edi
    563d:	e8 5e ce ff ff       	call   24a0 <malloc@plt>
    5642:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    5645:	48 85 c0             	test   %rax,%rax
    5648:	74 5d                	je     56a7 <handle_get_method+0x207>
            req->client_socket = client_socket;
    564a:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    564e:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    5653:	48 8d 50 10          	lea    0x10(%rax),%rdx
    5657:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    565a:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    5661:	e8 5a f5 ff ff       	call   4bc0 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    5666:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    566b:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    566f:	4c 89 f7             	mov    %r14,%rdi
    5672:	e8 79 fa ff ff       	call   50f0 <copy_file_contents>
    5677:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    567c:	4c 89 f2             	mov    %r14,%rdx
    567f:	31 c0                	xor    %eax,%eax
    5681:	48 8d 35 ad 2a 00 00 	lea    0x2aad(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    5688:	bf 01 00 00 00       	mov    $0x1,%edi
    568d:	e8 4e ce ff ff       	call   24e0 <__printf_chk@plt>
            add_write_request(req, ring);
    5692:	4c 89 ee             	mov    %r13,%rsi
    5695:	48 89 df             	mov    %rbx,%rdi
    5698:	e8 13 fb ff ff       	call   51b0 <add_write_request>
    569d:	e9 c9 fe ff ff       	jmp    556b <handle_get_method+0xcb>
}
    56a2:	e8 f9 cc ff ff       	call   23a0 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    56a7:	48 8b 0d 72 59 00 00 	mov    0x5972(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    56ae:	ba 28 00 00 00       	mov    $0x28,%edx
    56b3:	be 01 00 00 00       	mov    $0x1,%esi
    56b8:	48 8d 3d 01 2f 00 00 	lea    0x2f01(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    56bf:	e8 9c ce ff ff       	call   2560 <fwrite@plt>
        exit(1);
    56c4:	bf 01 00 00 00       	mov    $0x1,%edi
    56c9:	e8 72 ce ff ff       	call   2540 <exit@plt>
    56ce:	66 90                	xchg   %ax,%ax

00000000000056d0 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    56d0:	f3 0f 1e fa          	endbr64
    56d4:	41 57                	push   %r15
    56d6:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    56d8:	4c 8d 35 cd 29 00 00 	lea    0x29cd(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    56df:	41 55                	push   %r13
    56e1:	49 89 d5             	mov    %rdx,%r13
    56e4:	41 54                	push   %r12
    56e6:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    56e9:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    56ec:	55                   	push   %rbp
    56ed:	53                   	push   %rbx
    56ee:	48 83 ec 18          	sub    $0x18,%rsp
    56f2:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    56fb:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5700:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5702:	49 89 e7             	mov    %rsp,%r15
    5705:	4c 89 fa             	mov    %r15,%rdx
    5708:	e8 f3 cc ff ff       	call   2400 <strtok_r@plt>
    for (; *str; ++str)
    570d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5711:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5714:	84 db                	test   %bl,%bl
    5716:	74 1d                	je     5735 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5718:	e8 b3 ce ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    571d:	48 89 ea             	mov    %rbp,%rdx
    5720:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    5723:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    5727:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    572a:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    572d:	48 0f be 1a          	movsbq (%rdx),%rbx
    5731:	84 db                	test   %bl,%bl
    5733:	75 eb                	jne    5720 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    5735:	4c 89 fa             	mov    %r15,%rdx
    5738:	4c 89 f6             	mov    %r14,%rsi
    573b:	31 ff                	xor    %edi,%edi
    573d:	e8 be cc ff ff       	call   2400 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    5742:	48 8d 35 11 2a 00 00 	lea    0x2a11(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    5749:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    574c:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    574f:	e8 dc cc ff ff       	call   2430 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    5754:	4c 89 ea             	mov    %r13,%rdx
    5757:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    575a:	85 c0                	test   %eax,%eax
    575c:	75 2a                	jne    5788 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    575e:	48 89 df             	mov    %rbx,%rdi
    5761:	e8 3a fd ff ff       	call   54a0 <handle_get_method>
}
    5766:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    576b:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5774:	75 20                	jne    5796 <handle_http_method+0xc6>
    5776:	48 83 c4 18          	add    $0x18,%rsp
    577a:	5b                   	pop    %rbx
    577b:	5d                   	pop    %rbp
    577c:	41 5c                	pop    %r12
    577e:	41 5d                	pop    %r13
    5780:	41 5e                	pop    %r14
    5782:	41 5f                	pop    %r15
    5784:	c3                   	ret
    5785:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5788:	48 8b 3d 89 58 00 00 	mov    0x5889(%rip),%rdi        # b018 <unimplemented_content>
    578f:	e8 9c fb ff ff       	call   5330 <_send_static_string_content>
}
    5794:	eb d0                	jmp    5766 <handle_http_method+0x96>
    5796:	e8 05 cc ff ff       	call   23a0 <__stack_chk_fail@plt>
    579b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000057a0 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    57a0:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    57a4:	85 d2                	test   %edx,%edx
    57a6:	7e 38                	jle    57e0 <get_line+0x40>
    57a8:	48 63 d2             	movslq %edx,%rdx
    57ab:	48 83 c7 01          	add    $0x1,%rdi
    57af:	48 01 f2             	add    %rsi,%rdx
    57b2:	eb 11                	jmp    57c5 <get_line+0x25>
    57b4:	0f 1f 40 00          	nopl   0x0(%rax)
    57b8:	48 83 c6 01          	add    $0x1,%rsi
    57bc:	48 83 c7 01          	add    $0x1,%rdi
    57c0:	48 39 d6             	cmp    %rdx,%rsi
    57c3:	74 1b                	je     57e0 <get_line+0x40>
        dest[i] = src[i];
    57c5:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    57c9:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    57cb:	3c 0d                	cmp    $0xd,%al
    57cd:	75 e9                	jne    57b8 <get_line+0x18>
    57cf:	80 3f 0a             	cmpb   $0xa,(%rdi)
    57d2:	75 e4                	jne    57b8 <get_line+0x18>
            dest[i] = '\0';
    57d4:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    57d7:	31 c0                	xor    %eax,%eax
    57d9:	c3                   	ret
    57da:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    57e0:	b8 01 00 00 00       	mov    $0x1,%eax
}
    57e5:	c3                   	ret
    57e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000057f0 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    57f0:	f3 0f 1e fa          	endbr64
    57f4:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    57fb:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    57ff:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5808:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5810:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5812:	49 89 e2             	mov    %rsp,%r10
    5815:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    581d:	4c 89 d0             	mov    %r10,%rax
    5820:	eb 13                	jmp    5835 <handle_client_request+0x45>
    5822:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    5828:	48 83 c0 01          	add    $0x1,%rax
    582c:	48 83 c1 01          	add    $0x1,%rcx
    5830:	4c 39 c8             	cmp    %r9,%rax
    5833:	74 4b                	je     5880 <handle_client_request+0x90>
        dest[i] = src[i];
    5835:	44 0f b6 01          	movzbl (%rcx),%r8d
    5839:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    583c:	41 80 f8 0d          	cmp    $0xd,%r8b
    5840:	75 e6                	jne    5828 <handle_client_request+0x38>
    5842:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    5846:	75 e0                	jne    5828 <handle_client_request+0x38>
            dest[i] = '\0';
    5848:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    584b:	8b 47 08             	mov    0x8(%rdi),%eax
    584e:	48 89 f2             	mov    %rsi,%rdx
    5851:	4c 89 d7             	mov    %r10,%rdi
    5854:	89 c6                	mov    %eax,%esi
    5856:	e8 75 fe ff ff       	call   56d0 <handle_http_method>
}
    585b:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    5863:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    586c:	75 39                	jne    58a7 <handle_client_request+0xb7>
    586e:	31 c0                	xor    %eax,%eax
    5870:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    5877:	c3                   	ret
    5878:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5880:	48 8b 0d 99 57 00 00 	mov    0x5799(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5887:	ba 12 00 00 00       	mov    $0x12,%edx
    588c:	be 01 00 00 00       	mov    $0x1,%esi
    5891:	48 8d 3d c6 28 00 00 	lea    0x28c6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5898:	e8 c3 cc ff ff       	call   2560 <fwrite@plt>
        exit(1);
    589d:	bf 01 00 00 00       	mov    $0x1,%edi
    58a2:	e8 99 cc ff ff       	call   2540 <exit@plt>
}
    58a7:	e8 f4 ca ff ff       	call   23a0 <__stack_chk_fail@plt>
    58ac:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000058b0 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    58b0:	f3 0f 1e fa          	endbr64
    58b4:	55                   	push   %rbp
    58b5:	53                   	push   %rbx
    58b6:	48 89 cb             	mov    %rcx,%rbx
    58b9:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    58bd:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    58c0:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    58c3:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    58c9:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    58cc:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    58cf:	f6 c1 02             	test   $0x2,%cl
    58d2:	74 00                	je     58d4 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    58d4:	41 89 c0             	mov    %eax,%r8d
    58d7:	45 29 c8             	sub    %r9d,%r8d
    58da:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    58de:	0f 82 68 cd ff ff    	jb     264c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    58e4:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58e7:	8b 6b 44             	mov    0x44(%rbx),%ebp
    58ea:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    58ed:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    58f0:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    58f3:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    58f7:	d3 e5                	shl    %cl,%ebp
    58f9:	48 c1 e5 06          	shl    $0x6,%rbp
    58fd:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5901:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5904:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5909:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5910:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5914:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5918:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    5920:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    5928:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    592c:	e8 6f cb ff ff       	call   24a0 <malloc@plt>
  io_uring_submit(ring);
    5931:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    5934:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    593a:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    593e:	48 83 c4 08          	add    $0x8,%rsp
    5942:	5b                   	pop    %rbx
    5943:	5d                   	pop    %rbp
  io_uring_submit(ring);
    5944:	e9 67 ca ff ff       	jmp    23b0 <io_uring_submit@plt>
    5949:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000005950 <io_thread>:
void* io_thread(void *arg) {
    5950:	f3 0f 1e fa          	endbr64
    5954:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5956:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    5958:	41 56                	push   %r14
    595a:	41 55                	push   %r13
    595c:	41 54                	push   %r12
    595e:	55                   	push   %rbp
    595f:	48 89 fd             	mov    %rdi,%rbp
    5962:	53                   	push   %rbx
    5963:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    596a:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5973:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    597b:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    597f:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5984:	bf 00 01 00 00       	mov    $0x100,%edi
    5989:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    598c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5990:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5995:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    599a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    599f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    59a4:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    59ac:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    59b1:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    59b9:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    59be:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    59c6:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    59cb:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    59d3:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    59d8:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    59e0:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    59e5:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    59ed:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    59f5:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    59fd:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5a05:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    5a0d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5a15:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    5a1d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    5a25:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    5a2d:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    5a35:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    5a3d:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    5a44:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    5a4c:	e8 1f ca ff ff       	call   2470 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    5a51:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    5a55:	31 f6                	xor    %esi,%esi
    5a57:	e8 24 cb ff ff       	call   2580 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    5a5c:	31 d2                	xor    %edx,%edx
    5a5e:	be 01 00 00 00       	mov    $0x1,%esi
    5a63:	bf 02 00 00 00       	mov    $0x2,%edi
    5a68:	e8 83 cb ff ff       	call   25f0 <socket@plt>
  if (sock == -1)
    5a6d:	83 f8 ff             	cmp    $0xffffffff,%eax
    5a70:	0f 84 18 cc ff ff    	je     268e <io_thread.cold+0x38>
  if (setsockopt(sock,
    5a76:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    5a7b:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5a81:	89 c7                	mov    %eax,%edi
    5a83:	41 89 c4             	mov    %eax,%r12d
    5a86:	ba 02 00 00 00       	mov    $0x2,%edx
    5a8b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5a90:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5a98:	e8 c3 c8 ff ff       	call   2360 <setsockopt@plt>
    5a9d:	85 c0                	test   %eax,%eax
    5a9f:	0f 88 bd cb ff ff    	js     2662 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5aa5:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    5aaa:	ba 10 00 00 00       	mov    $0x10,%edx
    5aaf:	44 89 e7             	mov    %r12d,%edi
    5ab2:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5abb:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5ac3:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    5acb:	e8 20 ca ff ff       	call   24f0 <bind@plt>
    5ad0:	85 c0                	test   %eax,%eax
    5ad2:	0f 88 c2 cb ff ff    	js     269a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5ad8:	be 0a 00 00 00       	mov    $0xa,%esi
    5add:	44 89 e7             	mov    %r12d,%edi
    5ae0:	e8 cb c9 ff ff       	call   24b0 <listen@plt>
    5ae5:	85 c0                	test   %eax,%eax
    5ae7:	0f 88 81 cb ff ff    	js     266e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5aed:	ba db 18 00 00       	mov    $0x18db,%edx
    5af2:	48 8d 35 aa 26 00 00 	lea    0x26aa(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5af9:	bf 01 00 00 00       	mov    $0x1,%edi
    5afe:	31 c0                	xor    %eax,%eax
    5b00:	e8 db c9 ff ff       	call   24e0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5b05:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5b0a:	48 89 d9             	mov    %rbx,%rcx
    5b0d:	44 89 e7             	mov    %r12d,%edi
    5b10:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5b15:	48 89 c6             	mov    %rax,%rsi
    5b18:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5b1d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5b22:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5b2a:	e8 81 fd ff ff       	call   58b0 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5b2f:	bf 01 00 00 00       	mov    $0x1,%edi
    5b34:	be 10 00 00 00       	mov    $0x10,%esi
    5b39:	e8 e2 c8 ff ff       	call   2420 <calloc@plt>
    void *buf = malloc(size);
    5b3e:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5b43:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5b46:	e8 55 c9 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    5b4b:	48 85 c0             	test   %rax,%rax
    5b4e:	0f 84 ae 04 00 00    	je     6002 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5b54:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5b58:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5b5f:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5b66:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5b6e:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5b71:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5b76:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5b78:	f6 c1 02             	test   $0x2,%cl
    5b7b:	0f 85 0f 04 00 00    	jne    5f90 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5b81:	89 d0                	mov    %edx,%eax
    5b83:	29 f0                	sub    %esi,%eax
    5b85:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5b8c:	0f 82 f2 ca ff ff    	jb     2684 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5b92:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5b95:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5b99:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5b9d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5ba0:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5ba7:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5baa:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5bb1:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5bb8:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5bba:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5bbd:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5bc2:	48 c1 e0 06          	shl    $0x6,%rax
    5bc6:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5bce:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5bd4:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5bd7:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5bdf:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5be3:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5beb:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5bf3:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5bf7:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5bfb:	e8 b0 c7 ff ff       	call   23b0 <io_uring_submit@plt>
  while (data->running == 1) {
    5c00:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5c04:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5c09:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5c11:	0f 85 d7 01 00 00    	jne    5dee <io_thread+0x49e>
    5c17:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5c1c:	4d 89 ce             	mov    %r9,%r14
    5c1f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5c24:	0f 1f 40 00          	nopl   0x0(%rax)
    5c28:	48 8d 3d 8a 25 00 00 	lea    0x258a(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5c2f:	e8 1c c7 ff ff       	call   2350 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5c34:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5c3b:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5c42:	c1 e9 0b             	shr    $0xb,%ecx
    5c45:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5c48:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5c50:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5c52:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5c5a:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5c5c:	39 d0                	cmp    %edx,%eax
    5c5e:	74 36                	je     5c96 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5c60:	89 f8                	mov    %edi,%eax
    5c62:	21 d0                	and    %edx,%eax
    5c64:	d3 e0                	shl    %cl,%eax
    5c66:	48 c1 e0 04          	shl    $0x4,%rax
    5c6a:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5c72:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5c7a:	0f 85 a8 01 00 00    	jne    5e28 <io_thread+0x4d8>
    5c80:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5c84:	0f 85 0e 03 00 00    	jne    5f98 <io_thread+0x648>
			if (cqe->res < 0)
    5c8a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5c8d:	83 c2 01             	add    $0x1,%edx
    5c90:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5c92:	85 c0                	test   %eax,%eax
    5c94:	79 b2                	jns    5c48 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5c96:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5c9f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5ca0:	45 31 c0             	xor    %r8d,%r8d
    5ca3:	31 d2                	xor    %edx,%edx
    5ca5:	b9 01 00 00 00       	mov    $0x1,%ecx
    5caa:	4c 89 f6             	mov    %r14,%rsi
    5cad:	48 89 df             	mov    %rbx,%rdi
    5cb0:	e8 1b c8 ff ff       	call   24d0 <__io_uring_get_cqe@plt>
    5cb5:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5cb8:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5cbd:	48 83 38 01          	cmpq   $0x1,(%rax)
    5cc1:	0f 84 e1 02 00 00    	je     5fa8 <io_thread+0x658>
    5cc7:	48 8d 3d 11 25 00 00 	lea    0x2511(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5cce:	e8 7d c6 ff ff       	call   2350 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5cd3:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5cd8:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5cdb:	45 85 ff             	test   %r15d,%r15d
    5cde:	0f 88 72 c9 ff ff    	js     2656 <io_thread.cold>
      if (cqe->res < 0) {
    5ce4:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5ce7:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    5ceb:	85 c0                	test   %eax,%eax
    5ced:	0f 88 d5 02 00 00    	js     5fc8 <io_thread+0x678>
      switch (req->event_type) {
    5cf3:	41 83 f8 01          	cmp    $0x1,%r8d
    5cf7:	0f 84 7b 01 00 00    	je     5e78 <io_thread+0x528>
    5cfd:	41 83 f8 02          	cmp    $0x2,%r8d
    5d01:	0f 84 a1 01 00 00    	je     5ea8 <io_thread+0x558>
    5d07:	45 85 c0             	test   %r8d,%r8d
    5d0a:	0f 85 50 01 00 00    	jne    5e60 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5d10:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5d15:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5d1a:	48 89 d9             	mov    %rbx,%rcx
    5d1d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5d21:	e8 8a fb ff ff       	call   58b0 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5d26:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5d2b:	48 89 de             	mov    %rbx,%rsi
    5d2e:	8b 78 08             	mov    0x8(%rax),%edi
    5d31:	e8 1a f5 ff ff       	call   5250 <add_read_request>
              free(req);
    5d36:	4c 89 e7             	mov    %r12,%rdi
    5d39:	e8 e2 c5 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5d3e:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5d43:	48 85 c0             	test   %rax,%rax
    5d46:	0f 85 14 01 00 00    	jne    5e60 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    5d4c:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5d53:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5d5a:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5d5d:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5d62:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5d64:	f6 c1 02             	test   $0x2,%cl
    5d67:	74 00                	je     5d69 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5d69:	89 d0                	mov    %edx,%eax
    5d6b:	29 f0                	sub    %esi,%eax
    5d6d:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5d74:	0f 82 00 c9 ff ff    	jb     267a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5d7a:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5d7d:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5d82:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5d86:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d89:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5d90:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d93:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5d9a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5da1:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5da3:	8b 55 60             	mov    0x60(%rbp),%edx
    5da6:	48 c1 e0 06          	shl    $0x6,%rax
    5daa:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5db2:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5db8:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5dbb:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5dc3:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5dc7:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5dcf:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5dd7:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5ddb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5ddf:	e8 cc c5 ff ff       	call   23b0 <io_uring_submit@plt>
  while (data->running == 1) {
    5de4:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5de8:	0f 84 3a fe ff ff    	je     5c28 <io_thread+0x2d8>
    5dee:	48 8d 3d 23 24 00 00 	lea    0x2423(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5df5:	e8 56 c5 ff ff       	call   2350 <puts@plt>
}
    5dfa:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5e02:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5e0b:	0f 85 18 02 00 00    	jne    6029 <io_thread+0x6d9>
    5e11:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5e18:	31 c0                	xor    %eax,%eax
    5e1a:	5b                   	pop    %rbx
    5e1b:	5d                   	pop    %rbp
    5e1c:	41 5c                	pop    %r12
    5e1e:	41 5d                	pop    %r13
    5e20:	41 5e                	pop    %r14
    5e22:	41 5f                	pop    %r15
    5e24:	c3                   	ret
    5e25:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5e28:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5e2d:	48 85 c0             	test   %rax,%rax
    5e30:	0f 84 6a fe ff ff    	je     5ca0 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5e36:	48 83 38 01          	cmpq   $0x1,(%rax)
    5e3a:	0f 84 68 01 00 00    	je     5fa8 <io_thread+0x658>
    5e40:	48 8d 3d 98 23 00 00 	lea    0x2398(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5e47:	e8 04 c5 ff ff       	call   2350 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5e4c:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5e51:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5e54:	e9 8b fe ff ff       	jmp    5ce4 <io_thread+0x394>
    5e59:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5e60:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5e68:	8b 02                	mov    (%rdx),%eax
    5e6a:	83 c0 01             	add    $0x1,%eax
    5e6d:	89 02                	mov    %eax,(%rdx)
}
    5e6f:	e9 d8 fe ff ff       	jmp    5d4c <io_thread+0x3fc>
    5e74:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5e78:	85 c0                	test   %eax,%eax
    5e7a:	75 74                	jne    5ef0 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5e7c:	48 8b 0d 9d 51 00 00 	mov    0x519d(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5e83:	ba 0f 00 00 00       	mov    $0xf,%edx
    5e88:	be 01 00 00 00       	mov    $0x1,%esi
    5e8d:	48 8d 3d 74 23 00 00 	lea    0x2374(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5e94:	e8 c7 c6 ff ff       	call   2560 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5e99:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5e9e:	e9 a0 fe ff ff       	jmp    5d43 <io_thread+0x3f3>
    5ea3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5ea8:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5ead:	45 31 ff             	xor    %r15d,%r15d
    5eb0:	85 c0                	test   %eax,%eax
    5eb2:	7e 20                	jle    5ed4 <io_thread+0x584>
    5eb4:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5eb8:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5ebb:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5ebf:	48 c1 e0 04          	shl    $0x4,%rax
    5ec3:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5ec8:	e8 53 c4 ff ff       	call   2320 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5ecd:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5ed2:	7f e4                	jg     5eb8 <io_thread+0x568>
              close(req->client_socket);
    5ed4:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5ed9:	e8 12 c5 ff ff       	call   23f0 <close@plt>
              free(req);
    5ede:	4c 89 e7             	mov    %r12,%rdi
    5ee1:	e8 3a c4 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5ee6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5eeb:	e9 53 fe ff ff       	jmp    5d43 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5ef0:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5ef5:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5efa:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5f02:	eb 11                	jmp    5f15 <io_thread+0x5c5>
    5f04:	0f 1f 40 00          	nopl   0x0(%rax)
    5f08:	48 83 c0 01          	add    $0x1,%rax
    5f0c:	48 83 c2 01          	add    $0x1,%rdx
    5f10:	48 39 c6             	cmp    %rax,%rsi
    5f13:	74 4b                	je     5f60 <io_thread+0x610>
        dest[i] = src[i];
    5f15:	0f b6 0a             	movzbl (%rdx),%ecx
    5f18:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5f1a:	80 f9 0d             	cmp    $0xd,%cl
    5f1d:	75 e9                	jne    5f08 <io_thread+0x5b8>
    5f1f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5f23:	75 e3                	jne    5f08 <io_thread+0x5b8>
            dest[i] = '\0';
    5f25:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5f28:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5f2d:	48 89 da             	mov    %rbx,%rdx
    5f30:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5f35:	e8 96 f7 ff ff       	call   56d0 <handle_http_method>
              free(req->iov[0].iov_base);
    5f3a:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5f3f:	e8 dc c3 ff ff       	call   2320 <free@plt>
              free(req);
    5f44:	4c 89 e7             	mov    %r12,%rdi
    5f47:	e8 d4 c3 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5f4c:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5f51:	e9 ed fd ff ff       	jmp    5d43 <io_thread+0x3f3>
    5f56:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5f60:	48 8b 0d b9 50 00 00 	mov    0x50b9(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5f67:	ba 12 00 00 00       	mov    $0x12,%edx
    5f6c:	be 01 00 00 00       	mov    $0x1,%esi
    5f71:	48 8d 3d e6 21 00 00 	lea    0x21e6(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5f78:	e8 e3 c5 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    5f7d:	bf 01 00 00 00       	mov    $0x1,%edi
    5f82:	e8 b9 c5 ff ff       	call   2540 <exit@plt>
    5f87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5f90:	e9 ec fb ff ff       	jmp    5b81 <io_thread+0x231>
    5f95:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5f98:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5f9d:	e9 94 fe ff ff       	jmp    5e36 <io_thread+0x4e6>
    5fa2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5fa8:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5fb0:	48 8d 3d 14 22 00 00 	lea    0x2214(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    5fb7:	8b 02                	mov    (%rdx),%eax
    5fb9:	83 c0 01             	add    $0x1,%eax
    5fbc:	89 02                	mov    %eax,(%rdx)
    5fbe:	e8 8d c3 ff ff       	call   2350 <puts@plt>
    5fc3:	e9 26 fe ff ff       	jmp    5dee <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5fc8:	f7 d8                	neg    %eax
    5fca:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5fcf:	89 c7                	mov    %eax,%edi
    5fd1:	e8 ca c5 ff ff       	call   25a0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5fd6:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5fdb:	be 01 00 00 00       	mov    $0x1,%esi
    5fe0:	48 8b 3d 39 50 00 00 	mov    0x5039(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    5fe7:	48 89 c1             	mov    %rax,%rcx
    5fea:	48 8d 15 ff 25 00 00 	lea    0x25ff(%rip),%rdx        # 85f0 <_IO_stdin_used+0x5f0>
    5ff1:	31 c0                	xor    %eax,%eax
    5ff3:	e8 78 c5 ff ff       	call   2570 <__fprintf_chk@plt>
          exit(1);
    5ff8:	bf 01 00 00 00       	mov    $0x1,%edi
    5ffd:	e8 3e c5 ff ff       	call   2540 <exit@plt>
    6002:	48 8b 0d 17 50 00 00 	mov    0x5017(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    6009:	ba 28 00 00 00       	mov    $0x28,%edx
    600e:	be 01 00 00 00       	mov    $0x1,%esi
    6013:	48 8d 3d a6 25 00 00 	lea    0x25a6(%rip),%rdi        # 85c0 <_IO_stdin_used+0x5c0>
    601a:	e8 41 c5 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    601f:	bf 01 00 00 00       	mov    $0x1,%edi
    6024:	e8 17 c5 ff ff       	call   2540 <exit@plt>
}
    6029:	e8 72 c3 ff ff       	call   23a0 <__stack_chk_fail@plt>
    602e:	66 90                	xchg   %ax,%ax

0000000000006030 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    6030:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6034:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    603b:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    6041:	85 c9                	test   %ecx,%ecx
    6043:	0f 8e ea 00 00 00    	jle    6133 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    6049:	41 56                	push   %r14
    604b:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    604d:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    6050:	41 54                	push   %r12
    6052:	49 89 fc             	mov    %rdi,%r12
    6055:	55                   	push   %rbp
    6056:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6057:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    605b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6060:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    6064:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    606c:	31 db                	xor    %ebx,%ebx
    606e:	8b 10                	mov    (%rax),%edx
    6070:	85 d2                	test   %edx,%edx
    6072:	7e 26                	jle    609a <barriered_work_ingest+0x6a>
    6074:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    6078:	48 89 dd             	mov    %rbx,%rbp
    607b:	48 c1 e5 08          	shl    $0x8,%rbp
    607f:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    6083:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    608a:	74 24                	je     60b0 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    608c:	48 83 c3 01          	add    $0x1,%rbx
    6090:	39 da                	cmp    %ebx,%edx
    6092:	7f e4                	jg     6078 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6094:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    609a:	49 83 c5 01          	add    $0x1,%r13
    609e:	44 39 e9             	cmp    %r13d,%ecx
    60a1:	7f bd                	jg     6060 <barriered_work_ingest+0x30>
}
    60a3:	5b                   	pop    %rbx
    60a4:	31 c0                	xor    %eax,%eax
    60a6:	5d                   	pop    %rbp
    60a7:	41 5c                	pop    %r12
    60a9:	41 5d                	pop    %r13
    60ab:	41 5e                	pop    %r14
    60ad:	c3                   	ret
    60ae:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    60b0:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    60b9:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    60c0:	bf 04 00 00 00       	mov    $0x4,%edi
    60c5:	48 c1 e6 05          	shl    $0x5,%rsi
    60c9:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    60d0:	48 83 c6 10          	add    $0x10,%rsi
    60d4:	e8 97 c2 ff ff       	call   2370 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    60d9:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    60e1:	48 8b 40 50          	mov    0x50(%rax),%rax
    60e5:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    60e9:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    60ed:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    60f7:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    60fd:	83 c0 01             	add    $0x1,%eax
    6100:	99                   	cltd
    6101:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    6107:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    610d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6110:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    6118:	48 83 c3 01          	add    $0x1,%rbx
    611c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    6120:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    6124:	8b 10                	mov    (%rax),%edx
    6126:	39 da                	cmp    %ebx,%edx
    6128:	0f 8f 46 ff ff ff    	jg     6074 <barriered_work_ingest+0x44>
    612e:	e9 61 ff ff ff       	jmp    6094 <barriered_work_ingest+0x64>
}
    6133:	31 c0                	xor    %eax,%eax
    6135:	c3                   	ret
    6136:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006140 <barriered_thread>:
void* barriered_thread(void *arg) {
    6140:	f3 0f 1e fa          	endbr64
    6144:	41 56                	push   %r14
    6146:	41 55                	push   %r13
    6148:	41 54                	push   %r12
  int t = 0;
    614a:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    614d:	55                   	push   %rbp
  int waiting = 0;
    614e:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    6150:	53                   	push   %rbx
    6151:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    6154:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6158:	0f 85 74 02 00 00    	jne    63d2 <barriered_thread+0x292>
    if (t >= data->task_count) {
    615e:	8b 43 40             	mov    0x40(%rbx),%eax
    6161:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6168:	41 39 c4             	cmp    %eax,%r12d
    616b:	0f 8d 6f 01 00 00    	jge    62e0 <barriered_thread+0x1a0>
    6171:	49 63 fc             	movslq %r12d,%rdi
    6174:	48 c1 e7 09          	shl    $0x9,%rdi
    6178:	49 89 fd             	mov    %rdi,%r13
    617b:	eb 32                	jmp    61af <barriered_thread+0x6f>
    617d:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    6180:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6184:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6188:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    618c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6190:	4c 01 ef             	add    %r13,%rdi
    6193:	e8 98 fe ff ff       	call   6030 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    6198:	8b 43 40             	mov    0x40(%rbx),%eax
    619b:	41 83 c4 01          	add    $0x1,%r12d
    619f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    61a6:	44 39 e0             	cmp    %r12d,%eax
    61a9:	0f 8e 19 02 00 00    	jle    63c8 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    61af:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    61b3:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    61b7:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    61be:	75 c0                	jne    6180 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    61c0:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    61c4:	83 e8 01             	sub    $0x1,%eax
    61c7:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    61cc:	45 85 e4             	test   %r12d,%r12d
    61cf:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    61d2:	45 85 c0             	test   %r8d,%r8d
    61d5:	0f 8e 2d 01 00 00    	jle    6308 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    61db:	48 63 c8             	movslq %eax,%rcx
    61de:	48 8b 43 18          	mov    0x18(%rbx),%rax
    61e2:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    61e5:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    61eb:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    61f2:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    61f6:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    61f9:	45 31 f6             	xor    %r14d,%r14d
    61fc:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6200:	48 8b 10             	mov    (%rax),%rdx
    6203:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6207:	49 01 cb             	add    %rcx,%r11
    620a:	4c 89 da             	mov    %r11,%rdx
    620d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6214:	75 04                	jne    621a <barriered_thread+0xda>
            arrived++;
    6216:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    621a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    6220:	75 04                	jne    6226 <barriered_thread+0xe6>
            prearrive++;
    6222:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6226:	48 83 c0 08          	add    $0x8,%rax
    622a:	48 39 c6             	cmp    %rax,%rsi
    622d:	75 d1                	jne    6200 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    622f:	45 85 d2             	test   %r10d,%r10d
    6232:	0f 84 c0 00 00 00    	je     62f8 <barriered_thread+0x1b8>
    6238:	45 39 d0             	cmp    %r10d,%r8d
    623b:	0f 84 b7 00 00 00    	je     62f8 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    6241:	45 85 f6             	test   %r14d,%r14d
    6244:	74 0a                	je     6250 <barriered_thread+0x110>
    6246:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    624a:	0f 85 ae 01 00 00    	jne    63fe <barriered_thread+0x2be>
    6250:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    6254:	4c 01 ea             	add    %r13,%rdx
    6257:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    625e:	45 85 e4             	test   %r12d,%r12d
    6261:	75 14                	jne    6277 <barriered_thread+0x137>
    6263:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    626a:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    6271:	0f 8c 69 01 00 00    	jl     63e0 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6277:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    627b:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    627f:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6289:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    628d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6291:	4c 01 ef             	add    %r13,%rdi
    6294:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    629a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    629e:	4c 01 e8             	add    %r13,%rax
    62a1:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    62a8:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    62ab:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    62b0:	83 e8 01             	sub    $0x1,%eax
    62b3:	44 39 e0             	cmp    %r12d,%eax
    62b6:	0f 84 a4 00 00 00    	je     6360 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    62bc:	0f ae f8             	sfence
          if (waiting == 0) {
    62bf:	85 ed                	test   %ebp,%ebp
    62c1:	0f 84 d1 00 00 00    	je     6398 <barriered_thread+0x258>
        int arrived = 0; 
    62c7:	bd 01 00 00 00       	mov    $0x1,%ebp
    62cc:	e9 c7 fe ff ff       	jmp    6198 <barriered_thread+0x58>
  while (data->running == 1) {
    62d1:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    62d5:	0f 85 f7 00 00 00    	jne    63d2 <barriered_thread+0x292>
    62db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    62e0:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    62e8:	85 c0                	test   %eax,%eax
    62ea:	7e e5                	jle    62d1 <barriered_thread+0x191>
    62ec:	45 31 e4             	xor    %r12d,%r12d
    62ef:	e9 7d fe ff ff       	jmp    6171 <barriered_thread+0x31>
    62f4:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    62f8:	83 fd 01             	cmp    $0x1,%ebp
    62fb:	74 1b                	je     6318 <barriered_thread+0x1d8>
        int arrived = 0; 
    62fd:	31 ed                	xor    %ebp,%ebp
    62ff:	e9 3d ff ff ff       	jmp    6241 <barriered_thread+0x101>
    6304:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6308:	83 fd 01             	cmp    $0x1,%ebp
    630b:	0f 85 43 ff ff ff    	jne    6254 <barriered_thread+0x114>
        int arrived = 0; 
    6311:	45 31 f6             	xor    %r14d,%r14d
    6314:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6318:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    631f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    6324:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6326:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    632a:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    6331:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    6336:	e8 35 c0 ff ff       	call   2370 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    633b:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    6342:	48 83 c0 01          	add    $0x1,%rax
    6346:	48 99                	cqto
    6348:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    634f:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    6356:	e9 e6 fe ff ff       	jmp    6241 <barriered_thread+0x101>
    635b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6360:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    6367:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    636e:	0f 8d 48 ff ff ff    	jge    62bc <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    6374:	48 c1 e6 04          	shl    $0x4,%rsi
    6378:	bf 04 00 00 00       	mov    $0x4,%edi
    637d:	48 03 73 70          	add    0x70(%rbx),%rsi
    6381:	e8 ea bf ff ff       	call   2370 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6386:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    638e:	e9 29 ff ff ff       	jmp    62bc <barriered_thread+0x17c>
    6393:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    6398:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    639f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    63a4:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    63a8:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    63af:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    63b3:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    63b7:	e8 b4 bf ff ff       	call   2370 <clock_gettime@plt>
            waiting = 1;
    63bc:	e9 06 ff ff ff       	jmp    62c7 <barriered_thread+0x187>
    63c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    63c8:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    63cc:	0f 84 96 fd ff ff    	je     6168 <barriered_thread+0x28>
}
    63d2:	5b                   	pop    %rbx
    63d3:	31 c0                	xor    %eax,%eax
    63d5:	5d                   	pop    %rbp
    63d6:	41 5c                	pop    %r12
    63d8:	41 5d                	pop    %r13
    63da:	41 5e                	pop    %r14
    63dc:	c3                   	ret
    63dd:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    63e0:	48 c1 e6 04          	shl    $0x4,%rsi
    63e4:	bf 04 00 00 00       	mov    $0x4,%edi
    63e9:	48 03 73 68          	add    0x68(%rbx),%rsi
    63ed:	e8 7e bf ff ff       	call   2370 <clock_gettime@plt>
          data->tasks[t].available = 0;
    63f2:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    63f6:	4c 01 ea             	add    %r13,%rdx
    63f9:	e9 79 fe ff ff       	jmp    6277 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    63fe:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6402:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6406:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    640a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    640e:	4c 01 ef             	add    %r13,%rdi
    6411:	e8 1a fc ff ff       	call   6030 <barriered_work_ingest>
          break;
    6416:	e9 39 fd ff ff       	jmp    6154 <barriered_thread+0x14>
    641b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000006420 <receive>:
int receive(struct BarrierTask *data) {
    6420:	f3 0f 1e fa          	endbr64
    6424:	41 57                	push   %r15
    6426:	41 56                	push   %r14
    6428:	41 55                	push   %r13
    642a:	41 54                	push   %r12
    642c:	55                   	push   %rbp
    642d:	53                   	push   %rbx
    642e:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6432:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    6439:	45 85 f6             	test   %r14d,%r14d
    643c:	0f 8e 37 01 00 00    	jle    6579 <receive+0x159>
    if (n == data->thread->real_thread_index) { continue; }
    6442:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    6449:	48 89 f9             	mov    %rdi,%rcx
    644c:	45 31 e4             	xor    %r12d,%r12d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    644f:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    6451:	49 63 6f 08          	movslq 0x8(%r15),%rbp
    6455:	49 89 ed             	mov    %rbp,%r13
    6458:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    6460:	41 39 dd             	cmp    %ebx,%r13d
    6463:	0f 84 00 01 00 00    	je     6569 <receive+0x149>
    struct Data *me = data->mailboxes[n].lower;
    6469:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    6470:	4a 8b 34 20          	mov    (%rax,%r12,1),%rsi
    if (me->available_reading == 1) {
    6474:	8b 86 00 02 00 00    	mov    0x200(%rsi),%eax
    647a:	83 f8 01             	cmp    $0x1,%eax
    647d:	74 11                	je     6490 <receive+0x70>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    647f:	83 be 18 03 00 00 02 	cmpl   $0x2,0x318(%rsi)
    6486:	75 08                	jne    6490 <receive+0x70>
    6488:	85 c0                	test   %eax,%eax
    648a:	0f 84 d9 00 00 00    	je     6569 <receive+0x149>
    for (int x = 0 ; x < me->messages_count ; x++) {
    6490:	48 8b be 80 00 00 00 	mov    0x80(%rsi),%rdi
    6497:	48 85 ff             	test   %rdi,%rdi
    649a:	0f 8e a0 00 00 00    	jle    6540 <receive+0x120>
      data->sends++;
    64a0:	48 8b 91 78 01 00 00 	mov    0x178(%rcx),%rdx
    64a7:	4c 8b 06             	mov    (%rsi),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    64aa:	4c 63 59 04          	movslq 0x4(%rcx),%r11
    64ae:	49 89 d1             	mov    %rdx,%r9
    64b1:	48 8d 42 01          	lea    0x1(%rdx),%rax
    64b5:	49 f7 d9             	neg    %r9
    64b8:	48 01 c7             	add    %rax,%rdi
    64bb:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    64bf:	4c 8b 89 08 01 00 00 	mov    0x108(%rcx),%r9
      me->received++;
    64c6:	4c 8b 86 10 03 00 00 	mov    0x310(%rsi),%r8
      data->n++;
    64cd:	49 29 d1             	sub    %rdx,%r9
      me->received++;
    64d0:	49 29 d0             	sub    %rdx,%r8
    64d3:	eb 0c                	jmp    64e1 <receive+0xc1>
    64d5:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    64d8:	48 83 c0 01          	add    $0x1,%rax
    64dc:	48 39 c7             	cmp    %rax,%rdi
    64df:	74 5f                	je     6540 <receive+0x120>
      data->n++;
    64e1:	49 8d 14 01          	lea    (%r9,%rax,1),%rdx
      data->sends++;
    64e5:	48 89 81 78 01 00 00 	mov    %rax,0x178(%rcx)
      data->n++;
    64ec:	48 89 91 08 01 00 00 	mov    %rdx,0x108(%rcx)
      me->received++;
    64f3:	49 8d 14 00          	lea    (%r8,%rax,1),%rdx
    64f7:	48 89 96 10 03 00 00 	mov    %rdx,0x310(%rsi)
      if (me->messages[x]->group == data->group) {
    64fe:	49 8b 54 c2 f8       	mov    -0x8(%r10,%rax,8),%rdx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    6503:	4c 39 5a 10          	cmp    %r11,0x10(%rdx)
    6507:	75 cf                	jne    64d8 <receive+0xb8>
    6509:	48 39 6a 08          	cmp    %rbp,0x8(%rdx)
    650d:	75 c9                	jne    64d8 <receive+0xb8>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    650f:	49 63 47 04          	movslq 0x4(%r15),%rax
    6513:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6515:	bf 01 00 00 00       	mov    $0x1,%edi
    651a:	ba 01 00 00 00       	mov    $0x1,%edx
    651f:	48 8d 35 f2 20 00 00 	lea    0x20f2(%rip),%rsi        # 8618 <_IO_stdin_used+0x618>
    6526:	48 39 e8             	cmp    %rbp,%rax
    6529:	0f 94 c1             	sete   %cl
    652c:	31 c0                	xor    %eax,%eax
    652e:	e8 ad bf ff ff       	call   24e0 <__printf_chk@plt>
        exit(1);
    6533:	bf 01 00 00 00       	mov    $0x1,%edi
    6538:	e8 03 c0 ff ff       	call   2540 <exit@plt>
    653d:	0f 1f 00             	nopl   (%rax)
    me->messages_count = 0;
    6540:	48 c7 86 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rsi)
      me->available_reading = 0;
    654b:	c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi)
      me->finished_reading = 1;
    6555:	c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rsi)
      me->available_sending = 1;
    655f:	c7 86 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rsi)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6569:	83 c3 01             	add    $0x1,%ebx
    656c:	49 83 c4 38          	add    $0x38,%r12
    6570:	44 39 f3             	cmp    %r14d,%ebx
    6573:	0f 85 e7 fe ff ff    	jne    6460 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    6579:	0f ae f8             	sfence
}
    657c:	48 83 c4 08          	add    $0x8,%rsp
    6580:	31 c0                	xor    %eax,%eax
    6582:	5b                   	pop    %rbx
    6583:	5d                   	pop    %rbp
    6584:	41 5c                	pop    %r12
    6586:	41 5d                	pop    %r13
    6588:	41 5e                	pop    %r14
    658a:	41 5f                	pop    %r15
    658c:	c3                   	ret
    658d:	0f 1f 00             	nopl   (%rax)

0000000000006590 <sendm>:
int sendm(struct BarrierTask *data) {
    6590:	f3 0f 1e fa          	endbr64
    6594:	41 57                	push   %r15
    6596:	41 56                	push   %r14
    6598:	41 55                	push   %r13
    659a:	41 54                	push   %r12
    659c:	55                   	push   %rbp
    659d:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    659e:	44 8b a7 40 01 00 00 	mov    0x140(%rdi),%r12d
    65a5:	45 85 e4             	test   %r12d,%r12d
    65a8:	0f 8e ae 00 00 00    	jle    665c <sendm+0xcc>
        if (n == data->thread->real_thread_index) { continue; }
    65ae:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    65b5:	48 89 fe             	mov    %rdi,%rsi
    65b8:	31 d2                	xor    %edx,%edx
    65ba:	44 8b 68 08          	mov    0x8(%rax),%r13d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    65be:	31 c0                	xor    %eax,%eax
    65c0:	eb 38                	jmp    65fa <sendm+0x6a>
    65c2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          data->mailboxes[n].higher = them;
    65c8:	4c 89 47 08          	mov    %r8,0x8(%rdi)
          them = data->mailboxes[n].pending;
    65cc:	4c 89 c1             	mov    %r8,%rcx
          data->mailboxes[n].pending = NULL;
    65cf:	48 c7 47 10 00 00 00 00 	movq   $0x0,0x10(%rdi)
        if (them->messages_count > 0) {
    65d7:	49 8b b8 80 00 00 00 	mov    0x80(%r8),%rdi
          them->available_sending = 1;
    65de:	41 c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r8)
        if (them->messages_count > 0) {
    65e9:	48 85 ff             	test   %rdi,%rdi
    65ec:	7e 4f                	jle    663d <sendm+0xad>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    65ee:	83 c0 01             	add    $0x1,%eax
    65f1:	48 83 c2 38          	add    $0x38,%rdx
    65f5:	44 39 e0             	cmp    %r12d,%eax
    65f8:	74 62                	je     665c <sendm+0xcc>
        if (n == data->thread->real_thread_index) { continue; }
    65fa:	41 39 c5             	cmp    %eax,%r13d
    65fd:	74 ef                	je     65ee <sendm+0x5e>
        struct Data *them = data->mailboxes[n].higher;
    65ff:	48 8b be 70 01 00 00 	mov    0x170(%rsi),%rdi
    6606:	48 01 d7             	add    %rdx,%rdi
        if (data->mailboxes[n].pending != NULL) {
    6609:	4c 8b 47 10          	mov    0x10(%rdi),%r8
        struct Data *them = data->mailboxes[n].higher;
    660d:	48 8b 4f 08          	mov    0x8(%rdi),%rcx
        if (data->mailboxes[n].pending != NULL) {
    6611:	4d 85 c0             	test   %r8,%r8
    6614:	75 b2                	jne    65c8 <sendm+0x38>
        if (them->messages_count > 0) {
    6616:	48 8b b9 80 00 00 00 	mov    0x80(%rcx),%rdi
    661d:	48 85 ff             	test   %rdi,%rdi
    6620:	7f cc                	jg     65ee <sendm+0x5e>
        if (them->available_sending == 1) {
    6622:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    6629:	41 83 f8 01          	cmp    $0x1,%r8d
    662d:	74 0e                	je     663d <sendm+0xad>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    662f:	83 b9 18 03 00 00 02 	cmpl   $0x2,0x318(%rcx)
    6636:	75 05                	jne    663d <sendm+0xad>
    6638:	45 85 c0             	test   %r8d,%r8d
    663b:	74 b1                	je     65ee <sendm+0x5e>
        if (data->sending == 1) {
    663d:	83 be 80 01 00 00 01 	cmpl   $0x1,0x180(%rsi)
    6644:	74 2a                	je     6670 <sendm+0xe0>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6646:	83 c0 01             	add    $0x1,%eax
    6649:	48 83 c2 38          	add    $0x38,%rdx
          them->available_receiving = 1;
    664d:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    6657:	44 39 e0             	cmp    %r12d,%eax
    665a:	75 9e                	jne    65fa <sendm+0x6a>
      asm volatile ("sfence" ::: "memory");
    665c:	0f ae f8             	sfence
}
    665f:	31 c0                	xor    %eax,%eax
    6661:	5b                   	pop    %rbx
    6662:	5d                   	pop    %rbp
    6663:	41 5c                	pop    %r12
    6665:	41 5d                	pop    %r13
    6667:	41 5e                	pop    %r14
    6669:	41 5f                	pop    %r15
    666b:	c3                   	ret
    666c:	0f 1f 40 00          	nopl   0x0(%rax)
          for (; them->messages_count < min;) {
    6670:	48 63 99 88 00 00 00 	movslq 0x88(%rcx),%rbx
    6677:	48 39 df             	cmp    %rbx,%rdi
    667a:	0f 8d b2 00 00 00    	jge    6732 <sendm+0x1a2>
    6680:	49 89 db             	mov    %rbx,%r11
    6683:	4c 8b be 08 01 00 00 	mov    0x108(%rsi),%r15
    668a:	4c 8b b1 08 03 00 00 	mov    0x308(%rcx),%r14
    6691:	49 29 fb             	sub    %rdi,%r11
            them->messages[them->messages_count++] = data->message; 
    6694:	4c 8b 11             	mov    (%rcx),%r10
    6697:	4d 8d 43 ff          	lea    -0x1(%r11),%r8
    669b:	4c 89 7c 24 e8       	mov    %r15,-0x18(%rsp)
    66a0:	4c 89 74 24 f0       	mov    %r14,-0x10(%rsp)
    66a5:	49 83 f8 02          	cmp    $0x2,%r8
    66a9:	0f 86 11 01 00 00    	jbe    67c0 <sendm+0x230>
    66af:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    66b7:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    66bf:	4f 8d 34 0a          	lea    (%r10,%r9,1),%r14
    66c3:	4c 8d be 88 01 00 00 	lea    0x188(%rsi),%r15
    66ca:	4b 8d 2c 02          	lea    (%r10,%r8,1),%rbp
    66ce:	4d 39 f7             	cmp    %r14,%r15
    66d1:	73 75                	jae    6748 <sendm+0x1b8>
    66d3:	4c 8d b6 90 01 00 00 	lea    0x190(%rsi),%r14
    66da:	4c 39 f5             	cmp    %r14,%rbp
    66dd:	73 69                	jae    6748 <sendm+0x1b8>
    66df:	4d 01 d0             	add    %r10,%r8
    66e2:	4b 8d 3c 0a          	lea    (%r10,%r9,1),%rdi
    66e6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    66f0:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
          for (; them->messages_count < min;) {
    66f7:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    66fb:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    66ff:	4c 39 c7             	cmp    %r8,%rdi
    6702:	75 ec                	jne    66f0 <sendm+0x160>
    6704:	0f 1f 40 00          	nopl   0x0(%rax)
    6708:	48 8b 7c 24 e8       	mov    -0x18(%rsp),%rdi
    670d:	4c 01 df             	add    %r11,%rdi
    6710:	48 89 be 08 01 00 00 	mov    %rdi,0x108(%rsi)
    6717:	48 8b 7c 24 f0       	mov    -0x10(%rsp),%rdi
    671c:	48 89 99 80 00 00 00 	mov    %rbx,0x80(%rcx)
    6723:	4c 01 df             	add    %r11,%rdi
    6726:	48 89 b9 08 03 00 00 	mov    %rdi,0x308(%rcx)
    672d:	4d 89 4c da f8       	mov    %r9,-0x8(%r10,%rbx,8)
          them->available_sending = 0;
    6732:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
    673c:	e9 05 ff ff ff       	jmp    6646 <sendm+0xb6>
    6741:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6748:	4d 89 de             	mov    %r11,%r14
    674b:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
    6752:	49 89 e8             	mov    %rbp,%r8
    6755:	49 d1 ee             	shr    %r14
    6758:	49 c1 e6 04          	shl    $0x4,%r14
    675c:	66 49 0f 6e c1       	movq   %r9,%xmm0
    6761:	4e 8d 7c 35 00       	lea    0x0(%rbp,%r14,1),%r15
    6766:	41 83 e6 10          	and    $0x10,%r14d
    676a:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    676e:	74 10                	je     6780 <sendm+0x1f0>
            them->messages[them->messages_count++] = data->message; 
    6770:	49 83 c0 10          	add    $0x10,%r8
    6774:	0f 11 45 00          	movups %xmm0,0x0(%rbp)
          for (; them->messages_count < min;) {
    6778:	4d 39 f8             	cmp    %r15,%r8
    677b:	74 15                	je     6792 <sendm+0x202>
    677d:	0f 1f 00             	nopl   (%rax)
            them->messages[them->messages_count++] = data->message; 
    6780:	41 0f 11 00          	movups %xmm0,(%r8)
    6784:	49 83 c0 20          	add    $0x20,%r8
    6788:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    678d:	4d 39 f8             	cmp    %r15,%r8
    6790:	75 ee                	jne    6780 <sendm+0x1f0>
    6792:	4d 89 d8             	mov    %r11,%r8
    6795:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6799:	4c 01 c7             	add    %r8,%rdi
    679c:	41 f6 c3 01          	test   $0x1,%r11b
    67a0:	0f 84 62 ff ff ff    	je     6708 <sendm+0x178>
            them->messages[them->messages_count++] = data->message; 
    67a6:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
    67ad:	4d 89 0c fa          	mov    %r9,(%r10,%rdi,8)
          for (; them->messages_count < min;) {
    67b1:	e9 52 ff ff ff       	jmp    6708 <sendm+0x178>
    67b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    67c0:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    67c8:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    67d0:	e9 0a ff ff ff       	jmp    66df <sendm+0x14f>
    67d5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

00000000000067e0 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    67e0:	f3 0f 1e fa          	endbr64
    67e4:	41 57                	push   %r15
    67e6:	41 56                	push   %r14
    67e8:	41 55                	push   %r13
    67ea:	41 54                	push   %r12
    67ec:	55                   	push   %rbp
    67ed:	53                   	push   %rbx
      receive(data);
    67ee:	48 89 fb             	mov    %rdi,%rbx
int barriered_work(struct BarrierTask *data) {
    67f1:	48 83 ec 38          	sub    $0x38,%rsp
        int t = data->task_index;
    67f5:	4c 63 67 04          	movslq 0x4(%rdi),%r12
int barriered_work(struct BarrierTask *data) {
    67f9:	48 89 3c 24          	mov    %rdi,(%rsp)
  if (data->thread_index == data->task_index) {
    67fd:	44 39 a7 30 01 00 00 	cmp    %r12d,0x130(%rdi)
    6804:	74 52                	je     6858 <barriered_work+0x78>
    receive(data);
    6806:	e8 15 fc ff ff       	call   6420 <receive>
    while (data->scheduled == 1) {
    680b:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6812:	75 20                	jne    6834 <barriered_work+0x54>
    6814:	48 8b 04 24          	mov    (%rsp),%rax
    6818:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
      data->n++;
    6820:	48 83 80 08 01 00 00 01 	addq   $0x1,0x108(%rax)
      asm volatile ("sfence" ::: "memory");
    6828:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    682b:	83 b8 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rax)
    6832:	74 ec                	je     6820 <barriered_work+0x40>
    sendm(data);
    6834:	48 8b 3c 24          	mov    (%rsp),%rdi
    6838:	e8 53 fd ff ff       	call   6590 <sendm>
  asm volatile ("sfence" ::: "memory");
    683d:	0f ae f8             	sfence
}
    6840:	48 83 c4 38          	add    $0x38,%rsp
    6844:	31 c0                	xor    %eax,%eax
    6846:	5b                   	pop    %rbx
    6847:	5d                   	pop    %rbp
    6848:	41 5c                	pop    %r12
    684a:	41 5d                	pop    %r13
    684c:	41 5e                	pop    %r14
    684e:	41 5f                	pop    %r15
    6850:	c3                   	ret
    6851:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      receive(data);
    6858:	e8 c3 fb ff ff       	call   6420 <receive>
      data->swap++;
    685d:	8b 83 98 01 00 00    	mov    0x198(%rbx),%eax
    6863:	89 44 24 08          	mov    %eax,0x8(%rsp)
    6867:	83 c0 01             	add    $0x1,%eax
    686a:	89 83 98 01 00 00    	mov    %eax,0x198(%rbx)
        if (data->swap % 2 == 0) {
    6870:	a8 01                	test   $0x1,%al
    6872:	0f 84 70 02 00 00    	je     6ae8 <barriered_work+0x308>
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6878:	48 8b 04 24          	mov    (%rsp),%rax
    687c:	48 8b b8 28 01 00 00 	mov    0x128(%rax),%rdi
          int k = data->group;
    6883:	48 8b 04 24          	mov    (%rsp),%rax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6887:	48 63 97 c4 00 00 00 	movslq 0xc4(%rdi),%rdx
          int k = data->group;
    688e:	8b 80 94 01 00 00    	mov    0x194(%rax),%eax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6894:	85 d2                	test   %edx,%edx
    6896:	0f 8e 3b 01 00 00    	jle    69d7 <barriered_work+0x1f7>
            int y = (k * data->thread->threads_per_group) + d;
    689c:	0f af c2             	imul   %edx,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    689f:	49 c1 e4 09          	shl    $0x9,%r12
              int next_task = abs((t + 1) % (data->thread_count));
    68a3:	48 8b 1c 24          	mov    (%rsp),%rbx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    68a7:	4c 89 64 24 10       	mov    %r12,0x10(%rsp)
              int next_task = abs((t + 1) % (data->thread_count));
    68ac:	44 8b 8b 34 01 00 00 	mov    0x134(%rbx),%r9d
    68b3:	48 98                	cltq
    68b5:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    68b9:	48 8d 34 c9          	lea    (%rcx,%rcx,8),%rsi
    68bd:	48 8b 4f 20          	mov    0x20(%rdi),%rcx
    68c1:	4c 8d 34 f1          	lea    (%rcx,%rsi,8),%r14
    68c5:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    68cd:	48 29 c1             	sub    %rax,%rcx
    68d0:	48 01 d0             	add    %rdx,%rax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    68d3:	4d 89 f2             	mov    %r14,%r10
    68d6:	4d 89 f7             	mov    %r14,%r15
    68d9:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
    68e1:	4c 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r8
    68e9:	48 29 c5             	sub    %rax,%rbp
    68ec:	4d 89 c3             	mov    %r8,%r11
    68ef:	4c 89 c3             	mov    %r8,%rbx
    68f2:	48 c1 e5 03          	shl    $0x3,%rbp
    68f6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6900:	4d 8b 62 38          	mov    0x38(%r10),%r12
    6904:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6909:	48 89 de             	mov    %rbx,%rsi
    690c:	4c 89 ff             	mov    %r15,%rdi
    690f:	4d 89 d0             	mov    %r10,%r8
    6912:	4d 8b b4 04 70 01 00 00 	mov    0x170(%r12,%rax,1),%r14
    691a:	eb 18                	jmp    6934 <barriered_work+0x154>
    691c:	0f 1f 40 00          	nopl   0x0(%rax)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6920:	48 83 c6 38          	add    $0x38,%rsi
    6924:	48 81 c7 d8 00 00 00 	add    $0xd8,%rdi
    692b:	48 39 ee             	cmp    %rbp,%rsi
    692e:	0f 84 8c 00 00 00    	je     69c0 <barriered_work+0x1e0>
              if (kind == MAILBOX_FRIEND) {
    6934:	41 83 7c 36 30 01    	cmpl   $0x1,0x30(%r14,%rsi,1)
    693a:	75 e4                	jne    6920 <barriered_work+0x140>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    693c:	4c 8b 57 38          	mov    0x38(%rdi),%r10
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6940:	45 85 c9             	test   %r9d,%r9d
    6943:	7e db                	jle    6920 <barriered_work+0x140>
    6945:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    694a:	49 81 c2 70 01 00 00 	add    $0x170,%r10
    6951:	31 c9                	xor    %ecx,%ecx
    6953:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                    int next_task = abs((nn + 1) % (data->thread_count));
    6958:	83 c1 01             	add    $0x1,%ecx
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    695b:	4d 8b 2a             	mov    (%r10),%r13
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    695e:	49 81 c2 00 02 00 00 	add    $0x200,%r10
                    int next_task = abs((nn + 1) % (data->thread_count));
    6965:	89 c8                	mov    %ecx,%eax
    6967:	99                   	cltd
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6968:	4d 01 dd             	add    %r11,%r13
                    int next_task = abs((nn + 1) % (data->thread_count));
    696b:	41 f7 f9             	idiv   %r9d
    return mailbox->lower;
    696e:	4d 8b 75 00          	mov    0x0(%r13),%r14
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6972:	48 63 d2             	movslq %edx,%rdx
    6975:	48 c1 e2 09          	shl    $0x9,%rdx
    6979:	49 8b 84 14 70 01 00 00 	mov    0x170(%r12,%rdx,1),%rax
    mailbox->lower = data;
    6981:	49 8b 55 08          	mov    0x8(%r13),%rdx
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6985:	48 01 f0             	add    %rsi,%rax
    return mailbox->higher;
    6988:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    698c:	48 89 10             	mov    %rdx,(%rax)
    return mailbox->lower;
    698f:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
    mailbox->lower = data;
    6994:	41 0f 11 45 00       	movups %xmm0,0x0(%r13)
    mailbox->higher = data;
    6999:	4c 89 70 08          	mov    %r14,0x8(%rax)
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    699d:	41 39 c9             	cmp    %ecx,%r9d
    69a0:	75 b6                	jne    6958 <barriered_work+0x178>
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    69a2:	48 83 c6 38          	add    $0x38,%rsi
    69a6:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    69ab:	48 81 c7 d8 00 00 00 	add    $0xd8,%rdi
    69b2:	48 39 ee             	cmp    %rbp,%rsi
    69b5:	0f 85 79 ff ff ff    	jne    6934 <barriered_work+0x154>
    69bb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    69c0:	4d 89 c2             	mov    %r8,%r10
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    69c3:	49 83 c3 38          	add    $0x38,%r11
    69c7:	49 81 c2 d8 00 00 00 	add    $0xd8,%r10
    69ce:	49 39 eb             	cmp    %rbp,%r11
    69d1:	0f 85 29 ff ff ff    	jne    6900 <barriered_work+0x120>
      receive(data);
    69d7:	48 8b 1c 24          	mov    (%rsp),%rbx
    69db:	48 89 df             	mov    %rbx,%rdi
    69de:	e8 3d fa ff ff       	call   6420 <receive>
      asm volatile ("sfence" ::: "memory");
    69e3:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    69e6:	48 89 d8             	mov    %rbx,%rax
    69e9:	48 8b 9b 60 01 00 00 	mov    0x160(%rbx),%rbx
    69f0:	31 ff                	xor    %edi,%edi
    69f2:	48 89 de             	mov    %rbx,%rsi
    69f5:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    69fa:	48 89 c3             	mov    %rax,%rbx
    69fd:	48 c1 e6 05          	shl    $0x5,%rsi
    6a01:	48 03 b0 50 01 00 00 	add    0x150(%rax),%rsi
    6a08:	e8 63 b9 ff ff       	call   2370 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6a0d:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6a14:	48 89 df             	mov    %rbx,%rdi
    6a17:	48 8b 2c 24          	mov    (%rsp),%rbp
    6a1b:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6a1f:	8b 5a 10             	mov    0x10(%rdx),%ebx
    6a22:	83 c3 01             	add    $0x1,%ebx
    while (data->scheduled == 1) {
    6a25:	83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rdi)
    int modcount = ++data->thread->protected_state->modcount;
    6a2c:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6a2f:	74 0e                	je     6a3f <barriered_work+0x25f>
    6a31:	eb 61                	jmp    6a94 <barriered_work+0x2b4>
    6a33:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (modcount != data->thread->protected_state->modcount) {
    6a38:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6a3f:	48 63 95 30 01 00 00 	movslq 0x130(%rbp),%rdx
    6a46:	48 8b 40 18          	mov    0x18(%rax),%rax
    6a4a:	48 63 7d 04          	movslq 0x4(%rbp),%rdi
      data->n++;
    6a4e:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6a56:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6a5a:	48 c1 e7 09          	shl    $0x9,%rdi
    6a5e:	48 03 78 38          	add    0x38(%rax),%rdi
    6a62:	ff 95 20 01 00 00    	call   *0x120(%rbp)
      asm volatile ("sfence" ::: "memory");
    6a68:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6a6b:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    6a72:	74 c4                	je     6a38 <barriered_work+0x258>
    if (modcount != data->thread->protected_state->modcount) {
    6a74:	48 8b 04 24          	mov    (%rsp),%rax
    6a78:	48 8b 80 28 01 00 00 	mov    0x128(%rax),%rax
    6a7f:	48 8b 40 48          	mov    0x48(%rax),%rax
    6a83:	3b 58 10             	cmp    0x10(%rax),%ebx
    6a86:	74 0c                	je     6a94 <barriered_work+0x2b4>
    6a88:	48 8d 3d b7 17 00 00 	lea    0x17b7(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6a8f:	e8 bc b8 ff ff       	call   2350 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6a94:	48 8b 1c 24          	mov    (%rsp),%rbx
    6a98:	31 ff                	xor    %edi,%edi
    6a9a:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6aa1:	48 89 c6             	mov    %rax,%rsi
    6aa4:	48 89 04 24          	mov    %rax,(%rsp)
    6aa8:	48 c1 e6 05          	shl    $0x5,%rsi
    6aac:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6ab3:	48 83 c6 10          	add    $0x10,%rsi
    6ab7:	e8 b4 b8 ff ff       	call   2370 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6abc:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    sendm(data);
    6ac3:	48 89 df             	mov    %rbx,%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6ac6:	48 89 04 24          	mov    %rax,(%rsp)
    6aca:	48 83 c0 01          	add    $0x1,%rax
    6ace:	48 99                	cqto
    6ad0:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6ad7:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    sendm(data);
    6ade:	e8 ad fa ff ff       	call   6590 <sendm>
    6ae3:	e9 55 fd ff ff       	jmp    683d <barriered_work+0x5d>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6ae8:	44 8b 93 40 01 00 00 	mov    0x140(%rbx),%r10d
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6aef:	48 8b bb 28 01 00 00 	mov    0x128(%rbx),%rdi
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6af6:	45 85 d2             	test   %r10d,%r10d
    6af9:	0f 8e 84 fd ff ff    	jle    6883 <barriered_work+0xa3>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    6aff:	49 63 c4             	movslq %r12d,%rax
    6b02:	31 f6                	xor    %esi,%esi
    6b04:	31 d2                	xor    %edx,%edx
    6b06:	44 89 64 24 2c       	mov    %r12d,0x2c(%rsp)
    6b0b:	48 c1 e0 09          	shl    $0x9,%rax
    6b0f:	48 89 f3             	mov    %rsi,%rbx
    6b12:	45 89 d1             	mov    %r10d,%r9d
    6b15:	49 89 d6             	mov    %rdx,%r14
    6b18:	48 89 c6             	mov    %rax,%rsi
    6b1b:	eb 17                	jmp    6b34 <barriered_work+0x354>
    6b1d:	0f 1f 00             	nopl   (%rax)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6b20:	48 83 c3 01          	add    $0x1,%rbx
    6b24:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    6b2b:	41 39 d9             	cmp    %ebx,%r9d
    6b2e:	0f 8e 68 02 00 00    	jle    6d9c <barriered_work+0x5bc>
              int b = data->thread->real_thread_index;
    6b34:	48 63 57 08          	movslq 0x8(%rdi),%rdx
              if (y == b) { continue; }
    6b38:	39 da                	cmp    %ebx,%edx
    6b3a:	74 e4                	je     6b20 <barriered_work+0x340>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    6b3c:	4c 63 ea             	movslq %edx,%r13
    6b3f:	4c 8b 47 20          	mov    0x20(%rdi),%r8
    6b43:	4b 8d 44 6d 00       	lea    0x0(%r13,%r13,2),%rax
    6b48:	4c 8d 24 c0          	lea    (%rax,%rax,8),%r12
    6b4c:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    6b54:	49 c1 e4 03          	shl    $0x3,%r12
    6b58:	48 29 d8             	sub    %rbx,%rax
    6b5b:	4f 8b 44 20 38       	mov    0x38(%r8,%r12,1),%r8
    6b60:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
    6b68:	4d 8b 84 30 70 01 00 00 	mov    0x170(%r8,%rsi,1),%r8
    6b70:	41 83 7c c0 30 02    	cmpl   $0x2,0x30(%r8,%rax,8)
    6b76:	75 a8                	jne    6b20 <barriered_work+0x340>
  if (a < b) { return a; }
    6b78:	39 da                	cmp    %ebx,%edx
    6b7a:	0f 8c 26 02 00 00    	jl     6da6 <barriered_work+0x5c6>
  if (b < a) { return b; }
    6b80:	0f 4f d3             	cmovg  %ebx,%edx
    6b83:	4c 89 e8             	mov    %r13,%rax
                    pthread_mutex_lock(&data->thread->swapmutex[min]);   
    6b86:	4c 63 fa             	movslq %edx,%r15
                    pthread_mutex_lock(&data->thread->swapmutex[max]);   
    6b89:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    6b8d:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    6b92:	48 c1 e0 03          	shl    $0x3,%rax
    6b96:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6b9b:	48 03 87 c8 00 00 00 	add    0xc8(%rdi),%rax
    6ba2:	48 89 c7             	mov    %rax,%rdi
    6ba5:	e8 16 ba ff ff       	call   25c0 <pthread_mutex_lock@plt>
                    pthread_mutex_lock(&data->thread->swapmutex[min]);   
    6baa:	4b 8d 04 bf          	lea    (%r15,%r15,4),%rax
    6bae:	4c 8b 3c 24          	mov    (%rsp),%r15
    6bb2:	4c 8d 14 c5 00 00 00 00 	lea    0x0(,%rax,8),%r10
    6bba:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    6bc1:	4c 89 d7             	mov    %r10,%rdi
    6bc4:	4c 89 54 24 10       	mov    %r10,0x10(%rsp)
    6bc9:	48 03 b8 c8 00 00 00 	add    0xc8(%rax),%rdi
    6bd0:	e8 eb b9 ff ff       	call   25c0 <pthread_mutex_lock@plt>
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6bd5:	4c 89 f8             	mov    %r15,%rax
    6bd8:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
    6bdd:	45 8b bf 34 01 00 00 	mov    0x134(%r15),%r15d
    6be4:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    6be9:	45 85 ff             	test   %r15d,%r15d
    6bec:	0f 8e c3 01 00 00    	jle    6db5 <barriered_work+0x5d5>
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6bf2:	48 8b 80 28 01 00 00 	mov    0x128(%rax),%rax
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6bf9:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6bfe:	31 c9                	xor    %ecx,%ecx
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6c00:	bf 70 01 00 00       	mov    $0x170,%edi
    6c05:	4e 8d 04 ed 00 00 00 00 	lea    0x0(,%r13,8),%r8
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6c0d:	48 8b 50 20          	mov    0x20(%rax),%rdx
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6c11:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    6c16:	4d 29 e8             	sub    %r13,%r8
    6c19:	49 c1 e0 03          	shl    $0x3,%r8
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6c1d:	4e 8b 5c 22 38       	mov    0x38(%rdx,%r12,1),%r11
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6c22:	4e 8b 4c 32 38       	mov    0x38(%rdx,%r14,1),%r9
    6c27:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
                      int next_task = abs((nn + 1) % data->thread_count);
    6c30:	83 c1 01             	add    $0x1,%ecx
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6c33:	49 8b 34 3b          	mov    (%r11,%rdi,1),%rsi
                      int next_task = abs((nn + 1) % data->thread_count);
    6c37:	89 c8                	mov    %ecx,%eax
    6c39:	99                   	cltd
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6c3a:	48 01 ee             	add    %rbp,%rsi
                      int next_task = abs((nn + 1) % data->thread_count);
    6c3d:	41 f7 ff             	idiv   %r15d
    return mailbox->lower;
    6c40:	4c 8b 2e             	mov    (%rsi),%r13
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6c43:	48 63 d2             	movslq %edx,%rdx
    6c46:	48 c1 e2 09          	shl    $0x9,%rdx
    6c4a:	49 8b 84 11 70 01 00 00 	mov    0x170(%r9,%rdx,1),%rax
    mailbox->lower = data;
    6c52:	48 8b 56 08          	mov    0x8(%rsi),%rdx
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6c56:	4c 01 c0             	add    %r8,%rax
    return mailbox->higher;
    6c59:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    6c5d:	48 89 10             	mov    %rdx,(%rax)
    return mailbox->lower;
    6c60:	66 0f 6f c8          	movdqa %xmm0,%xmm1
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6c64:	0f 12 d0             	movhlps %xmm0,%xmm2
    return mailbox->lower;
    6c67:	66 0f c6 c8 01       	shufpd $0x1,%xmm0,%xmm1
    mailbox->lower = data;
    6c6c:	0f 11 0e             	movups %xmm1,(%rsi)
    mailbox->higher = data;
    6c6f:	4c 89 68 08          	mov    %r13,0x8(%rax)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6c73:	49 8b 14 39          	mov    (%r9,%rdi,1),%rdx
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6c77:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6c7e:	48 8b 76 08          	mov    0x8(%rsi),%rsi
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6c82:	48 8b 00             	mov    (%rax),%rax
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6c85:	4a 8b 54 02 08       	mov    0x8(%rdx,%r8,1),%rdx
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6c8a:	c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    6c94:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    6c9e:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6ca8:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    6cb2:	66 48 0f 7e d2       	movq   %xmm2,%rdx
    6cb7:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    6cc1:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    6ccb:	44 39 f9             	cmp    %r15d,%ecx
    6cce:	0f 85 5c ff ff ff    	jne    6c30 <barriered_work+0x450>
    6cd4:	4c 8b 6c 24 10       	mov    0x10(%rsp),%r13
    6cd9:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    6cde:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
                    pthread_mutex_unlock(&data->thread->swapmutex[min]);
    6ce3:	48 8b b8 c8 00 00 00 	mov    0xc8(%rax),%rdi
    6cea:	48 89 74 24 10       	mov    %rsi,0x10(%rsp)
    6cef:	4c 01 d7             	add    %r10,%rdi
    6cf2:	e8 99 b7 ff ff       	call   2490 <pthread_mutex_unlock@plt>
                    pthread_mutex_unlock(&data->thread->swapmutex[max]);
    6cf7:	4c 8b 3c 24          	mov    (%rsp),%r15
    6cfb:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6d00:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    6d07:	48 03 b8 c8 00 00 00 	add    0xc8(%rax),%rdi
    6d0e:	e8 7d b7 ff ff       	call   2490 <pthread_mutex_unlock@plt>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6d13:	49 63 87 34 01 00 00 	movslq 0x134(%r15),%rax
    6d1a:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    6d1f:	85 c0                	test   %eax,%eax
    6d21:	0f 8e 9e 00 00 00    	jle    6dc5 <barriered_work+0x5e5>
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6d27:	48 8b 3c 24          	mov    (%rsp),%rdi
    6d2b:	48 c1 e0 09          	shl    $0x9,%rax
    6d2f:	4c 8d 80 70 01 00 00 	lea    0x170(%rax),%r8
    6d36:	b8 70 01 00 00       	mov    $0x170,%eax
    6d3b:	48 8b bf 28 01 00 00 	mov    0x128(%rdi),%rdi
    6d42:	48 8b 57 20          	mov    0x20(%rdi),%rdx
    6d46:	4e 8b 5c 22 38       	mov    0x38(%rdx,%r12,1),%r11
    6d4b:	4e 8d 24 ed 00 00 00 00 	lea    0x0(,%r13,8),%r12
    6d53:	4e 8b 4c 32 38       	mov    0x38(%rdx,%r14,1),%r9
    6d58:	4d 29 ec             	sub    %r13,%r12
    6d5b:	49 c1 e4 03          	shl    $0x3,%r12
    6d5f:	90                   	nop
    6d60:	49 8b 14 01          	mov    (%r9,%rax,1),%rdx
    6d64:	49 8b 0c 03          	mov    (%r11,%rax,1),%rcx
    6d68:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    6d6c:	48 39 14 29          	cmp    %rdx,(%rcx,%rbp,1)
    6d70:	74 6a                	je     6ddc <barriered_work+0x5fc>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6d72:	48 05 00 02 00 00    	add    $0x200,%rax
    6d78:	49 39 c0             	cmp    %rax,%r8
    6d7b:	75 e3                	jne    6d60 <barriered_work+0x580>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6d7d:	48 8b 04 24          	mov    (%rsp),%rax
    6d81:	48 83 c3 01          	add    $0x1,%rbx
    6d85:	49 81 c6 d8 00 00 00 	add    $0xd8,%r14
    6d8c:	44 8b 88 40 01 00 00 	mov    0x140(%rax),%r9d
    6d93:	41 39 d9             	cmp    %ebx,%r9d
    6d96:	0f 8f 98 fd ff ff    	jg     6b34 <barriered_work+0x354>
    6d9c:	4c 63 64 24 2c       	movslq 0x2c(%rsp),%r12
    6da1:	e9 dd fa ff ff       	jmp    6883 <barriered_work+0xa3>
  if (b > a) { return b; }
    6da6:	48 63 c3             	movslq %ebx,%rax
    6da9:	4d 89 ef             	mov    %r13,%r15
    6dac:	48 0f 4d c2          	cmovge %rdx,%rax
    6db0:	e9 d4 fd ff ff       	jmp    6b89 <barriered_work+0x3a9>
                    pthread_mutex_unlock(&data->thread->swapmutex[min]);
    6db5:	48 8b 04 24          	mov    (%rsp),%rax
    6db9:	48 8b 80 28 01 00 00 	mov    0x128(%rax),%rax
    6dc0:	e9 1e ff ff ff       	jmp    6ce3 <barriered_work+0x503>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6dc5:	48 8b 04 24          	mov    (%rsp),%rax
    6dc9:	44 8b 88 40 01 00 00 	mov    0x140(%rax),%r9d
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6dd0:	48 8b b8 28 01 00 00 	mov    0x128(%rax),%rdi
    6dd7:	e9 44 fd ff ff       	jmp    6b20 <barriered_work+0x340>
    6ddc:	bf 01 00 00 00       	mov    $0x1,%edi
    6de1:	48 8d 35 43 14 00 00 	lea    0x1443(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6de8:	31 c0                	xor    %eax,%eax
    6dea:	e8 f1 b6 ff ff       	call   24e0 <__printf_chk@plt>
                          exit(1);
    6def:	bf 01 00 00 00       	mov    $0x1,%edi
    6df4:	e8 47 b7 ff ff       	call   2540 <exit@plt>
    6df9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006e00 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6e00:	f3 0f 1e fa          	endbr64
    6e04:	53                   	push   %rbx
    6e05:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6e08:	e8 23 f2 ff ff       	call   6030 <barriered_work_ingest>
  barriered_work(data);
    6e0d:	48 89 df             	mov    %rbx,%rdi
}
    6e10:	5b                   	pop    %rbx
  barriered_work(data);
    6e11:	e9 ca f9 ff ff       	jmp    67e0 <barriered_work>
    6e16:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006e20 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6e20:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6e24:	85 f6                	test   %esi,%esi
    6e26:	74 10                	je     6e38 <mailboxkind+0x18>
  return NULL;
    6e28:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    6e2a:	83 fe 01             	cmp    $0x1,%esi
    6e2d:	74 01                	je     6e30 <mailboxkind+0x10>
}
    6e2f:	c3                   	ret
    return mailbox->higher;
    6e30:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    6e34:	c3                   	ret
    6e35:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
    6e38:	48 8b 07             	mov    (%rdi),%rax
    6e3b:	c3                   	ret
    6e3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006e40 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    6e40:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6e44:	85 d2                	test   %edx,%edx
    6e46:	75 08                	jne    6e50 <setmailboxkind+0x10>
    mailbox->lower = data;
    6e48:	48 89 37             	mov    %rsi,(%rdi)
}
    6e4b:	31 c0                	xor    %eax,%eax
    6e4d:	c3                   	ret
    6e4e:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    6e50:	83 fa 01             	cmp    $0x1,%edx
    6e53:	74 13                	je     6e68 <setmailboxkind+0x28>
  if (kind == 2) {
    6e55:	83 fa 02             	cmp    $0x2,%edx
    6e58:	75 f1                	jne    6e4b <setmailboxkind+0xb>
    mailbox->pending = data;
    6e5a:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
    6e5e:	31 c0                	xor    %eax,%eax
    6e60:	c3                   	ret
    6e61:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    mailbox->higher = data;
    6e68:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    6e6c:	31 c0                	xor    %eax,%eax
    6e6e:	c3                   	ret
    6e6f:	90                   	nop

0000000000006e70 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6e70:	f3 0f 1e fa          	endbr64
}
    6e74:	31 c0                	xor    %eax,%eax
    6e76:	c3                   	ret
    6e77:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006e80 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6e80:	f3 0f 1e fa          	endbr64
    6e84:	31 c0                	xor    %eax,%eax
    6e86:	c3                   	ret
    6e87:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006e90 <after>:
int after(struct timespec left, struct timespec right) {
    6e90:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6e94:	31 c0                	xor    %eax,%eax
    6e96:	48 39 d7             	cmp    %rdx,%rdi
    6e99:	7e 08                	jle    6ea3 <after+0x13>
    6e9b:	31 c0                	xor    %eax,%eax
    6e9d:	48 39 ce             	cmp    %rcx,%rsi
    6ea0:	0f 9f c0             	setg   %al
}
    6ea3:	c3                   	ret
    6ea4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6eaf:	90                   	nop

0000000000006eb0 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6eb0:	f3 0f 1e fa          	endbr64
    6eb4:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6eb9:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    6ebe:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6ec0:	48 39 d7             	cmp    %rdx,%rdi
    6ec3:	7f 18                	jg     6edd <within+0x2d>
    6ec5:	4d 39 d8             	cmp    %r11,%r8
    6ec8:	0f 9e c2             	setle  %dl
    6ecb:	48 39 ce             	cmp    %rcx,%rsi
    6ece:	0f 9e c0             	setle  %al
    6ed1:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6ed3:	31 c0                	xor    %eax,%eax
    6ed5:	4d 39 d1             	cmp    %r10,%r9
    6ed8:	0f 9e c0             	setle  %al
    6edb:	21 d0                	and    %edx,%eax
}
    6edd:	c3                   	ret
    6ede:	66 90                	xchg   %ax,%ax

0000000000006ee0 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6ee0:	f3 0f 1e fa          	endbr64
    6ee4:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6ee9:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6eee:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6ef3:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6ef8:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6efd:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6f02:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6f07:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6f0c:	48 39 fe             	cmp    %rdi,%rsi
    6f0f:	7d 2f                	jge    6f40 <overlap+0x60>
    6f11:	48 39 ca             	cmp    %rcx,%rdx
    6f14:	7d 62                	jge    6f78 <overlap+0x98>
    6f16:	4d 39 da             	cmp    %r11,%r10
    6f19:	7d 0e                	jge    6f29 <overlap+0x49>
    return 1;
    6f1b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6f20:	4d 39 c1             	cmp    %r8,%r9
    6f23:	0f 8c 7f 00 00 00    	jl     6fa8 <overlap+0xc8>
  return 0;
    6f29:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f2b:	4d 39 c1             	cmp    %r8,%r9
    6f2e:	7f 4c                	jg     6f7c <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6f30:	31 c0                	xor    %eax,%eax
    6f32:	4d 39 da             	cmp    %r11,%r10
    6f35:	0f 9e c0             	setle  %al
    6f38:	c3                   	ret
    6f39:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6f40:	7e 4e                	jle    6f90 <overlap+0xb0>
    6f42:	48 39 ca             	cmp    %rcx,%rdx
    6f45:	7f 39                	jg     6f80 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f47:	75 31                	jne    6f7a <overlap+0x9a>
    6f49:	4d 39 c1             	cmp    %r8,%r9
    6f4c:	7c 2c                	jl     6f7a <overlap+0x9a>
    return 1;
    6f4e:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6f53:	4d 39 da             	cmp    %r11,%r10
    6f56:	7d 24                	jge    6f7c <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f58:	48 39 ca             	cmp    %rcx,%rdx
    6f5b:	0f 94 c2             	sete   %dl
    6f5e:	48 39 fe             	cmp    %rdi,%rsi
    6f61:	0f 94 c0             	sete   %al
    6f64:	21 c2                	and    %eax,%edx
    6f66:	31 c0                	xor    %eax,%eax
    6f68:	4d 39 c1             	cmp    %r8,%r9
    6f6b:	0f 94 c0             	sete   %al
    6f6e:	21 d0                	and    %edx,%eax
    6f70:	c3                   	ret
    6f71:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6f78:	74 af                	je     6f29 <overlap+0x49>
  return 0;
    6f7a:	31 c0                	xor    %eax,%eax
}
    6f7c:	c3                   	ret
    6f7d:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6f80:	4d 39 da             	cmp    %r11,%r10
    6f83:	7e c4                	jle    6f49 <overlap+0x69>
    return 1;
    6f85:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6f8a:	4d 39 c1             	cmp    %r8,%r9
    6f8d:	7e ba                	jle    6f49 <overlap+0x69>
    6f8f:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6f90:	48 39 ca             	cmp    %rcx,%rdx
    6f93:	7c 94                	jl     6f29 <overlap+0x49>
    6f95:	4d 39 c1             	cmp    %r8,%r9
    6f98:	7d b4                	jge    6f4e <overlap+0x6e>
    6f9a:	48 39 ca             	cmp    %rcx,%rdx
    6f9d:	74 91                	je     6f30 <overlap+0x50>
    6f9f:	eb d9                	jmp    6f7a <overlap+0x9a>
    6fa1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6fa8:	c3                   	ret
    6fa9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006fb0 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6fb0:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6fb4:	85 f6                	test   %esi,%esi
    6fb6:	0f 8e 44 03 00 00    	jle    7300 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    6fbc:	41 57                	push   %r15
    6fbe:	41 89 f7             	mov    %esi,%r15d
    6fc1:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6fc3:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6fc6:	41 55                	push   %r13
    6fc8:	41 54                	push   %r12
    6fca:	55                   	push   %rbp
    6fcb:	53                   	push   %rbx
    6fcc:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6fd0:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6fd4:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6fd9:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6fde:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6fe1:	45 39 e6             	cmp    %r12d,%r14d
    6fe4:	0f 84 4e 02 00 00    	je     7238 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6fea:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6fef:	8b 50 08             	mov    0x8(%rax),%edx
    6ff2:	85 d2                	test   %edx,%edx
    6ff4:	0f 8e 3e 02 00 00    	jle    7238 <verify+0x288>
    6ffa:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    6fff:	31 c9                	xor    %ecx,%ecx
    7001:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    7006:	31 c0                	xor    %eax,%eax
    7008:	44 89 f2             	mov    %r14d,%edx
    700b:	bf 01 00 00 00       	mov    $0x1,%edi
    7010:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    7015:	48 8d 35 3a 12 00 00 	lea    0x123a(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    701c:	e8 bf b4 ff ff       	call   24e0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    7021:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7026:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    702b:	8b 40 08             	mov    0x8(%rax),%eax
    702e:	85 c0                	test   %eax,%eax
    7030:	0f 8e e6 01 00 00    	jle    721c <verify+0x26c>
    7036:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    7039:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    703e:	31 db                	xor    %ebx,%ebx
    7040:	48 c1 e0 09          	shl    $0x9,%rax
    7044:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    7049:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    704e:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7053:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    7058:	4c 8b 20             	mov    (%rax),%r12
    705b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7060:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    7065:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    706a:	49 89 de             	mov    %rbx,%r14
    706d:	48 8d 35 f7 11 00 00 	lea    0x11f7(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    7074:	49 c1 e6 09          	shl    $0x9,%r14
    7078:	bf 01 00 00 00       	mov    $0x1,%edi
    707d:	48 8b 45 00          	mov    0x0(%rbp),%rax
    7081:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    7089:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    708e:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    7096:	31 c0                	xor    %eax,%eax
    7098:	e8 43 b4 ff ff       	call   24e0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    709d:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    70a2:	4c 8b 20             	mov    (%rax),%r12
    70a5:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    70ae:	0f 8e 47 01 00 00    	jle    71fb <verify+0x24b>
    70b4:	4c 03 75 00          	add    0x0(%rbp),%r14
    70b8:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    70bd:	ba 01 00 00 00       	mov    $0x1,%edx
    70c2:	4d 89 f5             	mov    %r14,%r13
    70c5:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    70cc:	4d 85 f6             	test   %r14,%r14
    70cf:	0f 8e 21 01 00 00    	jle    71f6 <verify+0x246>
    70d5:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    70d8:	48 89 d5             	mov    %rdx,%rbp
    70db:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    70e0:	31 db                	xor    %ebx,%ebx
    70e2:	4d 89 f2             	mov    %r14,%r10
    70e5:	48 c1 e5 05          	shl    $0x5,%rbp
    70e9:	48 83 ed 20          	sub    $0x20,%rbp
    70ed:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    70f1:	49 89 ee             	mov    %rbp,%r14
    70f4:	48 89 dd             	mov    %rbx,%rbp
    70f7:	48 89 d3             	mov    %rdx,%rbx
    70fa:	eb 31                	jmp    712d <verify+0x17d>
    70fc:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    7100:	4c 39 c2             	cmp    %r8,%rdx
    7103:	0f 8d 57 01 00 00    	jge    7260 <verify+0x2b0>
    7109:	4c 39 df             	cmp    %r11,%rdi
    710c:	7e 05                	jle    7113 <verify+0x163>
    710e:	49 39 c1             	cmp    %rax,%r9
    7111:	7c 75                	jl     7188 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7113:	4c 39 df             	cmp    %r11,%rdi
    7116:	0f 8d ab 01 00 00    	jge    72c7 <verify+0x317>
    711c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7120:	48 83 c5 01          	add    $0x1,%rbp
    7124:	49 39 ea             	cmp    %rbp,%r10
    7127:	0f 8e a9 00 00 00    	jle    71d6 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    712d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    7134:	48 89 e8             	mov    %rbp,%rax
    7137:	48 c1 e0 05          	shl    $0x5,%rax
    713b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    7142:	4c 01 f2             	add    %r14,%rdx
    7145:	48 8b 08             	mov    (%rax),%rcx
    7148:	48 8b 78 10          	mov    0x10(%rax),%rdi
    714c:	48 8b 32             	mov    (%rdx),%rsi
    714f:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    7153:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    7157:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    715b:	48 8b 50 08          	mov    0x8(%rax),%rdx
    715f:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    7163:	48 39 f1             	cmp    %rsi,%rcx
    7166:	7c 98                	jl     7100 <verify+0x150>
    7168:	0f 8e 42 01 00 00    	jle    72b0 <verify+0x300>
    716e:	4c 39 c2             	cmp    %r8,%rdx
    7171:	0f 8f f9 00 00 00    	jg     7270 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7177:	75 a7                	jne    7120 <verify+0x170>
    7179:	4c 39 df             	cmp    %r11,%rdi
    717c:	7f a2                	jg     7120 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    717e:	49 39 c1             	cmp    %rax,%r9
    7181:	7c 9d                	jl     7120 <verify+0x170>
    7183:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    7188:	49 89 c1             	mov    %rax,%r9
    718b:	48 89 f9             	mov    %rdi,%rcx
    718e:	48 89 f2             	mov    %rsi,%rdx
    7191:	bf 01 00 00 00       	mov    $0x1,%edi
    7196:	48 8d 35 a3 14 00 00 	lea    0x14a3(%rip),%rsi        # 8640 <_IO_stdin_used+0x640>
    719d:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    719f:	48 83 c5 01          	add    $0x1,%rbp
    71a3:	e8 38 b3 ff ff       	call   24e0 <__printf_chk@plt>
    71a8:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    71ad:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    71b2:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    71b5:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    71ba:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    71c1:	4c 8b 20             	mov    (%rax),%r12
    71c4:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    71c9:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    71cd:	49 39 ea             	cmp    %rbp,%r10
    71d0:	0f 8f 57 ff ff ff    	jg     712d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    71d6:	48 89 da             	mov    %rbx,%rdx
    71d9:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    71e0:	7d 14                	jge    71f6 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    71e2:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    71e9:	48 83 c2 01          	add    $0x1,%rdx
    71ed:	4d 85 f6             	test   %r14,%r14
    71f0:	0f 8f e2 fe ff ff    	jg     70d8 <verify+0x128>
    71f6:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    71fb:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7200:	48 83 c3 01          	add    $0x1,%rbx
    7204:	39 58 08             	cmp    %ebx,0x8(%rax)
    7207:	0f 8f 53 fe ff ff    	jg     7060 <verify+0xb0>
    720d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    7212:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    7217:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    721c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7221:	48 83 c1 01          	add    $0x1,%rcx
    7225:	39 48 08             	cmp    %ecx,0x8(%rax)
    7228:	0f 8f d8 fd ff ff    	jg     7006 <verify+0x56>
    722e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    7233:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    7238:	48 81 44 24 10 d8 00 00 00 	addq   $0xd8,0x10(%rsp)
    7241:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    7246:	41 39 c7             	cmp    %eax,%r15d
    7249:	0f 84 86 00 00 00    	je     72d5 <verify+0x325>
    724f:	41 89 c4             	mov    %eax,%r12d
    7252:	e9 8a fd ff ff       	jmp    6fe1 <verify+0x31>
    7257:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7260:	0f 85 ba fe ff ff    	jne    7120 <verify+0x170>
    7266:	e9 a8 fe ff ff       	jmp    7113 <verify+0x163>
    726b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    7270:	49 39 c1             	cmp    %rax,%r9
    7273:	7e 09                	jle    727e <verify+0x2ce>
    7275:	4c 39 df             	cmp    %r11,%rdi
    7278:	0f 8c 0a ff ff ff    	jl     7188 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    727e:	4c 39 df             	cmp    %r11,%rdi
    7281:	0f 8f 99 fe ff ff    	jg     7120 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7287:	49 39 c1             	cmp    %rax,%r9
    728a:	0f 8d f8 fe ff ff    	jge    7188 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7290:	48 39 f1             	cmp    %rsi,%rcx
    7293:	0f 85 87 fe ff ff    	jne    7120 <verify+0x170>
    7299:	4c 39 c2             	cmp    %r8,%rdx
    729c:	0f 85 7e fe ff ff    	jne    7120 <verify+0x170>
    72a2:	4c 39 df             	cmp    %r11,%rdi
    72a5:	0f 84 dd fe ff ff    	je     7188 <verify+0x1d8>
    72ab:	e9 70 fe ff ff       	jmp    7120 <verify+0x170>
    72b0:	4c 39 c2             	cmp    %r8,%rdx
    72b3:	0f 8c 5a fe ff ff    	jl     7113 <verify+0x163>
    72b9:	4c 39 df             	cmp    %r11,%rdi
    72bc:	7e c9                	jle    7287 <verify+0x2d7>
    72be:	4c 39 c2             	cmp    %r8,%rdx
    72c1:	0f 85 59 fe ff ff    	jne    7120 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    72c7:	49 39 c1             	cmp    %rax,%r9
    72ca:	0f 8f 50 fe ff ff    	jg     7120 <verify+0x170>
    72d0:	e9 b3 fe ff ff       	jmp    7188 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    72d5:	48 81 44 24 18 d8 00 00 00 	addq   $0xd8,0x18(%rsp)
    72de:	41 8d 46 01          	lea    0x1(%r14),%eax
    72e2:	45 39 e6             	cmp    %r12d,%r14d
    72e5:	74 08                	je     72ef <verify+0x33f>
    72e7:	41 89 c6             	mov    %eax,%r14d
    72ea:	e9 ea fc ff ff       	jmp    6fd9 <verify+0x29>
}
    72ef:	48 83 c4 58          	add    $0x58,%rsp
    72f3:	31 c0                	xor    %eax,%eax
    72f5:	5b                   	pop    %rbx
    72f6:	5d                   	pop    %rbp
    72f7:	41 5c                	pop    %r12
    72f9:	41 5d                	pop    %r13
    72fb:	41 5e                	pop    %r14
    72fd:	41 5f                	pop    %r15
    72ff:	c3                   	ret
    7300:	31 c0                	xor    %eax,%eax
    7302:	c3                   	ret

Disassembly of section .fini:

0000000000007304 <_fini>:
    7304:	f3 0f 1e fa          	endbr64
    7308:	48 83 ec 08          	sub    $0x8,%rsp
    730c:	48 83 c4 08          	add    $0x8,%rsp
    7310:	c3                   	ret
