
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
    26b6:	48 8d 3d 9b 5f 00 00 	lea    0x5f9b(%rip),%rdi        # 8658 <_IO_stdin_used+0x658>
    26bd:	41 56                	push   %r14
    26bf:	41 55                	push   %r13
    26c1:	41 54                	push   %r12
    26c3:	55                   	push   %rbp
    26c4:	53                   	push   %rbx
    26c5:	48 81 ec f8 00 00 00 	sub    $0xf8,%rsp
    26cc:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    26d5:	48 89 84 24 e8 00 00 00 	mov    %rax,0xe8(%rsp)
    26dd:	48 8d 05 3c 1d 00 00 	lea    0x1d3c(%rip),%rax        # 4420 <barriered_reset>
    26e4:	66 48 0f 6e f0       	movq   %rax,%xmm6
    26e9:	0f 16 35 58 85 00 00 	movhps 0x8558(%rip),%xmm6        # ac48 <__do_global_dtors_aux_fini_array_entry+0x8>
    26f0:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    26f8:	e8 53 fc ff ff       	call   2350 <puts@plt>
    26fd:	bf 0a 00 00 00       	mov    $0xa,%edi
    2702:	e8 29 fc ff ff       	call   2330 <putchar@plt>
    2707:	ba 01 00 00 00       	mov    $0x1,%edx
    270c:	48 8d 35 61 5b 00 00 	lea    0x5b61(%rip),%rsi        # 8274 <_IO_stdin_used+0x274>
    2713:	31 c0                	xor    %eax,%eax
    2715:	bf 01 00 00 00       	mov    $0x1,%edi
    271a:	e8 c1 fd ff ff       	call   24e0 <__printf_chk@plt>
    271f:	ba 06 00 00 00       	mov    $0x6,%edx
    2724:	48 8d 35 59 5b 00 00 	lea    0x5b59(%rip),%rsi        # 8284 <_IO_stdin_used+0x284>
    272b:	31 c0                	xor    %eax,%eax
    272d:	bf 01 00 00 00       	mov    $0x1,%edi
    2732:	e8 a9 fd ff ff       	call   24e0 <__printf_chk@plt>
    2737:	ba 03 00 00 00       	mov    $0x3,%edx
    273c:	48 8d 35 56 5b 00 00 	lea    0x5b56(%rip),%rsi        # 8299 <_IO_stdin_used+0x299>
    2743:	31 c0                	xor    %eax,%eax
    2745:	bf 01 00 00 00       	mov    $0x1,%edi
    274a:	e8 91 fd ff ff       	call   24e0 <__printf_chk@plt>
    274f:	ba 02 00 00 00       	mov    $0x2,%edx
    2754:	48 8d 35 4e 5b 00 00 	lea    0x5b4e(%rip),%rsi        # 82a9 <_IO_stdin_used+0x2a9>
    275b:	31 c0                	xor    %eax,%eax
    275d:	bf 01 00 00 00       	mov    $0x1,%edi
    2762:	e8 79 fd ff ff       	call   24e0 <__printf_chk@plt>
    2767:	48 8d 3d 51 5b 00 00 	lea    0x5b51(%rip),%rdi        # 82bf <_IO_stdin_used+0x2bf>
    276e:	e8 dd fb ff ff       	call   2350 <puts@plt>
    2773:	ba 02 00 00 00       	mov    $0x2,%edx
    2778:	48 8d 35 5c 5b 00 00 	lea    0x5b5c(%rip),%rsi        # 82db <_IO_stdin_used+0x2db>
    277f:	31 c0                	xor    %eax,%eax
    2781:	bf 01 00 00 00       	mov    $0x1,%edi
    2786:	e8 55 fd ff ff       	call   24e0 <__printf_chk@plt>
    278b:	ba 0a 00 00 00       	mov    $0xa,%edx
    2790:	48 8d 35 5e 5b 00 00 	lea    0x5b5e(%rip),%rsi        # 82f5 <_IO_stdin_used+0x2f5>
    2797:	31 c0                	xor    %eax,%eax
    2799:	bf 01 00 00 00       	mov    $0x1,%edi
    279e:	e8 3d fd ff ff       	call   24e0 <__printf_chk@plt>
    27a3:	ba 01 00 00 00       	mov    $0x1,%edx
    27a8:	48 8d 35 5a 5b 00 00 	lea    0x5b5a(%rip),%rsi        # 8309 <_IO_stdin_used+0x309>
    27af:	31 c0                	xor    %eax,%eax
    27b1:	bf 01 00 00 00       	mov    $0x1,%edi
    27b6:	e8 25 fd ff ff       	call   24e0 <__printf_chk@plt>
    27bb:	ba 01 00 00 00       	mov    $0x1,%edx
    27c0:	48 8d 35 53 5b 00 00 	lea    0x5b53(%rip),%rsi        # 831a <_IO_stdin_used+0x31a>
    27c7:	31 c0                	xor    %eax,%eax
    27c9:	bf 01 00 00 00       	mov    $0x1,%edi
    27ce:	e8 0d fd ff ff       	call   24e0 <__printf_chk@plt>
    27d3:	ba 02 00 00 00       	mov    $0x2,%edx
    27d8:	48 8d 35 53 5b 00 00 	lea    0x5b53(%rip),%rsi        # 8332 <_IO_stdin_used+0x332>
    27df:	31 c0                	xor    %eax,%eax
    27e1:	bf 01 00 00 00       	mov    $0x1,%edi
    27e6:	e8 f5 fc ff ff       	call   24e0 <__printf_chk@plt>
    27eb:	ba 01 00 00 00       	mov    $0x1,%edx
    27f0:	48 8d 35 c9 5e 00 00 	lea    0x5ec9(%rip),%rsi        # 86c0 <_IO_stdin_used+0x6c0>
    27f7:	31 c0                	xor    %eax,%eax
    27f9:	bf 01 00 00 00       	mov    $0x1,%edi
    27fe:	e8 dd fc ff ff       	call   24e0 <__printf_chk@plt>
    2803:	ba 01 00 00 00       	mov    $0x1,%edx
    2808:	48 8d 35 e1 5e 00 00 	lea    0x5ee1(%rip),%rsi        # 86f0 <_IO_stdin_used+0x6f0>
    280f:	31 c0                	xor    %eax,%eax
    2811:	bf 01 00 00 00       	mov    $0x1,%edi
    2816:	e8 c5 fc ff ff       	call   24e0 <__printf_chk@plt>
    281b:	ba 40 42 0f 00       	mov    $0xf4240,%edx
    2820:	48 8d 35 27 5b 00 00 	lea    0x5b27(%rip),%rsi        # 834e <_IO_stdin_used+0x34e>
    2827:	31 c0                	xor    %eax,%eax
    2829:	bf 01 00 00 00       	mov    $0x1,%edi
    282e:	e8 ad fc ff ff       	call   24e0 <__printf_chk@plt>
    2833:	ba 05 00 00 00       	mov    $0x5,%edx
    2838:	48 8d 35 29 5b 00 00 	lea    0x5b29(%rip),%rsi        # 8368 <_IO_stdin_used+0x368>
    283f:	31 c0                	xor    %eax,%eax
    2841:	bf 01 00 00 00       	mov    $0x1,%edi
    2846:	e8 95 fc ff ff       	call   24e0 <__printf_chk@plt>
    284b:	48 8d 3d a3 58 00 00 	lea    0x58a3(%rip),%rdi        # 80f5 <_IO_stdin_used+0xf5>
    2852:	e8 f9 fa ff ff       	call   2350 <puts@plt>
  printf("duration %d seconds", DURATION);
  printf("\n\n");

  int dataid = 0;

  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2857:	be 18 00 00 00       	mov    $0x18,%esi
    285c:	bf 03 00 00 00       	mov    $0x3,%edi
    2861:	e8 ba fb ff ff       	call   2420 <calloc@plt>
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2866:	be d0 00 00 00       	mov    $0xd0,%esi
    286b:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct ProtectedState *protected_state = calloc(group_count, sizeof(struct ProtectedState));
    2870:	48 89 84 24 98 00 00 00 	mov    %rax,0x98(%rsp)
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2878:	e8 a3 fb ff ff       	call   2420 <calloc@plt>
  
  pthread_mutex_t * swapmutex = calloc(total_threads, sizeof(pthread_mutex_t));
    287d:	be 28 00 00 00       	mov    $0x28,%esi
    2882:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct KernelThread *thread_data = calloc(total_threads, sizeof(struct KernelThread)); 
    2887:	48 89 44 24 30       	mov    %rax,0x30(%rsp)
  pthread_mutex_t * swapmutex = calloc(total_threads, sizeof(pthread_mutex_t));
    288c:	e8 8f fb ff ff       	call   2420 <calloc@plt>
    2891:	48 89 84 24 c8 00 00 00 	mov    %rax,0xc8(%rsp)
  for (int x = 0 ; x < total_threads; x++) {
    2899:	48 89 c3             	mov    %rax,%rbx
    289c:	48 8d a8 90 01 00 00 	lea    0x190(%rax),%rbp
    pthread_mutex_init(&swapmutex[x], NULL);
    28a3:	48 89 df             	mov    %rbx,%rdi
    28a6:	31 f6                	xor    %esi,%esi
  for (int x = 0 ; x < total_threads; x++) {
    28a8:	48 83 c3 28          	add    $0x28,%rbx
    pthread_mutex_init(&swapmutex[x], NULL);
    28ac:	e8 ff fc ff ff       	call   25b0 <pthread_mutex_init@plt>
  for (int x = 0 ; x < total_threads; x++) {
    28b1:	48 39 dd             	cmp    %rbx,%rbp
    28b4:	75 ed                	jne    28a3 <main+0x1f3>
    28b6:	ba 06 00 00 00       	mov    $0x6,%edx
    28bb:	48 8d 35 ba 5a 00 00 	lea    0x5aba(%rip),%rsi        # 837c <_IO_stdin_used+0x37c>
    28c2:	bf 01 00 00 00       	mov    $0x1,%edi
    28c7:	31 c0                	xor    %eax,%eax
    28c9:	e8 12 fc ff ff       	call   24e0 <__printf_chk@plt>
    28ce:	ba 0c 00 00 00       	mov    $0xc,%edx
    28d3:	48 8d 35 b8 5a 00 00 	lea    0x5ab8(%rip),%rsi        # 8392 <_IO_stdin_used+0x392>
    28da:	31 c0                	xor    %eax,%eax
    28dc:	bf 01 00 00 00       	mov    $0x1,%edi
    28e1:	e8 fa fb ff ff       	call   24e0 <__printf_chk@plt>
  int timer_index = group_count * thread_count;
  int io_index = timer_index + timer_count;
  printf("Timer index start %d\n", timer_index);
  int buffers_required = (group_count * thread_count) * barrier_count;
  printf("Need %d buffers required\n", buffers_required);
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    28e6:	be 10 00 00 00       	mov    $0x10,%esi
    28eb:	bf 0c 00 00 00       	mov    $0xc,%edi
    28f0:	e8 2b fb ff ff       	call   2420 <calloc@plt>
    28f5:	48 89 84 24 a8 00 00 00 	mov    %rax,0xa8(%rsp)
    28fd:	49 89 c7             	mov    %rax,%r15
  int snapshot_limit = 100;
  for (int x = 0 ; x < buffers_required; x++) {
    2900:	48 8d 98 c0 00 00 00 	lea    0xc0(%rax),%rbx
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    2907:	49 89 c6             	mov    %rax,%r14
    buffers[x].count = buffer_size;
    290a:	41 c7 06 01 00 00 00 	movl   $0x1,(%r14)
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    2911:	be 00 01 00 00       	mov    $0x100,%esi
    2916:	bf 01 00 00 00       	mov    $0x1,%edi
  for (int x = 0 ; x < buffers_required; x++) {
    291b:	49 83 c6 10          	add    $0x10,%r14
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    291f:	e8 fc fa ff ff       	call   2420 <calloc@plt>
    for (int y = 0 ; y < buffer_size; y++) {
      buffers[x].buffer[y].available = 0;
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2924:	be 20 00 00 00       	mov    $0x20,%esi
    2929:	bf 64 00 00 00       	mov    $0x64,%edi
    buffers[x].buffer = calloc(buffer_size, sizeof(struct Buffer));
    292e:	49 89 46 f8          	mov    %rax,-0x8(%r14)
    2932:	48 89 c5             	mov    %rax,%rbp
      buffers[x].buffer[y].available = 0;
    2935:	c7 80 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rax)
      buffers[x].buffer[y].snapshot_limit = snapshot_limit;
    293f:	c7 80 90 00 00 00 64 00 00 00 	movl   $0x64,0x90(%rax)
      buffers[x].buffer[y].snapshots = calloc(snapshot_limit, sizeof(struct Snapshot));
    2949:	e8 d2 fa ff ff       	call   2420 <calloc@plt>
    294e:	48 89 85 88 00 00 00 	mov    %rax,0x88(%rbp)
  for (int x = 0 ; x < buffers_required; x++) {
    2955:	4c 39 f3             	cmp    %r14,%rbx
    2958:	75 b0                	jne    290a <main+0x25a>
    295a:	48 8b b4 24 98 00 00 00 	mov    0x98(%rsp),%rsi
    2962:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
  int timestamp_limit = 100;
  int cores = 12;
  int curcpu = 0;
  int my_buffers = 0;
  int cur_buffer = 0;
  int swap = 0;
    2967:	c7 44 24 38 00 00 00 00 	movl   $0x0,0x38(%rsp)
  for (int k = 0 ; k < group_count ; k++) {
    296f:	45 31 e4             	xor    %r12d,%r12d
  int cur_buffer = 0;
    2972:	c7 44 24 74 00 00 00 00 	movl   $0x0,0x74(%rsp)
    297a:	48 89 b4 24 88 00 00 00 	mov    %rsi,0x88(%rsp)
    2982:	48 89 dd             	mov    %rbx,%rbp
  int curcpu = 0;
    2985:	c7 44 24 78 00 00 00 00 	movl   $0x0,0x78(%rsp)
    298d:	48 89 9c 24 a0 00 00 00 	mov    %rbx,0xa0(%rsp)
    2995:	4c 89 fb             	mov    %r15,%rbx
    2998:	45 89 e7             	mov    %r12d,%r15d
    for (int d = 0 ; d < threads_per_group ; d++) {
    299b:	48 63 44 24 74       	movslq 0x74(%rsp),%rax
    29a0:	44 89 7c 24 7c       	mov    %r15d,0x7c(%rsp)
  struct Buffers *buffers = calloc(buffers_required, sizeof(struct Buffers));
    29a5:	49 89 e9             	mov    %rbp,%r9
    29a8:	48 89 ac 24 d0 00 00 00 	mov    %rbp,0xd0(%rsp)
    29b0:	48 c1 e0 04          	shl    $0x4,%rax
    29b4:	48 89 b4 24 c0 00 00 00 	mov    %rsi,0xc0(%rsp)
    29bc:	48 01 d8             	add    %rbx,%rax
    29bf:	48 89 9c 24 d8 00 00 00 	mov    %rbx,0xd8(%rsp)
    29c7:	48 89 44 24 60       	mov    %rax,0x60(%rsp)
    29cc:	43 8d 04 3f          	lea    (%r15,%r15,1),%eax
    29d0:	8d 78 01             	lea    0x1(%rax),%edi
    29d3:	83 c0 03             	add    $0x3,%eax
    29d6:	89 7c 24 18          	mov    %edi,0x18(%rsp)
    29da:	89 84 24 94 00 00 00 	mov    %eax,0x94(%rsp)
    29e1:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
    29e5:	8b 54 24 7c          	mov    0x7c(%rsp),%edx
    29e9:	bf 01 00 00 00       	mov    $0x1,%edi
    29ee:	31 c0                	xor    %eax,%eax
    29f0:	48 8d 35 21 5d 00 00 	lea    0x5d21(%rip),%rsi        # 8718 <_IO_stdin_used+0x718>
    29f7:	4c 89 0c 24          	mov    %r9,(%rsp)
      int x = (k * threads_per_group) + d;
    29fb:	44 8d 7b ff          	lea    -0x1(%rbx),%r15d
    29ff:	44 89 f9             	mov    %r15d,%ecx
    2a02:	e8 d9 fa ff ff       	call   24e0 <__printf_chk@plt>
      printf("Creating thread data for group %d thread %d\n", k, x);
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a07:	be 08 00 00 00       	mov    $0x8,%esi
    2a0c:	bf 02 00 00 00       	mov    $0x2,%edi
    2a11:	e8 0a fa ff ff       	call   2420 <calloc@plt>
      int other = -1;
      int me_thread = 0;
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a16:	be 80 00 00 00       	mov    $0x80,%esi
    2a1b:	bf 01 00 00 00       	mov    $0x1,%edi
      struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    2a20:	49 89 c5             	mov    %rax,%r13
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a23:	e8 f8 f9 ff ff       	call   2420 <calloc@plt>
      CPU_ZERO(sendercpu);
      if (x % 2 == 1) {
    2a28:	45 89 f8             	mov    %r15d,%r8d
    2a2b:	4c 8b 0c 24          	mov    (%rsp),%r9
    2a2f:	41 83 e0 01          	and    $0x1,%r8d
      cpu_set_t *sendercpu = calloc(1, sizeof(cpu_set_t));
    2a33:	48 89 c5             	mov    %rax,%rbp
      if (x % 2 == 1) {
    2a36:	44 89 44 24 70       	mov    %r8d,0x70(%rsp)
    2a3b:	0f 84 d5 10 00 00    	je     3b16 <main+0x1466>
        other = abs(x - 1) % total_threads;
    2a41:	8d 43 fe             	lea    -0x2(%rbx),%eax
    2a44:	89 df                	mov    %ebx,%edi
        thread_data[x].thread_index = 1;
        my_thread_data[0] = &thread_data[other]; 
    2a46:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    2a4b:	48 8d 14 40          	lea    (%rax,%rax,2),%rdx
        other = abs(x - 1) % total_threads;
    2a4f:	49 89 c6             	mov    %rax,%r14
        my_thread_data[0] = &thread_data[other]; 
    2a52:	48 8d 04 90          	lea    (%rax,%rdx,4),%rax
        my_thread_data[1] = &thread_data[x]; 
    2a56:	4c 89 ca             	mov    %r9,%rdx
        my_thread_data[0] = &thread_data[other]; 
    2a59:	48 c1 e0 04          	shl    $0x4,%rax
    2a5d:	48 01 d8             	add    %rbx,%rax
          thread_data[x].tasks[y].message = messaged;
          thread_data[x].tasks[y].sending = 1;
          thread_data[x].tasks[y].snapshot_count = 99;
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
          thread_data[x].tasks[y].current_snapshot = 0;
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    2a60:	49 8d 5d 08          	lea    0x8(%r13),%rbx
    2a64:	48 89 5c 24 40       	mov    %rbx,0x40(%rsp)
    2a69:	89 fb                	mov    %edi,%ebx
        thread_data[x].protected_state = &protected_state[k];
    2a6b:	48 8b bc 24 c0 00 00 00 	mov    0xc0(%rsp),%rdi
        thread_data[x].thread_index = 1;
    2a73:	45 89 41 04          	mov    %r8d,0x4(%r9)
    2a77:	44 89 f1             	mov    %r14d,%ecx
    2a7a:	48 8d 35 c7 5c 00 00 	lea    0x5cc7(%rip),%rsi        # 8748 <_IO_stdin_used+0x748>
    2a81:	49 89 55 08          	mov    %rdx,0x8(%r13)
    2a85:	44 89 fa             	mov    %r15d,%edx
        thread_data[x].protected_state = &protected_state[k];
    2a88:	49 89 79 48          	mov    %rdi,0x48(%r9)
    2a8c:	bf 01 00 00 00       	mov    $0x1,%edi
    2a91:	49 89 45 00          	mov    %rax,0x0(%r13)
    2a95:	31 c0                	xor    %eax,%eax
    2a97:	4c 89 0c 24          	mov    %r9,(%rsp)
    2a9b:	e8 40 fa ff ff       	call   24e0 <__printf_chk@plt>
      thread_data[x].other = other;
    2aa0:	4c 8b 0c 24          	mov    (%rsp),%r9
    2aa4:	8b 4c 24 78          	mov    0x78(%rsp),%ecx
    2aa8:	31 c0                	xor    %eax,%eax
    2aaa:	44 89 fa             	mov    %r15d,%edx
    2aad:	48 8d 35 c4 5c 00 00 	lea    0x5cc4(%rip),%rsi        # 8778 <_IO_stdin_used+0x778>
    2ab4:	bf 01 00 00 00       	mov    $0x1,%edi
    2ab9:	45 89 b1 b8 00 00 00 	mov    %r14d,0xb8(%r9)
    2ac0:	e8 1b fa ff ff       	call   24e0 <__printf_chk@plt>
        if (x < thread_count) {
    2ac5:	41 83 ff 01          	cmp    $0x1,%r15d
    2ac9:	4c 8b 0c 24          	mov    (%rsp),%r9
    2acd:	0f 87 6e 10 00 00    	ja     3b41 <main+0x1491>
          CPU_SET(curcpu, sendercpu);
    2ad3:	48 63 44 24 78       	movslq 0x78(%rsp),%rax
    2ad8:	48 89 c7             	mov    %rax,%rdi
    2adb:	48 3d ff 03 00 00    	cmp    $0x3ff,%rax
    2ae1:	77 13                	ja     2af6 <main+0x446>
    2ae3:	48 c1 e8 06          	shr    $0x6,%rax
    2ae7:	ba 01 00 00 00       	mov    $0x1,%edx
    2aec:	89 f9                	mov    %edi,%ecx
    2aee:	48 d3 e2             	shl    %cl,%rdx
    2af1:	48 09 54 c5 00       	or     %rdx,0x0(%rbp,%rax,8)
          curcpu += 2;
    2af6:	83 44 24 78 02       	addl   $0x2,0x78(%rsp)
      thread_data[x].real_thread_index = x;
    2afb:	45 89 79 08          	mov    %r15d,0x8(%r9)
      thread_data[x].swapmutex = swapmutex;
    2aff:	48 8b 84 24 c8 00 00 00 	mov    0xc8(%rsp),%rax
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b07:	be 10 00 00 00       	mov    $0x10,%esi
    2b0c:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].cpu_set = sendercpu;
    2b11:	49 89 a9 b0 00 00 00 	mov    %rbp,0xb0(%r9)
        for (int y = 0 ; y < total_barrier_count ; y++) {
    2b18:	31 ed                	xor    %ebp,%ebp
      thread_data[x].swapmutex = swapmutex;
    2b1a:	49 89 81 c8 00 00 00 	mov    %rax,0xc8(%r9)
      thread_data[x].all_threads = thread_data;
    2b21:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
      thread_data[x].kind = KERNEL_THREAD;
    2b26:	41 c7 01 5f 00 00 00 	movl   $0x5f,(%r9)
      thread_data[x].all_threads = thread_data;
    2b2d:	49 89 41 20          	mov    %rax,0x20(%r9)
      thread_data[x].group_count = group_count;
    2b31:	48 8b 05 68 61 00 00 	mov    0x6168(%rip),%rax        # 8ca0 <_IO_stdin_used+0xca0>
      thread_data[x].threads = my_thread_data;
    2b38:	4d 89 69 18          	mov    %r13,0x18(%r9)
      thread_data[x].group_count = group_count;
    2b3c:	49 89 81 c0 00 00 00 	mov    %rax,0xc0(%r9)
      thread_data[x].thread_count = 2;
    2b43:	48 8b 05 5e 61 00 00 	mov    0x615e(%rip),%rax        # 8ca8 <_IO_stdin_used+0xca8>
      thread_data[x].task_count = total_barrier_count;
    2b4a:	41 c7 41 40 03 00 00 00 	movl   $0x3,0x40(%r9)
      thread_data[x].thread_count = 2;
    2b52:	49 89 41 28          	mov    %rax,0x28(%r9)
      thread_data[x].task_count = total_barrier_count;
    2b56:	4c 89 0c 24          	mov    %r9,(%rsp)
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b5a:	e8 c1 f8 ff ff       	call   2420 <calloc@plt>
    2b5f:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2b63:	be 10 00 00 00       	mov    $0x10,%esi
    2b68:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].start = calloc(timestamp_limit, sizeof(struct timespec));
    2b6d:	49 89 41 68          	mov    %rax,0x68(%r9)
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2b71:	e8 aa f8 ff ff       	call   2420 <calloc@plt>
    2b76:	4c 8b 0c 24          	mov    (%rsp),%r9
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2b7a:	be 28 00 00 00       	mov    $0x28,%esi
      thread_data[x].timestamp_count = 0;
    2b7f:	66 0f 6f 3d e9 60 00 00 	movdqa 0x60e9(%rip),%xmm7        # 8c70 <_IO_stdin_used+0xc70>
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2b87:	bf 64 00 00 00       	mov    $0x64,%edi
      thread_data[x].end = calloc(timestamp_limit, sizeof(struct timespec));
    2b8c:	49 89 41 70          	mov    %rax,0x70(%r9)
      thread_data[x].timestamp_count = 0;
    2b90:	41 0f 11 b9 80 00 00 00 	movups %xmm7,0x80(%r9)
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2b98:	e8 83 f8 ff ff       	call   2420 <calloc@plt>
    2b9d:	4c 8b 0c 24          	mov    (%rsp),%r9
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2ba1:	bf 03 00 00 00       	mov    $0x3,%edi
      thread_data[x].task_timestamp_count = 0;
    2ba6:	66 0f 6f 35 c2 60 00 00 	movdqa 0x60c2(%rip),%xmm6        # 8c70 <_IO_stdin_used+0xc70>
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2bae:	be 00 02 00 00       	mov    $0x200,%esi
      thread_data[x].task_snapshot = calloc(timestamp_limit, sizeof(struct TaskSnapshot));
    2bb3:	49 89 81 90 00 00 00 	mov    %rax,0x90(%r9)
      thread_data[x].task_timestamp_count = 0;
    2bba:	41 0f 11 b1 98 00 00 00 	movups %xmm6,0x98(%r9)
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2bc2:	e8 59 f8 ff ff       	call   2420 <calloc@plt>
        thread_data[x].tasks = barriers;
    2bc7:	4c 8b 0c 24          	mov    (%rsp),%r9
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2bcb:	48 89 df             	mov    %rbx,%rdi
            data[0].messages_count = 0;
    2bce:	44 89 fb             	mov    %r15d,%ebx
        struct BarrierTask *barriers = calloc(total_barrier_count, sizeof(struct BarrierTask));
    2bd1:	49 89 c6             	mov    %rax,%r14
            data[0].messages_count = 0;
    2bd4:	44 8b 7c 24 7c       	mov    0x7c(%rsp),%r15d
        thread_data[x].tasks = barriers;
    2bd9:	49 89 41 38          	mov    %rax,0x38(%r9)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2bdd:	b8 ab aa aa aa       	mov    $0xaaaaaaab,%eax
            data[0].messages_count = 0;
    2be2:	4c 89 f1             	mov    %r14,%rcx
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2be5:	48 0f af f8          	imul   %rax,%rdi
            data[0].messages_count = 0;
    2be9:	4c 89 4c 24 50       	mov    %r9,0x50(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2bee:	48 c1 ef 22          	shr    $0x22,%rdi
    2bf2:	8d 04 7f             	lea    (%rdi,%rdi,2),%eax
    2bf5:	8b 7c 24 18          	mov    0x18(%rsp),%edi
    2bf9:	01 c0                	add    %eax,%eax
    2bfb:	29 c7                	sub    %eax,%edi
    2bfd:	8b 44 24 38          	mov    0x38(%rsp),%eax
            data[0].messages_count = 0;
    2c01:	89 bc 24 90 00 00 00 	mov    %edi,0x90(%rsp)
                mailboxes[b].other = abs((x + 1) % mailboxes_needed);
    2c08:	89 44 24 48          	mov    %eax,0x48(%rsp)
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c0c:	48 63 c5             	movslq %ebp,%rax
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c0f:	be 38 00 00 00       	mov    $0x38,%esi
    2c14:	bf 06 00 00 00       	mov    $0x6,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c19:	45 31 f6             	xor    %r14d,%r14d
          thread_data[x].tasks[y].protected = do_protected_write; 
    2c1c:	48 89 44 24 28       	mov    %rax,0x28(%rsp)
    2c21:	48 c1 e0 09          	shl    $0x9,%rax
    2c25:	4c 8d 2c 01          	lea    (%rcx,%rax,1),%r13
    2c29:	48 89 44 24 20       	mov    %rax,0x20(%rsp)
    2c2e:	48 8d 05 ab 17 00 00 	lea    0x17ab(%rip),%rax        # 43e0 <do_protected_write>
    2c35:	49 89 85 20 01 00 00 	mov    %rax,0x120(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c3c:	e8 df f7 ff ff       	call   2420 <calloc@plt>
          thread_data[x].tasks[y].mailboxes = mailboxes;
    2c41:	49 89 85 70 01 00 00 	mov    %rax,0x170(%r13)
          struct Mailbox *mailboxes = calloc(mailboxes_needed, sizeof(struct Mailbox));
    2c48:	48 89 c1             	mov    %rax,%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c4b:	8b 44 24 70          	mov    0x70(%rsp),%eax
    2c4f:	85 c0                	test   %eax,%eax
    2c51:	0f 84 68 06 00 00    	je     32bf <main+0xc0f>
                mailboxes[b].other = abs((x - 1) % mailboxes_needed);
    2c57:	8b 44 24 18          	mov    0x18(%rsp),%eax
    2c5b:	89 1c 24             	mov    %ebx,(%rsp)
    2c5e:	49 89 cd             	mov    %rcx,%r13
    2c61:	48 89 8c 24 80 00 00 00 	mov    %rcx,0x80(%rsp)
    2c69:	83 e8 02             	sub    $0x2,%eax
    2c6c:	89 44 24 68          	mov    %eax,0x68(%rsp)
    2c70:	eb 18                	jmp    2c8a <main+0x5da>
    2c72:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2c78:	41 83 c6 01          	add    $0x1,%r14d
    2c7c:	49 83 c5 38          	add    $0x38,%r13
    2c80:	41 83 fe 06          	cmp    $0x6,%r14d
    2c84:	0f 84 50 01 00 00    	je     2dda <main+0x72a>
            int group_of = b / threads_per_group;
    2c8a:	44 89 f3             	mov    %r14d,%ebx
    2c8d:	31 c0                	xor    %eax,%eax
    2c8f:	44 89 f2             	mov    %r14d,%edx
    2c92:	bf 01 00 00 00       	mov    $0x1,%edi
    2c97:	d1 fb                	sar    %ebx
    2c99:	48 8d 35 0c 57 00 00 	lea    0x570c(%rip),%rsi        # 83ac <_IO_stdin_used+0x3ac>
    2ca0:	89 d9                	mov    %ebx,%ecx
    2ca2:	e8 39 f8 ff ff       	call   24e0 <__printf_chk@plt>
            if (k == group_of) {
    2ca7:	41 39 df             	cmp    %ebx,%r15d
    2caa:	75 cc                	jne    2c78 <main+0x5c8>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2cac:	be 08 00 00 00       	mov    $0x8,%esi
    2cb1:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2cb6:	49 83 c5 38          	add    $0x38,%r13
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2cba:	e8 61 f7 ff ff       	call   2420 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cbf:	be 08 00 00 00       	mov    $0x8,%esi
    2cc4:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2cc9:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cce:	e8 4d f7 ff ff       	call   2420 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    2cd3:	be 80 03 00 00       	mov    $0x380,%esi
    2cd8:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2cdd:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    2ce2:	e8 39 f7 ff ff       	call   2420 <calloc@plt>
              data[0].a = x;
    2ce7:	8b 3c 24             	mov    (%rsp),%edi
              mailboxes[b].pending = NULL;
    2cea:	49 c7 45 d8 00 00 00 00 	movq   $0x0,-0x28(%r13)
    2cf2:	44 89 f2             	mov    %r14d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    2cf5:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    2cf8:	44 89 b0 24 03 00 00 	mov    %r14d,0x324(%rax)
    2cff:	48 8d 35 92 5a 00 00 	lea    0x5a92(%rip),%rsi        # 8798 <_IO_stdin_used+0x798>
              data[0].a = x;
    2d06:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].kind = MAILBOX_LOWER;
    2d0c:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
    2d16:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    2d1c:	41 8d 44 24 01       	lea    0x1(%r12),%eax
              data[1].id = dataid++;
    2d21:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    2d28:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    2d2f:	49 89 45 d0          	mov    %rax,-0x30(%r13)
    2d33:	8b 44 24 68          	mov    0x68(%rsp),%eax
              data[0].id = dataid++;
    2d37:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
              data[1].id = dataid++;
    2d3e:	41 83 c4 02          	add    $0x2,%r12d
              data[1].a = x;
    2d42:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    2d49:	89 c1                	mov    %eax,%ecx
    2d4b:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].c = b;
    2d50:	45 89 b1 a4 06 00 00 	mov    %r14d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2d57:	41 83 c6 01          	add    $0x1,%r14d
              mailboxes[b].lower = &data[0];
    2d5b:	4d 89 4d c8          	mov    %r9,-0x38(%r13)
    2d5f:	41 89 45 fc          	mov    %eax,-0x4(%r13)
    2d63:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    2d65:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].b = y;
    2d70:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    2d77:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    2d82:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    2d8d:	41 c7 45 f8 01 00 00 00 	movl   $0x1,-0x8(%r13)
              data[1].finished_reading = 1;
    2d95:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    2d9a:	e8 41 f7 ff ff       	call   24e0 <__printf_chk@plt>
              data[0].messages = messages;
    2d9f:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    2da4:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
              data[0].messages_count = 0;
    2da9:	66 0f 6f 35 cf 5e 00 00 	movdqa 0x5ecf(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
              data[1].messages = messages2;
    2db1:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
              data[0].messages = messages;
    2db6:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    2db9:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    2dc0:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    2dc8:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2dd0:	41 83 fe 06          	cmp    $0x6,%r14d
    2dd4:	0f 85 b0 fe ff ff    	jne    2c8a <main+0x5da>
    2dda:	8b 1c 24             	mov    (%rsp),%ebx
    2ddd:	48 8b 8c 24 80 00 00 00 	mov    0x80(%rsp),%rcx
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2de5:	45 31 ed             	xor    %r13d,%r13d
    2de8:	44 89 3c 24          	mov    %r15d,(%rsp)
    2dec:	41 89 d8             	mov    %ebx,%r8d
    2def:	41 89 ef             	mov    %ebp,%r15d
    2df2:	44 89 eb             	mov    %r13d,%ebx
    2df5:	49 89 cd             	mov    %rcx,%r13
    2df8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
            int group_of = b / threads_per_group;
    2e00:	89 d8                	mov    %ebx,%eax
    2e02:	d1 f8                	sar    %eax
            if (k == group_of) {
    2e04:	39 04 24             	cmp    %eax,(%rsp)
    2e07:	0f 84 58 01 00 00    	je     2f65 <main+0x8b5>
    2e0d:	89 da                	mov    %ebx,%edx
    2e0f:	48 8d 35 a6 55 00 00 	lea    0x55a6(%rip),%rsi        # 83bc <_IO_stdin_used+0x3bc>
    2e16:	bf 01 00 00 00       	mov    $0x1,%edi
    2e1b:	31 c0                	xor    %eax,%eax
    2e1d:	44 89 44 24 10       	mov    %r8d,0x10(%rsp)
    2e22:	e8 b9 f6 ff ff       	call   24e0 <__printf_chk@plt>
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e27:	be 08 00 00 00       	mov    $0x8,%esi
    2e2c:	bf 01 00 00 00       	mov    $0x1,%edi
    2e31:	e8 ea f5 ff ff       	call   2420 <calloc@plt>
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e36:	be 08 00 00 00       	mov    $0x8,%esi
    2e3b:	bf 01 00 00 00       	mov    $0x1,%edi
            struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    2e40:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e45:	e8 d6 f5 ff ff       	call   2420 <calloc@plt>
            struct Data *data = calloc(3, sizeof(struct Data));
    2e4a:	be 80 03 00 00       	mov    $0x380,%esi
    2e4f:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    2e54:	48 89 c5             	mov    %rax,%rbp
            struct Data *data = calloc(3, sizeof(struct Data));
    2e57:	e8 c4 f5 ff ff       	call   2420 <calloc@plt>
            struct Data **stack = calloc(3, sizeof(struct Data));
    2e5c:	be 80 03 00 00       	mov    $0x380,%esi
    2e61:	bf 03 00 00 00       	mov    $0x3,%edi
            struct Data *data = calloc(3, sizeof(struct Data));
    2e66:	49 89 c6             	mov    %rax,%r14
            struct Data **stack = calloc(3, sizeof(struct Data));
    2e69:	e8 b2 f5 ff ff       	call   2420 <calloc@plt>
            data[0].id = dataid++;
    2e6e:	41 8d 74 24 01       	lea    0x1(%r12),%esi
            data[0].a = x;
    2e73:	44 8b 44 24 10       	mov    0x10(%rsp),%r8d
            data[0].messages = messages;
    2e78:	48 8b 54 24 08       	mov    0x8(%rsp),%rdx
            data[1].id = dataid++;
    2e7d:	41 89 b6 a8 06 00 00 	mov    %esi,0x6a8(%r14)
            mailboxes[b].higher = &data[1];
    2e84:	49 8d b6 80 03 00 00 	lea    0x380(%r14),%rsi
            data[0].messages_count = 0;
    2e8b:	66 0f 6f 35 ed 5d 00 00 	movdqa 0x5ded(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
            data[0].kind = MAILBOX_LOWER;
    2e93:	41 c7 86 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%r14)
            data[0].a = x;
    2e9e:	45 89 86 1c 03 00 00 	mov    %r8d,0x31c(%r14)
            data[0].b = y;
    2ea5:	45 89 be 20 03 00 00 	mov    %r15d,0x320(%r14)
            data[0].c = b;
    2eac:	41 89 9e 24 03 00 00 	mov    %ebx,0x324(%r14)
            data[1].kind = MAILBOX_HIGHER;
    2eb3:	41 c7 86 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r14)
            data[1].a = x;
    2ebe:	45 89 86 9c 06 00 00 	mov    %r8d,0x69c(%r14)
            data[1].b = y;
    2ec5:	45 89 be a0 06 00 00 	mov    %r15d,0x6a0(%r14)
            data[1].c = b;
    2ecc:	41 89 9e a4 06 00 00 	mov    %ebx,0x6a4(%r14)
            mailboxes[b].lower = &data[0];
    2ed3:	4d 89 75 00          	mov    %r14,0x0(%r13)
            mailboxes[b].my_lower = &data[0];
    2ed7:	4d 89 75 20          	mov    %r14,0x20(%r13)
            mailboxes[b].higher = &data[1];
    2edb:	49 89 75 08          	mov    %rsi,0x8(%r13)
            mailboxes[b].pending = NULL;
    2edf:	49 c7 45 10 00 00 00 00 	movq   $0x0,0x10(%r13)
            data[0].finished_reading = 1;
    2ee7:	41 c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r14)
            data[1].finished_reading = 1;
    2ef2:	41 c7 86 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r14)
            mailboxes[b].my_higher = &data[1];
    2efd:	49 89 75 28          	mov    %rsi,0x28(%r13)
            mailboxes[b].kind = MAILBOX_FOREIGN;
    2f01:	41 c7 45 30 02 00 00 00 	movl   $0x2,0x30(%r13)
            stack[0] = mailboxes[b].lower;
    2f09:	4c 89 30             	mov    %r14,(%rax)
            stack[1] = mailboxes[b].higher;
    2f0c:	48 89 70 08          	mov    %rsi,0x8(%rax)
            mailboxes[b].stack = (void**)stack;
    2f10:	49 89 45 18          	mov    %rax,0x18(%r13)
            data[0].available_sending = 0;
    2f14:	41 c7 86 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%r14)
            data[0].available_receiving = 0;
    2f1f:	41 c7 86 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%r14)
            data[0].messages = messages;
    2f2a:	49 89 16             	mov    %rdx,(%r14)
            data[1].messages = messages2;
    2f2d:	49 89 ae 80 03 00 00 	mov    %rbp,0x380(%r14)
            data[1].available_sending = 1;
    2f34:	41 c7 86 80 04 00 00 01 00 00 00 	movl   $0x1,0x480(%r14)
            data[1].available_receiving = 0;
    2f3f:	41 c7 86 00 05 00 00 00 00 00 00 	movl   $0x0,0x500(%r14)
            data[0].id = dataid++;
    2f4a:	45 89 a6 28 03 00 00 	mov    %r12d,0x328(%r14)
            data[1].id = dataid++;
    2f51:	41 83 c4 02          	add    $0x2,%r12d
            data[0].messages_count = 0;
    2f55:	41 0f 29 b6 80 00 00 00 	movaps %xmm6,0x80(%r14)
            data[1].messages_count = 0;
    2f5d:	41 0f 29 b6 00 04 00 00 	movaps %xmm6,0x400(%r14)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    2f65:	83 c3 01             	add    $0x1,%ebx
    2f68:	49 83 c5 38          	add    $0x38,%r13
    2f6c:	83 fb 06             	cmp    $0x6,%ebx
    2f6f:	0f 85 8b fe ff ff    	jne    2e00 <main+0x750>
          char *message = malloc(sizeof(char) * 256);
    2f75:	be 01 00 00 00       	mov    $0x1,%esi
    2f7a:	bf 00 01 00 00       	mov    $0x100,%edi
    2f7f:	44 89 fd             	mov    %r15d,%ebp
    2f82:	44 89 c3             	mov    %r8d,%ebx
    2f85:	44 8b 3c 24          	mov    (%rsp),%r15d
    2f89:	e8 92 f4 ff ff       	call   2420 <calloc@plt>
          struct Message *messaged = malloc(sizeof(struct Message));
    2f8e:	bf 20 00 00 00       	mov    $0x20,%edi
          char *message = malloc(sizeof(char) * 256);
    2f93:	49 89 c5             	mov    %rax,%r13
          struct Message *messaged = malloc(sizeof(struct Message));
    2f96:	e8 05 f5 ff ff       	call   24a0 <malloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    2f9b:	48 83 ec 08          	sub    $0x8,%rsp
    2f9f:	4c 89 ef             	mov    %r13,%rdi
    2fa2:	41 89 e9             	mov    %ebp,%r9d
    2fa5:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    2faa:	41 89 d8             	mov    %ebx,%r8d
    2fad:	ba 00 01 00 00       	mov    $0x100,%edx
    2fb2:	31 c0                	xor    %eax,%eax
    2fb4:	41 57                	push   %r15
    2fb6:	48 8d 0d 03 58 00 00 	lea    0x5803(%rip),%rcx        # 87c0 <_IO_stdin_used+0x7c0>
    2fbd:	be 01 00 00 00       	mov    $0x1,%esi
    2fc2:	e8 19 f6 ff ff       	call   25e0 <__sprintf_chk@plt>
          messaged->message = message;
    2fc7:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
          messaged->thread_index = thread_data[x].real_thread_index;
    2fcc:	4c 8b 74 24 60       	mov    0x60(%rsp),%r14
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2fd1:	be 20 00 00 00       	mov    $0x20,%esi
          messaged->task_index = y;
    2fd6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
          thread_data[x].tasks[y].swap = swap++;
    2fdb:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    2fe0:	bf 63 00 00 00       	mov    $0x63,%edi
          thread_data[x].tasks[y].swap = swap++;
    2fe5:	49 8b 4e 38          	mov    0x38(%r14),%rcx
          messaged->message = message;
    2fe9:	4d 89 2a             	mov    %r13,(%r10)
          messaged->task_index = y;
    2fec:	49 89 42 10          	mov    %rax,0x10(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2ff0:	49 63 46 08          	movslq 0x8(%r14),%rax
          thread_data[x].tasks[y].swap = swap++;
    2ff4:	48 01 ca             	add    %rcx,%rdx
          messaged->group = k;
    2ff7:	45 89 7a 18          	mov    %r15d,0x18(%r10)
          messaged->thread_index = thread_data[x].real_thread_index;
    2ffb:	49 89 42 08          	mov    %rax,0x8(%r10)
          thread_data[x].tasks[y].swap = swap++;
    2fff:	8b 44 24 58          	mov    0x58(%rsp),%eax
          thread_data[x].tasks[y].group = k;
    3003:	44 89 ba 94 01 00 00 	mov    %r15d,0x194(%rdx)
          thread_data[x].tasks[y].swap = swap++;
    300a:	89 82 98 01 00 00    	mov    %eax,0x198(%rdx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    3010:	8d 45 01             	lea    0x1(%rbp),%eax
    3013:	83 e0 01             	and    $0x1,%eax
          thread_data[x].tasks[y].kind = BARRIER_TASK;
    3016:	c7 02 41 00 00 00    	movl   $0x41,(%rdx)
          thread_data[x].tasks[y].next_thread = (y + 1) % thread_count;
    301c:	89 82 90 01 00 00    	mov    %eax,0x190(%rdx)
          thread_data[x].tasks[y].message = messaged;
    3022:	4c 89 92 88 01 00 00 	mov    %r10,0x188(%rdx)
          thread_data[x].tasks[y].sending = 1;
    3029:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
          thread_data[x].tasks[y].snapshot_count = 99;
    3033:	48 c7 82 58 01 00 00 63 00 00 00 	movq   $0x63,0x158(%rdx)
          thread_data[x].tasks[y].swap = swap++;
    303e:	83 44 24 48 01       	addl   $0x1,0x48(%rsp)
    3043:	48 89 4c 24 18       	mov    %rcx,0x18(%rsp)
          thread_data[x].tasks[y].snapshot_count = 99;
    3048:	48 89 54 24 10       	mov    %rdx,0x10(%rsp)
          thread_data[x].tasks[y].snapshots = calloc(thread_data[x].tasks[y].snapshot_count, sizeof(struct Snapshot));
    304d:	e8 ce f3 ff ff       	call   2420 <calloc@plt>
    3052:	48 8b 54 24 10       	mov    0x10(%rsp),%rdx
    3057:	48 89 82 50 01 00 00 	mov    %rax,0x150(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    305e:	48 8b 44 24 50       	mov    0x50(%rsp),%rax
          thread_data[x].tasks[y].current_snapshot = 0;
    3063:	48 c7 82 60 01 00 00 00 00 00 00 	movq   $0x0,0x160(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    306e:	48 8b 00             	mov    (%rax),%rax
    3071:	8b 70 04             	mov    0x4(%rax),%esi
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    3074:	4c 39 f0             	cmp    %r14,%rax
          thread_data[x].tasks[y].thread = my_thread_data[me_thread]; 
    3077:	48 89 82 28 01 00 00 	mov    %rax,0x128(%rdx)
          thread_data[x].tasks[y].thread_index = my_thread_data[me_thread]->thread_index;
    307e:	89 b2 30 01 00 00    	mov    %esi,0x130(%rdx)
          if (thread_data[x].tasks[y].thread != &thread_data[x]) {
    3084:	41 5b                	pop    %r11
    3086:	41 5d                	pop    %r13
    3088:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    308d:	0f 85 45 12 00 00    	jne    42d8 <main+0x1c28>
            exit(1);
          }
          thread_data[x].tasks[y].available = 1;
          thread_data[x].tasks[y].arrived = 0;
          thread_data[x].tasks[y].thread_count = 2;
    3093:	66 0f 6f 05 f5 5b 00 00 	movdqa 0x5bf5(%rip),%xmm0        # 8c90 <_IO_stdin_used+0xc90>
          thread_data[x].tasks[y].total_thread_count = thread_count;
          thread_data[x].tasks[y].all_thread_count = thread_count;
          thread_data[x].tasks[y].mailbox_thread_count = mailboxes_needed;
          thread_data[x].tasks[y].task_count = total_barrier_count;
          thread_data[x].tasks[y].worker_count = thread_count;
          thread_data[x].tasks[y].task_index = y;
    309b:	89 6a 04             	mov    %ebp,0x4(%rdx)
          thread_data[x].tasks[y].available = 1;
    309e:	4c 8b 2d 0b 5c 00 00 	mov    0x5c0b(%rip),%r13        # 8cb0 <_IO_stdin_used+0xcb0>
          thread_data[x].tasks[y].arrived = 0;
    30a5:	c7 82 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rdx)
          thread_data[x].tasks[y].worker_count = thread_count;
    30af:	c7 82 84 01 00 00 02 00 00 00 	movl   $0x2,0x184(%rdx)
          thread_data[x].tasks[y].available = 1;
    30b9:	4c 89 aa 44 01 00 00 	mov    %r13,0x144(%rdx)
          thread_data[x].tasks[y].thread_count = 2;
    30c0:	0f 11 82 34 01 00 00 	movups %xmm0,0x134(%rdx)
          if (y == barrier_count - 1) {
    30c7:	83 fd 01             	cmp    $0x1,%ebp
    30ca:	0f 84 92 03 00 00    	je     3462 <main+0xdb2>
              thread_data[x].tasks[y].run = barriered_nulltask; 
            }
            */
            thread_data[x].tasks[y].run = barriered_work; 
          } else {
            if (y == 0) {
    30d0:	85 ed                	test   %ebp,%ebp
    30d2:	0f 84 6a 03 00 00    	je     3442 <main+0xd92>
              // printf("Thread %d is an ingest thread\n", x);
              thread_data[x].tasks[y].run = barriered_work_ingest_andwork; 
              assigned = 1;
             } else {
               thread_data[x].tasks[y].run = barriered_work; 
    30d8:	4c 8b 4c 24 50       	mov    0x50(%rsp),%r9
    30dd:	48 8d 05 7c 36 00 00 	lea    0x367c(%rip),%rax        # 6760 <barriered_work>
             }
          }
        }
        thread_data[x].buffers_count = buffers_per_thread;
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    30e4:	bf 01 00 00 00       	mov    $0x1,%edi
               thread_data[x].tasks[y].run = barriered_work; 
    30e9:	49 89 ce             	mov    %rcx,%r14
    30ec:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    30f3:	be 08 00 00 00       	mov    $0x8,%esi
        thread_data[x].buffers_count = buffers_per_thread;
    30f8:	41 c7 81 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r9)
    3103:	4c 89 0c 24          	mov    %r9,(%rsp)
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3107:	e8 14 f3 ff ff       	call   2420 <calloc@plt>
    310c:	4c 8b 0c 24          	mov    (%rsp),%r9
        for (int b = 0 ; b < buffers_per_thread; b++) {	
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3110:	48 8b 7c 24 60       	mov    0x60(%rsp),%rdi
        }
        thread_data[x].tasks[barrier_count].protected = do_protected_write; 
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3115:	66 0f 6f bc 24 b0 00 00 00 	movdqa 0xb0(%rsp),%xmm7
    for (int d = 0 ; d < threads_per_group ; d++) {
    311e:	83 44 24 18 01       	addl   $0x1,0x18(%rsp)
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    3123:	48 89 38             	mov    %rdi,(%rax)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3126:	48 83 c7 10          	add    $0x10,%rdi
    312a:	49 81 c1 d0 00 00 00 	add    $0xd0,%r9
        thread_data[x].buffers = calloc(buffers_per_thread, sizeof(struct Buffers*)); 
    3131:	49 89 41 80          	mov    %rax,-0x80(%r9)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3135:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
          thread_data[x].buffers[b] = &buffers[cur_buffer++];
    313a:	83 44 24 74 01       	addl   $0x1,0x74(%rsp)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    313f:	48 8b 00             	mov    (%rax),%rax
    for (int d = 0 ; d < threads_per_group ; d++) {
    3142:	48 89 7c 24 60       	mov    %rdi,0x60(%rsp)
        thread_data[x].tasks[barrier_count].available = 1; 
        thread_data[x].tasks[barrier_count].arrived = 0; 
    3147:	41 c7 86 80 04 00 00 00 00 00 00 	movl   $0x0,0x480(%r14)
        thread_data[x].tasks[barrier_count].thread = my_thread_data[me_thread]; 
    3152:	49 89 86 28 05 00 00 	mov    %rax,0x528(%r14)
        thread_data[x].tasks[barrier_count].task_index = barrier_count; 
    3159:	41 c7 86 04 04 00 00 02 00 00 00 	movl   $0x2,0x404(%r14)
        thread_data[x].tasks[barrier_count].thread_count = 2; 
    3164:	41 c7 86 34 05 00 00 02 00 00 00 	movl   $0x2,0x534(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    316f:	41 8b 81 34 ff ff ff 	mov    -0xcc(%r9),%eax
        thread_data[x].tasks[barrier_count].run = barriered_reset; 
    3176:	41 0f 11 be 18 05 00 00 	movups %xmm7,0x518(%r14)
        thread_data[x].tasks[barrier_count].thread_index = thread_data[x].thread_index; 
    317e:	41 89 86 30 05 00 00 	mov    %eax,0x530(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    3185:	8b 44 24 18          	mov    0x18(%rsp),%eax
        thread_data[x].tasks[barrier_count].worker_count = thread_count; 
    3189:	41 c7 86 84 05 00 00 02 00 00 00 	movl   $0x2,0x584(%r14)
        thread_data[x].tasks[barrier_count].available = 1; 
    3194:	4d 89 ae 44 05 00 00 	mov    %r13,0x544(%r14)
    for (int d = 0 ; d < threads_per_group ; d++) {
    319b:	39 84 24 94 00 00 00 	cmp    %eax,0x94(%rsp)
    31a2:	0f 85 39 f8 ff ff    	jne    29e1 <main+0x331>
    31a8:	44 8b 7c 24 7c       	mov    0x7c(%rsp),%r15d
    31ad:	48 8b ac 24 d0 00 00 00 	mov    0xd0(%rsp),%rbp
    31b5:	48 8b b4 24 c0 00 00 00 	mov    0xc0(%rsp),%rsi
    31bd:	48 8b 9c 24 d8 00 00 00 	mov    0xd8(%rsp),%rbx
  for (int k = 0 ; k < group_count ; k++) {
    31c5:	41 83 c7 01          	add    $0x1,%r15d
    31c9:	48 81 c5 a0 01 00 00 	add    $0x1a0,%rbp
    31d0:	48 83 c6 18          	add    $0x18,%rsi
    31d4:	41 83 ff 03          	cmp    $0x3,%r15d
    31d8:	0f 85 bd f7 ff ff    	jne    299b <main+0x2eb>
        thread_data[x].tasks[barrier_count].task_count = total_barrier_count; 
    }
  }
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    31de:	be 08 00 00 00       	mov    $0x8,%esi
    31e3:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas_size = 0; 
    31e8:	45 31 e4             	xor    %r12d,%r12d
  struct Data ** cdatas = calloc(1024, sizeof(struct Data*)); 
    31eb:	e8 30 f2 ff ff       	call   2420 <calloc@plt>
    31f0:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    31f5:	48 89 c5             	mov    %rax,%rbp
    31f8:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    31fa:	49 89 d1             	mov    %rdx,%r9
    31fd:	31 db                	xor    %ebx,%ebx
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    31ff:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3203:	45 85 d2             	test   %r10d,%r10d
    3206:	0f 8e 9a 00 00 00    	jle    32a6 <main+0xbf6>
    320c:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3210:	4d 63 c2             	movslq %r10d,%r8
    3213:	49 63 cc             	movslq %r12d,%rcx
    3216:	49 c1 e0 09          	shl    $0x9,%r8
    321a:	48 8d 74 cd 00       	lea    0x0(%rbp,%rcx,8),%rsi
    321f:	49 01 f8             	add    %rdi,%r8
    3222:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3228:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    322f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3236:	48 83 c6 60          	add    $0x60,%rsi
    323a:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    323f:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    3244:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    324c:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3250:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3258:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    325c:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    3260:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    3268:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    326f:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    3273:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3277:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    327e:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          cdatas[datas_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3285:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3289:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    328d:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3291:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3295:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3299:	49 39 f8             	cmp    %rdi,%r8
    329c:	75 8a                	jne    3228 <main+0xb78>
    329e:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    32a2:	45 8d 24 8c          	lea    (%r12,%rcx,4),%r12d
    for (int d = 0 ; d < threads_per_group ; d++) {
    32a6:	49 81 c1 d0 00 00 00 	add    $0xd0,%r9
    32ad:	85 db                	test   %ebx,%ebx
    32af:	0f 85 bb 01 00 00    	jne    3470 <main+0xdc0>
    32b5:	bb 01 00 00 00       	mov    $0x1,%ebx
    32ba:	e9 40 ff ff ff       	jmp    31ff <main+0xb4f>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    32bf:	45 89 f5             	mov    %r14d,%r13d
    32c2:	89 1c 24             	mov    %ebx,(%rsp)
    32c5:	49 89 ce             	mov    %rcx,%r14
    32c8:	48 89 4c 24 68       	mov    %rcx,0x68(%rsp)
    32cd:	eb 13                	jmp    32e2 <main+0xc32>
    32cf:	90                   	nop
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    32d0:	41 83 c5 01          	add    $0x1,%r13d
    32d4:	49 83 c6 38          	add    $0x38,%r14
    32d8:	41 83 fd 06          	cmp    $0x6,%r13d
    32dc:	0f 84 53 01 00 00    	je     3435 <main+0xd85>
            int group_of = b / threads_per_group;
    32e2:	44 89 eb             	mov    %r13d,%ebx
    32e5:	31 c0                	xor    %eax,%eax
    32e7:	44 89 ea             	mov    %r13d,%edx
    32ea:	bf 01 00 00 00       	mov    $0x1,%edi
    32ef:	d1 fb                	sar    %ebx
    32f1:	48 8d 35 b4 50 00 00 	lea    0x50b4(%rip),%rsi        # 83ac <_IO_stdin_used+0x3ac>
    32f8:	89 d9                	mov    %ebx,%ecx
    32fa:	e8 e1 f1 ff ff       	call   24e0 <__printf_chk@plt>
            if (k == group_of) {
    32ff:	41 39 df             	cmp    %ebx,%r15d
    3302:	75 cc                	jne    32d0 <main+0xc20>
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3304:	be 08 00 00 00       	mov    $0x8,%esi
    3309:	bf 01 00 00 00       	mov    $0x1,%edi
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    330e:	49 83 c6 38          	add    $0x38,%r14
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3312:	e8 09 f1 ff ff       	call   2420 <calloc@plt>
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3317:	be 08 00 00 00       	mov    $0x8,%esi
    331c:	bf 01 00 00 00       	mov    $0x1,%edi
              struct Message **messages = calloc(messages_limit, sizeof(struct Message*));
    3321:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3326:	e8 f5 f0 ff ff       	call   2420 <calloc@plt>
              struct Data *data = calloc(3, sizeof(struct Data));
    332b:	be 80 03 00 00       	mov    $0x380,%esi
    3330:	bf 03 00 00 00       	mov    $0x3,%edi
              struct Message **messages2 = calloc(messages_limit, sizeof(struct Message*));
    3335:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
              struct Data *data = calloc(3, sizeof(struct Data));
    333a:	e8 e1 f0 ff ff       	call   2420 <calloc@plt>
              data[0].a = x;
    333f:	8b 3c 24             	mov    (%rsp),%edi
              mailboxes[b].pending = NULL;
    3342:	49 c7 46 d8 00 00 00 00 	movq   $0x0,-0x28(%r14)
    334a:	44 89 ea             	mov    %r13d,%edx
              struct Data *data = calloc(3, sizeof(struct Data));
    334d:	49 89 c1             	mov    %rax,%r9
              data[0].c = b;
    3350:	44 89 a8 24 03 00 00 	mov    %r13d,0x324(%rax)
    3357:	48 8d 35 3a 54 00 00 	lea    0x543a(%rip),%rsi        # 8798 <_IO_stdin_used+0x798>
              data[0].a = x;
    335e:	89 b8 1c 03 00 00    	mov    %edi,0x31c(%rax)
              data[0].kind = MAILBOX_LOWER;
    3364:	c7 80 18 03 00 00 01 00 00 00 	movl   $0x1,0x318(%rax)
              data[0].b = y;
    336e:	89 a8 20 03 00 00    	mov    %ebp,0x320(%rax)
              data[0].id = dataid++;
    3374:	41 8d 44 24 01       	lea    0x1(%r12),%eax
              data[1].id = dataid++;
    3379:	41 89 81 a8 06 00 00 	mov    %eax,0x6a8(%r9)
              mailboxes[b].higher = &data[1];
    3380:	49 8d 81 80 03 00 00 	lea    0x380(%r9),%rax
    3387:	49 89 46 d0          	mov    %rax,-0x30(%r14)
    338b:	8b 84 24 90 00 00 00 	mov    0x90(%rsp),%eax
              data[0].id = dataid++;
    3392:	45 89 a1 28 03 00 00 	mov    %r12d,0x328(%r9)
              data[1].id = dataid++;
    3399:	41 83 c4 02          	add    $0x2,%r12d
              data[1].a = x;
    339d:	41 89 b9 9c 06 00 00 	mov    %edi,0x69c(%r9)
    33a4:	89 c1                	mov    %eax,%ecx
    33a6:	bf 01 00 00 00       	mov    $0x1,%edi
              data[1].c = b;
    33ab:	45 89 a9 a4 06 00 00 	mov    %r13d,0x6a4(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    33b2:	41 83 c5 01          	add    $0x1,%r13d
              mailboxes[b].lower = &data[0];
    33b6:	4d 89 4e c8          	mov    %r9,-0x38(%r14)
    33ba:	41 89 46 fc          	mov    %eax,-0x4(%r14)
    33be:	31 c0                	xor    %eax,%eax
              data[1].kind = MAILBOX_HIGHER;
    33c0:	41 c7 81 98 06 00 00 02 00 00 00 	movl   $0x2,0x698(%r9)
              data[1].b = y;
    33cb:	41 89 a9 a0 06 00 00 	mov    %ebp,0x6a0(%r9)
              data[0].finished_reading = 1;
    33d2:	41 c7 81 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%r9)
              data[1].finished_reading = 1;
    33dd:	41 c7 81 80 06 00 00 01 00 00 00 	movl   $0x1,0x680(%r9)
              mailboxes[b].kind = MAILBOX_FRIEND;
    33e8:	41 c7 46 f8 01 00 00 00 	movl   $0x1,-0x8(%r14)
              data[1].finished_reading = 1;
    33f0:	4c 89 4c 24 08       	mov    %r9,0x8(%rsp)
    33f5:	e8 e6 f0 ff ff       	call   24e0 <__printf_chk@plt>
              data[0].messages = messages;
    33fa:	4c 8b 4c 24 08       	mov    0x8(%rsp),%r9
    33ff:	4c 8b 5c 24 58       	mov    0x58(%rsp),%r11
              data[0].messages_count = 0;
    3404:	66 0f 6f 35 74 58 00 00 	movdqa 0x5874(%rip),%xmm6        # 8c80 <_IO_stdin_used+0xc80>
              data[1].messages = messages2;
    340c:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
              data[0].messages = messages;
    3411:	4d 89 19             	mov    %r11,(%r9)
              data[1].messages = messages2;
    3414:	4d 89 91 80 03 00 00 	mov    %r10,0x380(%r9)
              data[0].messages_count = 0;
    341b:	41 0f 29 b1 80 00 00 00 	movaps %xmm6,0x80(%r9)
              data[1].messages_count = 0;
    3423:	41 0f 29 b1 00 04 00 00 	movaps %xmm6,0x400(%r9)
          for (int b = 0 ; b < mailboxes_needed ; b++) {
    342b:	41 83 fd 06          	cmp    $0x6,%r13d
    342f:	0f 85 ad fe ff ff    	jne    32e2 <main+0xc32>
    3435:	8b 1c 24             	mov    (%rsp),%ebx
    3438:	48 8b 4c 24 68       	mov    0x68(%rsp),%rcx
    343d:	e9 a3 f9 ff ff       	jmp    2de5 <main+0x735>
    3442:	48 8d 05 17 39 00 00 	lea    0x3917(%rip),%rax        # 6d60 <barriered_work_ingest_andwork>
    3449:	bd 01 00 00 00       	mov    $0x1,%ebp
            thread_data[x].tasks[y].run = barriered_work; 
    344e:	48 89 82 18 01 00 00 	mov    %rax,0x118(%rdx)
    3455:	8b 44 24 38          	mov    0x38(%rsp),%eax
    3459:	89 44 24 48          	mov    %eax,0x48(%rsp)
    345d:	e9 aa f7 ff ff       	jmp    2c0c <main+0x55c>
    3462:	48 8d 05 f7 32 00 00 	lea    0x32f7(%rip),%rax        # 6760 <barriered_work>
    3469:	bd 02 00 00 00       	mov    $0x2,%ebp
    346e:	eb de                	jmp    344e <main+0xd9e>
  for (int k = 0 ; k < group_count ; k++) {
    3470:	83 c0 02             	add    $0x2,%eax
    3473:	48 81 c2 a0 01 00 00 	add    $0x1a0,%rdx
    347a:	83 f8 06             	cmp    $0x6,%eax
    347d:	0f 85 77 fd ff ff    	jne    31fa <main+0xb4a>
    3483:	48 8d 3d 50 4f 00 00 	lea    0x4f50(%rip),%rdi        # 83da <_IO_stdin_used+0x3da>
    348a:	e8 c1 ee ff ff       	call   2350 <puts@plt>
      }
    }
  }
  printf("Mailboxes list mlist\n");
  FILE *m1;
  m1 = fopen("mailbox1", "w");
    348f:	48 8d 35 59 4f 00 00 	lea    0x4f59(%rip),%rsi        # 83ef <_IO_stdin_used+0x3ef>
    3496:	48 8d 3d 54 4f 00 00 	lea    0x4f54(%rip),%rdi        # 83f1 <_IO_stdin_used+0x3f1>
    349d:	e8 7e f0 ff ff       	call   2520 <fopen@plt>
    34a2:	49 89 c7             	mov    %rax,%r15
  for (int x = 0 ; x < datas_size; x++) {
    34a5:	45 85 e4             	test   %r12d,%r12d
    34a8:	7e 78                	jle    3522 <main+0xe72>
    34aa:	48 8d 05 61 4f 00 00 	lea    0x4f61(%rip),%rax        # 8412 <_IO_stdin_used+0x412>
    34b1:	4d 63 e4             	movslq %r12d,%r12
    34b4:	49 89 ed             	mov    %rbp,%r13
    34b7:	48 89 04 24          	mov    %rax,(%rsp)
    34bb:	4a 8d 6c e5 00       	lea    0x0(%rbp,%r12,8),%rbp
    34c0:	4c 8d 35 07 4f 00 00 	lea    0x4f07(%rip),%r14        # 83ce <_IO_stdin_used+0x3ce>
    char * c = calloc(250, sizeof(char));
    34c7:	be 01 00 00 00       	mov    $0x1,%esi
    34cc:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas_size; x++) {
    34d1:	49 83 c5 08          	add    $0x8,%r13
    char * c = calloc(250, sizeof(char));
    34d5:	e8 46 ef ff ff       	call   2420 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    34da:	4c 89 f1             	mov    %r14,%rcx
    34dd:	ba fa 00 00 00       	mov    $0xfa,%edx
    34e2:	be 01 00 00 00       	mov    $0x1,%esi
    34e7:	49 89 c4             	mov    %rax,%r12
    sprintf(c, "mailbox %d\n", cdatas[x]->id);
    34ea:	49 8b 45 f8          	mov    -0x8(%r13),%rax
    34ee:	4c 89 e7             	mov    %r12,%rdi
    34f1:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    34f8:	31 c0                	xor    %eax,%eax
    34fa:	e8 e1 f0 ff ff       	call   25e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    34ff:	48 8b 34 24          	mov    (%rsp),%rsi
    3503:	4c 89 e2             	mov    %r12,%rdx
    3506:	31 c0                	xor    %eax,%eax
    3508:	bf 01 00 00 00       	mov    $0x1,%edi
    350d:	e8 ce ef ff ff       	call   24e0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3512:	4c 89 fe             	mov    %r15,%rsi
    3515:	4c 89 e7             	mov    %r12,%rdi
    3518:	e8 c3 ee ff ff       	call   23e0 <fputs@plt>
  for (int x = 0 ; x < datas_size; x++) {
    351d:	4c 39 ed             	cmp    %r13,%rbp
    3520:	75 a5                	jne    34c7 <main+0xe17>
    printf("%s", c);
    fprintf(m1, "%s", c);
  } 
  fclose(m1);
    3522:	4c 89 ff             	mov    %r15,%rdi

  printf("Serialising thread_data\n");

  for (int k = 0 ; k < group_count ; k++) {
    3525:	31 ed                	xor    %ebp,%ebp
    3527:	4c 8d 35 0e 4f 00 00 	lea    0x4f0e(%rip),%r14        # 843c <_IO_stdin_used+0x43c>
  fclose(m1);
    352e:	e8 4d ee ff ff       	call   2380 <fclose@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3533:	48 8d 3d c0 4e 00 00 	lea    0x4ec0(%rip),%rdi        # 83fa <_IO_stdin_used+0x3fa>
    353a:	41 89 ec             	mov    %ebp,%r12d
    353d:	e8 0e ee ff ff       	call   2350 <puts@plt>
    3542:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3547:	48 89 04 24          	mov    %rax,(%rsp)
    354b:	44 89 e2             	mov    %r12d,%edx
    354e:	48 8d 35 c0 4e 00 00 	lea    0x4ec0(%rip),%rsi        # 8415 <_IO_stdin_used+0x415>
    3555:	31 c0                	xor    %eax,%eax
    printf("group-%d\n", k); 
    for (int d = 0 ; d < threads_per_group ; d++) {
    3557:	45 31 ed             	xor    %r13d,%r13d
    355a:	bf 01 00 00 00       	mov    $0x1,%edi
    355f:	47 8d 3c 24          	lea    (%r12,%r12,1),%r15d
    3563:	e8 78 ef ff ff       	call   24e0 <__printf_chk@plt>
    3568:	48 8b 2c 24          	mov    (%rsp),%rbp
    356c:	44 89 7c 24 08       	mov    %r15d,0x8(%rsp)
    3571:	44 89 e8             	mov    %r13d,%eax
    3574:	49 89 ed             	mov    %rbp,%r13
    3577:	89 dd                	mov    %ebx,%ebp
    3579:	89 c3                	mov    %eax,%ebx
      int x = (k * threads_per_group) + d;
    357b:	8b 44 24 08          	mov    0x8(%rsp),%eax
    357f:	89 da                	mov    %ebx,%edx
    3581:	48 8d 35 97 4e 00 00 	lea    0x4e97(%rip),%rsi        # 841f <_IO_stdin_used+0x41f>
    3588:	45 31 ff             	xor    %r15d,%r15d
    358b:	bf 01 00 00 00       	mov    $0x1,%edi
    3590:	8d 0c 03             	lea    (%rbx,%rax,1),%ecx
    3593:	31 c0                	xor    %eax,%eax
    3595:	e8 46 ef ff ff       	call   24e0 <__printf_chk@plt>
    359a:	89 6c 24 10          	mov    %ebp,0x10(%rsp)
    359e:	44 89 64 24 18       	mov    %r12d,0x18(%rsp)
    35a3:	89 5c 24 20          	mov    %ebx,0x20(%rsp)
    35a7:	44 89 fa             	mov    %r15d,%edx
    35aa:	48 8d 35 80 4e 00 00 	lea    0x4e80(%rip),%rsi        # 8431 <_IO_stdin_used+0x431>
    35b1:	31 c0                	xor    %eax,%eax
    35b3:	4c 89 fb             	mov    %r15,%rbx
    35b6:	bf 01 00 00 00       	mov    $0x1,%edi
    35bb:	48 c1 e3 09          	shl    $0x9,%rbx
    35bf:	45 31 e4             	xor    %r12d,%r12d
      printf("\tthread-%d rt-%d\n", d, x);
      for (int y = 0 ; y < total_barrier_count ; y++) {
        printf("\t\ttask-%d\n", y);  
        
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    35c2:	31 ed                	xor    %ebp,%ebp
    35c4:	e8 17 ef ff ff       	call   24e0 <__printf_chk@plt>
    35c9:	eb 2f                	jmp    35fa <main+0xf4a>
    35cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          char * mailbox_kind = calloc(100, sizeof(char));
          memset(mailbox_kind, '\0', 100);
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
            sprintf(mailbox_kind, "%s", "foreign");
          } else if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FRIEND) {
    35d0:	83 fa 01             	cmp    $0x1,%edx
    35d3:	0f 84 91 00 00 00    	je     366a <main+0xfba>
    35d9:	44 8b 40 34          	mov    0x34(%rax),%r8d
    35dd:	89 ea                	mov    %ebp,%edx
    35df:	4c 89 f6             	mov    %r14,%rsi
    35e2:	bf 01 00 00 00       	mov    $0x1,%edi
    35e7:	31 c0                	xor    %eax,%eax
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    35e9:	83 c5 01             	add    $0x1,%ebp
    35ec:	49 83 c4 38          	add    $0x38,%r12
    35f0:	e8 eb ee ff ff       	call   24e0 <__printf_chk@plt>
    35f5:	83 fd 06             	cmp    $0x6,%ebp
    35f8:	74 43                	je     363d <main+0xf8d>
          char * mailbox_kind = calloc(100, sizeof(char));
    35fa:	be 01 00 00 00       	mov    $0x1,%esi
    35ff:	bf 64 00 00 00       	mov    $0x64,%edi
    3604:	e8 17 ee ff ff       	call   2420 <calloc@plt>
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3609:	49 8b 75 38          	mov    0x38(%r13),%rsi
          char * mailbox_kind = calloc(100, sizeof(char));
    360d:	48 89 c1             	mov    %rax,%rcx
          if (thread_data[x].tasks[y].mailboxes[m].kind == MAILBOX_FOREIGN) {
    3610:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    3618:	4c 01 e0             	add    %r12,%rax
    361b:	8b 50 30             	mov    0x30(%rax),%edx
    361e:	83 fa 02             	cmp    $0x2,%edx
    3621:	75 ad                	jne    35d0 <main+0xf20>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3623:	48 b8 66 6f 72 65 69 67 6e 00 	movabs $0x6e676965726f66,%rax
    362d:	48 89 01             	mov    %rax,(%rcx)
            sprintf(mailbox_kind, "%s", "friend");

          }
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3630:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    3638:	4c 01 e0             	add    %r12,%rax
    363b:	eb 9c                	jmp    35d9 <main+0xf29>
      for (int y = 0 ; y < total_barrier_count ; y++) {
    363d:	49 83 c7 01          	add    $0x1,%r15
    3641:	49 83 ff 03          	cmp    $0x3,%r15
    3645:	0f 85 5c ff ff ff    	jne    35a7 <main+0xef7>
    for (int d = 0 ; d < threads_per_group ; d++) {
    364b:	8b 5c 24 20          	mov    0x20(%rsp),%ebx
    364f:	8b 6c 24 10          	mov    0x10(%rsp),%ebp
    3653:	49 81 c5 d0 00 00 00 	add    $0xd0,%r13
    365a:	44 8b 64 24 18       	mov    0x18(%rsp),%r12d
    365f:	85 db                	test   %ebx,%ebx
    3661:	75 24                	jne    3687 <main+0xfd7>
    3663:	89 eb                	mov    %ebp,%ebx
    3665:	e9 11 ff ff ff       	jmp    357b <main+0xecb>
    366a:	c7 01 66 72 69 65    	movl   $0x65697266,(%rcx)
    3670:	c7 41 03 65 6e 64 00 	movl   $0x646e65,0x3(%rcx)
          printf("\t\t\tmailbox-%d-%s other-%d\n", m, mailbox_kind, thread_data[x].tasks[y].mailboxes[m].other);
    3677:	48 8b 84 1e 70 01 00 00 	mov    0x170(%rsi,%rbx,1),%rax
    367f:	4c 01 e0             	add    %r12,%rax
    3682:	e9 52 ff ff ff       	jmp    35d9 <main+0xf29>
  for (int k = 0 ; k < group_count ; k++) {
    3687:	41 83 c4 01          	add    $0x1,%r12d
    368b:	41 89 dd             	mov    %ebx,%r13d
    368e:	48 81 04 24 a0 01 00 00 	addq   $0x1a0,(%rsp)
    3696:	89 eb                	mov    %ebp,%ebx
    3698:	41 83 fc 03          	cmp    $0x3,%r12d
    369c:	0f 85 a9 fe ff ff    	jne    354b <main+0xe9b>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    36a2:	ba 07 00 00 00       	mov    $0x7,%edx
    36a7:	bf 01 00 00 00       	mov    $0x1,%edi
    36ac:	31 c0                	xor    %eax,%eax
    36ae:	45 89 ec             	mov    %r13d,%r12d
    36b1:	48 8d 35 9f 4d 00 00 	lea    0x4d9f(%rip),%rsi        # 8457 <_IO_stdin_used+0x457>
    36b8:	e8 23 ee ff ff       	call   24e0 <__printf_chk@plt>
  }
  

  printf("io index = %d\n", io_index);
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    struct KernelThread **my_thread_data = calloc(2, sizeof(struct KernelThread*)); 
    36bd:	be 08 00 00 00       	mov    $0x8,%esi
    36c2:	bf 02 00 00 00       	mov    $0x2,%edi
    36c7:	e8 54 ed ff ff       	call   2420 <calloc@plt>
    my_thread_data[0] = &thread_data[x]; 
    36cc:	48 8b 6c 24 30       	mov    0x30(%rsp),%rbp
  // schedule first task
  for (int n = 0 ; n < thread_count ; n++) {
    thread_data[n].tasks[0].scheduled = 1;
  }

  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    36d1:	be 38 00 00 00       	mov    $0x38,%esi
    36d6:	bf 0a 00 00 00       	mov    $0xa,%edi
    my_thread_data[0] = &thread_data[x]; 
    36db:	4c 8d b5 b0 05 00 00 	lea    0x5b0(%rbp),%r14
    my_thread_data[1] = &thread_data[(x + 1) % thread_count]; 
    36e2:	48 89 68 08          	mov    %rbp,0x8(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    36e6:	4c 8d ad d0 00 00 00 	lea    0xd0(%rbp),%r13
    thread_data[x].threads = my_thread_data;
    36ed:	48 89 85 c8 05 00 00 	mov    %rax,0x5c8(%rbp)
    my_thread_data[0] = &thread_data[x]; 
    36f4:	4c 89 30             	mov    %r14,(%rax)
    thread_data[n].tasks[0].scheduled = 1;
    36f7:	48 8b 45 38          	mov    0x38(%rbp),%rax
    thread_data[x].thread_count = 2;
    36fb:	c7 85 d8 05 00 00 02 00 00 00 	movl   $0x2,0x5d8(%rbp)
    thread_data[x].thread_index = 0;
    3705:	c7 85 b4 05 00 00 00 00 00 00 	movl   $0x0,0x5b4(%rbp)
    thread_data[x].task_count = total_barrier_count;
    370f:	c7 85 f0 05 00 00 03 00 00 00 	movl   $0x3,0x5f0(%rbp)
    thread_data[n].tasks[0].scheduled = 1;
    3719:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
    3723:	48 8b 85 08 01 00 00 	mov    0x108(%rbp),%rax
    372a:	4c 89 2c 24          	mov    %r13,(%rsp)
    372e:	c7 80 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rax)
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3738:	e8 e3 ec ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    373d:	be 38 00 00 00       	mov    $0x38,%esi
    3742:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *thread_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3747:	48 89 44 24 18       	mov    %rax,0x18(%rsp)
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    374c:	e8 cf ec ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3751:	be 38 00 00 00       	mov    $0x38,%esi
    3756:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *timer_attr = calloc(total_threads, sizeof(pthread_attr_t));
    375b:	49 89 c7             	mov    %rax,%r15
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    375e:	e8 bd ec ff ff       	call   2420 <calloc@plt>
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3763:	be 38 00 00 00       	mov    $0x38,%esi
    3768:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *io_attr = calloc(total_threads, sizeof(pthread_attr_t));
    376d:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3772:	e8 a9 ec ff ff       	call   2420 <calloc@plt>
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3777:	be 08 00 00 00       	mov    $0x8,%esi
    377c:	bf 0a 00 00 00       	mov    $0xa,%edi
  pthread_attr_t      *external_attr = calloc(total_threads, sizeof(pthread_attr_t));
    3781:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    3786:	e8 95 ec ff ff       	call   2420 <calloc@plt>




  // thread_data[thread_count].threads = thread_data;
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    378b:	be 08 00 00 00       	mov    $0x8,%esi
    3790:	bf 0a 00 00 00       	mov    $0xa,%edi
  thread_data[timer_threadi].type = TIMER;
    3795:	c7 85 ec 04 00 00 00 00 00 00 	movl   $0x0,0x4ec(%rbp)
  pthread_t *thread = calloc(total_threads, sizeof(pthread_t));
    379f:	48 89 c3             	mov    %rax,%rbx
  thread_data[timer_threadi].task_count = total_barrier_count;
    37a2:	48 8b 05 0f 55 00 00 	mov    0x550f(%rip),%rax        # 8cb8 <_IO_stdin_used+0xcb8>
    37a9:	48 89 85 20 05 00 00 	mov    %rax,0x520(%rbp)
  struct KernelThread **my_thread_data = calloc(total_threads, sizeof(struct KernelThread*)); 
    37b0:	e8 6b ec ff ff       	call   2420 <calloc@plt>
  for (int n = 0 ; n < total_threads ; n++) {
    my_thread_data[n] = &thread_data[n]; 
    37b5:	48 8d 95 a0 01 00 00 	lea    0x1a0(%rbp),%rdx
    37bc:	bf 01 00 00 00       	mov    $0x1,%edi
    37c1:	48 8d 8d e0 04 00 00 	lea    0x4e0(%rbp),%rcx
    37c8:	48 89 50 10          	mov    %rdx,0x10(%rax)
    37cc:	48 8d 95 70 02 00 00 	lea    0x270(%rbp),%rdx
    37d3:	48 8d 35 8c 4c 00 00 	lea    0x4c8c(%rip),%rsi        # 8466 <_IO_stdin_used+0x466>
    37da:	48 89 50 18          	mov    %rdx,0x18(%rax)
    37de:	48 8d 95 40 03 00 00 	lea    0x340(%rbp),%rdx
    37e5:	48 89 50 20          	mov    %rdx,0x20(%rax)
    37e9:	48 8d 95 10 04 00 00 	lea    0x410(%rbp),%rdx
    37f0:	4c 89 68 08          	mov    %r13,0x8(%rax)
    37f4:	4c 8d ad 80 06 00 00 	lea    0x680(%rbp),%r13
    37fb:	48 89 50 28          	mov    %rdx,0x28(%rax)
    37ff:	48 8d 95 50 07 00 00 	lea    0x750(%rbp),%rdx
    3806:	48 89 48 30          	mov    %rcx,0x30(%rax)
    380a:	4c 89 70 38          	mov    %r14,0x38(%rax)
    380e:	48 89 50 48          	mov    %rdx,0x48(%rax)
    3812:	ba 06 00 00 00       	mov    $0x6,%edx
    3817:	48 89 28             	mov    %rbp,(%rax)
    381a:	4c 89 68 40          	mov    %r13,0x40(%rax)
  }
  thread_data[timer_threadi].threads = my_thread_data;
    381e:	48 89 85 f8 04 00 00 	mov    %rax,0x4f8(%rbp)
  thread_data[timer_threadi].total_thread_count = total_threads;
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3825:	48 8b 05 94 54 00 00 	mov    0x5494(%rip),%rax        # 8cc0 <_IO_stdin_used+0xcc0>
  thread_data[timer_threadi].my_thread_count = group_count * threads_per_group;
    382c:	c7 85 10 05 00 00 06 00 00 00 	movl   $0x6,0x510(%rbp)
  thread_data[timer_threadi].thread_count = group_count * threads_per_group;
    3836:	48 89 85 08 05 00 00 	mov    %rax,0x508(%rbp)
    383d:	31 c0                	xor    %eax,%eax
  thread_data[timer_threadi].thread_index = 0;
    383f:	c7 85 e4 04 00 00 00 00 00 00 	movl   $0x0,0x4e4(%rbp)
    my_thread_data[n] = &thread_data[n]; 
    3849:	48 89 4c 24 20       	mov    %rcx,0x20(%rsp)
    384e:	e8 8d ec ff ff       	call   24e0 <__printf_chk@plt>

  printf("Creating scheduler thread %d\n", timer_threadi);
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3853:	48 8b 4c 24 20       	mov    0x20(%rsp),%rcx
    3858:	49 8d b7 50 01 00 00 	lea    0x150(%r15),%rsi
  for (int k = 0 ; k < group_count ; k++) {
    385f:	45 31 ff             	xor    %r15d,%r15d
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    3862:	48 8d 15 37 0d 00 00 	lea    0xd37(%rip),%rdx        # 45a0 <timer_thread>
    3869:	48 8d 7b 30          	lea    0x30(%rbx),%rdi
    386d:	e8 8e ec ff ff       	call   2500 <pthread_create@plt>
  for (int k = 0 ; k < group_count ; k++) {
    3872:	48 89 5c 24 20       	mov    %rbx,0x20(%rsp)
    3877:	48 89 d9             	mov    %rbx,%rcx
  pthread_create(&thread[timer_threadi], &timer_attr[timer_threadi], &timer_thread, &thread_data[timer_threadi]);
    387a:	48 89 ea             	mov    %rbp,%rdx
    387d:	44 89 64 24 28       	mov    %r12d,0x28(%rsp)
    3882:	41 ba 02 00 00 00    	mov    $0x2,%r10d
    3888:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    388d:	4c 89 6c 24 38       	mov    %r13,0x38(%rsp)
    3892:	4c 89 74 24 18       	mov    %r14,0x18(%rsp)
    3897:	45 89 d6             	mov    %r10d,%r14d
    for (int d = 0 ; d < threads_per_group ; d++) {
    389a:	48 89 44 24 40       	mov    %rax,0x40(%rsp)
    389f:	47 8d 24 3f          	lea    (%r15,%r15,1),%r12d
        for (int m = 0 ; m < mailboxes_needed ; m++) {
    38a3:	49 89 c5             	mov    %rax,%r13
    38a6:	48 89 cb             	mov    %rcx,%rbx
    38a9:	48 89 4c 24 48       	mov    %rcx,0x48(%rsp)
    38ae:	48 89 d5             	mov    %rdx,%rbp
    38b1:	48 89 54 24 50       	mov    %rdx,0x50(%rsp)
      int x = (k * threads_per_group) + d;
      thread_data[x].type = WORKER;
    38b6:	c7 45 0c 01 00 00 00 	movl   $0x1,0xc(%rbp)
    38bd:	44 89 e2             	mov    %r12d,%edx
    38c0:	44 89 f9             	mov    %r15d,%ecx
    38c3:	31 c0                	xor    %eax,%eax
      thread_data[x].running = 1;
    38c5:	c7 45 44 01 00 00 00 	movl   $0x1,0x44(%rbp)
    38cc:	48 8d 35 1d 4f 00 00 	lea    0x4f1d(%rip),%rsi        # 87f0 <_IO_stdin_used+0x7f0>
    38d3:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int d = 0 ; d < threads_per_group ; d++) {
    38d8:	41 83 c4 01          	add    $0x1,%r12d
    38dc:	e8 ff eb ff ff       	call   24e0 <__printf_chk@plt>
      printf("Creating kernel worker thread %d in group %d\n", x, k);
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    38e1:	48 89 e9             	mov    %rbp,%rcx
    38e4:	4c 89 ee             	mov    %r13,%rsi
    38e7:	48 89 df             	mov    %rbx,%rdi
    38ea:	48 8d 15 cf 27 00 00 	lea    0x27cf(%rip),%rdx        # 60c0 <barriered_thread>
    for (int d = 0 ; d < threads_per_group ; d++) {
    38f1:	48 81 c5 d0 00 00 00 	add    $0xd0,%rbp
    38f8:	48 83 c3 08          	add    $0x8,%rbx
    38fc:	49 83 c5 38          	add    $0x38,%r13
      pthread_create(&thread[x], &thread_attr[x], &barriered_thread, &thread_data[x]);
    3900:	e8 fb eb ff ff       	call   2500 <pthread_create@plt>
      pthread_setaffinity_np(thread[x], sizeof(thread_data[x].cpu_set), thread_data[x].cpu_set);
    3905:	48 8b 55 e0          	mov    -0x20(%rbp),%rdx
    3909:	48 8b 7b f8          	mov    -0x8(%rbx),%rdi
    390d:	be 08 00 00 00       	mov    $0x8,%esi
    3912:	e8 29 ea ff ff       	call   2340 <pthread_setaffinity_np@plt>
    for (int d = 0 ; d < threads_per_group ; d++) {
    3917:	45 39 e6             	cmp    %r12d,%r14d
    391a:	75 9a                	jne    38b6 <main+0x1206>
  for (int k = 0 ; k < group_count ; k++) {
    391c:	48 8b 44 24 40       	mov    0x40(%rsp),%rax
    3921:	48 8b 4c 24 48       	mov    0x48(%rsp),%rcx
    3926:	41 83 c7 01          	add    $0x1,%r15d
    392a:	41 83 c6 02          	add    $0x2,%r14d
    392e:	48 8b 54 24 50       	mov    0x50(%rsp),%rdx
    3933:	48 83 c1 10          	add    $0x10,%rcx
    3937:	48 83 c0 70          	add    $0x70,%rax
    393b:	48 81 c2 a0 01 00 00 	add    $0x1a0,%rdx
    3942:	41 83 ff 03          	cmp    $0x3,%r15d
    3946:	0f 85 4e ff ff ff    	jne    389a <main+0x11ea>
    }
  }
  for (int x = io_index ; x < io_index + io_threads ; x++) {
    thread_data[x].type = IO;
    394c:	4c 8b 7c 24 30       	mov    0x30(%rsp),%r15
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;

    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3951:	be d8 00 00 00       	mov    $0xd8,%esi
    3956:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    395b:	48 8b 05 66 53 00 00 	mov    0x5366(%rip),%rax        # 8cc8 <_IO_stdin_used+0xcc8>
    thread_data[x].type = IO;
    3962:	48 8b 5c 24 20       	mov    0x20(%rsp),%rbx
    3967:	4c 8b 74 24 18       	mov    0x18(%rsp),%r14
    396c:	41 c7 87 bc 05 00 00 02 00 00 00 	movl   $0x2,0x5bc(%r15)
    3977:	44 8b 64 24 28       	mov    0x28(%rsp),%r12d
    thread_data[x].task_count = 0;
    397c:	49 89 87 f0 05 00 00 	mov    %rax,0x5f0(%r15)
    thread_data[x].type = IO;
    3983:	4c 8b 6c 24 38       	mov    0x38(%rsp),%r13
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3988:	e8 93 ea ff ff       	call   2420 <calloc@plt>
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    398d:	be 00 08 00 00       	mov    $0x800,%esi
    3992:	31 ff                	xor    %edi,%edi
    thread_data[x].ring = calloc(1, sizeof(struct io_uring));
    3994:	49 89 87 08 06 00 00 	mov    %rax,0x608(%r15)
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    399b:	e8 b0 eb ff ff       	call   2550 <eventfd@plt>
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39a0:	be 08 00 00 00       	mov    $0x8,%esi
    39a5:	bf 02 00 00 00       	mov    $0x2,%edi
    thread_data[x]._eventfd = eventfd(0, EFD_NONBLOCK); 
    39aa:	41 89 87 10 06 00 00 	mov    %eax,0x610(%r15)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    39b1:	e8 6a ea ff ff       	call   2420 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    39b6:	48 8b 3c 24          	mov    (%rsp),%rdi
    }
    thread_data[x].threads = my_thread_data;
    // thread_data[x].threads = thread_data;
    thread_data[x].thread_count = thread_count;
    39ba:	41 c7 87 d8 05 00 00 02 00 00 00 	movl   $0x2,0x5d8(%r15)
    39c5:	ba 07 00 00 00       	mov    $0x7,%edx
      my_thread_data[n] = &thread_data[n]; 
    39ca:	4c 89 38             	mov    %r15,(%rax)
    39cd:	48 8d 35 b0 4a 00 00 	lea    0x4ab0(%rip),%rsi        # 8484 <_IO_stdin_used+0x484>
    39d4:	48 89 78 08          	mov    %rdi,0x8(%rax)
    39d8:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].threads = my_thread_data;
    39dd:	49 89 87 c8 05 00 00 	mov    %rax,0x5c8(%r15)
    39e4:	31 c0                	xor    %eax,%eax
    thread_data[x].thread_index = x;
    39e6:	41 c7 87 b4 05 00 00 07 00 00 00 	movl   $0x7,0x5b4(%r15)
    39f1:	4d 89 ef             	mov    %r13,%r15
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
  }
  int external_index = io_index + io_threads;
  printf("External index is %d\n", external_index);
	int next_buffer = 0;
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    39f4:	41 bd 08 00 00 00    	mov    $0x8,%r13d
    39fa:	e8 e1 ea ff ff       	call   24e0 <__printf_chk@plt>
    pthread_create(&thread[x], &io_attr[x], &io_thread, &thread_data[x]);
    39ff:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
    3a04:	48 8d 7b 38          	lea    0x38(%rbx),%rdi
    3a08:	4c 89 f1             	mov    %r14,%rcx
    3a0b:	48 8d 15 be 1e 00 00 	lea    0x1ebe(%rip),%rdx        # 58d0 <io_thread>
    3a12:	4c 8d 73 40          	lea    0x40(%rbx),%r14
    3a16:	48 81 c6 88 01 00 00 	add    $0x188,%rsi
    3a1d:	e8 de ea ff ff       	call   2500 <pthread_create@plt>
    3a22:	ba 08 00 00 00       	mov    $0x8,%edx
    3a27:	48 8d 35 6d 4a 00 00 	lea    0x4a6d(%rip),%rsi        # 849b <_IO_stdin_used+0x49b>
    3a2e:	31 c0                	xor    %eax,%eax
    3a30:	bf 01 00 00 00       	mov    $0x1,%edi
    3a35:	e8 a6 ea ff ff       	call   24e0 <__printf_chk@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3a3a:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    3a3f:	44 89 e0             	mov    %r12d,%eax
    3a42:	49 89 dc             	mov    %rbx,%r12
    3a45:	89 c3                	mov    %eax,%ebx
    3a47:	48 81 c5 c0 01 00 00 	add    $0x1c0,%rbp
    3a4e:	44 89 ea             	mov    %r13d,%edx
    3a51:	48 8d 35 59 4a 00 00 	lea    0x4a59(%rip),%rsi        # 84b1 <_IO_stdin_used+0x4b1>
    3a58:	bf 01 00 00 00       	mov    $0x1,%edi
    3a5d:	31 c0                	xor    %eax,%eax
    3a5f:	e8 7c ea ff ff       	call   24e0 <__printf_chk@plt>
    printf("Creating external thread %d\n", x);
    thread_data[x].type = EXTERNAL;
    thread_data[x].running = 1;
    thread_data[x].task_count = 0;
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3a64:	be 08 00 00 00       	mov    $0x8,%esi
    3a69:	bf 01 00 00 00       	mov    $0x1,%edi
    thread_data[x].task_count = 0;
    3a6e:	48 8b 05 53 52 00 00 	mov    0x5253(%rip),%rax        # 8cc8 <_IO_stdin_used+0xcc8>
    thread_data[x].type = EXTERNAL;
    3a75:	41 c7 47 0c 03 00 00 00 	movl   $0x3,0xc(%r15)
    thread_data[x].task_count = 0;
    3a7d:	49 89 47 40          	mov    %rax,0x40(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3a81:	e8 9a e9 ff ff       	call   2420 <calloc@plt>
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3a86:	48 8b bc 24 a8 00 00 00 	mov    0xa8(%rsp),%rdi
	  thread_data[x].buffers_count = 1;
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3a8e:	be 08 00 00 00       	mov    $0x8,%esi
	  thread_data[x].buffers_count = 1;
    3a93:	41 c7 87 bc 00 00 00 01 00 00 00 	movl   $0x1,0xbc(%r15)
    thread_data[x].buffers = calloc(1, sizeof(struct Buffers*));
    3a9e:	49 89 47 50          	mov    %rax,0x50(%r15)
		thread_data[x].buffers[0] = &buffers[next_buffer++];
    3aa2:	48 89 38             	mov    %rdi,(%rax)
    struct KernelThread **my_thread_data = calloc(thread_count, sizeof(struct KernelThread*)); 
    3aa5:	bf 02 00 00 00       	mov    $0x2,%edi
    3aaa:	e8 71 e9 ff ff       	call   2420 <calloc@plt>
    for (int n = 0 ; n < thread_count ; n++) {
      my_thread_data[n] = &thread_data[n]; 
    3aaf:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    }
    thread_data[x].threads = my_thread_data;
    thread_data[x].thread_count = thread_count;
    thread_data[x].total_thread_count = total_threads;
    thread_data[x].thread_index = x;
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3ab4:	4c 89 f9             	mov    %r15,%rcx
    3ab7:	4c 89 f7             	mov    %r14,%rdi
    thread_data[x].threads = my_thread_data;
    3aba:	49 89 47 18          	mov    %rax,0x18(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3abe:	48 8d 15 cb 09 00 00 	lea    0x9cb(%rip),%rdx        # 4490 <external_thread>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3ac5:	49 83 c6 08          	add    $0x8,%r14
    3ac9:	49 81 c7 d0 00 00 00 	add    $0xd0,%r15
      my_thread_data[n] = &thread_data[n]; 
    3ad0:	48 89 30             	mov    %rsi,(%rax)
    3ad3:	48 8b 34 24          	mov    (%rsp),%rsi
    thread_data[x].thread_index = x;
    3ad7:	45 89 af 34 ff ff ff 	mov    %r13d,-0xcc(%r15)
      my_thread_data[n] = &thread_data[n]; 
    3ade:	48 89 70 08          	mov    %rsi,0x8(%rax)
    thread_data[x].thread_count = thread_count;
    3ae2:	48 8b 05 bf 51 00 00 	mov    0x51bf(%rip),%rax        # 8ca8 <_IO_stdin_used+0xca8>
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3ae9:	48 89 ee             	mov    %rbp,%rsi
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3aec:	48 83 c5 38          	add    $0x38,%rbp
    thread_data[x].thread_count = thread_count;
    3af0:	49 89 87 58 ff ff ff 	mov    %rax,-0xa8(%r15)
    pthread_create(&thread[x], &external_attr[x], &external_thread, &thread_data[x]);
    3af7:	e8 04 ea ff ff       	call   2500 <pthread_create@plt>
  for (int x = external_index, buffer_index = 0 ; x < external_index + external_threads; x++, buffer_index++) {
    3afc:	48 83 84 24 a8 00 00 00 10 	addq   $0x10,0xa8(%rsp)
    3b05:	41 83 fd 08          	cmp    $0x8,%r13d
    3b09:	75 43                	jne    3b4e <main+0x149e>
    3b0b:	41 bd 09 00 00 00    	mov    $0x9,%r13d
    3b11:	e9 38 ff ff ff       	jmp    3a4e <main+0x139e>
        other = (x + 1) % total_threads;
    3b16:	8b 5c 24 18          	mov    0x18(%rsp),%ebx
        my_thread_data[1] = &thread_data[other]; 
    3b1a:	4c 89 6c 24 40       	mov    %r13,0x40(%rsp)
    3b1f:	45 31 c0             	xor    %r8d,%r8d
    3b22:	48 8d 04 5b          	lea    (%rbx,%rbx,2),%rax
        other = (x + 1) % total_threads;
    3b26:	41 89 de             	mov    %ebx,%r14d
        my_thread_data[1] = &thread_data[other]; 
    3b29:	48 8d 14 83          	lea    (%rbx,%rax,4),%rdx
    3b2d:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3b32:	48 c1 e2 04          	shl    $0x4,%rdx
    3b36:	48 01 c2             	add    %rax,%rdx
        my_thread_data[0] = &thread_data[x]; 
    3b39:	4c 89 c8             	mov    %r9,%rax
    3b3c:	e9 2a ef ff ff       	jmp    2a6b <main+0x3bb>
            CPU_SET(j, sendercpu);
    3b41:	48 81 4d 00 ff 0f 00 00 	orq    $0xfff,0x0(%rbp)
          for (int j = 0 ; j < cores ; j++) {
    3b49:	e9 ad ef ff ff       	jmp    2afb <main+0x44b>
    3b4e:	89 d8                	mov    %ebx,%eax
    3b50:	4c 89 e3             	mov    %r12,%rbx
    3b53:	48 8d 2d 74 49 00 00 	lea    0x4974(%rip),%rbp        # 84ce <_IO_stdin_used+0x4ce>
    3b5a:	41 89 c4             	mov    %eax,%r12d
    3b5d:	48 8b 44 24 30       	mov    0x30(%rsp),%rax
    3b62:	4c 8d 70 04          	lea    0x4(%rax),%r14
    3b66:	4c 8d a8 24 08 00 00 	lea    0x824(%rax),%r13
    3b6d:	41 8b 4e 04          	mov    0x4(%r14),%ecx
    3b71:	41 8b 16             	mov    (%r14),%edx
    3b74:	48 89 ee             	mov    %rbp,%rsi
    3b77:	bf 01 00 00 00       	mov    $0x1,%edi
    3b7c:	31 c0                	xor    %eax,%eax
  }

  for (int x = 0 ; x < total_threads ; x++) {
    3b7e:	49 81 c6 d0 00 00 00 	add    $0xd0,%r14
    3b85:	e8 56 e9 ff ff       	call   24e0 <__printf_chk@plt>
    3b8a:	4d 39 f5             	cmp    %r14,%r13
    3b8d:	75 de                	jne    3b6d <main+0x14bd>
    3b8f:	48 8d 3d 4b 49 00 00 	lea    0x494b(%rip),%rdi        # 84e1 <_IO_stdin_used+0x4e1>
    3b96:	45 31 f6             	xor    %r14d,%r14d
    3b99:	4c 8d ac 24 e0 00 00 00 	lea    0xe0(%rsp),%r13
    3ba1:	e8 aa e7 ff ff       	call   2350 <puts@plt>
    printf("threadindex %d %d\n", thread_data[x].thread_index, thread_data[x].real_thread_index);
  }

  printf("Waiting for threads to finish\n");  
  for (int x = 0 ; x < total_threads ; x++) {
    3ba6:	48 8d 2d 52 49 00 00 	lea    0x4952(%rip),%rbp        # 84ff <_IO_stdin_used+0x4ff>
    void * result; 
    pthread_join(thread[x], &result);
    3bad:	4a 8b 3c f3          	mov    (%rbx,%r14,8),%rdi
    3bb1:	4c 89 ee             	mov    %r13,%rsi
    3bb4:	e8 d7 e9 ff ff       	call   2590 <pthread_join@plt>
    3bb9:	44 89 f2             	mov    %r14d,%edx
    3bbc:	48 89 ee             	mov    %rbp,%rsi
    3bbf:	bf 01 00 00 00       	mov    $0x1,%edi
    3bc4:	31 c0                	xor    %eax,%eax
  for (int x = 0 ; x < total_threads ; x++) {
    3bc6:	49 83 c6 01          	add    $0x1,%r14
    3bca:	e8 11 e9 ff ff       	call   24e0 <__printf_chk@plt>
    3bcf:	49 83 fe 0a          	cmp    $0xa,%r14
    3bd3:	75 d8                	jne    3bad <main+0x14fd>
    printf("Finished thread %d\n", x);
  }
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3bd5:	be 08 00 00 00       	mov    $0x8,%esi
    3bda:	bf 00 04 00 00       	mov    $0x400,%edi
  int datas2_size = 0; 
    3bdf:	31 db                	xor    %ebx,%ebx
  struct Data ** datas = calloc(1024, sizeof(struct Data*)); 
    3be1:	e8 3a e8 ff ff       	call   2420 <calloc@plt>
    3be6:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
    3beb:	49 89 c7             	mov    %rax,%r15
    3bee:	31 c0                	xor    %eax,%eax
  for (int k = 0 ; k < group_count ; k++) {
    for (int d = 0 ; d < threads_per_group ; d++) {
    3bf0:	49 89 d1             	mov    %rdx,%r9
    3bf3:	45 31 db             	xor    %r11d,%r11d
      int x = (k * threads_per_group) + d;
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3bf6:	45 8b 51 40          	mov    0x40(%r9),%r10d
    3bfa:	45 85 d2             	test   %r10d,%r10d
    3bfd:	0f 8e 9a 00 00 00    	jle    3c9d <main+0x15ed>
    3c03:	49 8b 79 38          	mov    0x38(%r9),%rdi
    3c07:	4d 63 c2             	movslq %r10d,%r8
    3c0a:	48 63 cb             	movslq %ebx,%rcx
    3c0d:	49 c1 e0 09          	shl    $0x9,%r8
    3c11:	49 8d 34 cf          	lea    (%r15,%rcx,8),%rsi
    3c15:	49 01 f8             	add    %rdi,%r8
    3c18:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c20:	48 8b 8f 70 01 00 00 	mov    0x170(%rdi),%rcx
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c27:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
    3c2e:	48 83 c6 60          	add    $0x60,%rsi
    3c32:	f3 0f 7e 61 38       	movq   0x38(%rcx),%xmm4
    3c37:	f3 0f 7e 59 70       	movq   0x70(%rcx),%xmm3
    3c3c:	f3 0f 7e 91 a8 00 00 00 	movq   0xa8(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c44:	f3 0f 7e 29          	movq   (%rcx),%xmm5
    3c48:	f3 0f 7e 89 e0 00 00 00 	movq   0xe0(%rcx),%xmm1
    3c50:	0f 16 61 40          	movhps 0x40(%rcx),%xmm4
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3c54:	0f 16 59 78          	movhps 0x78(%rcx),%xmm3
    3c58:	f3 0f 7e 81 18 01 00 00 	movq   0x118(%rcx),%xmm0
    3c60:	0f 16 91 b0 00 00 00 	movhps 0xb0(%rcx),%xmm2
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c67:	0f 16 69 08          	movhps 0x8(%rcx),%xmm5
    3c6b:	0f 11 66 b0          	movups %xmm4,-0x50(%rsi)
    3c6f:	0f 16 89 e8 00 00 00 	movhps 0xe8(%rcx),%xmm1
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher);
    3c76:	0f 16 81 20 01 00 00 	movhps 0x120(%rcx),%xmm0
          datas[datas2_size++] = ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower);
    3c7d:	0f 11 6e a0          	movups %xmm5,-0x60(%rsi)
    3c81:	0f 11 5e c0          	movups %xmm3,-0x40(%rsi)
    3c85:	0f 11 56 d0          	movups %xmm2,-0x30(%rsi)
    3c89:	0f 11 4e e0          	movups %xmm1,-0x20(%rsi)
    3c8d:	0f 11 46 f0          	movups %xmm0,-0x10(%rsi)
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3c91:	4c 39 c7             	cmp    %r8,%rdi
    3c94:	75 8a                	jne    3c20 <main+0x1570>
    3c96:	43 8d 0c 52          	lea    (%r10,%r10,2),%ecx
    3c9a:	8d 1c 8b             	lea    (%rbx,%rcx,4),%ebx
    for (int d = 0 ; d < threads_per_group ; d++) {
    3c9d:	49 81 c1 d0 00 00 00 	add    $0xd0,%r9
    3ca4:	45 85 db             	test   %r11d,%r11d
    3ca7:	75 08                	jne    3cb1 <main+0x1601>
    3ca9:	45 89 e3             	mov    %r12d,%r11d
    3cac:	e9 45 ff ff ff       	jmp    3bf6 <main+0x1546>
  for (int k = 0 ; k < group_count ; k++) {
    3cb1:	83 c0 02             	add    $0x2,%eax
    3cb4:	48 81 c2 a0 01 00 00 	add    $0x1a0,%rdx
    3cbb:	83 f8 06             	cmp    $0x6,%eax
    3cbe:	0f 85 2c ff ff ff    	jne    3bf0 <main+0x1540>
    3cc4:	48 8d 3d 48 48 00 00 	lea    0x4848(%rip),%rdi        # 8513 <_IO_stdin_used+0x513>
    3ccb:	e8 80 e6 ff ff       	call   2350 <puts@plt>
      }
    }
  }
  printf("Mailboxes list 2 mlist2\n");
  FILE *m2;
  m2 = fopen("mailbox2", "w");
    3cd0:	48 8d 35 18 47 00 00 	lea    0x4718(%rip),%rsi        # 83ef <_IO_stdin_used+0x3ef>
    3cd7:	48 8d 3d 4d 48 00 00 	lea    0x484d(%rip),%rdi        # 852b <_IO_stdin_used+0x52b>
    3cde:	e8 3d e8 ff ff       	call   2520 <fopen@plt>
    3ce3:	49 89 c4             	mov    %rax,%r12
  for (int x = 0 ; x < datas2_size; x++) {
    3ce6:	85 db                	test   %ebx,%ebx
    3ce8:	7e 74                	jle    3d5e <main+0x16ae>
    3cea:	48 8d 05 21 47 00 00 	lea    0x4721(%rip),%rax        # 8412 <_IO_stdin_used+0x412>
    3cf1:	48 63 db             	movslq %ebx,%rbx
    3cf4:	4c 8d 35 d3 46 00 00 	lea    0x46d3(%rip),%r14        # 83ce <_IO_stdin_used+0x3ce>
    3cfb:	48 89 04 24          	mov    %rax,(%rsp)
    3cff:	49 8d 2c df          	lea    (%r15,%rbx,8),%rbp
    char * c = calloc(250, sizeof(char));
    3d03:	be 01 00 00 00       	mov    $0x1,%esi
    3d08:	bf fa 00 00 00       	mov    $0xfa,%edi
  for (int x = 0 ; x < datas2_size; x++) {
    3d0d:	49 83 c7 08          	add    $0x8,%r15
    char * c = calloc(250, sizeof(char));
    3d11:	e8 0a e7 ff ff       	call   2420 <calloc@plt>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    3d16:	4c 89 f1             	mov    %r14,%rcx
    3d19:	ba fa 00 00 00       	mov    $0xfa,%edx
    3d1e:	be 01 00 00 00       	mov    $0x1,%esi
    3d23:	48 89 c3             	mov    %rax,%rbx
    sprintf(c, "mailbox %d\n", datas[x]->id);
    3d26:	49 8b 47 f8          	mov    -0x8(%r15),%rax
    3d2a:	48 89 df             	mov    %rbx,%rdi
    3d2d:	44 8b 80 28 03 00 00 	mov    0x328(%rax),%r8d
    3d34:	31 c0                	xor    %eax,%eax
    3d36:	e8 a5 e8 ff ff       	call   25e0 <__sprintf_chk@plt>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3d3b:	48 8b 34 24          	mov    (%rsp),%rsi
    3d3f:	48 89 da             	mov    %rbx,%rdx
    3d42:	31 c0                	xor    %eax,%eax
    3d44:	bf 01 00 00 00       	mov    $0x1,%edi
    3d49:	e8 92 e7 ff ff       	call   24e0 <__printf_chk@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    3d4e:	4c 89 e6             	mov    %r12,%rsi
    3d51:	48 89 df             	mov    %rbx,%rdi
    3d54:	e8 87 e6 ff ff       	call   23e0 <fputs@plt>
  for (int x = 0 ; x < datas2_size; x++) {
    3d59:	49 39 ef             	cmp    %rbp,%r15
    3d5c:	75 a5                	jne    3d03 <main+0x1653>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
        struct timespec end = thread_data[x].task_snapshot[n].task_end;
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3d5e:	49 bd db 34 b6 d7 82 de 1b 43 	movabs $0x431bde82d7b634db,%r13
  fclose(m2);
    3d68:	4c 89 e7             	mov    %r12,%rdi
  long received = 0;
    3d6b:	45 31 f6             	xor    %r14d,%r14d
  long sents = 0;
    3d6e:	45 31 e4             	xor    %r12d,%r12d
  fclose(m2);
    3d71:	e8 0a e6 ff ff       	call   2380 <fclose@plt>
    3d76:	b8 ff ff ff ff       	mov    $0xffffffff,%eax
  long sends = 0;
    3d7b:	48 c7 44 24 20 00 00 00 00 	movq   $0x0,0x20(%rsp)
  long ingests = 0;
    3d84:	48 c7 44 24 18 00 00 00 00 	movq   $0x0,0x18(%rsp)
  long total = 0;
    3d8d:	48 c7 44 24 28 00 00 00 00 	movq   $0x0,0x28(%rsp)
  int datas2_size = 0; 
    3d96:	48 8b bc 24 88 00 00 00 	mov    0x88(%rsp),%rdi
    3d9e:	8d 48 02             	lea    0x2(%rax),%ecx
    3da1:	89 44 24 08          	mov    %eax,0x8(%rsp)
    3da5:	89 4c 24 40          	mov    %ecx,0x40(%rsp)
    3da9:	4c 8b bc 24 a0 00 00 00 	mov    0xa0(%rsp),%r15
    3db1:	48 89 7c 24 38       	mov    %rdi,0x38(%rsp)
      int x = (k * threads_per_group) + d;
    3db6:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    3dba:	89 f8                	mov    %edi,%eax
    3dbc:	83 c7 01             	add    $0x1,%edi
        other = abs(x - 1) % total_threads;
    3dbf:	8d 50 02             	lea    0x2(%rax),%edx
    3dc2:	89 7c 24 08          	mov    %edi,0x8(%rsp)
    3dc6:	83 e7 01             	and    $0x1,%edi
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    3dc9:	bf 0a 00 00 00       	mov    $0xa,%edi
    3dce:	0f 44 c2             	cmove  %edx,%eax
    3dd1:	48 63 d8             	movslq %eax,%rbx
    3dd4:	e8 57 e5 ff ff       	call   2330 <putchar@plt>
    3dd9:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3dde:	bf 01 00 00 00       	mov    $0x1,%edi
    3de3:	48 8d 35 4a 47 00 00 	lea    0x474a(%rip),%rsi        # 8534 <_IO_stdin_used+0x534>
    3dea:	48 8b 10             	mov    (%rax),%rdx
    3ded:	31 c0                	xor    %eax,%eax
    3def:	e8 ec e6 ff ff       	call   24e0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3df4:	41 8b 57 40          	mov    0x40(%r15),%edx
    3df8:	85 d2                	test   %edx,%edx
    3dfa:	0f 8e d1 04 00 00    	jle    42d1 <main+0x1c21>
    3e00:	48 63 ca             	movslq %edx,%rcx
    3e03:	49 8b 47 38          	mov    0x38(%r15),%rax
      long v = 0;
    3e07:	31 d2                	xor    %edx,%edx
    3e09:	48 c1 e1 09          	shl    $0x9,%rcx
    3e0d:	48 01 c1             	add    %rax,%rcx
        v += thread_data[me].tasks[n].v;
    3e10:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[me].task_count ; n++) {
    3e17:	48 05 00 02 00 00    	add    $0x200,%rax
    3e1d:	48 39 c8             	cmp    %rcx,%rax
    3e20:	75 ee                	jne    3e10 <main+0x1760>
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3e22:	48 8d 04 5b          	lea    (%rbx,%rbx,2),%rax
    3e26:	48 8b 7c 24 30       	mov    0x30(%rsp),%rdi
    3e2b:	48 8d 04 83          	lea    (%rbx,%rax,4),%rax
    3e2f:	48 c1 e0 04          	shl    $0x4,%rax
    3e33:	48 01 f8             	add    %rdi,%rax
    3e36:	48 63 48 40          	movslq 0x40(%rax),%rcx
    3e3a:	85 c9                	test   %ecx,%ecx
    3e3c:	7e 24                	jle    3e62 <main+0x17b2>
    3e3e:	48 8b 40 38          	mov    0x38(%rax),%rax
    3e42:	48 c1 e1 09          	shl    $0x9,%rcx
    3e46:	48 01 c1             	add    %rax,%rcx
    3e49:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        v += thread_data[other].tasks[n].v;
    3e50:	48 03 90 10 01 00 00 	add    0x110(%rax),%rdx
      for (int n = 0 ; n < thread_data[other].task_count ; n++) {
    3e57:	48 05 00 02 00 00    	add    $0x200,%rax
    3e5d:	48 39 c8             	cmp    %rcx,%rax
    3e60:	75 ee                	jne    3e50 <main+0x17a0>
    3e62:	48 8d 35 e0 46 00 00 	lea    0x46e0(%rip),%rsi        # 8549 <_IO_stdin_used+0x549>
    3e69:	bf 01 00 00 00       	mov    $0x1,%edi
    3e6e:	31 c0                	xor    %eax,%eax
    3e70:	e8 6b e6 ff ff       	call   24e0 <__printf_chk@plt>
      printf("Total Protected per second %ld\n", protected_state[me].protected / DURATION);
    3e75:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    3e7a:	bf 01 00 00 00       	mov    $0x1,%edi
    3e7f:	48 8d 35 9a 49 00 00 	lea    0x499a(%rip),%rsi        # 8820 <_IO_stdin_used+0x820>
    3e86:	48 8b 08             	mov    (%rax),%rcx
    3e89:	48 b8 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rax
    3e93:	48 f7 e9             	imul   %rcx
    3e96:	48 c1 f9 3f          	sar    $0x3f,%rcx
    3e9a:	31 c0                	xor    %eax,%eax
    3e9c:	48 d1 fa             	sar    %rdx
    3e9f:	48 29 ca             	sub    %rcx,%rdx
    3ea2:	e8 39 e6 ff ff       	call   24e0 <__printf_chk@plt>
    3ea7:	bf 0a 00 00 00       	mov    $0xa,%edi
    3eac:	e8 7f e4 ff ff       	call   2330 <putchar@plt>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3eb1:	45 8b 57 40          	mov    0x40(%r15),%r10d
    3eb5:	45 85 d2             	test   %r10d,%r10d
    3eb8:	0f 8e 00 01 00 00    	jle    3fbe <main+0x190e>
        total += thread_data[x].tasks[n].n;
    3ebe:	49 8b 4f 38          	mov    0x38(%r15),%rcx
    3ec2:	4c 8b 44 24 28       	mov    0x28(%rsp),%r8
    3ec7:	31 d2                	xor    %edx,%edx
    3ec9:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3ece:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3ed3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    3ed8:	48 89 d5             	mov    %rdx,%rbp
    3edb:	89 14 24             	mov    %edx,(%rsp)
        sends += thread_data[x].tasks[n].sends;
    3ede:	31 db                	xor    %ebx,%ebx
    3ee0:	48 c1 e5 09          	shl    $0x9,%rbp
    3ee4:	48 89 54 24 28       	mov    %rdx,0x28(%rsp)
        total += thread_data[x].tasks[n].n;
    3ee9:	48 01 e9             	add    %rbp,%rcx
        sends += thread_data[x].tasks[n].sends;
    3eec:	48 89 e8             	mov    %rbp,%rax
    3eef:	4c 89 e5             	mov    %r12,%rbp
    3ef2:	4d 89 f4             	mov    %r14,%r12
        total += thread_data[x].tasks[n].n;
    3ef5:	4c 03 81 08 01 00 00 	add    0x108(%rcx),%r8
        ingests += thread_data[x].tasks[n].ingest_count;
    3efc:	48 03 b1 68 01 00 00 	add    0x168(%rcx),%rsi
        sends += thread_data[x].tasks[n].sends;
    3f03:	49 89 c6             	mov    %rax,%r14
    3f06:	48 03 b9 78 01 00 00 	add    0x178(%rcx),%rdi
    3f0d:	4c 89 44 24 10       	mov    %r8,0x10(%rsp)
    3f12:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    3f17:	48 89 7c 24 20       	mov    %rdi,0x20(%rsp)
    3f1c:	0f 1f 40 00          	nopl   0x0(%rax)
    3f20:	8b 0c 24             	mov    (%rsp),%ecx
    3f23:	8b 54 24 08          	mov    0x8(%rsp),%edx
    3f27:	41 89 d8             	mov    %ebx,%r8d
    3f2a:	bf 01 00 00 00       	mov    $0x1,%edi
    3f2f:	48 8d 35 20 46 00 00 	lea    0x4620(%rip),%rsi        # 8556 <_IO_stdin_used+0x556>
    3f36:	31 c0                	xor    %eax,%eax
    3f38:	e8 a3 e5 ff ff       	call   24e0 <__printf_chk@plt>
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f3d:	49 8b 4f 38          	mov    0x38(%r15),%rcx
    3f41:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    3f49:	48 29 d8             	sub    %rbx,%rax
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3f4c:	48 83 c3 01          	add    $0x1,%rbx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f50:	4a 8b 94 31 70 01 00 00 	mov    0x170(%rcx,%r14,1),%rdx
    3f58:	48 8d 04 c2          	lea    (%rdx,%rax,8),%rax
    3f5c:	48 8b 10             	mov    (%rax),%rdx
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3f5f:	48 8b 40 08          	mov    0x8(%rax),%rax
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f63:	4c 8b 8a 08 03 00 00 	mov    0x308(%rdx),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3f6a:	4c 8b 92 10 03 00 00 	mov    0x310(%rdx),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->sent;
    3f71:	49 01 e9             	add    %rbp,%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).lower)->received;
    3f74:	4d 01 e2             	add    %r12,%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3f77:	4c 03 88 08 03 00 00 	add    0x308(%rax),%r9
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3f7e:	4c 03 90 10 03 00 00 	add    0x310(%rax),%r10
          sents += ((struct Data*) ((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->sent;
    3f85:	4c 89 cd             	mov    %r9,%rbp
          received += ((struct Data*)((struct Mailbox)thread_data[x].tasks[n].mailboxes[kk]).higher)->received;
    3f88:	4d 89 d4             	mov    %r10,%r12
        for (int kk = 0 ; kk < mailboxes_needed ; kk++) {
    3f8b:	48 83 fb 06          	cmp    $0x6,%rbx
    3f8f:	75 8f                	jne    3f20 <main+0x1870>
      for (int n = 0 ; n < thread_data[x].task_count ; n++) {
    3f91:	48 8b 54 24 28       	mov    0x28(%rsp),%rdx
    3f96:	4c 8b 44 24 10       	mov    0x10(%rsp),%r8
    3f9b:	4d 89 d6             	mov    %r10,%r14
    3f9e:	4d 89 cc             	mov    %r9,%r12
    3fa1:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    3fa6:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    3fab:	48 83 c2 01          	add    $0x1,%rdx
    3faf:	41 39 57 40          	cmp    %edx,0x40(%r15)
    3fb3:	0f 8f 1f ff ff ff    	jg     3ed8 <main+0x1828>
    3fb9:	4c 89 44 24 28       	mov    %r8,0x28(%rsp)
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3fbe:	31 ed                	xor    %ebp,%ebp
    3fc0:	49 83 bf a0 00 00 00 00 	cmpq   $0x0,0xa0(%r15)
    3fc8:	48 8d 1d 71 48 00 00 	lea    0x4871(%rip),%rbx        # 8840 <_IO_stdin_used+0x840>
    3fcf:	7e 60                	jle    4031 <main+0x1981>
    3fd1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3fd8:	49 8b 87 90 00 00 00 	mov    0x90(%r15),%rax
    3fdf:	48 8d 54 ad 00       	lea    0x0(%rbp,%rbp,4),%rdx
    3fe4:	48 83 ec 08          	sub    $0x8,%rsp
    3fe8:	bf 01 00 00 00       	mov    $0x1,%edi
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    3fed:	48 83 c5 01          	add    $0x1,%rbp
        struct timespec start = thread_data[x].task_snapshot[n].task_start;
    3ff1:	48 8d 0c d0          	lea    (%rax,%rdx,8),%rcx
        const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    3ff5:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    3ff9:	48 2b 71 08          	sub    0x8(%rcx),%rsi
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    3ffd:	48 89 f0             	mov    %rsi,%rax
        const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    4000:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    4004:	4c 2b 01             	sub    (%rcx),%r8
        printf("%d tasks (%d) synchronized in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, thread_data[x].task_snapshot[n].task, seconds, seconds2 / 1000000, seconds2);
    4007:	49 f7 e5             	mul    %r13
    400a:	8b 49 20             	mov    0x20(%rcx),%ecx
    400d:	56                   	push   %rsi
    400e:	31 c0                	xor    %eax,%eax
    4010:	48 89 de             	mov    %rbx,%rsi
    4013:	48 c1 ea 12          	shr    $0x12,%rdx
    4017:	49 89 d1             	mov    %rdx,%r9
    401a:	ba 02 00 00 00       	mov    $0x2,%edx
    401f:	e8 bc e4 ff ff       	call   24e0 <__printf_chk@plt>
      for (int n = 0 ; n < thread_data[x].task_timestamp_limit ; n++) {
    4024:	41 58                	pop    %r8
    4026:	41 59                	pop    %r9
    4028:	49 39 af a0 00 00 00 	cmp    %rbp,0xa0(%r15)
    402f:	7f a7                	jg     3fd8 <main+0x1928>
        // printf("%ldns per thread\n", (seconds2 / 2));
      }
      // printf("cycles %ld\n", thread_data[x].cycles);

      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4031:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4038:	85 c9                	test   %ecx,%ecx
    403a:	0f 8e f4 00 00 00    	jle    4134 <main+0x1a84>
    4040:	4c 89 64 24 48       	mov    %r12,0x48(%rsp)
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4045:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    4049:	31 db                	xor    %ebx,%ebx
    404b:	4c 89 74 24 50       	mov    %r14,0x50(%rsp)
    4050:	49 8b 04 d9          	mov    (%r9,%rbx,8),%rax
    4054:	41 89 dc             	mov    %ebx,%r12d
    4057:	4c 8d 34 dd 00 00 00 00 	lea    0x0(,%rbx,8),%r14
    405f:	8b 30                	mov    (%rax),%esi
    4061:	85 f6                	test   %esi,%esi
    4063:	0f 8e b5 00 00 00    	jle    411e <main+0x1a6e>
    4069:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    406e:	48 8b 48 08          	mov    0x8(%rax),%rcx
    4072:	31 ff                	xor    %edi,%edi
    4074:	0f 1f 40 00          	nopl   0x0(%rax)
    4078:	48 89 fb             	mov    %rdi,%rbx
    407b:	31 ed                	xor    %ebp,%ebp
    407d:	48 c1 e3 08          	shl    $0x8,%rbx
    4081:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    4085:	8b 90 94 00 00 00    	mov    0x94(%rax),%edx
    408b:	85 d2                	test   %edx,%edx
    408d:	7e 77                	jle    4106 <main+0x1a56>
    408f:	48 89 3c 24          	mov    %rdi,(%rsp)
    4093:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    4098:	48 89 e9             	mov    %rbp,%rcx
    409b:	48 83 ec 08          	sub    $0x8,%rsp
    409f:	bf 01 00 00 00       	mov    $0x1,%edi
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    40a4:	48 83 c5 01          	add    $0x1,%rbp
      struct timespec end = thread_data[x].buffers[b]->buffer[n].snapshots[k].end;
    40a8:	48 c1 e1 05          	shl    $0x5,%rcx
    40ac:	48 03 88 88 00 00 00 	add    0x88(%rax),%rcx
      struct timespec start = thread_data[x].buffers[b]->buffer[n].snapshots[k].start;
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
      const uint64_t seconds2 = (end.tv_nsec) - (start.tv_nsec);
    40b3:	48 8b 71 18          	mov    0x18(%rcx),%rsi
    40b7:	48 2b 71 08          	sub    0x8(%rcx),%rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    40bb:	48 89 f0             	mov    %rsi,%rax
      const uint64_t seconds = (end.tv_sec) - (start.tv_sec);
    40be:	4c 8b 41 10          	mov    0x10(%rcx),%r8
    40c2:	4c 2b 01             	sub    (%rcx),%r8
    40c5:	56                   	push   %rsi
      printf("%d external ingest latency (%d) in %ld seconds %ld milliseconds %ld nanoseconds\n", 2, b, seconds, seconds2 / 1000000, seconds2);
    40c6:	49 f7 e5             	mul    %r13
    40c9:	44 89 e1             	mov    %r12d,%ecx
    40cc:	48 8d 35 bd 47 00 00 	lea    0x47bd(%rip),%rsi        # 8890 <_IO_stdin_used+0x890>
    40d3:	31 c0                	xor    %eax,%eax
    40d5:	48 c1 ea 12          	shr    $0x12,%rdx
    40d9:	49 89 d1             	mov    %rdx,%r9
    40dc:	ba 02 00 00 00       	mov    $0x2,%edx
    40e1:	e8 fa e3 ff ff       	call   24e0 <__printf_chk@plt>
    for (int k = 0 ; k < thread_data[x].buffers[b]->buffer[n].ingest_snapshot ; k++) {
    40e6:	4d 8b 4f 50          	mov    0x50(%r15),%r9
    40ea:	5e                   	pop    %rsi
    40eb:	5f                   	pop    %rdi
    40ec:	4b 8b 14 31          	mov    (%r9,%r14,1),%rdx
    40f0:	48 8b 4a 08          	mov    0x8(%rdx),%rcx
    40f4:	48 8d 04 19          	lea    (%rcx,%rbx,1),%rax
    40f8:	39 a8 94 00 00 00    	cmp    %ebp,0x94(%rax)
    40fe:	7f 98                	jg     4098 <main+0x19e8>
        for (int n = 0 ; n < thread_data[x].buffers[b]->count ; n++) {
    4100:	48 8b 3c 24          	mov    (%rsp),%rdi
    4104:	8b 32                	mov    (%rdx),%esi
    4106:	48 83 c7 01          	add    $0x1,%rdi
    410a:	39 fe                	cmp    %edi,%esi
    410c:	0f 8f 66 ff ff ff    	jg     4078 <main+0x19c8>
      for (int b = 0 ; b < thread_data[x].buffers_count ; b++) {
    4112:	48 8b 5c 24 10       	mov    0x10(%rsp),%rbx
    4117:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    411e:	48 83 c3 01          	add    $0x1,%rbx
    4122:	39 d9                	cmp    %ebx,%ecx
    4124:	0f 8f 26 ff ff ff    	jg     4050 <main+0x19a0>
    412a:	4c 8b 64 24 48       	mov    0x48(%rsp),%r12
    412f:	4c 8b 74 24 50       	mov    0x50(%rsp),%r14
    for (int d = 0 ; d < threads_per_group ; d++) {
    4134:	48 83 44 24 38 18    	addq   $0x18,0x38(%rsp)
    413a:	8b 7c 24 08          	mov    0x8(%rsp),%edi
    413e:	49 81 c7 d0 00 00 00 	add    $0xd0,%r15
    4145:	39 7c 24 40          	cmp    %edi,0x40(%rsp)
    4149:	0f 85 67 fc ff ff    	jne    3db6 <main+0x1706>
  for (int k = 0 ; k < group_count ; k++) {
    414f:	48 81 84 24 a0 00 00 00 a0 01 00 00 	addq   $0x1a0,0xa0(%rsp)
    415b:	8b 4c 24 40          	mov    0x40(%rsp),%ecx
    415f:	48 83 84 24 88 00 00 00 30 	addq   $0x30,0x88(%rsp)
    4168:	83 f9 05             	cmp    $0x5,%ecx
    416b:	74 07                	je     4174 <main+0x1ac4>
    416d:	89 c8                	mov    %ecx,%eax
    416f:	e9 22 fc ff ff       	jmp    3d96 <main+0x16e6>
    4174:	4c 8b 7c 24 28       	mov    0x28(%rsp),%r15
    4179:	48 8d 35 e6 43 00 00 	lea    0x43e6(%rip),%rsi        # 8566 <_IO_stdin_used+0x566>
    4180:	bf 01 00 00 00       	mov    $0x1,%edi
    4185:	31 c0                	xor    %eax,%eax
    }
  }
  printf("Total Requests %ld\n", total);
  printf("\n");
  printf("Total money %ld (correct if 0 or 500)\n", protected_state->balance);
  printf("Total external thread ingests per second %ld\n", ingests / DURATION);
    4187:	48 bb 67 66 66 66 66 66 66 66 	movabs $0x6666666666666667,%rbx
    4191:	4c 89 fa             	mov    %r15,%rdx
    4194:	e8 47 e3 ff ff       	call   24e0 <__printf_chk@plt>
    4199:	bf 0a 00 00 00       	mov    $0xa,%edi
    419e:	e8 8d e1 ff ff       	call   2330 <putchar@plt>
    41a3:	48 8b bc 24 98 00 00 00 	mov    0x98(%rsp),%rdi
    41ab:	48 8d 35 36 47 00 00 	lea    0x4736(%rip),%rsi        # 88e8 <_IO_stdin_used+0x8e8>
    41b2:	31 c0                	xor    %eax,%eax
    41b4:	48 8b 57 08          	mov    0x8(%rdi),%rdx
    41b8:	bf 01 00 00 00       	mov    $0x1,%edi
    41bd:	e8 1e e3 ff ff       	call   24e0 <__printf_chk@plt>
    41c2:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    41c7:	48 8b 7c 24 18       	mov    0x18(%rsp),%rdi
    41cc:	48 8d 35 3d 47 00 00 	lea    0x473d(%rip),%rsi        # 8910 <_IO_stdin_used+0x910>
    41d3:	48 f7 eb             	imul   %rbx
    41d6:	48 c1 ff 3f          	sar    $0x3f,%rdi
    41da:	31 c0                	xor    %eax,%eax
    41dc:	48 d1 fa             	sar    %rdx
    41df:	48 29 fa             	sub    %rdi,%rdx
    41e2:	bf 01 00 00 00       	mov    $0x1,%edi
    41e7:	e8 f4 e2 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total intra thread sends per second %ld\n", sends / DURATION);
    41ec:	48 8b 44 24 20       	mov    0x20(%rsp),%rax
    41f1:	48 8b 7c 24 20       	mov    0x20(%rsp),%rdi
    41f6:	48 8d 35 43 47 00 00 	lea    0x4743(%rip),%rsi        # 8940 <_IO_stdin_used+0x940>
    41fd:	48 f7 eb             	imul   %rbx
    4200:	48 c1 ff 3f          	sar    $0x3f,%rdi
    4204:	31 c0                	xor    %eax,%eax
    4206:	48 d1 fa             	sar    %rdx
    4209:	48 29 fa             	sub    %rdi,%rdx
    420c:	bf 01 00 00 00       	mov    $0x1,%edi
    4211:	e8 ca e2 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total Requests per second %ld\n", total / DURATION);
    4216:	4c 89 f8             	mov    %r15,%rax
    4219:	4c 89 ff             	mov    %r15,%rdi
    421c:	48 8d 35 4d 47 00 00 	lea    0x474d(%rip),%rsi        # 8970 <_IO_stdin_used+0x970>
    4223:	48 f7 eb             	imul   %rbx
    4226:	48 c1 ff 3f          	sar    $0x3f,%rdi
    422a:	31 c0                	xor    %eax,%eax
    422c:	48 d1 fa             	sar    %rdx
    422f:	48 29 fa             	sub    %rdi,%rdx
    4232:	bf 01 00 00 00       	mov    $0x1,%edi
    4237:	e8 a4 e2 ff ff       	call   24e0 <__printf_chk@plt>
  long sentdur = sents / DURATION;
    423c:	4c 89 e0             	mov    %r12,%rax
    423f:	bf 01 00 00 00       	mov    $0x1,%edi
    4244:	48 8d 35 2f 43 00 00 	lea    0x432f(%rip),%rsi        # 857a <_IO_stdin_used+0x57a>
    424b:	48 f7 eb             	imul   %rbx
    424e:	4c 89 e0             	mov    %r12,%rax
    4251:	48 c1 f8 3f          	sar    $0x3f,%rax
    4255:	48 d1 fa             	sar    %rdx
    4258:	48 29 c2             	sub    %rax,%rdx
    425b:	31 c0                	xor    %eax,%eax
    425d:	48 89 d5             	mov    %rdx,%rbp
    4260:	e8 7b e2 ff ff       	call   24e0 <__printf_chk@plt>
  printf("Total sents %ld\n", sentdur);
  long recdur = received / DURATION;
    4265:	4c 89 f0             	mov    %r14,%rax
    4268:	bf 01 00 00 00       	mov    $0x1,%edi
    426d:	48 8d 35 17 43 00 00 	lea    0x4317(%rip),%rsi        # 858b <_IO_stdin_used+0x58b>
    4274:	48 f7 eb             	imul   %rbx
    4277:	4c 89 f0             	mov    %r14,%rax
    427a:	48 c1 f8 3f          	sar    $0x3f,%rax
    427e:	48 89 d3             	mov    %rdx,%rbx
    4281:	48 d1 fb             	sar    %rbx
    4284:	48 29 c3             	sub    %rax,%rbx
    4287:	31 c0                	xor    %eax,%eax
    4289:	48 89 da             	mov    %rbx,%rdx
  printf("Total receives %ld\n", recdur);
  // verify(thread_data, thread_count);
  printf("Difference %ld\n", recdur - sentdur);
    428c:	48 29 eb             	sub    %rbp,%rbx
    428f:	e8 4c e2 ff ff       	call   24e0 <__printf_chk@plt>
    4294:	31 c0                	xor    %eax,%eax
    4296:	48 89 da             	mov    %rbx,%rdx
    4299:	bf 01 00 00 00       	mov    $0x1,%edi
    429e:	48 8d 35 fa 42 00 00 	lea    0x42fa(%rip),%rsi        # 859f <_IO_stdin_used+0x59f>
    42a5:	e8 36 e2 ff ff       	call   24e0 <__printf_chk@plt>
  return 0;

}
    42aa:	48 8b 84 24 e8 00 00 00 	mov    0xe8(%rsp),%rax
    42b2:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    42bb:	75 25                	jne    42e2 <main+0x1c32>
    42bd:	48 81 c4 f8 00 00 00 	add    $0xf8,%rsp
    42c4:	31 c0                	xor    %eax,%eax
    42c6:	5b                   	pop    %rbx
    42c7:	5d                   	pop    %rbp
    42c8:	41 5c                	pop    %r12
    42ca:	41 5d                	pop    %r13
    42cc:	41 5e                	pop    %r14
    42ce:	41 5f                	pop    %r15
    42d0:	c3                   	ret
      long v = 0;
    42d1:	31 d2                	xor    %edx,%edx
    42d3:	e9 4a fb ff ff       	jmp    3e22 <main+0x1772>
            exit(1);
    42d8:	bf 01 00 00 00       	mov    $0x1,%edi
    42dd:	e8 5e e2 ff ff       	call   2540 <exit@plt>
}
    42e2:	e8 b9 e0 ff ff       	call   23a0 <__stack_chk_fail@plt>
    42e7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

00000000000042f0 <_start>:
    42f0:	f3 0f 1e fa          	endbr64
    42f4:	31 ed                	xor    %ebp,%ebp
    42f6:	49 89 d1             	mov    %rdx,%r9
    42f9:	5e                   	pop    %rsi
    42fa:	48 89 e2             	mov    %rsp,%rdx
    42fd:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
    4301:	50                   	push   %rax
    4302:	54                   	push   %rsp
    4303:	45 31 c0             	xor    %r8d,%r8d
    4306:	31 c9                	xor    %ecx,%ecx
    4308:	48 8d 3d a1 e3 ff ff 	lea    -0x1c5f(%rip),%rdi        # 26b0 <main>
    430f:	ff 15 c3 6c 00 00    	call   *0x6cc3(%rip)        # afd8 <__libc_start_main@GLIBC_2.34>
    4315:	f4                   	hlt
    4316:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000004320 <deregister_tm_clones>:
    4320:	48 8d 3d f9 6c 00 00 	lea    0x6cf9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4327:	48 8d 05 f2 6c 00 00 	lea    0x6cf2(%rip),%rax        # b020 <stderr@GLIBC_2.2.5>
    432e:	48 39 f8             	cmp    %rdi,%rax
    4331:	74 15                	je     4348 <deregister_tm_clones+0x28>
    4333:	48 8b 05 a6 6c 00 00 	mov    0x6ca6(%rip),%rax        # afe0 <_ITM_deregisterTMCloneTable@Base>
    433a:	48 85 c0             	test   %rax,%rax
    433d:	74 09                	je     4348 <deregister_tm_clones+0x28>
    433f:	ff e0                	jmp    *%rax
    4341:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4348:	c3                   	ret
    4349:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004350 <register_tm_clones>:
    4350:	48 8d 3d c9 6c 00 00 	lea    0x6cc9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    4357:	48 8d 35 c2 6c 00 00 	lea    0x6cc2(%rip),%rsi        # b020 <stderr@GLIBC_2.2.5>
    435e:	48 29 fe             	sub    %rdi,%rsi
    4361:	48 89 f0             	mov    %rsi,%rax
    4364:	48 c1 ee 3f          	shr    $0x3f,%rsi
    4368:	48 c1 f8 03          	sar    $0x3,%rax
    436c:	48 01 c6             	add    %rax,%rsi
    436f:	48 d1 fe             	sar    %rsi
    4372:	74 14                	je     4388 <register_tm_clones+0x38>
    4374:	48 8b 05 75 6c 00 00 	mov    0x6c75(%rip),%rax        # aff0 <_ITM_registerTMCloneTable@Base>
    437b:	48 85 c0             	test   %rax,%rax
    437e:	74 08                	je     4388 <register_tm_clones+0x38>
    4380:	ff e0                	jmp    *%rax
    4382:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4388:	c3                   	ret
    4389:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000004390 <__do_global_dtors_aux>:
    4390:	f3 0f 1e fa          	endbr64
    4394:	80 3d 8d 6c 00 00 00 	cmpb   $0x0,0x6c8d(%rip)        # b028 <completed.0>
    439b:	75 2b                	jne    43c8 <__do_global_dtors_aux+0x38>
    439d:	55                   	push   %rbp
    439e:	48 83 3d 52 6c 00 00 00 	cmpq   $0x0,0x6c52(%rip)        # aff8 <__cxa_finalize@GLIBC_2.2.5>
    43a6:	48 89 e5             	mov    %rsp,%rbp
    43a9:	74 0c                	je     43b7 <__do_global_dtors_aux+0x27>
    43ab:	48 8b 3d 56 6c 00 00 	mov    0x6c56(%rip),%rdi        # b008 <__dso_handle>
    43b2:	e8 59 df ff ff       	call   2310 <__cxa_finalize@plt>
    43b7:	e8 64 ff ff ff       	call   4320 <deregister_tm_clones>
    43bc:	c6 05 65 6c 00 00 01 	movb   $0x1,0x6c65(%rip)        # b028 <completed.0>
    43c3:	5d                   	pop    %rbp
    43c4:	c3                   	ret
    43c5:	0f 1f 00             	nopl   (%rax)
    43c8:	c3                   	ret
    43c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000043d0 <frame_dummy>:
    43d0:	f3 0f 1e fa          	endbr64
    43d4:	e9 77 ff ff ff       	jmp    4350 <register_tm_clones>
    43d9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000043e0 <do_protected_write>:
int do_protected_write(struct BarrierTask *data) {
    43e0:	f3 0f 1e fa          	endbr64
  struct ProtectedState *protected = data->thread->protected_state;
    43e4:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    43eb:	48 8b 40 48          	mov    0x48(%rax),%rax
  data->v++; // thread local
    43ef:	48 83 87 10 01 00 00 01 	addq   $0x1,0x110(%rdi)
  if (protected->balance > 0) {
    43f7:	48 8b 48 08          	mov    0x8(%rax),%rcx
  protected->protected++; // shared between all threads
    43fb:	48 83 00 01          	addq   $0x1,(%rax)
    protected->balance -= 500; // shared between all threads
    43ff:	48 8d b1 0c fe ff ff 	lea    -0x1f4(%rcx),%rsi
    4406:	48 85 c9             	test   %rcx,%rcx
    4409:	48 8d 91 f4 01 00 00 	lea    0x1f4(%rcx),%rdx
    4410:	48 0f 4f d6          	cmovg  %rsi,%rdx
    4414:	48 89 50 08          	mov    %rdx,0x8(%rax)
}
    4418:	31 c0                	xor    %eax,%eax
    441a:	c3                   	ret
    441b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000004420 <barriered_reset>:
int barriered_reset(struct BarrierTask *data) {
    4420:	f3 0f 1e fa          	endbr64
    for (int x = 0 ; x < data->task_count ; x++) {
    4424:	48 63 8f 48 01 00 00 	movslq 0x148(%rdi),%rcx
    442b:	85 c9                	test   %ecx,%ecx
    442d:	7e 4f                	jle    447e <barriered_reset+0x5e>
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    442f:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    4436:	48 63 b7 30 01 00 00 	movslq 0x130(%rdi),%rsi
    443d:	48 c1 e1 09          	shl    $0x9,%rcx
    4441:	48 8b 50 18          	mov    0x18(%rax),%rdx
    4445:	48 8b 14 f2          	mov    (%rdx,%rsi,8),%rdx
      data->thread->tasks[x].available = 1; 
    4449:	48 8b 70 38          	mov    0x38(%rax),%rsi
    444d:	31 c0                	xor    %eax,%eax
      data->thread->threads[data->thread_index]->tasks[x].arrived++; 
    444f:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4453:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4458:	83 84 02 80 00 00 00 01 	addl   $0x1,0x80(%rdx,%rax,1)
      data->thread->threads[data->thread_index]->tasks[x].prearrive++; 
    4460:	83 84 02 00 01 00 00 01 	addl   $0x1,0x100(%rdx,%rax,1)
      data->thread->tasks[x].available = 1; 
    4468:	c7 84 06 44 01 00 00 01 00 00 00 	movl   $0x1,0x144(%rsi,%rax,1)
    for (int x = 0 ; x < data->task_count ; x++) {
    4473:	48 05 00 02 00 00    	add    $0x200,%rax
    4479:	48 39 c1             	cmp    %rax,%rcx
    447c:	75 da                	jne    4458 <barriered_reset+0x38>
  asm volatile ("sfence" ::: "memory");
    447e:	0f ae f8             	sfence
}
    4481:	31 c0                	xor    %eax,%eax
    4483:	c3                   	ret
    4484:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    448f:	90                   	nop

0000000000004490 <external_thread>:
void * external_thread(void *arg) {
    4490:	f3 0f 1e fa          	endbr64
  while (data->running == 1) {
    4494:	83 7f 44 01          	cmpl   $0x1,0x44(%rdi)
    4498:	0f 85 fb 00 00 00    	jne    4599 <external_thread+0x109>
void * external_thread(void *arg) {
    449e:	41 57                	push   %r15
    44a0:	49 89 ff             	mov    %rdi,%r15
    44a3:	41 56                	push   %r14
    44a5:	41 55                	push   %r13
					data->buffers[b]->buffer[x].data = "Hello world";
    44a7:	4c 8d 2d 56 3b 00 00 	lea    0x3b56(%rip),%r13        # 8004 <_IO_stdin_used+0x4>
void * external_thread(void *arg) {
    44ae:	41 54                	push   %r12
    44b0:	55                   	push   %rbp
    44b1:	53                   	push   %rbx
    44b2:	48 83 ec 08          	sub    $0x8,%rsp
    for (int b = 0; b < data->buffers_count; b++) {
    44b6:	8b 8f bc 00 00 00    	mov    0xbc(%rdi),%ecx
    44bc:	48 8b 7f 50          	mov    0x50(%rdi),%rdi
    44c0:	85 c9                	test   %ecx,%ecx
    44c2:	7e 6e                	jle    4532 <external_thread+0xa2>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    44c4:	45 31 e4             	xor    %r12d,%r12d
    44c7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    44d0:	4e 8d 34 e5 00 00 00 00 	lea    0x0(,%r12,8),%r14
    44d8:	31 db                	xor    %ebx,%ebx
    44da:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    44de:	48 8b 06             	mov    (%rsi),%rax
    44e1:	8b 10                	mov    (%rax),%edx
    44e3:	85 d2                	test   %edx,%edx
    44e5:	7e 2a                	jle    4511 <external_thread+0x81>
    44e7:	48 8b 48 08          	mov    0x8(%rax),%rcx
				if (data->buffers[b]->buffer[x].available == 0) {
    44eb:	48 89 dd             	mov    %rbx,%rbp
    44ee:	48 c1 e5 08          	shl    $0x8,%rbp
    44f2:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    44f6:	44 8b 80 80 00 00 00 	mov    0x80(%rax),%r8d
    44fd:	45 85 c0             	test   %r8d,%r8d
    4500:	74 36                	je     4538 <external_thread+0xa8>
      for (int x = 0; x < data->buffers[b]->count; x++) {
    4502:	48 83 c3 01          	add    $0x1,%rbx
    4506:	39 da                	cmp    %ebx,%edx
    4508:	7f e1                	jg     44eb <external_thread+0x5b>
    for (int b = 0; b < data->buffers_count; b++) {
    450a:	41 8b 8f bc 00 00 00 	mov    0xbc(%r15),%ecx
    4511:	49 83 c4 01          	add    $0x1,%r12
    4515:	44 39 e1             	cmp    %r12d,%ecx
    4518:	7f b6                	jg     44d0 <external_thread+0x40>
  while (data->running == 1) {
    451a:	41 83 7f 44 01       	cmpl   $0x1,0x44(%r15)
    451f:	74 9f                	je     44c0 <external_thread+0x30>
}
    4521:	48 83 c4 08          	add    $0x8,%rsp
    4525:	31 c0                	xor    %eax,%eax
    4527:	5b                   	pop    %rbx
    4528:	5d                   	pop    %rbp
    4529:	41 5c                	pop    %r12
    452b:	41 5d                	pop    %r13
    452d:	41 5e                	pop    %r14
    452f:	41 5f                	pop    %r15
    4531:	c3                   	ret
  while (data->running == 1) {
    4532:	eb fe                	jmp    4532 <external_thread+0xa2>
    4534:	0f 1f 40 00          	nopl   0x0(%rax)
					data->buffers[b]->buffer[x].data = "Hello world";
    4538:	4c 89 28             	mov    %r13,(%rax)
					clock_gettime(CLOCK_MONOTONIC_RAW, &data->buffers[b]->buffer[x].snapshots[data->buffers[b]->buffer[x].ingest_snapshot].start);
    453b:	48 8b 06             	mov    (%rsi),%rax
    453e:	48 8b 78 08          	mov    0x8(%rax),%rdi
    4542:	48 01 ef             	add    %rbp,%rdi
    4545:	48 63 b7 94 00 00 00 	movslq 0x94(%rdi),%rsi
    454c:	48 c1 e6 05          	shl    $0x5,%rsi
    4550:	48 03 b7 88 00 00 00 	add    0x88(%rdi),%rsi
    4557:	bf 04 00 00 00       	mov    $0x4,%edi
    455c:	e8 0f de ff ff       	call   2370 <clock_gettime@plt>
					data->buffers[b]->buffer[x].available = 1;
    4561:	49 8b 47 50          	mov    0x50(%r15),%rax
    4565:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    4569:	48 8b 40 08          	mov    0x8(%rax),%rax
    456d:	c7 84 28 80 00 00 00 01 00 00 00 	movl   $0x1,0x80(%rax,%rbp,1)
          asm volatile ("sfence" ::: "memory");
    4578:	0f ae f8             	sfence
      for (int x = 0; x < data->buffers[b]->count; x++) {
    457b:	49 8b 7f 50          	mov    0x50(%r15),%rdi
    457f:	48 83 c3 01          	add    $0x1,%rbx
    4583:	4a 8d 34 37          	lea    (%rdi,%r14,1),%rsi
    4587:	48 8b 06             	mov    (%rsi),%rax
    458a:	8b 10                	mov    (%rax),%edx
    458c:	39 da                	cmp    %ebx,%edx
    458e:	0f 8f 53 ff ff ff    	jg     44e7 <external_thread+0x57>
    4594:	e9 71 ff ff ff       	jmp    450a <external_thread+0x7a>
}
    4599:	31 c0                	xor    %eax,%eax
    459b:	c3                   	ret
    459c:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000045a0 <timer_thread>:
void* timer_thread(void *arg) {
    45a0:	f3 0f 1e fa          	endbr64
    45a4:	41 57                	push   %r15
    45a6:	48 8d 35 63 3a 00 00 	lea    0x3a63(%rip),%rsi        # 8010 <_IO_stdin_used+0x10>
    45ad:	41 56                	push   %r14
    45af:	41 55                	push   %r13
    45b1:	41 54                	push   %r12
    45b3:	55                   	push   %rbp
    45b4:	53                   	push   %rbx
    45b5:	48 89 fb             	mov    %rdi,%rbx
    45b8:	48 83 ec 68          	sub    $0x68,%rsp
    45bc:	8b 57 04             	mov    0x4(%rdi),%edx
    45bf:	bf 01 00 00 00       	mov    $0x1,%edi
    45c4:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    45cd:	48 89 44 24 58       	mov    %rax,0x58(%rsp)
    45d2:	31 c0                	xor    %eax,%eax
    45d4:	e8 07 df ff ff       	call   24e0 <__printf_chk@plt>
  struct timespec preempt = {
    45d9:	66 0f 6f 05 af 45 00 00 	movdqa 0x45af(%rip),%xmm0        # 8b90 <_IO_stdin_used+0xb90>
    45e1:	ba 88 13 00 00       	mov    $0x1388,%edx
    45e6:	31 c0                	xor    %eax,%eax
    45e8:	48 8d 35 33 3a 00 00 	lea    0x3a33(%rip),%rsi        # 8022 <_IO_stdin_used+0x22>
    45ef:	bf 01 00 00 00       	mov    $0x1,%edi
    45f4:	0f 29 44 24 20       	movaps %xmm0,0x20(%rsp)
    45f9:	e8 e2 de ff ff       	call   24e0 <__printf_chk@plt>
  while (data->running && n < times) {
    45fe:	8b 6b 44             	mov    0x44(%rbx),%ebp
    4601:	85 ed                	test   %ebp,%ebp
    4603:	0f 84 9b 00 00 00    	je     46a4 <timer_thread+0x104>
  int n = 0;
    4609:	45 31 ff             	xor    %r15d,%r15d
  int y = 0;
    460c:	31 ed                	xor    %ebp,%ebp
    460e:	4c 8d 74 24 10       	lea    0x10(%rsp),%r14
    y++;
    4613:	45 31 e4             	xor    %r12d,%r12d
    4616:	4c 8d 6c 24 20       	lea    0x20(%rsp),%r13
    nanosleep(&preempt , &rem2);
    461b:	4c 89 ef             	mov    %r13,%rdi
    461e:	4c 89 f6             	mov    %r14,%rsi
    n++;
    4621:	41 83 c7 01          	add    $0x1,%r15d
    nanosleep(&preempt , &rem2);
    4625:	e8 96 dd ff ff       	call   23c0 <nanosleep@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    462a:	48 63 43 30          	movslq 0x30(%rbx),%rax
    y++;
    462e:	8d 7d 01             	lea    0x1(%rbp),%edi
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4631:	85 c0                	test   %eax,%eax
    4633:	7e 48                	jle    467d <timer_thread+0xdd>
    4635:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    4639:	4c 63 c5             	movslq %ebp,%r8
    463c:	49 c1 e0 09          	shl    $0x9,%r8
    4640:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4644:	0f 1f 40 00          	nopl   0x0(%rax)
        int next = (y + 1) % data->threads[x]->task_count;
    4648:	4c 8b 19             	mov    (%rcx),%r11
    464b:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    464d:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4651:	99                   	cltd
    4652:	41 f7 7b 40          	idivl  0x40(%r11)
        data->threads[x]->tasks[next].scheduled = 1;
    4656:	49 8b 73 38          	mov    0x38(%r11),%rsi
    465a:	48 63 d2             	movslq %edx,%rdx
    465d:	48 c1 e2 09          	shl    $0x9,%rdx
    4661:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    466c:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4678:	49 39 c9             	cmp    %rcx,%r9
    467b:	75 cb                	jne    4648 <timer_thread+0xa8>
    asm volatile ("mfence" ::: "memory");
    467d:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4680:	48 8b 43 18          	mov    0x18(%rbx),%rax
  while (data->running && n < times) {
    4684:	8b 4b 44             	mov    0x44(%rbx),%ecx
    if (y >= data->threads[0]->task_count) {
    4687:	48 8b 00             	mov    (%rax),%rax
    y++;
    468a:	39 78 40             	cmp    %edi,0x40(%rax)
    468d:	41 0f 4e fc          	cmovle %r12d,%edi
    4691:	89 fd                	mov    %edi,%ebp
  while (data->running && n < times) {
    4693:	85 c9                	test   %ecx,%ecx
    4695:	74 0d                	je     46a4 <timer_thread+0x104>
    4697:	41 81 ff 88 13 00 00 	cmp    $0x1388,%r15d
    469e:	0f 85 77 ff ff ff    	jne    461b <timer_thread+0x7b>
    46a4:	48 8d 3d 8d 39 00 00 	lea    0x398d(%rip),%rdi        # 8038 <_IO_stdin_used+0x38>
    46ab:	e8 a0 dc ff ff       	call   2350 <puts@plt>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    46b0:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    46b4:	85 d2                	test   %edx,%edx
    46b6:	7e 6d                	jle    4725 <timer_thread+0x185>
    for (int y = 0 ; y < data->task_count ; y++) {
    46b8:	48 63 43 40          	movslq 0x40(%rbx),%rax
    46bc:	85 c0                	test   %eax,%eax
    46be:	7e 65                	jle    4725 <timer_thread+0x185>
    46c0:	48 c1 e0 09          	shl    $0x9,%rax
      data->threads[x]->tasks[y].sending = 0;
    46c4:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    46c8:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    46d0:	31 c9                	xor    %ecx,%ecx
    46d2:	48 89 c6             	mov    %rax,%rsi
    46d5:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    46d9:	48 8b 40 38          	mov    0x38(%rax),%rax
    46dd:	48 8d 14 06          	lea    (%rsi,%rax,1),%rdx
    46e1:	f7 c6 00 02 00 00    	test   $0x200,%esi
    46e7:	74 17                	je     4700 <timer_thread+0x160>
    46e9:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    46f3:	48 05 00 02 00 00    	add    $0x200,%rax
    46f9:	48 39 c2             	cmp    %rax,%rdx
    46fc:	74 1e                	je     471c <timer_thread+0x17c>
    46fe:	66 90                	xchg   %ax,%ax
      data->threads[x]->tasks[y].sending = 0;
    4700:	c7 80 80 01 00 00 00 00 00 00 	movl   $0x0,0x180(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    470a:	48 05 00 04 00 00    	add    $0x400,%rax
      data->threads[x]->tasks[y].sending = 0;
    4710:	c7 40 80 00 00 00 00 	movl   $0x0,-0x80(%rax)
    for (int y = 0 ; y < data->task_count ; y++) {
    4717:	48 39 c2             	cmp    %rax,%rdx
    471a:	75 e4                	jne    4700 <timer_thread+0x160>
  for (int x = 0 ; x < data->my_thread_count ; x++) {
    471c:	48 83 c1 08          	add    $0x8,%rcx
    4720:	48 39 cf             	cmp    %rcx,%rdi
    4723:	75 b0                	jne    46d5 <timer_thread+0x135>
  asm volatile ("mfence" ::: "memory");
    4725:	0f ae f0             	mfence
  struct timespec drain = {
    4728:	66 0f 6f 05 70 44 00 00 	movdqa 0x4470(%rip),%xmm0        # 8ba0 <_IO_stdin_used+0xba0>
    4730:	4c 8d 3d 26 39 00 00 	lea    0x3926(%rip),%r15        # 805d <_IO_stdin_used+0x5d>
    4737:	0f 29 44 24 40       	movaps %xmm0,0x40(%rsp)
    for (int x = 0 ; x < data->thread_count ; x++) {
    473c:	48 63 43 28          	movslq 0x28(%rbx),%rax
    y++;
    4740:	8d 7d 01             	lea    0x1(%rbp),%edi
    for (int x = 0 ; x < data->thread_count ; x++) {
    4743:	85 c0                	test   %eax,%eax
    4745:	7e 4e                	jle    4795 <timer_thread+0x1f5>
    4747:	48 8b 4b 18          	mov    0x18(%rbx),%rcx
        data->threads[x]->tasks[y].scheduled = 0;
    474b:	4c 63 c5             	movslq %ebp,%r8
    474e:	49 c1 e0 09          	shl    $0x9,%r8
    4752:	4c 8d 0c c1          	lea    (%rcx,%rax,8),%r9
    4756:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
        int next = (y + 1) % data->threads[x]->task_count;
    4760:	4c 8b 11             	mov    (%rcx),%r10
    4763:	89 f8                	mov    %edi,%eax
    for (int x = 0 ; x < data->thread_count ; x++) {
    4765:	48 83 c1 08          	add    $0x8,%rcx
        int next = (y + 1) % data->threads[x]->task_count;
    4769:	99                   	cltd
    476a:	41 f7 7a 40          	idivl  0x40(%r10)
        data->threads[x]->tasks[next].scheduled = 1;
    476e:	49 8b 72 38          	mov    0x38(%r10),%rsi
    4772:	48 63 d2             	movslq %edx,%rdx
    4775:	48 c1 e2 09          	shl    $0x9,%rdx
    4779:	c7 84 16 4c 01 00 00 01 00 00 00 	movl   $0x1,0x14c(%rsi,%rdx,1)
        data->threads[x]->tasks[y].scheduled = 0;
    4784:	42 c7 84 06 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rsi,%r8,1)
    for (int x = 0 ; x < data->thread_count ; x++) {
    4790:	4c 39 c9             	cmp    %r9,%rcx
    4793:	75 cb                	jne    4760 <timer_thread+0x1c0>
    asm volatile ("mfence" ::: "memory");
    4795:	0f ae f0             	mfence
    if (y >= data->threads[0]->task_count) {
    4798:	48 8b 43 18          	mov    0x18(%rbx),%rax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    479c:	44 8b 53 30          	mov    0x30(%rbx),%r10d
    if (y >= data->threads[0]->task_count) {
    47a0:	48 8b 00             	mov    (%rax),%rax
    y++;
    47a3:	39 78 40             	cmp    %edi,0x40(%rax)
    47a6:	b8 00 00 00 00       	mov    $0x0,%eax
    47ab:	0f 4f c7             	cmovg  %edi,%eax
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    47ae:	45 85 d2             	test   %r10d,%r10d
    47b1:	0f 8e 45 01 00 00    	jle    48fc <timer_thread+0x35c>
    int all_empty = 1;
    47b7:	89 44 24 0c          	mov    %eax,0xc(%rsp)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    47bb:	45 31 f6             	xor    %r14d,%r14d
    int all_empty = 1;
    47be:	41 bb 01 00 00 00    	mov    $0x1,%r11d
    47c4:	0f 1f 40 00          	nopl   0x0(%rax)
      for (int y = 0 ; y < 2 ; y++) {
    47c8:	45 31 ed             	xor    %r13d,%r13d
    47cb:	44 89 f5             	mov    %r14d,%ebp
    47ce:	4e 8d 24 f5 00 00 00 00 	lea    0x0(,%r14,8),%r12
    47d6:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    47d9:	45 85 d2             	test   %r10d,%r10d
    47dc:	0f 8e bd 00 00 00    	jle    489f <timer_thread+0x2ff>
    47e2:	44 89 5c 24 08       	mov    %r11d,0x8(%rsp)
    47e7:	4d 89 eb             	mov    %r13,%r11
      y = 0;
    47ea:	31 c0                	xor    %eax,%eax
        for (int k = 0 ; k < data->my_thread_count; k++) {
    47ec:	45 31 c0             	xor    %r8d,%r8d
    47ef:	49 c1 e3 09          	shl    $0x9,%r11
    47f3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (x == k) { continue; }
    47f8:	45 39 f0             	cmp    %r14d,%r8d
    47fb:	74 36                	je     4833 <timer_thread+0x293>
          if (((struct Data*)data->threads[x]->tasks[y].mailboxes[k].lower)->messages_count > 0 || ((struct Data*)data->threads[x]->tasks[y].mailboxes[k].higher)->messages_count > 0) {
    47fd:	48 8b 53 18          	mov    0x18(%rbx),%rdx
    4801:	4a 8b 14 22          	mov    (%rdx,%r12,1),%rdx
    4805:	48 8b 52 38          	mov    0x38(%rdx),%rdx
    4809:	4a 8b 8c 1a 70 01 00 00 	mov    0x170(%rdx,%r11,1),%rcx
    4811:	48 01 c1             	add    %rax,%rcx
    4814:	48 8b 11             	mov    (%rcx),%rdx
    4817:	48 8b 49 08          	mov    0x8(%rcx),%rcx
    481b:	4c 8b 8a 80 00 00 00 	mov    0x80(%rdx),%r9
    4822:	48 8b b1 80 00 00 00 	mov    0x80(%rcx),%rsi
    4829:	4d 85 c9             	test   %r9,%r9
    482c:	7f 2a                	jg     4858 <timer_thread+0x2b8>
    482e:	48 85 f6             	test   %rsi,%rsi
    4831:	7f 25                	jg     4858 <timer_thread+0x2b8>
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4833:	41 83 c0 01          	add    $0x1,%r8d
    4837:	48 83 c0 38          	add    $0x38,%rax
    483b:	45 39 d0             	cmp    %r10d,%r8d
    483e:	75 b8                	jne    47f8 <timer_thread+0x258>
      for (int y = 0 ; y < 2 ; y++) {
    4840:	49 83 fd 01          	cmp    $0x1,%r13
    4844:	0f 84 9e 00 00 00    	je     48e8 <timer_thread+0x348>
    484a:	49 83 c5 01          	add    $0x1,%r13
    484e:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4851:	eb 94                	jmp    47e7 <timer_thread+0x247>
    4853:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    4858:	8b 81 28 03 00 00    	mov    0x328(%rcx),%eax
    485e:	48 83 ec 08          	sub    $0x8,%rsp
    4862:	89 f9                	mov    %edi,%ecx
    4864:	bf 01 00 00 00       	mov    $0x1,%edi
    4869:	50                   	push   %rax
    486a:	8b 82 28 03 00 00    	mov    0x328(%rdx),%eax
    4870:	89 ea                	mov    %ebp,%edx
    4872:	50                   	push   %rax
    4873:	31 c0                	xor    %eax,%eax
    4875:	56                   	push   %rsi
    4876:	4c 89 fe             	mov    %r15,%rsi
    4879:	e8 62 dc ff ff       	call   24e0 <__printf_chk@plt>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    487e:	44 8b 53 30          	mov    0x30(%rbx),%r10d
      for (int y = 0 ; y < 2 ; y++) {
    4882:	48 83 c4 20          	add    $0x20,%rsp
    4886:	49 83 fd 01          	cmp    $0x1,%r13
    488a:	74 44                	je     48d0 <timer_thread+0x330>
    488c:	49 83 c5 01          	add    $0x1,%r13
    4890:	45 31 db             	xor    %r11d,%r11d
    4893:	44 89 ef             	mov    %r13d,%edi
        for (int k = 0 ; k < data->my_thread_count; k++) {
    4896:	45 85 d2             	test   %r10d,%r10d
    4899:	0f 8f 43 ff ff ff    	jg     47e2 <timer_thread+0x242>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    489f:	49 83 c6 01          	add    $0x1,%r14
    48a3:	45 39 f2             	cmp    %r14d,%r10d
    48a6:	0f 8f 1c ff ff ff    	jg     47c8 <timer_thread+0x228>
    48ac:	8b 6c 24 0c          	mov    0xc(%rsp),%ebp
    if (all_empty == 1) {
    48b0:	41 83 fb 01          	cmp    $0x1,%r11d
    48b4:	74 46                	je     48fc <timer_thread+0x35c>
      nanosleep(&drain , &drainrem);
    48b6:	48 8d 74 24 30       	lea    0x30(%rsp),%rsi
    48bb:	48 8d 7c 24 40       	lea    0x40(%rsp),%rdi
    48c0:	e8 fb da ff ff       	call   23c0 <nanosleep@plt>
    48c5:	e9 72 fe ff ff       	jmp    473c <timer_thread+0x19c>
    48ca:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    48d0:	49 83 c6 01          	add    $0x1,%r14
    48d4:	45 31 db             	xor    %r11d,%r11d
    48d7:	45 39 f2             	cmp    %r14d,%r10d
    48da:	0f 8f e8 fe ff ff    	jg     47c8 <timer_thread+0x228>
    48e0:	eb ca                	jmp    48ac <timer_thread+0x30c>
    48e2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    48e8:	49 83 c6 01          	add    $0x1,%r14
    48ec:	44 8b 5c 24 08       	mov    0x8(%rsp),%r11d
    48f1:	45 39 f2             	cmp    %r14d,%r10d
    48f4:	0f 8f ce fe ff ff    	jg     47c8 <timer_thread+0x228>
    48fa:	eb b0                	jmp    48ac <timer_thread+0x30c>
    48fc:	48 8d 3d 51 37 00 00 	lea    0x3751(%rip),%rdi        # 8054 <_IO_stdin_used+0x54>
    4903:	e8 48 da ff ff       	call   2350 <puts@plt>
  while (data->running) {
    4908:	8b 53 44             	mov    0x44(%rbx),%edx
    490b:	85 d2                	test   %edx,%edx
    490d:	0f 84 eb 00 00 00    	je     49fe <timer_thread+0x45e>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4913:	8b 43 2c             	mov    0x2c(%rbx),%eax
    4916:	31 ed                	xor    %ebp,%ebp
    4918:	4c 8d 25 5b 37 00 00 	lea    0x375b(%rip),%r12        # 807a <_IO_stdin_used+0x7a>
    491f:	4c 8d 2d 6f 37 00 00 	lea    0x376f(%rip),%r13        # 8095 <_IO_stdin_used+0x95>
    4926:	85 c0                	test   %eax,%eax
    4928:	7e 39                	jle    4963 <timer_thread+0x3c3>
    492a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4930:	31 c0                	xor    %eax,%eax
    4932:	89 ea                	mov    %ebp,%edx
    4934:	4c 89 e6             	mov    %r12,%rsi
    4937:	bf 01 00 00 00       	mov    $0x1,%edi
    493c:	e8 9f db ff ff       	call   24e0 <__printf_chk@plt>
      data->threads[x]->running = 0;
    4941:	48 8b 43 18          	mov    0x18(%rbx),%rax
    4945:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
      if (data->threads[x]->type == IO) {
    4949:	83 78 0c 02          	cmpl   $0x2,0xc(%rax)
      data->threads[x]->running = 0;
    494d:	c7 40 44 00 00 00 00 	movl   $0x0,0x44(%rax)
      if (data->threads[x]->type == IO) {
    4954:	0f 84 d1 00 00 00    	je     4a2b <timer_thread+0x48b>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    495a:	48 83 c5 01          	add    $0x1,%rbp
    495e:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
    4961:	7f cd                	jg     4930 <timer_thread+0x390>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    4963:	48 63 53 30          	movslq 0x30(%rbx),%rdx
    4967:	85 d2                	test   %edx,%edx
    4969:	7e 7d                	jle    49e8 <timer_thread+0x448>
      for (int y = 0 ; y < data->task_count ; y++) {
    496b:	8b 43 40             	mov    0x40(%rbx),%eax
    496e:	85 c0                	test   %eax,%eax
    4970:	7e 76                	jle    49e8 <timer_thread+0x448>
    4972:	48 63 f0             	movslq %eax,%rsi
        data->threads[x]->tasks[y].scheduled = 0;
    4975:	4c 8b 43 18          	mov    0x18(%rbx),%r8
    4979:	48 8d 3c d5 00 00 00 00 	lea    0x0(,%rdx,8),%rdi
    4981:	31 c9                	xor    %ecx,%ecx
    4983:	48 c1 e6 09          	shl    $0x9,%rsi
    4987:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
    4990:	49 8b 04 08          	mov    (%r8,%rcx,1),%rax
    4994:	48 8b 40 38          	mov    0x38(%rax),%rax
    4998:	48 8d 14 30          	lea    (%rax,%rsi,1),%rdx
    499c:	f7 c6 00 02 00 00    	test   $0x200,%esi
    49a2:	74 1c                	je     49c0 <timer_thread+0x420>
    49a4:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    49ae:	48 05 00 02 00 00    	add    $0x200,%rax
    49b4:	48 39 d0             	cmp    %rdx,%rax
    49b7:	74 26                	je     49df <timer_thread+0x43f>
    49b9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
        data->threads[x]->tasks[y].scheduled = 0;
    49c0:	c7 80 4c 01 00 00 00 00 00 00 	movl   $0x0,0x14c(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    49ca:	48 05 00 04 00 00    	add    $0x400,%rax
        data->threads[x]->tasks[y].scheduled = 0;
    49d0:	c7 80 4c ff ff ff 00 00 00 00 	movl   $0x0,-0xb4(%rax)
      for (int y = 0 ; y < data->task_count ; y++) {
    49da:	48 39 d0             	cmp    %rdx,%rax
    49dd:	75 e1                	jne    49c0 <timer_thread+0x420>
    for (int x = 0 ; x < data->my_thread_count ; x++) {
    49df:	48 83 c1 08          	add    $0x8,%rcx
    49e3:	48 39 f9             	cmp    %rdi,%rcx
    49e6:	75 a8                	jne    4990 <timer_thread+0x3f0>
    asm volatile ("mfence" ::: "memory");
    49e8:	0f ae f0             	mfence
    49eb:	48 8d 3d b5 36 00 00 	lea    0x36b5(%rip),%rdi        # 80a7 <_IO_stdin_used+0xa7>
    49f2:	e8 59 d9 ff ff       	call   2350 <puts@plt>
    data->running = 0;
    49f7:	c7 43 44 00 00 00 00 	movl   $0x0,0x44(%rbx)
    49fe:	48 8d 3d a9 36 00 00 	lea    0x36a9(%rip),%rdi        # 80ae <_IO_stdin_used+0xae>
    4a05:	e8 46 d9 ff ff       	call   2350 <puts@plt>
}
    4a0a:	48 8b 44 24 58       	mov    0x58(%rsp),%rax
    4a0f:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4a18:	75 40                	jne    4a5a <timer_thread+0x4ba>
    4a1a:	48 83 c4 68          	add    $0x68,%rsp
    4a1e:	31 c0                	xor    %eax,%eax
    4a20:	5b                   	pop    %rbx
    4a21:	5d                   	pop    %rbp
    4a22:	41 5c                	pop    %r12
    4a24:	41 5d                	pop    %r13
    4a26:	41 5e                	pop    %r14
    4a28:	41 5f                	pop    %r15
    4a2a:	c3                   	ret
    4a2b:	4c 89 ef             	mov    %r13,%rdi
    4a2e:	e8 1d d9 ff ff       	call   2350 <puts@plt>
        eventfd_write(data->threads[x]->_eventfd, 1);
    4a33:	48 8b 43 18          	mov    0x18(%rbx),%rax
    4a37:	be 01 00 00 00       	mov    $0x1,%esi
    4a3c:	48 8b 04 e8          	mov    (%rax,%rbp,8),%rax
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4a40:	48 83 c5 01          	add    $0x1,%rbp
        eventfd_write(data->threads[x]->_eventfd, 1);
    4a44:	8b 78 60             	mov    0x60(%rax),%edi
    4a47:	e8 34 da ff ff       	call   2480 <eventfd_write@plt>
    for (int x = 0 ; x < data->total_thread_count ; x++) {
    4a4c:	39 6b 2c             	cmp    %ebp,0x2c(%rbx)
    4a4f:	0f 8f db fe ff ff    	jg     4930 <timer_thread+0x390>
    4a55:	e9 09 ff ff ff       	jmp    4963 <timer_thread+0x3c3>
}
    4a5a:	e8 41 d9 ff ff       	call   23a0 <__stack_chk_fail@plt>
    4a5f:	90                   	nop

0000000000004a60 <minf>:
int minf(int a, int b) {
    4a60:	f3 0f 1e fa          	endbr64
  if (b < a) { return b; }
    4a64:	39 f7                	cmp    %esi,%edi
    4a66:	89 f0                	mov    %esi,%eax
    4a68:	0f 4e c7             	cmovle %edi,%eax
}
    4a6b:	c3                   	ret
    4a6c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a70 <maxf>:
int maxf(int a, int b) {
    4a70:	f3 0f 1e fa          	endbr64
  if (b > a) { return b; }
    4a74:	39 f7                	cmp    %esi,%edi
    4a76:	89 f0                	mov    %esi,%eax
    4a78:	0f 4d c7             	cmovge %edi,%eax
}
    4a7b:	c3                   	ret
    4a7c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004a80 <strtolower>:
void strtolower(char *str) {
    4a80:	f3 0f 1e fa          	endbr64
    4a84:	55                   	push   %rbp
    4a85:	53                   	push   %rbx
    4a86:	48 83 ec 08          	sub    $0x8,%rsp
    for (; *str; ++str)
    4a8a:	48 0f be 1f          	movsbq (%rdi),%rbx
    4a8e:	84 db                	test   %bl,%bl
    4a90:	74 24                	je     4ab6 <strtolower+0x36>
    4a92:	48 89 fd             	mov    %rdi,%rbp
        *str = (char)tolower(*str);
    4a95:	e8 36 db ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    4a9a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    4aa0:	48 8b 10             	mov    (%rax),%rdx
    for (; *str; ++str)
    4aa3:	48 83 c5 01          	add    $0x1,%rbp
        *str = (char)tolower(*str);
    4aa7:	8b 14 9a             	mov    (%rdx,%rbx,4),%edx
    4aaa:	88 55 ff             	mov    %dl,-0x1(%rbp)
    for (; *str; ++str)
    4aad:	48 0f be 5d 00       	movsbq 0x0(%rbp),%rbx
    4ab2:	84 db                	test   %bl,%bl
    4ab4:	75 ea                	jne    4aa0 <strtolower+0x20>
}
    4ab6:	48 83 c4 08          	add    $0x8,%rsp
    4aba:	5b                   	pop    %rbx
    4abb:	5d                   	pop    %rbp
    4abc:	c3                   	ret
    4abd:	0f 1f 00             	nopl   (%rax)

0000000000004ac0 <zh_malloc>:
void *zh_malloc(size_t size) {
    4ac0:	f3 0f 1e fa          	endbr64
    4ac4:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    4ac8:	e8 d3 d9 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4acd:	48 85 c0             	test   %rax,%rax
    4ad0:	74 05                	je     4ad7 <zh_malloc+0x17>
}
    4ad2:	48 83 c4 08          	add    $0x8,%rsp
    4ad6:	c3                   	ret
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    4ad7:	48 8b 0d 42 65 00 00 	mov    0x6542(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    4ade:	ba 28 00 00 00       	mov    $0x28,%edx
    4ae3:	be 01 00 00 00       	mov    $0x1,%esi
    4ae8:	48 8d 3d c1 3a 00 00 	lea    0x3ac1(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    4aef:	e8 6c da ff ff       	call   2560 <fwrite@plt>
        exit(1);
    4af4:	bf 01 00 00 00       	mov    $0x1,%edi
    4af9:	e8 42 da ff ff       	call   2540 <exit@plt>
    4afe:	66 90                	xchg   %ax,%ax

0000000000004b00 <get_filename_ext>:
const char *get_filename_ext(const char *filename) {
    4b00:	f3 0f 1e fa          	endbr64
    4b04:	53                   	push   %rbx
    const char *dot = strrchr(filename, '.');
    4b05:	be 2e 00 00 00       	mov    $0x2e,%esi
const char *get_filename_ext(const char *filename) {
    4b0a:	48 89 fb             	mov    %rdi,%rbx
    const char *dot = strrchr(filename, '.');
    4b0d:	e8 be d8 ff ff       	call   23d0 <strrchr@plt>
    if (!dot || dot == filename)
    4b12:	48 85 c0             	test   %rax,%rax
    4b15:	74 11                	je     4b28 <get_filename_ext+0x28>
    4b17:	48 39 c3             	cmp    %rax,%rbx
    4b1a:	74 0c                	je     4b28 <get_filename_ext+0x28>
    return dot + 1;
    4b1c:	48 83 c0 01          	add    $0x1,%rax
}
    4b20:	5b                   	pop    %rbx
    4b21:	c3                   	ret
    4b22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
        return "";
    4b28:	48 8d 05 c7 35 00 00 	lea    0x35c7(%rip),%rax        # 80f6 <_IO_stdin_used+0xf6>
}
    4b2f:	5b                   	pop    %rbx
    4b30:	c3                   	ret
    4b31:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    4b3c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000004b40 <send_headers>:
void send_headers(const char *path, off_t len, struct iovec *iov) {
    4b40:	f3 0f 1e fa          	endbr64
    4b44:	41 55                	push   %r13
    4b46:	49 89 f5             	mov    %rsi,%r13
#endif

__fortify_function char *
__NTH (strcpy (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4b49:	48 89 fe             	mov    %rdi,%rsi
    4b4c:	41 54                	push   %r12
    4b4e:	55                   	push   %rbp
    4b4f:	48 89 d5             	mov    %rdx,%rbp
    4b52:	ba 00 04 00 00       	mov    $0x400,%edx
    4b57:	53                   	push   %rbx
    4b58:	48 81 ec 18 08 00 00 	sub    $0x818,%rsp
    4b5f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    4b68:	48 89 84 24 08 08 00 00 	mov    %rax,0x808(%rsp)
    4b70:	31 c0                	xor    %eax,%eax
    4b72:	49 89 e4             	mov    %rsp,%r12
    4b75:	4c 89 e7             	mov    %r12,%rdi
    4b78:	e8 43 d9 ff ff       	call   24c0 <__strcpy_chk@plt>
    for (; *str; ++str)
    4b7d:	48 0f be 1c 24       	movsbq (%rsp),%rbx
    4b82:	84 db                	test   %bl,%bl
    4b84:	74 24                	je     4baa <send_headers+0x6a>
        *str = (char)tolower(*str);
    4b86:	e8 45 da ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    4b8b:	48 8b 08             	mov    (%rax),%rcx
    4b8e:	4c 89 e0             	mov    %r12,%rax
    4b91:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    4b98:	8b 14 99             	mov    (%rcx,%rbx,4),%edx
    for (; *str; ++str)
    4b9b:	48 83 c0 01          	add    $0x1,%rax
        *str = (char)tolower(*str);
    4b9f:	88 50 ff             	mov    %dl,-0x1(%rax)
    for (; *str; ++str)
    4ba2:	48 0f be 18          	movsbq (%rax),%rbx
    4ba6:	84 db                	test   %bl,%bl
    4ba8:	75 ee                	jne    4b98 <send_headers+0x58>
    void *buf = malloc(size);
    4baa:	bf 11 00 00 00       	mov    $0x11,%edi
    4baf:	e8 ec d8 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4bb4:	48 85 c0             	test   %rax,%rax
    4bb7:	0f 84 7e 04 00 00    	je     503b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4bbd:	66 0f 6f 05 eb 3f 00 00 	movdqa 0x3feb(%rip),%xmm0        # 8bb0 <_IO_stdin_used+0xbb0>
    iov[0].iov_base = zh_malloc(slen);
    4bc5:	48 89 45 00          	mov    %rax,0x0(%rbp)
    void *buf = malloc(size);
    4bc9:	bf 17 00 00 00       	mov    $0x17,%edi
    iov[0].iov_len = slen;
    4bce:	48 c7 45 08 11 00 00 00 	movq   $0x11,0x8(%rbp)
    4bd6:	c6 40 10 0a          	movb   $0xa,0x10(%rax)
    4bda:	0f 11 00             	movups %xmm0,(%rax)
    void *buf = malloc(size);
    4bdd:	e8 be d8 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4be2:	48 85 c0             	test   %rax,%rax
    4be5:	0f 84 50 04 00 00    	je     503b <send_headers+0x4fb>
    4beb:	66 0f 6f 05 cd 3f 00 00 	movdqa 0x3fcd(%rip),%xmm0        # 8bc0 <_IO_stdin_used+0xbc0>
    iov[1].iov_base = zh_malloc(slen);
    4bf3:	48 89 45 10          	mov    %rax,0x10(%rbp)
    const char *dot = strrchr(filename, '.');
    4bf7:	4c 89 e7             	mov    %r12,%rdi
    4bfa:	48 be 70 64 2f 30 2e 31 0d 0a 	movabs $0xa0d312e302f6470,%rsi
    iov[1].iov_len = slen;
    4c04:	48 c7 45 18 17 00 00 00 	movq   $0x17,0x18(%rbp)
    4c0c:	0f 11 00             	movups %xmm0,(%rax)
    4c0f:	48 89 70 0f          	mov    %rsi,0xf(%rax)
    const char *dot = strrchr(filename, '.');
    4c13:	be 2e 00 00 00       	mov    $0x2e,%esi
    4c18:	e8 b3 d7 ff ff       	call   23d0 <strrchr@plt>
    if (!dot || dot == filename)
    4c1d:	48 85 c0             	test   %rax,%rax
    4c20:	0f 84 ea 02 00 00    	je     4f10 <send_headers+0x3d0>
    4c26:	4c 39 e0             	cmp    %r12,%rax
    4c29:	0f 84 e1 02 00 00    	je     4f10 <send_headers+0x3d0>
    return dot + 1;
    4c2f:	48 8d 58 01          	lea    0x1(%rax),%rbx
    if (strcmp("jpg", file_ext) == 0)
    4c33:	48 8d 3d 8a 34 00 00 	lea    0x348a(%rip),%rdi        # 80c4 <_IO_stdin_used+0xc4>
    4c3a:	48 89 de             	mov    %rbx,%rsi
    4c3d:	e8 ee d7 ff ff       	call   2430 <strcmp@plt>
    4c42:	85 c0                	test   %eax,%eax
    4c44:	75 20                	jne    4c66 <send_headers+0x126>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4c46:	66 0f 6f 05 82 3f 00 00 	movdqa 0x3f82(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4c4e:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4c56:	66 0f 6f 05 82 3f 00 00 	movdqa 0x3f82(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4c5e:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("jpeg", file_ext) == 0)
    4c66:	48 89 de             	mov    %rbx,%rsi
    4c69:	48 8d 3d 58 34 00 00 	lea    0x3458(%rip),%rdi        # 80c8 <_IO_stdin_used+0xc8>
    4c70:	e8 bb d7 ff ff       	call   2430 <strcmp@plt>
    4c75:	85 c0                	test   %eax,%eax
    4c77:	75 20                	jne    4c99 <send_headers+0x159>
    4c79:	66 0f 6f 05 4f 3f 00 00 	movdqa 0x3f4f(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4c81:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4c89:	66 0f 6f 05 4f 3f 00 00 	movdqa 0x3f4f(%rip),%xmm0        # 8be0 <_IO_stdin_used+0xbe0>
    4c91:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    if (strcmp("png", file_ext) == 0)
    4c99:	48 89 de             	mov    %rbx,%rsi
    4c9c:	48 8d 3d 2a 34 00 00 	lea    0x342a(%rip),%rdi        # 80cd <_IO_stdin_used+0xcd>
    4ca3:	e8 88 d7 ff ff       	call   2430 <strcmp@plt>
    4ca8:	85 c0                	test   %eax,%eax
    4caa:	0f 84 10 02 00 00    	je     4ec0 <send_headers+0x380>
    if (strcmp("gif", file_ext) == 0)
    4cb0:	48 89 de             	mov    %rbx,%rsi
    4cb3:	48 8d 3d 17 34 00 00 	lea    0x3417(%rip),%rdi        # 80d1 <_IO_stdin_used+0xd1>
    4cba:	e8 71 d7 ff ff       	call   2430 <strcmp@plt>
    4cbf:	85 c0                	test   %eax,%eax
    4cc1:	0f 84 a9 02 00 00    	je     4f70 <send_headers+0x430>
    if (strcmp("htm", file_ext) == 0)
    4cc7:	48 89 de             	mov    %rbx,%rsi
    4cca:	48 8d 3d 04 34 00 00 	lea    0x3404(%rip),%rdi        # 80d5 <_IO_stdin_used+0xd5>
    4cd1:	e8 5a d7 ff ff       	call   2430 <strcmp@plt>
    4cd6:	85 c0                	test   %eax,%eax
    4cd8:	0f 84 6a 02 00 00    	je     4f48 <send_headers+0x408>
    if (strcmp("html", file_ext) == 0)
    4cde:	48 89 de             	mov    %rbx,%rsi
    4ce1:	48 8d 3d 30 34 00 00 	lea    0x3430(%rip),%rdi        # 8118 <_IO_stdin_used+0x118>
    4ce8:	e8 43 d7 ff ff       	call   2430 <strcmp@plt>
    4ced:	85 c0                	test   %eax,%eax
    4cef:	0f 84 2b 02 00 00    	je     4f20 <send_headers+0x3e0>
    if (strcmp("js", file_ext) == 0)
    4cf5:	80 3b 6a             	cmpb   $0x6a,(%rbx)
    4cf8:	0f 84 52 01 00 00    	je     4e50 <send_headers+0x310>
    if (strcmp("css", file_ext) == 0)
    4cfe:	48 89 de             	mov    %rbx,%rsi
    4d01:	48 8d 3d d1 33 00 00 	lea    0x33d1(%rip),%rdi        # 80d9 <_IO_stdin_used+0xd9>
    4d08:	e8 23 d7 ff ff       	call   2430 <strcmp@plt>
    4d0d:	85 c0                	test   %eax,%eax
    4d0f:	0f 84 ab 02 00 00    	je     4fc0 <send_headers+0x480>
    if (strcmp("txt", file_ext) == 0)
    4d15:	48 89 de             	mov    %rbx,%rsi
    4d18:	48 8d 3d be 33 00 00 	lea    0x33be(%rip),%rdi        # 80dd <_IO_stdin_used+0xdd>
    4d1f:	e8 0c d7 ff ff       	call   2430 <strcmp@plt>
    4d24:	85 c0                	test   %eax,%eax
    4d26:	0f 84 6c 02 00 00    	je     4f98 <send_headers+0x458>
    slen = strlen(send_buffer);
    4d2c:	4c 8d a4 24 00 04 00 00 	lea    0x400(%rsp),%r12
    4d34:	4c 89 e7             	mov    %r12,%rdi
    4d37:	e8 54 d6 ff ff       	call   2390 <strlen@plt>
    void *buf = malloc(size);
    4d3c:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4d3f:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4d42:	e8 59 d7 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4d47:	48 85 c0             	test   %rax,%rax
    4d4a:	0f 84 eb 02 00 00    	je     503b <send_headers+0x4fb>
    iov[2].iov_base = zh_malloc(slen);
    4d50:	48 89 45 20          	mov    %rax,0x20(%rbp)
    iov[2].iov_len = slen;
    4d54:	48 89 5d 28          	mov    %rbx,0x28(%rbp)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4d58:	83 fb 08             	cmp    $0x8,%ebx
    4d5b:	0f 83 3f 01 00 00    	jae    4ea0 <send_headers+0x360>
    4d61:	f6 c3 04             	test   $0x4,%bl
    4d64:	0f 85 7b 02 00 00    	jne    4fe5 <send_headers+0x4a5>
    4d6a:	85 db                	test   %ebx,%ebx
    4d6c:	74 13                	je     4d81 <send_headers+0x241>
    4d6e:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4d76:	88 10                	mov    %dl,(%rax)
    4d78:	f6 c3 02             	test   $0x2,%bl
    4d7b:	0f 85 96 02 00 00    	jne    5017 <send_headers+0x4d7>
  return __builtin___sprintf_chk (__s, __USE_FORTIFY_LEVEL - 1,
    4d81:	4d 89 e8             	mov    %r13,%r8
    4d84:	48 8d 0d 56 33 00 00 	lea    0x3356(%rip),%rcx        # 80e1 <_IO_stdin_used+0xe1>
    4d8b:	4c 89 e7             	mov    %r12,%rdi
    4d8e:	31 c0                	xor    %eax,%eax
    4d90:	ba 00 04 00 00       	mov    $0x400,%edx
    4d95:	be 01 00 00 00       	mov    $0x1,%esi
    4d9a:	e8 41 d8 ff ff       	call   25e0 <__sprintf_chk@plt>
    slen = strlen(send_buffer);
    4d9f:	4c 89 e7             	mov    %r12,%rdi
    4da2:	e8 e9 d5 ff ff       	call   2390 <strlen@plt>
    void *buf = malloc(size);
    4da7:	48 89 c7             	mov    %rax,%rdi
    slen = strlen(send_buffer);
    4daa:	48 89 c3             	mov    %rax,%rbx
    void *buf = malloc(size);
    4dad:	e8 ee d6 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4db2:	48 85 c0             	test   %rax,%rax
    4db5:	0f 84 80 02 00 00    	je     503b <send_headers+0x4fb>
    iov[3].iov_base = zh_malloc(slen);
    4dbb:	48 89 45 30          	mov    %rax,0x30(%rbp)
    iov[3].iov_len = slen;
    4dbf:	48 89 5d 38          	mov    %rbx,0x38(%rbp)
    4dc3:	83 fb 08             	cmp    $0x8,%ebx
    4dc6:	0f 83 1c 01 00 00    	jae    4ee8 <send_headers+0x3a8>
    4dcc:	f6 c3 04             	test   $0x4,%bl
    4dcf:	0f 85 29 02 00 00    	jne    4ffe <send_headers+0x4be>
    4dd5:	85 db                	test   %ebx,%ebx
    4dd7:	74 13                	je     4dec <send_headers+0x2ac>
    4dd9:	0f b6 94 24 00 04 00 00 	movzbl 0x400(%rsp),%edx
    4de1:	88 10                	mov    %dl,(%rax)
    4de3:	f6 c3 02             	test   $0x2,%bl
    4de6:	0f 85 3d 02 00 00    	jne    5029 <send_headers+0x4e9>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4dec:	b8 0d 0a 00 00       	mov    $0xa0d,%eax
    void *buf = malloc(size);
    4df1:	bf 02 00 00 00       	mov    $0x2,%edi
    4df6:	c6 84 24 02 04 00 00 00 	movb   $0x0,0x402(%rsp)
    4dfe:	66 89 84 24 00 04 00 00 	mov    %ax,0x400(%rsp)
    4e06:	e8 95 d6 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    4e0b:	48 85 c0             	test   %rax,%rax
    4e0e:	0f 84 27 02 00 00    	je     503b <send_headers+0x4fb>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4e14:	0f b7 94 24 00 04 00 00 	movzwl 0x400(%rsp),%edx
    iov[4].iov_base = zh_malloc(slen);
    4e1c:	48 89 45 40          	mov    %rax,0x40(%rbp)
    iov[4].iov_len = slen;
    4e20:	48 c7 45 48 02 00 00 00 	movq   $0x2,0x48(%rbp)
    4e28:	66 89 10             	mov    %dx,(%rax)
}
    4e2b:	48 8b 84 24 08 08 00 00 	mov    0x808(%rsp),%rax
    4e33:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    4e3c:	0f 85 20 02 00 00    	jne    5062 <send_headers+0x522>
    4e42:	48 81 c4 18 08 00 00 	add    $0x818,%rsp
    4e49:	5b                   	pop    %rbx
    4e4a:	5d                   	pop    %rbp
    4e4b:	41 5c                	pop    %r12
    4e4d:	41 5d                	pop    %r13
    4e4f:	c3                   	ret
    if (strcmp("js", file_ext) == 0)
    4e50:	80 7b 01 73          	cmpb   $0x73,0x1(%rbx)
    4e54:	0f 85 a4 fe ff ff    	jne    4cfe <send_headers+0x1be>
    4e5a:	80 7b 02 00          	cmpb   $0x0,0x2(%rbx)
    4e5e:	0f 85 9a fe ff ff    	jne    4cfe <send_headers+0x1be>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4e64:	66 0f 6f 05 c4 3d 00 00 	movdqa 0x3dc4(%rip),%xmm0        # 8c30 <_IO_stdin_used+0xc30>
    4e6c:	48 b8 63 72 69 70 74 0d 0a 00 	movabs $0xa0d7470697263,%rax
    4e76:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4e7e:	66 0f 6f 05 ba 3d 00 00 	movdqa 0x3dba(%rip),%xmm0        # 8c40 <_IO_stdin_used+0xc40>
    4e86:	0f 29 84 24 10 04 00 00 	movaps %xmm0,0x410(%rsp)
    4e8e:	48 89 84 24 1f 04 00 00 	mov    %rax,0x41f(%rsp)
    4e96:	e9 63 fe ff ff       	jmp    4cfe <send_headers+0x1be>
    4e9b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ea0:	89 da                	mov    %ebx,%edx
    4ea2:	48 89 c7             	mov    %rax,%rdi
    4ea5:	4c 89 e6             	mov    %r12,%rsi
    4ea8:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4ead:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4eb2:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4eb5:	c1 e9 03             	shr    $0x3,%ecx
    4eb8:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4ebb:	e9 c1 fe ff ff       	jmp    4d81 <send_headers+0x241>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4ec0:	66 0f 6f 05 08 3d 00 00 	movdqa 0x3d08(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4ec8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4ed0:	66 0f 6f 05 18 3d 00 00 	movdqa 0x3d18(%rip),%xmm0        # 8bf0 <_IO_stdin_used+0xbf0>
    4ed8:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4ee0:	e9 cb fd ff ff       	jmp    4cb0 <send_headers+0x170>
    4ee5:	0f 1f 00             	nopl   (%rax)
  return __builtin___memcpy_chk (__dest, __src, __len,
    4ee8:	89 da                	mov    %ebx,%edx
    4eea:	48 89 c7             	mov    %rax,%rdi
    4eed:	4c 89 e6             	mov    %r12,%rsi
    4ef0:	49 8b 4c 14 f8       	mov    -0x8(%r12,%rdx,1),%rcx
    4ef5:	48 89 4c 10 f8       	mov    %rcx,-0x8(%rax,%rdx,1)
    4efa:	8d 4b ff             	lea    -0x1(%rbx),%ecx
    4efd:	c1 e9 03             	shr    $0x3,%ecx
    4f00:	f3 48 a5             	rep movsq %ds:(%rsi),%es:(%rdi)
    4f03:	e9 e4 fe ff ff       	jmp    4dec <send_headers+0x2ac>
    4f08:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
        return "";
    4f10:	48 8d 1d df 31 00 00 	lea    0x31df(%rip),%rbx        # 80f6 <_IO_stdin_used+0xf6>
    4f17:	e9 94 fd ff ff       	jmp    4cb0 <send_headers+0x170>
    4f1c:	0f 1f 40 00          	nopl   0x0(%rax)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    4f20:	66 0f 6f 05 e8 3c 00 00 	movdqa 0x3ce8(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4f28:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f30:	66 0f 6f 05 e8 3c 00 00 	movdqa 0x3ce8(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4f38:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4f40:	e9 b0 fd ff ff       	jmp    4cf5 <send_headers+0x1b5>
    4f45:	0f 1f 00             	nopl   (%rax)
    4f48:	66 0f 6f 05 c0 3c 00 00 	movdqa 0x3cc0(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4f50:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f58:	66 0f 6f 05 c0 3c 00 00 	movdqa 0x3cc0(%rip),%xmm0        # 8c20 <_IO_stdin_used+0xc20>
    4f60:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4f68:	e9 71 fd ff ff       	jmp    4cde <send_headers+0x19e>
    4f6d:	0f 1f 00             	nopl   (%rax)
    4f70:	66 0f 6f 05 58 3c 00 00 	movdqa 0x3c58(%rip),%xmm0        # 8bd0 <_IO_stdin_used+0xbd0>
    4f78:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4f80:	66 0f 6f 05 78 3c 00 00 	movdqa 0x3c78(%rip),%xmm0        # 8c00 <_IO_stdin_used+0xc00>
    4f88:	0f 11 84 24 0a 04 00 00 	movups %xmm0,0x40a(%rsp)
    4f90:	e9 32 fd ff ff       	jmp    4cc7 <send_headers+0x187>
    4f95:	0f 1f 00             	nopl   (%rax)
    4f98:	66 0f 6f 05 70 3c 00 00 	movdqa 0x3c70(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4fa0:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fa8:	66 0f 6f 05 b0 3c 00 00 	movdqa 0x3cb0(%rip),%xmm0        # 8c60 <_IO_stdin_used+0xc60>
    4fb0:	0f 11 84 24 0b 04 00 00 	movups %xmm0,0x40b(%rsp)
    4fb8:	e9 6f fd ff ff       	jmp    4d2c <send_headers+0x1ec>
    4fbd:	0f 1f 00             	nopl   (%rax)
    4fc0:	66 0f 6f 05 48 3c 00 00 	movdqa 0x3c48(%rip),%xmm0        # 8c10 <_IO_stdin_used+0xc10>
    4fc8:	0f 29 84 24 00 04 00 00 	movaps %xmm0,0x400(%rsp)
    4fd0:	66 0f 6f 05 78 3c 00 00 	movdqa 0x3c78(%rip),%xmm0        # 8c50 <_IO_stdin_used+0xc50>
    4fd8:	0f 11 84 24 09 04 00 00 	movups %xmm0,0x409(%rsp)
    4fe0:	e9 30 fd ff ff       	jmp    4d15 <send_headers+0x1d5>
  return __builtin___memcpy_chk (__dest, __src, __len,
    4fe5:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    4fec:	89 db                	mov    %ebx,%ebx
    4fee:	89 10                	mov    %edx,(%rax)
    4ff0:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    4ff5:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    4ff9:	e9 83 fd ff ff       	jmp    4d81 <send_headers+0x241>
    4ffe:	8b 94 24 00 04 00 00 	mov    0x400(%rsp),%edx
    5005:	89 db                	mov    %ebx,%ebx
    5007:	89 10                	mov    %edx,(%rax)
    5009:	41 8b 54 1c fc       	mov    -0x4(%r12,%rbx,1),%edx
    500e:	89 54 18 fc          	mov    %edx,-0x4(%rax,%rbx,1)
    5012:	e9 d5 fd ff ff       	jmp    4dec <send_headers+0x2ac>
    5017:	89 db                	mov    %ebx,%ebx
    5019:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    501f:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5024:	e9 58 fd ff ff       	jmp    4d81 <send_headers+0x241>
    5029:	89 db                	mov    %ebx,%ebx
    502b:	41 0f b7 54 1c fe    	movzwl -0x2(%r12,%rbx,1),%edx
    5031:	66 89 54 18 fe       	mov    %dx,-0x2(%rax,%rbx,1)
    5036:	e9 b1 fd ff ff       	jmp    4dec <send_headers+0x2ac>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    503b:	48 8b 0d de 5f 00 00 	mov    0x5fde(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5042:	ba 28 00 00 00       	mov    $0x28,%edx
    5047:	be 01 00 00 00       	mov    $0x1,%esi
    504c:	48 8d 3d 5d 35 00 00 	lea    0x355d(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    5053:	e8 08 d5 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    5058:	bf 01 00 00 00       	mov    $0x1,%edi
    505d:	e8 de d4 ff ff       	call   2540 <exit@plt>
}
    5062:	e8 39 d3 ff ff       	call   23a0 <__stack_chk_fail@plt>
    5067:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000005070 <copy_file_contents>:
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5070:	f3 0f 1e fa          	endbr64
    5074:	41 55                	push   %r13
    5076:	49 89 d5             	mov    %rdx,%r13
    5079:	41 54                	push   %r12
    507b:	49 89 fc             	mov    %rdi,%r12
    void *buf = malloc(size);
    507e:	48 89 f7             	mov    %rsi,%rdi
void copy_file_contents(char *file_path, off_t file_size, struct iovec *iov) {
    5081:	55                   	push   %rbp
    5082:	53                   	push   %rbx
    5083:	48 89 f3             	mov    %rsi,%rbx
    5086:	48 83 ec 08          	sub    $0x8,%rsp
    void *buf = malloc(size);
    508a:	e8 11 d4 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    508f:	48 85 c0             	test   %rax,%rax
    5092:	74 6b                	je     50ff <copy_file_contents+0x8f>
      if (__OPEN_NEEDS_MODE (__oflag) && __va_arg_pack_len () < 1)
	{
	  __open_missing_mode ();
	  return __open_2 (__path, __oflag);
	}
      return __open_alias (__path, __oflag, __va_arg_pack ());
    5094:	4c 89 e7             	mov    %r12,%rdi
    5097:	48 89 c5             	mov    %rax,%rbp
    509a:	31 f6                	xor    %esi,%esi
    509c:	31 c0                	xor    %eax,%eax
    509e:	e8 6d d4 ff ff       	call   2510 <open@plt>
    50a3:	41 89 c4             	mov    %eax,%r12d
    if (fd < 0)
    50a6:	85 c0                	test   %eax,%eax
    50a8:	0f 88 68 d5 ff ff    	js     2616 <copy_file_contents.cold>
# include <bits/unistd-decl.h>

__fortify_function __wur ssize_t
read (int __fd, void *__buf, size_t __nbytes)
{
  return __glibc_fortify (read, __nbytes, sizeof (char),
    50ae:	48 89 da             	mov    %rbx,%rdx
    50b1:	48 89 ee             	mov    %rbp,%rsi
    50b4:	89 c7                	mov    %eax,%edi
    50b6:	e8 55 d3 ff ff       	call   2410 <read@plt>
    if (ret < file_size) {
    50bb:	48 98                	cltq
    50bd:	48 39 d8             	cmp    %rbx,%rax
    50c0:	7c 1e                	jl     50e0 <copy_file_contents+0x70>
    close(fd);
    50c2:	44 89 e7             	mov    %r12d,%edi
    50c5:	e8 26 d3 ff ff       	call   23f0 <close@plt>
    iov->iov_base = buf;
    50ca:	49 89 6d 00          	mov    %rbp,0x0(%r13)
    iov->iov_len = file_size;
    50ce:	49 89 5d 08          	mov    %rbx,0x8(%r13)
}
    50d2:	48 83 c4 08          	add    $0x8,%rsp
    50d6:	5b                   	pop    %rbx
    50d7:	5d                   	pop    %rbp
    50d8:	41 5c                	pop    %r12
    50da:	41 5d                	pop    %r13
    50dc:	c3                   	ret
    50dd:	0f 1f 00             	nopl   (%rax)
    50e0:	48 8b 0d 39 5f 00 00 	mov    0x5f39(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    50e7:	ba 1a 00 00 00       	mov    $0x1a,%edx
    50ec:	be 01 00 00 00       	mov    $0x1,%esi
    50f1:	48 8d 3d ff 2f 00 00 	lea    0x2fff(%rip),%rdi        # 80f7 <_IO_stdin_used+0xf7>
    50f8:	e8 63 d4 ff ff       	call   2560 <fwrite@plt>
    50fd:	eb c3                	jmp    50c2 <copy_file_contents+0x52>
    50ff:	48 8b 0d 1a 5f 00 00 	mov    0x5f1a(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5106:	ba 28 00 00 00       	mov    $0x28,%edx
    510b:	be 01 00 00 00       	mov    $0x1,%esi
    5110:	48 8d 3d 99 34 00 00 	lea    0x3499(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    5117:	e8 44 d4 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    511c:	bf 01 00 00 00       	mov    $0x1,%edi
    5121:	e8 1a d4 ff ff       	call   2540 <exit@plt>
    5126:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005130 <add_write_request>:
int add_write_request(struct Request *req, struct io_uring *ring) {
    5130:	f3 0f 1e fa          	endbr64
 * Returns a vacant sqe, or NULL if we're full.
 */
IOURINGINLINE struct io_uring_sqe *_io_uring_get_sqe(struct io_uring *ring)
{
	struct io_uring_sq *sq = &ring->sq;
	unsigned int head, next = sq->sqe_tail + 1;
    5134:	8b 46 44             	mov    0x44(%rsi),%eax
    5137:	48 89 fa             	mov    %rdi,%rdx
    513a:	48 89 f7             	mov    %rsi,%rdi
	int shift = 0;

	if (ring->flags & IORING_SETUP_SQE128)
    513d:	8b 8f c0 00 00 00    	mov    0xc0(%rdi),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5143:	8d 70 01             	lea    0x1(%rax),%esi
		shift = 1;
	if (!(ring->flags & IORING_SETUP_SQPOLL))
		head = IO_URING_READ_ONCE(*sq->khead);
    5146:	48 8b 07             	mov    (%rdi),%rax
    5149:	44 8b 00             	mov    (%rax),%r8d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    514c:	f6 c1 02             	test   $0x2,%cl
    514f:	74 00                	je     5151 <add_write_request+0x21>
	else
		head = io_uring_smp_load_acquire(sq->khead);

	if (next - head <= sq->ring_entries) {
    5151:	89 f0                	mov    %esi,%eax
    5153:	44 29 c0             	sub    %r8d,%eax
    5156:	39 47 5c             	cmp    %eax,0x5c(%rdi)
    5159:	0f 82 c3 d4 ff ff    	jb     2622 <add_write_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    515f:	c1 e9 0a             	shr    $0xa,%ecx
    5162:	48 83 ec 08          	sub    $0x8,%rsp
		struct io_uring_sqe *sqe;

		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5166:	8b 47 44             	mov    0x44(%rdi),%eax
    5169:	23 47 58             	and    0x58(%rdi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    516c:	83 e1 01             	and    $0x1,%ecx
		sq->sqe_tail = next;
    516f:	89 77 44             	mov    %esi,0x44(%rdi)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    5172:	8b 72 08             	mov    0x8(%rdx),%esi
	sqe->addr3 = 0;
    5175:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5179:	d3 e0                	shl    %cl,%eax
    517b:	8b 4a 04             	mov    0x4(%rdx),%ecx
    517e:	48 c1 e0 06          	shl    $0x6,%rax
    5182:	48 03 47 38          	add    0x38(%rdi),%rax
    req->event_type = EVENT_TYPE_WRITE;
    5186:	c7 02 02 00 00 00    	movl   $0x2,(%rdx)
	sqe->fd = fd;
    518c:	89 70 04             	mov    %esi,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    518f:	48 8d 72 10          	lea    0x10(%rdx),%rsi
	sqe->opcode = (__u8) op;
    5193:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5199:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    51a1:	48 89 70 10          	mov    %rsi,0x10(%rax)
	sqe->len = len;
    51a5:	89 48 18             	mov    %ecx,0x18(%rax)
	sqe->rw_flags = 0;
    51a8:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    51af:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    51b7:	48 89 50 20          	mov    %rdx,0x20(%rax)
	sqe->addr3 = 0;
    51bb:	0f 11 40 30          	movups %xmm0,0x30(%rax)
    io_uring_submit(ring);
    51bf:	e8 ec d1 ff ff       	call   23b0 <io_uring_submit@plt>
}
    51c4:	31 c0                	xor    %eax,%eax
    51c6:	48 83 c4 08          	add    $0x8,%rsp
    51ca:	c3                   	ret
    51cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000051d0 <add_read_request>:
int add_read_request(int client_socket, struct io_uring *ring) {
    51d0:	f3 0f 1e fa          	endbr64
    51d4:	41 55                	push   %r13
    51d6:	41 89 fd             	mov    %edi,%r13d
    51d9:	41 54                	push   %r12
    51db:	55                   	push   %rbp
    51dc:	53                   	push   %rbx
    51dd:	48 89 f3             	mov    %rsi,%rbx
    51e0:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    51e4:	8b 46 44             	mov    0x44(%rsi),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    51e7:	8b 8e c0 00 00 00    	mov    0xc0(%rsi),%ecx
		head = IO_URING_READ_ONCE(*sq->khead);
    51ed:	48 8b 16             	mov    (%rsi),%rdx
	unsigned int head, next = sq->sqe_tail + 1;
    51f0:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    51f3:	8b 32                	mov    (%rdx),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    51f5:	f6 c1 02             	test   $0x2,%cl
    51f8:	74 00                	je     51fa <add_read_request+0x2a>
	if (next - head <= sq->ring_entries) {
    51fa:	89 c2                	mov    %eax,%edx
    51fc:	29 f2                	sub    %esi,%edx
    51fe:	39 53 5c             	cmp    %edx,0x5c(%rbx)
    5201:	0f 82 2b d4 ff ff    	jb     2632 <add_read_request.cold>
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5207:	8b 6b 44             	mov    0x44(%rbx),%ebp
	if (ring->flags & IORING_SETUP_SQE128)
    520a:	c1 e9 0a             	shr    $0xa,%ecx
		sq->sqe_tail = next;
    520d:	89 43 44             	mov    %eax,0x44(%rbx)
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5210:	bf 20 00 00 00       	mov    $0x20,%edi
	if (ring->flags & IORING_SETUP_SQE128)
    5215:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5218:	23 6b 58             	and    0x58(%rbx),%ebp
    521b:	d3 e5                	shl    %cl,%ebp
    521d:	48 c1 e5 06          	shl    $0x6,%rbp
    5221:	48 03 6b 38          	add    0x38(%rbx),%rbp
    5225:	e8 76 d2 ff ff       	call   24a0 <malloc@plt>
    req->iov[0].iov_base = malloc(READ_SZ);
    522a:	be 01 00 00 00       	mov    $0x1,%esi
    522f:	bf 00 20 00 00       	mov    $0x2000,%edi
    struct Request *req = malloc(sizeof(*req) + sizeof(struct iovec));
    5234:	49 89 c4             	mov    %rax,%r12
    req->iov[0].iov_base = malloc(READ_SZ);
    5237:	e8 e4 d1 ff ff       	call   2420 <calloc@plt>
    req->client_socket = client_socket;
    523c:	45 89 6c 24 08       	mov    %r13d,0x8(%r12)
	sqe->addr3 = 0;
    5241:	66 0f ef c0          	pxor   %xmm0,%xmm0
    io_uring_submit(ring);
    5245:	48 89 df             	mov    %rbx,%rdi
    req->iov[0].iov_base = malloc(READ_SZ);
    5248:	49 89 44 24 10       	mov    %rax,0x10(%r12)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    524d:	49 8d 44 24 10       	lea    0x10(%r12),%rax
    req->iov[0].iov_len = READ_SZ;
    5252:	49 c7 44 24 18 00 20 00 00 	movq   $0x2000,0x18(%r12)
    req->event_type = EVENT_TYPE_READ;
    525b:	41 c7 04 24 01 00 00 00 	movl   $0x1,(%r12)
	sqe->fd = fd;
    5263:	44 89 6d 04          	mov    %r13d,0x4(%rbp)
	sqe->user_data = (unsigned long) data;
    5267:	4c 89 65 20          	mov    %r12,0x20(%rbp)
	sqe->opcode = (__u8) op;
    526b:	c7 45 00 01 00 00 00 	movl   $0x1,0x0(%rbp)
	sqe->off = offset;
    5272:	48 c7 45 08 00 00 00 00 	movq   $0x0,0x8(%rbp)
    io_uring_prep_readv(sqe, client_socket, &req->iov[0], 1, 0);
    527a:	48 89 45 10          	mov    %rax,0x10(%rbp)
	sqe->len = len;
    527e:	48 c7 45 18 01 00 00 00 	movq   $0x1,0x18(%rbp)
	sqe->buf_index = 0;
    5286:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->addr3 = 0;
    528e:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    io_uring_submit(ring);
    5292:	e8 19 d1 ff ff       	call   23b0 <io_uring_submit@plt>
}
    5297:	48 83 c4 08          	add    $0x8,%rsp
    529b:	31 c0                	xor    %eax,%eax
    529d:	5b                   	pop    %rbx
    529e:	5d                   	pop    %rbp
    529f:	41 5c                	pop    %r12
    52a1:	41 5d                	pop    %r13
    52a3:	c3                   	ret
    52a4:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    52af:	90                   	nop

00000000000052b0 <_send_static_string_content>:
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    52b0:	f3 0f 1e fa          	endbr64
    52b4:	41 56                	push   %r14
    52b6:	41 89 f6             	mov    %esi,%r14d
    52b9:	41 55                	push   %r13
    52bb:	49 89 fd             	mov    %rdi,%r13
    void *buf = malloc(size);
    52be:	bf 20 00 00 00       	mov    $0x20,%edi
void _send_static_string_content(const char *str, int client_socket, struct io_uring *ring) {
    52c3:	41 54                	push   %r12
    52c5:	55                   	push   %rbp
    52c6:	48 89 d5             	mov    %rdx,%rbp
    52c9:	53                   	push   %rbx
    void *buf = malloc(size);
    52ca:	e8 d1 d1 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    52cf:	48 85 c0             	test   %rax,%rax
    52d2:	0f 84 dd 00 00 00    	je     53b5 <_send_static_string_content+0x105>
    52d8:	48 89 c3             	mov    %rax,%rbx
    unsigned long slen = strlen(str);
    52db:	4c 89 ef             	mov    %r13,%rdi
    52de:	e8 ad d0 ff ff       	call   2390 <strlen@plt>
    req->iovec_count = 1;
    52e3:	c7 43 04 01 00 00 00 	movl   $0x1,0x4(%rbx)
    req->client_socket = client_socket;
    52ea:	44 89 73 08          	mov    %r14d,0x8(%rbx)
    void *buf = malloc(size);
    52ee:	48 89 c7             	mov    %rax,%rdi
    unsigned long slen = strlen(str);
    52f1:	49 89 c4             	mov    %rax,%r12
    void *buf = malloc(size);
    52f4:	e8 a7 d1 ff ff       	call   24a0 <malloc@plt>
    52f9:	48 89 c7             	mov    %rax,%rdi
    if (!buf) {
    52fc:	48 85 c0             	test   %rax,%rax
    52ff:	0f 84 b0 00 00 00    	je     53b5 <_send_static_string_content+0x105>
    req->iov[0].iov_base = zh_malloc(slen);
    5305:	48 89 43 10          	mov    %rax,0x10(%rbx)
    5309:	4c 89 e2             	mov    %r12,%rdx
    530c:	4c 89 ee             	mov    %r13,%rsi
    req->iov[0].iov_len = slen;
    530f:	4c 89 63 18          	mov    %r12,0x18(%rbx)
    5313:	e8 48 d1 ff ff       	call   2460 <memcpy@plt>
	unsigned int head, next = sq->sqe_tail + 1;
    5318:	8b 45 44             	mov    0x44(%rbp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    531b:	8b 8d c0 00 00 00    	mov    0xc0(%rbp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5321:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5324:	48 8b 45 00          	mov    0x0(%rbp),%rax
    5328:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    532a:	f6 c1 02             	test   $0x2,%cl
    532d:	0f 85 7d 00 00 00    	jne    53b0 <_send_static_string_content+0x100>
	if (next - head <= sq->ring_entries) {
    5333:	89 d0                	mov    %edx,%eax
    5335:	29 f0                	sub    %esi,%eax
    5337:	39 45 5c             	cmp    %eax,0x5c(%rbp)
    533a:	0f 82 fc d2 ff ff    	jb     263c <_send_static_string_content.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5340:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5343:	8b 45 44             	mov    0x44(%rbp),%eax
    5346:	23 45 58             	and    0x58(%rbp),%eax
		sq->sqe_tail = next;
    5349:	89 55 44             	mov    %edx,0x44(%rbp)
	if (ring->flags & IORING_SETUP_SQE128)
    534c:	83 e1 01             	and    $0x1,%ecx
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    534f:	8b 53 04             	mov    0x4(%rbx),%edx
    req->event_type = EVENT_TYPE_WRITE;
    5352:	c7 03 02 00 00 00    	movl   $0x2,(%rbx)
	sqe->addr3 = 0;
    5358:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    535c:	d3 e0                	shl    %cl,%eax
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    535e:	8b 4b 08             	mov    0x8(%rbx),%ecx
    io_uring_submit(ring);
    5361:	48 89 ef             	mov    %rbp,%rdi
    5364:	48 c1 e0 06          	shl    $0x6,%rax
    5368:	48 03 45 38          	add    0x38(%rbp),%rax
	sqe->fd = fd;
    536c:	89 48 04             	mov    %ecx,0x4(%rax)
    io_uring_prep_writev(sqe, req->client_socket, req->iov, req->iovec_count, 0);
    536f:	48 8d 4b 10          	lea    0x10(%rbx),%rcx
	sqe->opcode = (__u8) op;
    5373:	c7 00 02 00 00 00    	movl   $0x2,(%rax)
	sqe->off = offset;
    5379:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
    5381:	48 89 48 10          	mov    %rcx,0x10(%rax)
	sqe->len = len;
    5385:	89 50 18             	mov    %edx,0x18(%rax)
	sqe->rw_flags = 0;
    5388:	c7 40 1c 00 00 00 00 	movl   $0x0,0x1c(%rax)
	sqe->buf_index = 0;
    538f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5397:	48 89 58 20          	mov    %rbx,0x20(%rax)
	sqe->addr3 = 0;
    539b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
}
    539f:	5b                   	pop    %rbx
    53a0:	5d                   	pop    %rbp
    53a1:	41 5c                	pop    %r12
    53a3:	41 5d                	pop    %r13
    53a5:	41 5e                	pop    %r14
    io_uring_submit(ring);
    53a7:	e9 04 d0 ff ff       	jmp    23b0 <io_uring_submit@plt>
    53ac:	0f 1f 40 00          	nopl   0x0(%rax)
		head = io_uring_smp_load_acquire(sq->khead);
    53b0:	e9 7e ff ff ff       	jmp    5333 <_send_static_string_content+0x83>
    53b5:	48 8b 0d 64 5c 00 00 	mov    0x5c64(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    53bc:	ba 28 00 00 00       	mov    $0x28,%edx
    53c1:	be 01 00 00 00       	mov    $0x1,%esi
    53c6:	48 8d 3d e3 31 00 00 	lea    0x31e3(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    53cd:	e8 8e d1 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    53d2:	bf 01 00 00 00       	mov    $0x1,%edi
    53d7:	e8 64 d1 ff ff       	call   2540 <exit@plt>
    53dc:	0f 1f 40 00          	nopl   0x0(%rax)

00000000000053e0 <handle_unimplemented_method>:
void handle_unimplemented_method(int client_socket, struct io_uring *ring) {
    53e0:	f3 0f 1e fa          	endbr64
    53e4:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(unimplemented_content, client_socket, ring);
    53e7:	89 fe                	mov    %edi,%esi
    53e9:	48 8b 3d 28 5c 00 00 	mov    0x5c28(%rip),%rdi        # b018 <unimplemented_content>
    53f0:	e9 bb fe ff ff       	jmp    52b0 <_send_static_string_content>
    53f5:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005400 <handle_http_404>:
void handle_http_404(int client_socket, struct io_uring *ring) {
    5400:	f3 0f 1e fa          	endbr64
    5404:	48 89 f2             	mov    %rsi,%rdx
    _send_static_string_content(http_404_content, client_socket, ring);
    5407:	89 fe                	mov    %edi,%esi
    5409:	48 8b 3d 00 5c 00 00 	mov    0x5c00(%rip),%rdi        # b010 <http_404_content>
    5410:	e9 9b fe ff ff       	jmp    52b0 <_send_static_string_content>
    5415:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000005420 <handle_get_method>:
void handle_get_method(char *path, int client_socket, struct io_uring *ring) {
    5420:	f3 0f 1e fa          	endbr64
    5424:	41 56                	push   %r14
    5426:	41 55                	push   %r13
    5428:	49 89 d5             	mov    %rdx,%r13
    542b:	41 54                	push   %r12
    542d:	41 89 f4             	mov    %esi,%r12d
    5430:	55                   	push   %rbp
    5431:	48 89 fd             	mov    %rdi,%rbp
    5434:	53                   	push   %rbx
    5435:	48 81 ec a0 04 00 00 	sub    $0x4a0,%rsp
    543c:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5445:	48 89 84 24 98 04 00 00 	mov    %rax,0x498(%rsp)
    544d:	31 c0                	xor    %eax,%eax
    if (path[strlen(path) - 1] == '/') {
    544f:	e8 3c cf ff ff       	call   2390 <strlen@plt>
    5454:	80 7c 05 ff 2f       	cmpb   $0x2f,-0x1(%rbp,%rax,1)
    5459:	48 89 c3             	mov    %rax,%rbx
    545c:	0f 84 b6 00 00 00    	je     5518 <handle_get_method+0xf8>
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5462:	b8 69 63 00 00       	mov    $0x6369,%eax


__fortify_function char *
__NTH (strcat (char *__restrict __dest, const char *__restrict __src))
{
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5467:	48 89 ee             	mov    %rbp,%rsi
    546a:	48 8d 53 01          	lea    0x1(%rbx),%rdx
    546e:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5473:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    547b:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5483:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
    548e:	66 89 84 24 94 00 00 00 	mov    %ax,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5496:	e8 a5 cf ff ff       	call   2440 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    549b:	48 89 e6             	mov    %rsp,%rsi
    549e:	4c 89 f7             	mov    %r14,%rdi
    54a1:	e8 aa cf ff ff       	call   2450 <stat@plt>
    54a6:	83 f8 ff             	cmp    $0xffffffff,%eax
    54a9:	0f 84 d3 00 00 00    	je     5582 <handle_get_method+0x162>
        if (S_ISREG(path_stat.st_mode)) {
    54af:	8b 44 24 18          	mov    0x18(%rsp),%eax
    54b3:	25 00 f0 00 00       	and    $0xf000,%eax
    54b8:	3d 00 80 00 00       	cmp    $0x8000,%eax
    54bd:	0f 84 f5 00 00 00    	je     55b8 <handle_get_method+0x198>
    _send_static_string_content(http_404_content, client_socket, ring);
    54c3:	48 8b 3d 46 5b 00 00 	mov    0x5b46(%rip),%rdi        # b010 <http_404_content>
    54ca:	4c 89 ea             	mov    %r13,%rdx
    54cd:	44 89 e6             	mov    %r12d,%esi
    54d0:	e8 db fd ff ff       	call   52b0 <_send_static_string_content>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    54d5:	4c 89 f2             	mov    %r14,%rdx
    54d8:	bf 01 00 00 00       	mov    $0x1,%edi
    54dd:	31 c0                	xor    %eax,%eax
    54df:	48 8d 35 61 2c 00 00 	lea    0x2c61(%rip),%rsi        # 8147 <_IO_stdin_used+0x147>
    54e6:	e8 f5 cf ff ff       	call   24e0 <__printf_chk@plt>
}
    54eb:	48 8b 84 24 98 04 00 00 	mov    0x498(%rsp),%rax
    54f3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    54fc:	0f 85 20 01 00 00    	jne    5622 <handle_get_method+0x202>
    5502:	48 81 c4 a0 04 00 00 	add    $0x4a0,%rsp
    5509:	5b                   	pop    %rbx
    550a:	5d                   	pop    %rbp
    550b:	41 5c                	pop    %r12
    550d:	41 5d                	pop    %r13
    550f:	41 5e                	pop    %r14
    5511:	c3                   	ret
    5512:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5518:	ba 69 63 00 00       	mov    $0x6369,%edx
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    551d:	48 8d bc 24 96 00 00 00 	lea    0x96(%rsp),%rdi
    5525:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    552a:	48 89 ee             	mov    %rbp,%rsi
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    552d:	66 89 94 24 94 00 00 00 	mov    %dx,0x94(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    5535:	48 89 c2             	mov    %rax,%rdx
  return __builtin___strcpy_chk (__dest, __src, __glibc_objsize (__dest));
    5538:	4c 8d b4 24 90 00 00 00 	lea    0x90(%rsp),%r14
    5540:	c7 84 24 90 00 00 00 70 75 62 6c 	movl   $0x6c627570,0x90(%rsp)
  return __builtin___strcat_chk (__dest, __src, __glibc_objsize (__dest));
    554b:	e8 f0 ce ff ff       	call   2440 <__memcpy_chk@plt>
    5550:	b9 fa 03 00 00       	mov    $0x3fa,%ecx
    5555:	49 8d 7c 1e 06       	lea    0x6(%r14,%rbx,1),%rdi
    555a:	48 8d 35 b1 2b 00 00 	lea    0x2bb1(%rip),%rsi        # 8112 <_IO_stdin_used+0x112>
    5561:	48 29 d9             	sub    %rbx,%rcx
    5564:	ba 0b 00 00 00       	mov    $0xb,%edx
    5569:	e8 d2 ce ff ff       	call   2440 <__memcpy_chk@plt>
    if (stat(final_path, &path_stat) == -1) {
    556e:	48 89 e6             	mov    %rsp,%rsi
    5571:	4c 89 f7             	mov    %r14,%rdi
    5574:	e8 d7 ce ff ff       	call   2450 <stat@plt>
    5579:	83 f8 ff             	cmp    $0xffffffff,%eax
    557c:	0f 85 2d ff ff ff    	jne    54af <handle_get_method+0x8f>
    5582:	4c 89 f2             	mov    %r14,%rdx
    5585:	48 89 e9             	mov    %rbp,%rcx
    5588:	48 8d 35 8e 2b 00 00 	lea    0x2b8e(%rip),%rsi        # 811d <_IO_stdin_used+0x11d>
    558f:	31 c0                	xor    %eax,%eax
    5591:	bf 01 00 00 00       	mov    $0x1,%edi
    5596:	e8 45 cf ff ff       	call   24e0 <__printf_chk@plt>
    _send_static_string_content(http_404_content, client_socket, ring);
    559b:	48 8b 3d 6e 5a 00 00 	mov    0x5a6e(%rip),%rdi        # b010 <http_404_content>
    55a2:	4c 89 ea             	mov    %r13,%rdx
    55a5:	44 89 e6             	mov    %r12d,%esi
    55a8:	e8 03 fd ff ff       	call   52b0 <_send_static_string_content>
}
    55ad:	e9 39 ff ff ff       	jmp    54eb <handle_get_method+0xcb>
    55b2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    void *buf = malloc(size);
    55b8:	bf 70 00 00 00       	mov    $0x70,%edi
    55bd:	e8 de ce ff ff       	call   24a0 <malloc@plt>
    55c2:	48 89 c3             	mov    %rax,%rbx
    if (!buf) {
    55c5:	48 85 c0             	test   %rax,%rax
    55c8:	74 5d                	je     5627 <handle_get_method+0x207>
            req->client_socket = client_socket;
    55ca:	44 89 60 08          	mov    %r12d,0x8(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    55ce:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    55d3:	48 8d 50 10          	lea    0x10(%rax),%rdx
    55d7:	4c 89 f7             	mov    %r14,%rdi
            req->iovec_count = 6;
    55da:	c7 40 04 06 00 00 00 	movl   $0x6,0x4(%rax)
            send_headers(final_path, path_stat.st_size, req->iov);
    55e1:	e8 5a f5 ff ff       	call   4b40 <send_headers>
            copy_file_contents(final_path, path_stat.st_size, &req->iov[5]);
    55e6:	48 8b 74 24 30       	mov    0x30(%rsp),%rsi
    55eb:	48 8d 53 60          	lea    0x60(%rbx),%rdx
    55ef:	4c 89 f7             	mov    %r14,%rdi
    55f2:	e8 79 fa ff ff       	call   5070 <copy_file_contents>
    55f7:	48 8b 4c 24 30       	mov    0x30(%rsp),%rcx
    55fc:	4c 89 f2             	mov    %r14,%rdx
    55ff:	31 c0                	xor    %eax,%eax
    5601:	48 8d 35 2d 2b 00 00 	lea    0x2b2d(%rip),%rsi        # 8135 <_IO_stdin_used+0x135>
    5608:	bf 01 00 00 00       	mov    $0x1,%edi
    560d:	e8 ce ce ff ff       	call   24e0 <__printf_chk@plt>
            add_write_request(req, ring);
    5612:	4c 89 ee             	mov    %r13,%rsi
    5615:	48 89 df             	mov    %rbx,%rdi
    5618:	e8 13 fb ff ff       	call   5130 <add_write_request>
    561d:	e9 c9 fe ff ff       	jmp    54eb <handle_get_method+0xcb>
}
    5622:	e8 79 cd ff ff       	call   23a0 <__stack_chk_fail@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5627:	48 8b 0d f2 59 00 00 	mov    0x59f2(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    562e:	ba 28 00 00 00       	mov    $0x28,%edx
    5633:	be 01 00 00 00       	mov    $0x1,%esi
    5638:	48 8d 3d 71 2f 00 00 	lea    0x2f71(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    563f:	e8 1c cf ff ff       	call   2560 <fwrite@plt>
        exit(1);
    5644:	bf 01 00 00 00       	mov    $0x1,%edi
    5649:	e8 f2 ce ff ff       	call   2540 <exit@plt>
    564e:	66 90                	xchg   %ax,%ax

0000000000005650 <handle_http_method>:
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    5650:	f3 0f 1e fa          	endbr64
    5654:	41 57                	push   %r15
    5656:	41 56                	push   %r14
    method = strtok_r(method_buffer, " ", &saveptr);
    5658:	4c 8d 35 4d 2a 00 00 	lea    0x2a4d(%rip),%r14        # 80ac <_IO_stdin_used+0xac>
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    565f:	41 55                	push   %r13
    5661:	49 89 d5             	mov    %rdx,%r13
    5664:	41 54                	push   %r12
    5666:	41 89 f4             	mov    %esi,%r12d
    method = strtok_r(method_buffer, " ", &saveptr);
    5669:	4c 89 f6             	mov    %r14,%rsi
void handle_http_method(char *method_buffer, int client_socket, struct io_uring *ring) {
    566c:	55                   	push   %rbp
    566d:	53                   	push   %rbx
    566e:	48 83 ec 18          	sub    $0x18,%rsp
    5672:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    567b:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    5680:	31 c0                	xor    %eax,%eax
    method = strtok_r(method_buffer, " ", &saveptr);
    5682:	49 89 e7             	mov    %rsp,%r15
    5685:	4c 89 fa             	mov    %r15,%rdx
    5688:	e8 73 cd ff ff       	call   2400 <strtok_r@plt>
    for (; *str; ++str)
    568d:	48 0f be 18          	movsbq (%rax),%rbx
    method = strtok_r(method_buffer, " ", &saveptr);
    5691:	48 89 c5             	mov    %rax,%rbp
    for (; *str; ++str)
    5694:	84 db                	test   %bl,%bl
    5696:	74 1d                	je     56b5 <handle_http_method+0x65>
        *str = (char)tolower(*str);
    5698:	e8 33 cf ff ff       	call   25d0 <__ctype_tolower_loc@plt>
    569d:	48 89 ea             	mov    %rbp,%rdx
    56a0:	48 8b 08             	mov    (%rax),%rcx
    for (; *str; ++str)
    56a3:	48 83 c2 01          	add    $0x1,%rdx
        *str = (char)tolower(*str);
    56a7:	8b 0c 99             	mov    (%rcx,%rbx,4),%ecx
    56aa:	88 4a ff             	mov    %cl,-0x1(%rdx)
    for (; *str; ++str)
    56ad:	48 0f be 1a          	movsbq (%rdx),%rbx
    56b1:	84 db                	test   %bl,%bl
    56b3:	75 eb                	jne    56a0 <handle_http_method+0x50>
    path = strtok_r(NULL, " ", &saveptr);
    56b5:	4c 89 fa             	mov    %r15,%rdx
    56b8:	4c 89 f6             	mov    %r14,%rsi
    56bb:	31 ff                	xor    %edi,%edi
    56bd:	e8 3e cd ff ff       	call   2400 <strtok_r@plt>
    if (strcmp(method, "get") == 0) {
    56c2:	48 8d 35 91 2a 00 00 	lea    0x2a91(%rip),%rsi        # 815a <_IO_stdin_used+0x15a>
    56c9:	48 89 ef             	mov    %rbp,%rdi
    path = strtok_r(NULL, " ", &saveptr);
    56cc:	48 89 c3             	mov    %rax,%rbx
    if (strcmp(method, "get") == 0) {
    56cf:	e8 5c cd ff ff       	call   2430 <strcmp@plt>
        handle_get_method(path, client_socket, ring);
    56d4:	4c 89 ea             	mov    %r13,%rdx
    56d7:	44 89 e6             	mov    %r12d,%esi
    if (strcmp(method, "get") == 0) {
    56da:	85 c0                	test   %eax,%eax
    56dc:	75 2a                	jne    5708 <handle_http_method+0xb8>
        handle_get_method(path, client_socket, ring);
    56de:	48 89 df             	mov    %rbx,%rdi
    56e1:	e8 3a fd ff ff       	call   5420 <handle_get_method>
}
    56e6:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    56eb:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    56f4:	75 20                	jne    5716 <handle_http_method+0xc6>
    56f6:	48 83 c4 18          	add    $0x18,%rsp
    56fa:	5b                   	pop    %rbx
    56fb:	5d                   	pop    %rbp
    56fc:	41 5c                	pop    %r12
    56fe:	41 5d                	pop    %r13
    5700:	41 5e                	pop    %r14
    5702:	41 5f                	pop    %r15
    5704:	c3                   	ret
    5705:	0f 1f 00             	nopl   (%rax)
    _send_static_string_content(unimplemented_content, client_socket, ring);
    5708:	48 8b 3d 09 59 00 00 	mov    0x5909(%rip),%rdi        # b018 <unimplemented_content>
    570f:	e8 9c fb ff ff       	call   52b0 <_send_static_string_content>
}
    5714:	eb d0                	jmp    56e6 <handle_http_method+0x96>
    5716:	e8 85 cc ff ff       	call   23a0 <__stack_chk_fail@plt>
    571b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000005720 <get_line>:
int get_line(const char *src, char *dest, int dest_sz) {
    5720:	f3 0f 1e fa          	endbr64
    for (int i = 0; i < dest_sz; i++) {
    5724:	85 d2                	test   %edx,%edx
    5726:	7e 38                	jle    5760 <get_line+0x40>
    5728:	48 63 d2             	movslq %edx,%rdx
    572b:	48 83 c7 01          	add    $0x1,%rdi
    572f:	48 01 f2             	add    %rsi,%rdx
    5732:	eb 11                	jmp    5745 <get_line+0x25>
    5734:	0f 1f 40 00          	nopl   0x0(%rax)
    5738:	48 83 c6 01          	add    $0x1,%rsi
    573c:	48 83 c7 01          	add    $0x1,%rdi
    5740:	48 39 d6             	cmp    %rdx,%rsi
    5743:	74 1b                	je     5760 <get_line+0x40>
        dest[i] = src[i];
    5745:	0f b6 47 ff          	movzbl -0x1(%rdi),%eax
    5749:	88 06                	mov    %al,(%rsi)
        if (src[i] == '\r' && src[i+1] == '\n') {
    574b:	3c 0d                	cmp    $0xd,%al
    574d:	75 e9                	jne    5738 <get_line+0x18>
    574f:	80 3f 0a             	cmpb   $0xa,(%rdi)
    5752:	75 e4                	jne    5738 <get_line+0x18>
            dest[i] = '\0';
    5754:	c6 06 00             	movb   $0x0,(%rsi)
            return 0;
    5757:	31 c0                	xor    %eax,%eax
    5759:	c3                   	ret
    575a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    return 1;
    5760:	b8 01 00 00 00       	mov    $0x1,%eax
}
    5765:	c3                   	ret
    5766:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000005770 <handle_client_request>:
int handle_client_request(struct Request *req, struct io_uring *ring) {
    5770:	f3 0f 1e fa          	endbr64
    5774:	48 81 ec 18 04 00 00 	sub    $0x418,%rsp
    577b:	48 8b 4f 10          	mov    0x10(%rdi),%rcx
    577f:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    5788:	48 89 84 24 08 04 00 00 	mov    %rax,0x408(%rsp)
    5790:	31 c0                	xor    %eax,%eax
    for (int i = 0; i < dest_sz; i++) {
    5792:	49 89 e2             	mov    %rsp,%r10
    5795:	4c 8d 8c 24 00 04 00 00 	lea    0x400(%rsp),%r9
    579d:	4c 89 d0             	mov    %r10,%rax
    57a0:	eb 13                	jmp    57b5 <handle_client_request+0x45>
    57a2:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
    57a8:	48 83 c0 01          	add    $0x1,%rax
    57ac:	48 83 c1 01          	add    $0x1,%rcx
    57b0:	4c 39 c8             	cmp    %r9,%rax
    57b3:	74 4b                	je     5800 <handle_client_request+0x90>
        dest[i] = src[i];
    57b5:	44 0f b6 01          	movzbl (%rcx),%r8d
    57b9:	44 88 00             	mov    %r8b,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    57bc:	41 80 f8 0d          	cmp    $0xd,%r8b
    57c0:	75 e6                	jne    57a8 <handle_client_request+0x38>
    57c2:	80 79 01 0a          	cmpb   $0xa,0x1(%rcx)
    57c6:	75 e0                	jne    57a8 <handle_client_request+0x38>
            dest[i] = '\0';
    57c8:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    57cb:	8b 47 08             	mov    0x8(%rdi),%eax
    57ce:	48 89 f2             	mov    %rsi,%rdx
    57d1:	4c 89 d7             	mov    %r10,%rdi
    57d4:	89 c6                	mov    %eax,%esi
    57d6:	e8 75 fe ff ff       	call   5650 <handle_http_method>
}
    57db:	48 8b 84 24 08 04 00 00 	mov    0x408(%rsp),%rax
    57e3:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    57ec:	75 39                	jne    5827 <handle_client_request+0xb7>
    57ee:	31 c0                	xor    %eax,%eax
    57f0:	48 81 c4 18 04 00 00 	add    $0x418,%rsp
    57f7:	c3                   	ret
    57f8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    5800:	48 8b 0d 19 58 00 00 	mov    0x5819(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5807:	ba 12 00 00 00       	mov    $0x12,%edx
    580c:	be 01 00 00 00       	mov    $0x1,%esi
    5811:	48 8d 3d 46 29 00 00 	lea    0x2946(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5818:	e8 43 cd ff ff       	call   2560 <fwrite@plt>
        exit(1);
    581d:	bf 01 00 00 00       	mov    $0x1,%edi
    5822:	e8 19 cd ff ff       	call   2540 <exit@plt>
}
    5827:	e8 74 cb ff ff       	call   23a0 <__stack_chk_fail@plt>
    582c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000005830 <add_accept_request>:
                       socklen_t *client_addr_len, struct io_uring *ring) {
    5830:	f3 0f 1e fa          	endbr64
    5834:	55                   	push   %rbp
    5835:	53                   	push   %rbx
    5836:	48 89 cb             	mov    %rcx,%rbx
    5839:	48 83 ec 08          	sub    $0x8,%rsp
	unsigned int head, next = sq->sqe_tail + 1;
    583d:	8b 41 44             	mov    0x44(%rcx),%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    5840:	4c 8b 03             	mov    (%rbx),%r8
	if (ring->flags & IORING_SETUP_SQE128)
    5843:	8b 89 c0 00 00 00    	mov    0xc0(%rcx),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5849:	83 c0 01             	add    $0x1,%eax
		head = IO_URING_READ_ONCE(*sq->khead);
    584c:	45 8b 08             	mov    (%r8),%r9d
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    584f:	f6 c1 02             	test   $0x2,%cl
    5852:	74 00                	je     5854 <add_accept_request+0x24>
	if (next - head <= sq->ring_entries) {
    5854:	41 89 c0             	mov    %eax,%r8d
    5857:	45 29 c8             	sub    %r9d,%r8d
    585a:	44 39 43 5c          	cmp    %r8d,0x5c(%rbx)
    585e:	0f 82 e8 cd ff ff    	jb     264c <add_accept_request.cold>
	if (ring->flags & IORING_SETUP_SQE128)
    5864:	c1 e9 0a             	shr    $0xa,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5867:	8b 6b 44             	mov    0x44(%rbx),%ebp
    586a:	23 6b 58             	and    0x58(%rbx),%ebp
		sq->sqe_tail = next;
    586d:	89 43 44             	mov    %eax,0x44(%rbx)
	if (ring->flags & IORING_SETUP_SQE128)
    5870:	83 e1 01             	and    $0x1,%ecx
	sqe->addr3 = 0;
    5873:	66 0f ef c0          	pxor   %xmm0,%xmm0
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5877:	d3 e5                	shl    %cl,%ebp
    5879:	48 c1 e5 06          	shl    $0x6,%rbp
    587d:	48 03 6b 38          	add    0x38(%rbx),%rbp
	sqe->fd = fd;
    5881:	89 7d 04             	mov    %edi,0x4(%rbp)
  struct Request *req = malloc(sizeof(*req));
    5884:	bf 10 00 00 00       	mov    $0x10,%edi
	sqe->opcode = (__u8) op;
    5889:	c7 45 00 0d 00 00 00 	movl   $0xd,0x0(%rbp)
	sqe->off = offset;
    5890:	48 89 55 08          	mov    %rdx,0x8(%rbp)
	sqe->addr = (unsigned long) addr;
    5894:	48 89 75 10          	mov    %rsi,0x10(%rbp)
	sqe->buf_index = 0;
    5898:	48 c7 45 28 00 00 00 00 	movq   $0x0,0x28(%rbp)
	sqe->len = len;
    58a0:	48 c7 45 18 00 00 00 00 	movq   $0x0,0x18(%rbp)
	sqe->addr3 = 0;
    58a8:	0f 11 45 30          	movups %xmm0,0x30(%rbp)
    58ac:	e8 ef cb ff ff       	call   24a0 <malloc@plt>
  io_uring_submit(ring);
    58b1:	48 89 df             	mov    %rbx,%rdi
  req->event_type = EVENT_TYPE_ACCEPT;
    58b4:	c7 00 00 00 00 00    	movl   $0x0,(%rax)
	sqe->user_data = (unsigned long) data;
    58ba:	48 89 45 20          	mov    %rax,0x20(%rbp)
}
    58be:	48 83 c4 08          	add    $0x8,%rsp
    58c2:	5b                   	pop    %rbx
    58c3:	5d                   	pop    %rbp
  io_uring_submit(ring);
    58c4:	e9 e7 ca ff ff       	jmp    23b0 <io_uring_submit@plt>
    58c9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

00000000000058d0 <io_thread>:
void* io_thread(void *arg) {
    58d0:	f3 0f 1e fa          	endbr64
    58d4:	41 57                	push   %r15
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    58d6:	31 d2                	xor    %edx,%edx
void* io_thread(void *arg) {
    58d8:	41 56                	push   %r14
    58da:	41 55                	push   %r13
    58dc:	41 54                	push   %r12
    58de:	55                   	push   %rbp
    58df:	48 89 fd             	mov    %rdi,%rbp
    58e2:	53                   	push   %rbx
    58e3:	48 81 ec 58 05 00 00 	sub    $0x558,%rsp
  struct io_uring ring = *data->ring;
    58ea:	64 48 8b 04 25 28 00 00 00 	mov    %fs:0x28,%rax
    58f3:	48 89 84 24 48 05 00 00 	mov    %rax,0x548(%rsp)
    58fb:	48 8b 47 58          	mov    0x58(%rdi),%rax
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    58ff:	48 8d 5c 24 60       	lea    0x60(%rsp),%rbx
    5904:	bf 00 01 00 00       	mov    $0x100,%edi
    5909:	48 89 de             	mov    %rbx,%rsi
  struct io_uring ring = *data->ring;
    590c:	f3 0f 6f 08          	movdqu (%rax),%xmm1
    5910:	0f 29 4c 24 60       	movaps %xmm1,0x60(%rsp)
    5915:	f3 0f 6f 50 10       	movdqu 0x10(%rax),%xmm2
    591a:	0f 29 54 24 70       	movaps %xmm2,0x70(%rsp)
    591f:	f3 0f 6f 58 20       	movdqu 0x20(%rax),%xmm3
    5924:	0f 29 9c 24 80 00 00 00 	movaps %xmm3,0x80(%rsp)
    592c:	f3 0f 6f 60 30       	movdqu 0x30(%rax),%xmm4
    5931:	0f 29 a4 24 90 00 00 00 	movaps %xmm4,0x90(%rsp)
    5939:	f3 0f 6f 68 40       	movdqu 0x40(%rax),%xmm5
    593e:	0f 29 ac 24 a0 00 00 00 	movaps %xmm5,0xa0(%rsp)
    5946:	f3 0f 6f 70 50       	movdqu 0x50(%rax),%xmm6
    594b:	0f 29 b4 24 b0 00 00 00 	movaps %xmm6,0xb0(%rsp)
    5953:	f3 0f 6f 78 60       	movdqu 0x60(%rax),%xmm7
    5958:	0f 29 bc 24 c0 00 00 00 	movaps %xmm7,0xc0(%rsp)
    5960:	f3 0f 6f 48 70       	movdqu 0x70(%rax),%xmm1
    5965:	0f 29 8c 24 d0 00 00 00 	movaps %xmm1,0xd0(%rsp)
    596d:	f3 0f 6f 90 80 00 00 00 	movdqu 0x80(%rax),%xmm2
    5975:	0f 29 94 24 e0 00 00 00 	movaps %xmm2,0xe0(%rsp)
    597d:	f3 0f 6f 98 90 00 00 00 	movdqu 0x90(%rax),%xmm3
    5985:	0f 29 9c 24 f0 00 00 00 	movaps %xmm3,0xf0(%rsp)
    598d:	f3 0f 6f a0 a0 00 00 00 	movdqu 0xa0(%rax),%xmm4
    5995:	0f 29 a4 24 00 01 00 00 	movaps %xmm4,0x100(%rsp)
    599d:	f3 0f 6f a8 b0 00 00 00 	movdqu 0xb0(%rax),%xmm5
    59a5:	0f 29 ac 24 10 01 00 00 	movaps %xmm5,0x110(%rsp)
    59ad:	f3 0f 6f b0 c0 00 00 00 	movdqu 0xc0(%rax),%xmm6
    59b5:	0f 29 b4 24 20 01 00 00 	movaps %xmm6,0x120(%rsp)
    59bd:	48 8b 80 d0 00 00 00 	mov    0xd0(%rax),%rax
    59c4:	48 89 84 24 30 01 00 00 	mov    %rax,0x130(%rsp)
  io_uring_queue_init(QUEUE_DEPTH, &ring, 0);
    59cc:	e8 9f ca ff ff       	call   2470 <io_uring_queue_init@plt>
  io_uring_register_eventfd(data->ring, 0);
    59d1:	48 8b 7d 58          	mov    0x58(%rbp),%rdi
    59d5:	31 f6                	xor    %esi,%esi
    59d7:	e8 a4 cb ff ff       	call   2580 <io_uring_register_eventfd@plt>
  sock = socket(PF_INET, SOCK_STREAM, 0);
    59dc:	31 d2                	xor    %edx,%edx
    59de:	be 01 00 00 00       	mov    $0x1,%esi
    59e3:	bf 02 00 00 00       	mov    $0x2,%edi
    59e8:	e8 03 cc ff ff       	call   25f0 <socket@plt>
  if (sock == -1)
    59ed:	83 f8 ff             	cmp    $0xffffffff,%eax
    59f0:	0f 84 98 cc ff ff    	je     268e <io_thread.cold+0x38>
  if (setsockopt(sock,
    59f6:	48 8d 4c 24 30       	lea    0x30(%rsp),%rcx
    59fb:	41 b8 04 00 00 00    	mov    $0x4,%r8d
    5a01:	89 c7                	mov    %eax,%edi
    5a03:	41 89 c4             	mov    %eax,%r12d
    5a06:	ba 02 00 00 00       	mov    $0x2,%edx
    5a0b:	be 01 00 00 00       	mov    $0x1,%esi
  int enable = 1;
    5a10:	c7 44 24 30 01 00 00 00 	movl   $0x1,0x30(%rsp)
  if (setsockopt(sock,
    5a18:	e8 43 c9 ff ff       	call   2360 <setsockopt@plt>
    5a1d:	85 c0                	test   %eax,%eax
    5a1f:	0f 88 3d cc ff ff    	js     2662 <io_thread.cold+0xc>
  return __builtin___memset_chk (__dest, __ch, __len,
    5a25:	48 8d 74 24 40       	lea    0x40(%rsp),%rsi
  if (bind(sock,
    5a2a:	ba 10 00 00 00       	mov    $0x10,%edx
    5a2f:	44 89 e7             	mov    %r12d,%edi
    5a32:	48 c7 44 24 44 00 00 00 00 	movq   $0x0,0x44(%rsp)
    5a3b:	c7 44 24 4c 00 00 00 00 	movl   $0x0,0x4c(%rsp)
  srv_addr.sin_family = AF_INET;
    5a43:	c7 44 24 40 02 00 18 db 	movl   $0xdb180002,0x40(%rsp)
  if (bind(sock,
    5a4b:	e8 a0 ca ff ff       	call   24f0 <bind@plt>
    5a50:	85 c0                	test   %eax,%eax
    5a52:	0f 88 42 cc ff ff    	js     269a <io_thread.cold+0x44>
  if (listen(sock, 10) < 0) {
    5a58:	be 0a 00 00 00       	mov    $0xa,%esi
    5a5d:	44 89 e7             	mov    %r12d,%edi
    5a60:	e8 4b ca ff ff       	call   24b0 <listen@plt>
    5a65:	85 c0                	test   %eax,%eax
    5a67:	0f 88 01 cc ff ff    	js     266e <io_thread.cold+0x18>
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5a6d:	ba db 18 00 00       	mov    $0x18db,%edx
    5a72:	48 8d 35 2a 27 00 00 	lea    0x272a(%rip),%rsi        # 81a3 <_IO_stdin_used+0x1a3>
    5a79:	bf 01 00 00 00       	mov    $0x1,%edi
    5a7e:	31 c0                	xor    %eax,%eax
    5a80:	e8 5b ca ff ff       	call   24e0 <__printf_chk@plt>
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5a85:	48 8d 44 24 50       	lea    0x50(%rsp),%rax
    5a8a:	48 89 d9             	mov    %rbx,%rcx
    5a8d:	44 89 e7             	mov    %r12d,%edi
    5a90:	48 8d 54 24 34       	lea    0x34(%rsp),%rdx
    5a95:	48 89 c6             	mov    %rax,%rsi
    5a98:	48 89 44 24 10       	mov    %rax,0x10(%rsp)
    5a9d:	48 89 54 24 18       	mov    %rdx,0x18(%rsp)
  socklen_t client_addr_len = sizeof(client_addr);
    5aa2:	c7 44 24 34 10 00 00 00 	movl   $0x10,0x34(%rsp)
  add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5aaa:	e8 81 fd ff ff       	call   5830 <add_accept_request>
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5aaf:	bf 01 00 00 00       	mov    $0x1,%edi
    5ab4:	be 10 00 00 00       	mov    $0x10,%esi
    5ab9:	e8 62 c9 ff ff       	call   2420 <calloc@plt>
    void *buf = malloc(size);
    5abe:	bf 0a 00 00 00       	mov    $0xa,%edi
  struct iovec *iov = calloc(1, sizeof(struct iovec));
    5ac3:	49 89 c5             	mov    %rax,%r13
    void *buf = malloc(size);
    5ac6:	e8 d5 c9 ff ff       	call   24a0 <malloc@plt>
    if (!buf) {
    5acb:	48 85 c0             	test   %rax,%rax
    5ace:	0f 84 ae 04 00 00    	je     5f82 <io_thread+0x6b2>
  iov->iov_base = zh_malloc(10);
    5ad4:	49 89 45 00          	mov    %rax,0x0(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5ad8:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5adf:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
  iov->iov_len = 10;
    5ae6:	49 c7 45 08 0a 00 00 00 	movq   $0xa,0x8(%r13)
	unsigned int head, next = sq->sqe_tail + 1;
    5aee:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5af1:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5af6:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5af8:	f6 c1 02             	test   $0x2,%cl
    5afb:	0f 85 0f 04 00 00    	jne    5f10 <io_thread+0x640>
	if (next - head <= sq->ring_entries) {
    5b01:	89 d0                	mov    %edx,%eax
    5b03:	29 f0                	sub    %esi,%eax
    5b05:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5b0c:	0f 82 72 cb ff ff    	jb     2684 <io_thread.cold+0x2e>
	if (ring->flags & IORING_SETUP_SQE128)
    5b12:	c1 e9 0a             	shr    $0xa,%ecx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5b15:	48 8d 75 60          	lea    0x60(%rbp),%rsi
	sqe->addr3 = 0;
    5b19:	66 0f ef c0          	pxor   %xmm0,%xmm0
  io_uring_submit(&ring);
    5b1d:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5b20:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5b27:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5b2a:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5b31:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5b38:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5b3a:	8b 55 60             	mov    0x60(%rbp),%edx
        io_uring_sqe_set_data(sqe, &data->_eventfd); 
    5b3d:	48 89 74 24 08       	mov    %rsi,0x8(%rsp)
    5b42:	48 c1 e0 06          	shl    $0x6,%rax
    5b46:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5b4e:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5b54:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5b57:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5b5f:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5b63:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5b6b:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5b73:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5b77:	0f 11 40 30          	movups %xmm0,0x30(%rax)
  io_uring_submit(&ring);
    5b7b:	e8 30 c8 ff ff       	call   23b0 <io_uring_submit@plt>
  while (data->running == 1) {
    5b80:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5b84:	4c 8d 4c 24 38       	lea    0x38(%rsp),%r9
    5b89:	4c 8d 94 24 40 01 00 00 	lea    0x140(%rsp),%r10
    5b91:	0f 85 d7 01 00 00    	jne    5d6e <io_thread+0x49e>
    5b97:	44 89 64 24 24       	mov    %r12d,0x24(%rsp)
    5b9c:	4d 89 ce             	mov    %r9,%r14
    5b9f:	4c 89 54 24 28       	mov    %r10,0x28(%rsp)
    5ba4:	0f 1f 40 00          	nopl   0x0(%rax)
    5ba8:	48 8d 3d 0a 26 00 00 	lea    0x260a(%rip),%rdi        # 81b9 <_IO_stdin_used+0x1b9>
    5baf:	e8 9c c7 ff ff       	call   2350 <puts@plt>
	if (ring->flags & IORING_SETUP_CQE32)
    5bb4:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned mask = ring->cq.ring_mask;
    5bbb:	8b bc 24 10 01 00 00 	mov    0x110(%rsp),%edi
	if (ring->flags & IORING_SETUP_CQE32)
    5bc2:	c1 e9 0b             	shr    $0xb,%ecx
    5bc5:	83 e1 01             	and    $0x1,%ecx
		unsigned tail = io_uring_smp_load_acquire(ring->cq.ktail);
    5bc8:	48 8b 84 24 d0 00 00 00 	mov    0xd0(%rsp),%rax
    5bd0:	8b 00                	mov    (%rax),%eax
		unsigned head = *ring->cq.khead;
    5bd2:	48 8b b4 24 c8 00 00 00 	mov    0xc8(%rsp),%rsi
    5bda:	8b 16                	mov    (%rsi),%edx
		if (!available)
    5bdc:	39 d0                	cmp    %edx,%eax
    5bde:	74 36                	je     5c16 <io_thread+0x346>
		cqe = &ring->cq.cqes[(head & mask) << shift];
    5be0:	89 f8                	mov    %edi,%eax
    5be2:	21 d0                	and    %edx,%eax
    5be4:	d3 e0                	shl    %cl,%eax
    5be6:	48 c1 e0 04          	shl    $0x4,%rax
    5bea:	48 03 84 24 f8 00 00 00 	add    0xf8(%rsp),%rax
		if (!(ring->features & IORING_FEAT_EXT_ARG) &&
    5bf2:	f6 84 24 29 01 00 00 01 	testb  $0x1,0x129(%rsp)
    5bfa:	0f 85 a8 01 00 00    	jne    5da8 <io_thread+0x4d8>
    5c00:	48 83 38 ff          	cmpq   $0xffffffffffffffff,(%rax)
    5c04:	0f 85 0e 03 00 00    	jne    5f18 <io_thread+0x648>
			if (cqe->res < 0)
    5c0a:	8b 40 08             	mov    0x8(%rax),%eax
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5c0d:	83 c2 01             	add    $0x1,%edx
    5c10:	89 16                	mov    %edx,(%rsi)
			if (!err)
    5c12:	85 c0                	test   %eax,%eax
    5c14:	79 b2                	jns    5bc8 <io_thread+0x2f8>
	*cqe_ptr = cqe;
    5c16:	48 c7 44 24 38 00 00 00 00 	movq   $0x0,0x38(%rsp)
	return err;
    5c1f:	90                   	nop
	return __io_uring_get_cqe(ring, cqe_ptr, 0, wait_nr, NULL);
    5c20:	45 31 c0             	xor    %r8d,%r8d
    5c23:	31 d2                	xor    %edx,%edx
    5c25:	b9 01 00 00 00       	mov    $0x1,%ecx
    5c2a:	4c 89 f6             	mov    %r14,%rsi
    5c2d:	48 89 df             	mov    %rbx,%rdi
    5c30:	e8 9b c8 ff ff       	call   24d0 <__io_uring_get_cqe@plt>
    5c35:	41 89 c7             	mov    %eax,%r15d
      if (cqe->user_data == 1) {
    5c38:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5c3d:	48 83 38 01          	cmpq   $0x1,(%rax)
    5c41:	0f 84 e1 02 00 00    	je     5f28 <io_thread+0x658>
    5c47:	48 8d 3d 91 25 00 00 	lea    0x2591(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5c4e:	e8 fd c6 ff ff       	call   2350 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5c53:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5c58:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5c5b:	45 85 ff             	test   %r15d,%r15d
    5c5e:	0f 88 f2 c9 ff ff    	js     2656 <io_thread.cold>
      if (cqe->res < 0) {
    5c64:	8b 42 08             	mov    0x8(%rdx),%eax
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5c67:	45 8b 04 24          	mov    (%r12),%r8d
      if (cqe->res < 0) {
    5c6b:	85 c0                	test   %eax,%eax
    5c6d:	0f 88 d5 02 00 00    	js     5f48 <io_thread+0x678>
      switch (req->event_type) {
    5c73:	41 83 f8 01          	cmp    $0x1,%r8d
    5c77:	0f 84 7b 01 00 00    	je     5df8 <io_thread+0x528>
    5c7d:	41 83 f8 02          	cmp    $0x2,%r8d
    5c81:	0f 84 a1 01 00 00    	je     5e28 <io_thread+0x558>
    5c87:	45 85 c0             	test   %r8d,%r8d
    5c8a:	0f 85 50 01 00 00    	jne    5de0 <io_thread+0x510>
              add_accept_request(sock, &client_addr, &client_addr_len, &ring);
    5c90:	48 8b 54 24 18       	mov    0x18(%rsp),%rdx
    5c95:	48 8b 74 24 10       	mov    0x10(%rsp),%rsi
    5c9a:	48 89 d9             	mov    %rbx,%rcx
    5c9d:	8b 7c 24 24          	mov    0x24(%rsp),%edi
    5ca1:	e8 8a fb ff ff       	call   5830 <add_accept_request>
              add_read_request(cqe->res, &ring);
    5ca6:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5cab:	48 89 de             	mov    %rbx,%rsi
    5cae:	8b 78 08             	mov    0x8(%rax),%edi
    5cb1:	e8 1a f5 ff ff       	call   51d0 <add_read_request>
              free(req);
    5cb6:	4c 89 e7             	mov    %r12,%rdi
    5cb9:	e8 62 c6 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5cbe:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
	if (cqe)
    5cc3:	48 85 c0             	test   %rax,%rax
    5cc6:	0f 85 14 01 00 00    	jne    5de0 <io_thread+0x510>
	unsigned int head, next = sq->sqe_tail + 1;
    5ccc:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5cd3:	8b 8c 24 20 01 00 00 	mov    0x120(%rsp),%ecx
	unsigned int head, next = sq->sqe_tail + 1;
    5cda:	8d 50 01             	lea    0x1(%rax),%edx
		head = IO_URING_READ_ONCE(*sq->khead);
    5cdd:	48 8b 44 24 60       	mov    0x60(%rsp),%rax
    5ce2:	8b 30                	mov    (%rax),%esi
	if (!(ring->flags & IORING_SETUP_SQPOLL))
    5ce4:	f6 c1 02             	test   $0x2,%cl
    5ce7:	74 00                	je     5ce9 <io_thread+0x419>
	if (next - head <= sq->ring_entries) {
    5ce9:	89 d0                	mov    %edx,%eax
    5ceb:	29 f0                	sub    %esi,%eax
    5ced:	39 84 24 bc 00 00 00 	cmp    %eax,0xbc(%rsp)
    5cf4:	0f 82 80 c9 ff ff    	jb     267a <io_thread.cold+0x24>
	if (ring->flags & IORING_SETUP_SQE128)
    5cfa:	c1 e9 0a             	shr    $0xa,%ecx
	sqe->user_data = (unsigned long) data;
    5cfd:	48 8b 74 24 08       	mov    0x8(%rsp),%rsi
	sqe->addr3 = 0;
    5d02:	66 0f ef c0          	pxor   %xmm0,%xmm0
      io_uring_submit(&ring);
    5d06:	48 89 df             	mov    %rbx,%rdi
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d09:	8b 84 24 a4 00 00 00 	mov    0xa4(%rsp),%eax
	if (ring->flags & IORING_SETUP_SQE128)
    5d10:	83 e1 01             	and    $0x1,%ecx
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d13:	23 84 24 b8 00 00 00 	and    0xb8(%rsp),%eax
		sq->sqe_tail = next;
    5d1a:	89 94 24 a4 00 00 00 	mov    %edx,0xa4(%rsp)
		sqe = &sq->sqes[(sq->sqe_tail & sq->ring_mask) << shift];
    5d21:	d3 e0                	shl    %cl,%eax
        io_uring_prep_readv(sqe, data->_eventfd, iov, 1, 0);
    5d23:	8b 55 60             	mov    0x60(%rbp),%edx
    5d26:	48 c1 e0 06          	shl    $0x6,%rax
    5d2a:	48 03 84 24 98 00 00 00 	add    0x98(%rsp),%rax
	sqe->opcode = (__u8) op;
    5d32:	c7 00 01 00 00 00    	movl   $0x1,(%rax)
	sqe->fd = fd;
    5d38:	89 50 04             	mov    %edx,0x4(%rax)
	sqe->off = offset;
    5d3b:	48 c7 40 08 00 00 00 00 	movq   $0x0,0x8(%rax)
	sqe->addr = (unsigned long) addr;
    5d43:	4c 89 68 10          	mov    %r13,0x10(%rax)
	sqe->len = len;
    5d47:	48 c7 40 18 01 00 00 00 	movq   $0x1,0x18(%rax)
	sqe->buf_index = 0;
    5d4f:	48 c7 40 28 00 00 00 00 	movq   $0x0,0x28(%rax)
	sqe->user_data = (unsigned long) data;
    5d57:	48 89 70 20          	mov    %rsi,0x20(%rax)
	sqe->addr3 = 0;
    5d5b:	0f 11 40 30          	movups %xmm0,0x30(%rax)
      io_uring_submit(&ring);
    5d5f:	e8 4c c6 ff ff       	call   23b0 <io_uring_submit@plt>
  while (data->running == 1) {
    5d64:	83 7d 44 01          	cmpl   $0x1,0x44(%rbp)
    5d68:	0f 84 3a fe ff ff    	je     5ba8 <io_thread+0x2d8>
    5d6e:	48 8d 3d a3 24 00 00 	lea    0x24a3(%rip),%rdi        # 8218 <_IO_stdin_used+0x218>
    5d75:	e8 d6 c5 ff ff       	call   2350 <puts@plt>
}
    5d7a:	48 8b 84 24 48 05 00 00 	mov    0x548(%rsp),%rax
    5d82:	64 48 2b 04 25 28 00 00 00 	sub    %fs:0x28,%rax
    5d8b:	0f 85 18 02 00 00    	jne    5fa9 <io_thread+0x6d9>
    5d91:	48 81 c4 58 05 00 00 	add    $0x558,%rsp
    5d98:	31 c0                	xor    %eax,%eax
    5d9a:	5b                   	pop    %rbx
    5d9b:	5d                   	pop    %rbp
    5d9c:	41 5c                	pop    %r12
    5d9e:	41 5d                	pop    %r13
    5da0:	41 5e                	pop    %r14
    5da2:	41 5f                	pop    %r15
    5da4:	c3                   	ret
    5da5:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5da8:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	if (!__io_uring_peek_cqe(ring, cqe_ptr, NULL) && *cqe_ptr)
    5dad:	48 85 c0             	test   %rax,%rax
    5db0:	0f 84 6a fe ff ff    	je     5c20 <io_thread+0x350>
      if (cqe->user_data == 1) {
    5db6:	48 83 38 01          	cmpq   $0x1,(%rax)
    5dba:	0f 84 68 01 00 00    	je     5f28 <io_thread+0x658>
    5dc0:	48 8d 3d 18 24 00 00 	lea    0x2418(%rip),%rdi        # 81df <_IO_stdin_used+0x1df>
    5dc7:	e8 84 c5 ff ff       	call   2350 <puts@plt>
      struct Request *req = (struct Request *) cqe->user_data;
    5dcc:	48 8b 54 24 38       	mov    0x38(%rsp),%rdx
    5dd1:	4c 8b 22             	mov    (%rdx),%r12
      if (ret < 0)
    5dd4:	e9 8b fe ff ff       	jmp    5c64 <io_thread+0x394>
    5dd9:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5de0:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
    5de8:	8b 02                	mov    (%rdx),%eax
    5dea:	83 c0 01             	add    $0x1,%eax
    5ded:	89 02                	mov    %eax,(%rdx)
}
    5def:	e9 d8 fe ff ff       	jmp    5ccc <io_thread+0x3fc>
    5df4:	0f 1f 40 00          	nopl   0x0(%rax)
              if (!cqe->res) {
    5df8:	85 c0                	test   %eax,%eax
    5dfa:	75 74                	jne    5e70 <io_thread+0x5a0>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5dfc:	48 8b 0d 1d 52 00 00 	mov    0x521d(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5e03:	ba 0f 00 00 00       	mov    $0xf,%edx
    5e08:	be 01 00 00 00       	mov    $0x1,%esi
    5e0d:	48 8d 3d f4 23 00 00 	lea    0x23f4(%rip),%rdi        # 8208 <_IO_stdin_used+0x208>
    5e14:	e8 47 c7 ff ff       	call   2560 <fwrite@plt>
      io_uring_cqe_seen(&ring, cqe);
    5e19:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
    5e1e:	e9 a0 fe ff ff       	jmp    5cc3 <io_thread+0x3f3>
    5e23:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
              for (int i = 0; i < req->iovec_count; i++) {
    5e28:	41 8b 44 24 04       	mov    0x4(%r12),%eax
    5e2d:	45 31 ff             	xor    %r15d,%r15d
    5e30:	85 c0                	test   %eax,%eax
    5e32:	7e 20                	jle    5e54 <io_thread+0x584>
    5e34:	0f 1f 40 00          	nopl   0x0(%rax)
                  free(req->iov[i].iov_base);
    5e38:	4c 89 f8             	mov    %r15,%rax
              for (int i = 0; i < req->iovec_count; i++) {
    5e3b:	49 83 c7 01          	add    $0x1,%r15
                  free(req->iov[i].iov_base);
    5e3f:	48 c1 e0 04          	shl    $0x4,%rax
    5e43:	49 8b 7c 04 10       	mov    0x10(%r12,%rax,1),%rdi
    5e48:	e8 d3 c4 ff ff       	call   2320 <free@plt>
              for (int i = 0; i < req->iovec_count; i++) {
    5e4d:	45 39 7c 24 04       	cmp    %r15d,0x4(%r12)
    5e52:	7f e4                	jg     5e38 <io_thread+0x568>
              close(req->client_socket);
    5e54:	41 8b 7c 24 08       	mov    0x8(%r12),%edi
    5e59:	e8 92 c5 ff ff       	call   23f0 <close@plt>
              free(req);
    5e5e:	4c 89 e7             	mov    %r12,%rdi
    5e61:	e8 ba c4 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5e66:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5e6b:	e9 53 fe ff ff       	jmp    5cc3 <io_thread+0x3f3>
    for (int i = 0; i < dest_sz; i++) {
    5e70:	49 8b 54 24 10       	mov    0x10(%r12),%rdx
    5e75:	48 8b 44 24 28       	mov    0x28(%rsp),%rax
    5e7a:	48 8d b4 24 40 05 00 00 	lea    0x540(%rsp),%rsi
    5e82:	eb 11                	jmp    5e95 <io_thread+0x5c5>
    5e84:	0f 1f 40 00          	nopl   0x0(%rax)
    5e88:	48 83 c0 01          	add    $0x1,%rax
    5e8c:	48 83 c2 01          	add    $0x1,%rdx
    5e90:	48 39 c6             	cmp    %rax,%rsi
    5e93:	74 4b                	je     5ee0 <io_thread+0x610>
        dest[i] = src[i];
    5e95:	0f b6 0a             	movzbl (%rdx),%ecx
    5e98:	88 08                	mov    %cl,(%rax)
        if (src[i] == '\r' && src[i+1] == '\n') {
    5e9a:	80 f9 0d             	cmp    $0xd,%cl
    5e9d:	75 e9                	jne    5e88 <io_thread+0x5b8>
    5e9f:	80 7a 01 0a          	cmpb   $0xa,0x1(%rdx)
    5ea3:	75 e3                	jne    5e88 <io_thread+0x5b8>
            dest[i] = '\0';
    5ea5:	c6 00 00             	movb   $0x0,(%rax)
    handle_http_method(http_request, req->client_socket, ring);
    5ea8:	48 8b 7c 24 28       	mov    0x28(%rsp),%rdi
    5ead:	48 89 da             	mov    %rbx,%rdx
    5eb0:	41 8b 74 24 08       	mov    0x8(%r12),%esi
    5eb5:	e8 96 f7 ff ff       	call   5650 <handle_http_method>
              free(req->iov[0].iov_base);
    5eba:	49 8b 7c 24 10       	mov    0x10(%r12),%rdi
    5ebf:	e8 5c c4 ff ff       	call   2320 <free@plt>
              free(req);
    5ec4:	4c 89 e7             	mov    %r12,%rdi
    5ec7:	e8 54 c4 ff ff       	call   2320 <free@plt>
      io_uring_cqe_seen(&ring, cqe);
    5ecc:	48 8b 44 24 38       	mov    0x38(%rsp),%rax
              break;
    5ed1:	e9 ed fd ff ff       	jmp    5cc3 <io_thread+0x3f3>
    5ed6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    5ee0:	48 8b 0d 39 51 00 00 	mov    0x5139(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5ee7:	ba 12 00 00 00       	mov    $0x12,%edx
    5eec:	be 01 00 00 00       	mov    $0x1,%esi
    5ef1:	48 8d 3d 66 22 00 00 	lea    0x2266(%rip),%rdi        # 815e <_IO_stdin_used+0x15e>
    5ef8:	e8 63 c6 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    5efd:	bf 01 00 00 00       	mov    $0x1,%edi
    5f02:	e8 39 c6 ff ff       	call   2540 <exit@plt>
    5f07:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
		head = io_uring_smp_load_acquire(sq->khead);
    5f10:	e9 ec fb ff ff       	jmp    5b01 <io_thread+0x231>
    5f15:	0f 1f 00             	nopl   (%rax)
	*cqe_ptr = cqe;
    5f18:	48 89 44 24 38       	mov    %rax,0x38(%rsp)
	return err;
    5f1d:	e9 94 fe ff ff       	jmp    5db6 <io_thread+0x4e6>
    5f22:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
		io_uring_smp_store_release(cq->khead, *cq->khead + nr);
    5f28:	48 8b 94 24 c8 00 00 00 	mov    0xc8(%rsp),%rdx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    5f30:	48 8d 3d 94 22 00 00 	lea    0x2294(%rip),%rdi        # 81cb <_IO_stdin_used+0x1cb>
    5f37:	8b 02                	mov    (%rdx),%eax
    5f39:	83 c0 01             	add    $0x1,%eax
    5f3c:	89 02                	mov    %eax,(%rdx)
    5f3e:	e8 0d c4 ff ff       	call   2350 <puts@plt>
    5f43:	e9 26 fe ff ff       	jmp    5d6e <io_thread+0x49e>
          fprintf(stderr, "Async request failed: %s for event: %d\n",
    5f48:	f7 d8                	neg    %eax
    5f4a:	44 89 44 24 08       	mov    %r8d,0x8(%rsp)
    5f4f:	89 c7                	mov    %eax,%edi
    5f51:	e8 4a c6 ff ff       	call   25a0 <strerror@plt>
  return __fprintf_chk (__stream, __USE_FORTIFY_LEVEL - 1, __fmt,
    5f56:	44 8b 44 24 08       	mov    0x8(%rsp),%r8d
    5f5b:	be 01 00 00 00       	mov    $0x1,%esi
    5f60:	48 8b 3d b9 50 00 00 	mov    0x50b9(%rip),%rdi        # b020 <stderr@GLIBC_2.2.5>
    5f67:	48 89 c1             	mov    %rax,%rcx
    5f6a:	48 8d 15 6f 26 00 00 	lea    0x266f(%rip),%rdx        # 85e0 <_IO_stdin_used+0x5e0>
    5f71:	31 c0                	xor    %eax,%eax
    5f73:	e8 f8 c5 ff ff       	call   2570 <__fprintf_chk@plt>
          exit(1);
    5f78:	bf 01 00 00 00       	mov    $0x1,%edi
    5f7d:	e8 be c5 ff ff       	call   2540 <exit@plt>
    5f82:	48 8b 0d 97 50 00 00 	mov    0x5097(%rip),%rcx        # b020 <stderr@GLIBC_2.2.5>
    5f89:	ba 28 00 00 00       	mov    $0x28,%edx
    5f8e:	be 01 00 00 00       	mov    $0x1,%esi
    5f93:	48 8d 3d 16 26 00 00 	lea    0x2616(%rip),%rdi        # 85b0 <_IO_stdin_used+0x5b0>
    5f9a:	e8 c1 c5 ff ff       	call   2560 <fwrite@plt>
        exit(1);
    5f9f:	bf 01 00 00 00       	mov    $0x1,%edi
    5fa4:	e8 97 c5 ff ff       	call   2540 <exit@plt>
}
    5fa9:	e8 f2 c3 ff ff       	call   23a0 <__stack_chk_fail@plt>
    5fae:	66 90                	xchg   %ax,%ax

0000000000005fb0 <barriered_work_ingest>:
int barriered_work_ingest(struct BarrierTask *data) {
    5fb0:	f3 0f 1e fa          	endbr64
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    5fb4:	48 8b b7 28 01 00 00 	mov    0x128(%rdi),%rsi
    5fbb:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    5fc1:	85 c9                	test   %ecx,%ecx
    5fc3:	0f 8e ea 00 00 00    	jle    60b3 <barriered_work_ingest+0x103>
int barriered_work_ingest(struct BarrierTask *data) {
    5fc9:	41 56                	push   %r14
    5fcb:	41 55                	push   %r13
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5fcd:	45 31 ed             	xor    %r13d,%r13d
int barriered_work_ingest(struct BarrierTask *data) {
    5fd0:	41 54                	push   %r12
    5fd2:	49 89 fc             	mov    %rdi,%r12
    5fd5:	55                   	push   %rbp
    5fd6:	53                   	push   %rbx
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    5fd7:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    5fdb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    5fe0:	4a 8b 04 ef          	mov    (%rdi,%r13,8),%rax
    5fe4:	4e 8d 34 ed 00 00 00 00 	lea    0x0(,%r13,8),%r14
    5fec:	31 db                	xor    %ebx,%ebx
    5fee:	8b 10                	mov    (%rax),%edx
    5ff0:	85 d2                	test   %edx,%edx
    5ff2:	7e 26                	jle    601a <barriered_work_ingest+0x6a>
    5ff4:	48 8b 48 08          	mov    0x8(%rax),%rcx
      if (data->thread->buffers[b]->buffer[x].available == 1) {
    5ff8:	48 89 dd             	mov    %rbx,%rbp
    5ffb:	48 c1 e5 08          	shl    $0x8,%rbp
    5fff:	48 8d 04 29          	lea    (%rcx,%rbp,1),%rax
    6003:	83 b8 80 00 00 00 01 	cmpl   $0x1,0x80(%rax)
    600a:	74 24                	je     6030 <barriered_work_ingest+0x80>
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    600c:	48 83 c3 01          	add    $0x1,%rbx
    6010:	39 da                	cmp    %ebx,%edx
    6012:	7f e4                	jg     5ff8 <barriered_work_ingest+0x48>
  for (int b = 0 ; b < data->thread->buffers_count ; b++) {
    6014:	8b 8e bc 00 00 00    	mov    0xbc(%rsi),%ecx
    601a:	49 83 c5 01          	add    $0x1,%r13
    601e:	44 39 e9             	cmp    %r13d,%ecx
    6021:	7f bd                	jg     5fe0 <barriered_work_ingest+0x30>
}
    6023:	5b                   	pop    %rbx
    6024:	31 c0                	xor    %eax,%eax
    6026:	5d                   	pop    %rbp
    6027:	41 5c                	pop    %r12
    6029:	41 5d                	pop    %r13
    602b:	41 5e                	pop    %r14
    602d:	c3                   	ret
    602e:	66 90                	xchg   %ax,%ax
        data->ingest_count++;
    6030:	49 83 84 24 68 01 00 00 01 	addq   $0x1,0x168(%r12)
        clock_gettime(CLOCK_MONOTONIC_RAW, &data->thread->buffers[b]->buffer[x].snapshots[data->thread->buffers[b]->buffer[x].ingest_snapshot].end);
    6039:	48 63 b0 94 00 00 00 	movslq 0x94(%rax),%rsi
    6040:	bf 04 00 00 00       	mov    $0x4,%edi
    6045:	48 c1 e6 05          	shl    $0x5,%rsi
    6049:	48 03 b0 88 00 00 00 	add    0x88(%rax),%rsi
    6050:	48 83 c6 10          	add    $0x10,%rsi
    6054:	e8 17 c3 ff ff       	call   2370 <clock_gettime@plt>
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6059:	49 8b 84 24 28 01 00 00 	mov    0x128(%r12),%rax
    6061:	48 8b 40 50          	mov    0x50(%rax),%rax
    6065:	4a 8b 04 30          	mov    (%rax,%r14,1),%rax
    6069:	48 03 68 08          	add    0x8(%rax),%rbp
        data->thread->buffers[b]->buffer[x].available = 0;
    606d:	c7 85 80 00 00 00 00 00 00 00 	movl   $0x0,0x80(%rbp)
        data->thread->buffers[b]->buffer[x].ingest_snapshot = (data->thread->buffers[b]->buffer[x].ingest_snapshot + 1) % data->thread->buffers[b]->buffer[x].snapshot_limit;
    6077:	8b 85 94 00 00 00    	mov    0x94(%rbp),%eax
    607d:	83 c0 01             	add    $0x1,%eax
    6080:	99                   	cltd
    6081:	f7 bd 90 00 00 00    	idivl  0x90(%rbp)
    6087:	89 95 94 00 00 00    	mov    %edx,0x94(%rbp)
        asm volatile ("sfence" ::: "memory");
    608d:	0f ae f8             	sfence
    for (int x = 0 ; x < data->thread->buffers[b]->count ; x++) {
    6090:	49 8b b4 24 28 01 00 00 	mov    0x128(%r12),%rsi
    6098:	48 83 c3 01          	add    $0x1,%rbx
    609c:	48 8b 7e 50          	mov    0x50(%rsi),%rdi
    60a0:	4a 8b 04 37          	mov    (%rdi,%r14,1),%rax
    60a4:	8b 10                	mov    (%rax),%edx
    60a6:	39 da                	cmp    %ebx,%edx
    60a8:	0f 8f 46 ff ff ff    	jg     5ff4 <barriered_work_ingest+0x44>
    60ae:	e9 61 ff ff ff       	jmp    6014 <barriered_work_ingest+0x64>
}
    60b3:	31 c0                	xor    %eax,%eax
    60b5:	c3                   	ret
    60b6:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

00000000000060c0 <barriered_thread>:
void* barriered_thread(void *arg) {
    60c0:	f3 0f 1e fa          	endbr64
    60c4:	41 56                	push   %r14
    60c6:	41 55                	push   %r13
    60c8:	41 54                	push   %r12
  int t = 0;
    60ca:	45 31 e4             	xor    %r12d,%r12d
void* barriered_thread(void *arg) {
    60cd:	55                   	push   %rbp
  int waiting = 0;
    60ce:	31 ed                	xor    %ebp,%ebp
void* barriered_thread(void *arg) {
    60d0:	53                   	push   %rbx
    60d1:	48 89 fb             	mov    %rdi,%rbx
  while (data->running == 1) {
    60d4:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    60d8:	0f 85 74 02 00 00    	jne    6352 <barriered_thread+0x292>
    if (t >= data->task_count) {
    60de:	8b 43 40             	mov    0x40(%rbx),%eax
    60e1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    60e8:	41 39 c4             	cmp    %eax,%r12d
    60eb:	0f 8d 6f 01 00 00    	jge    6260 <barriered_thread+0x1a0>
    60f1:	49 63 fc             	movslq %r12d,%rdi
    60f4:	48 c1 e7 09          	shl    $0x9,%rdi
    60f8:	49 89 fd             	mov    %rdi,%r13
    60fb:	eb 32                	jmp    612f <barriered_thread+0x6f>
    60fd:	0f 1f 00             	nopl   (%rax)
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    6100:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6104:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6108:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    610c:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6110:	4c 01 ef             	add    %r13,%rdi
    6113:	e8 98 fe ff ff       	call   5fb0 <barriered_work_ingest>
    for (; t < data->task_count; t++) {
    6118:	8b 43 40             	mov    0x40(%rbx),%eax
    611b:	41 83 c4 01          	add    $0x1,%r12d
    611f:	49 81 c5 00 02 00 00 	add    $0x200,%r13
    6126:	44 39 e0             	cmp    %r12d,%eax
    6129:	0f 8e 19 02 00 00    	jle    6348 <barriered_thread+0x288>
      if (data->tasks[t].available == 1) {
    612f:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6133:	4a 8d 34 2a          	lea    (%rdx,%r13,1),%rsi
    6137:	83 be 44 01 00 00 01 	cmpl   $0x1,0x144(%rsi)
    613e:	75 c0                	jne    6100 <barriered_thread+0x40>
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6140:	44 8b 43 28          	mov    0x28(%rbx),%r8d
          previous = t - 1;
    6144:	83 e8 01             	sub    $0x1,%eax
    6147:	41 8d 4c 24 ff       	lea    -0x1(%r12),%ecx
    614c:	45 85 e4             	test   %r12d,%r12d
    614f:	0f 4f c1             	cmovg  %ecx,%eax
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    6152:	45 85 c0             	test   %r8d,%r8d
    6155:	0f 8e 2d 01 00 00    	jle    6288 <barriered_thread+0x1c8>
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    615b:	48 63 c8             	movslq %eax,%rcx
    615e:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6162:	49 63 d0             	movslq %r8d,%rdx
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    6165:	8b be 00 01 00 00    	mov    0x100(%rsi),%edi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    616b:	44 8b 8e 80 00 00 00 	mov    0x80(%rsi),%r9d
    6172:	48 c1 e1 09          	shl    $0x9,%rcx
        int prearrive = 0; 
    6176:	45 31 d2             	xor    %r10d,%r10d
        int arrived = 0; 
    6179:	45 31 f6             	xor    %r14d,%r14d
    617c:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
          if (data->threads[thread]->tasks[previous].arrived == data->tasks[t].arrived) {
    6180:	48 8b 10             	mov    (%rax),%rdx
    6183:	4c 8b 5a 38          	mov    0x38(%rdx),%r11
    6187:	49 01 cb             	add    %rcx,%r11
    618a:	4c 89 da             	mov    %r11,%rdx
    618d:	45 3b 8b 80 00 00 00 	cmp    0x80(%r11),%r9d
    6194:	75 04                	jne    619a <barriered_thread+0xda>
            arrived++;
    6196:	41 83 c6 01          	add    $0x1,%r14d
          if (data->threads[thread]->tasks[previous].prearrive == data->tasks[t].prearrive) {
    619a:	3b ba 00 01 00 00    	cmp    0x100(%rdx),%edi
    61a0:	75 04                	jne    61a6 <barriered_thread+0xe6>
            prearrive++;
    61a2:	41 83 c2 01          	add    $0x1,%r10d
        for (int thread = 0 ; thread < data->thread_count; thread++) {
    61a6:	48 83 c0 08          	add    $0x8,%rax
    61aa:	48 39 c6             	cmp    %rax,%rsi
    61ad:	75 d1                	jne    6180 <barriered_thread+0xc0>
        if (prearrive == 0 || prearrive == data->thread_count) {
    61af:	45 85 d2             	test   %r10d,%r10d
    61b2:	0f 84 c0 00 00 00    	je     6278 <barriered_thread+0x1b8>
    61b8:	45 39 d0             	cmp    %r10d,%r8d
    61bb:	0f 84 b7 00 00 00    	je     6278 <barriered_thread+0x1b8>
        if (arrived == 0 || arrived == data->thread_count) {
    61c1:	45 85 f6             	test   %r14d,%r14d
    61c4:	74 0a                	je     61d0 <barriered_thread+0x110>
    61c6:	44 39 73 28          	cmp    %r14d,0x28(%rbx)
    61ca:	0f 85 ae 01 00 00    	jne    637e <barriered_thread+0x2be>
    61d0:	48 8b 53 38          	mov    0x38(%rbx),%rdx
          data->tasks[t].prearrive++;
    61d4:	4c 01 ea             	add    %r13,%rdx
    61d7:	83 82 00 01 00 00 01 	addl   $0x1,0x100(%rdx)
          if (t == 0 && data->timestamp_count < data->timestamp_limit) {
    61de:	45 85 e4             	test   %r12d,%r12d
    61e1:	75 14                	jne    61f7 <barriered_thread+0x137>
    61e3:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    61ea:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    61f1:	0f 8c 69 01 00 00    	jl     6360 <barriered_thread+0x2a0>
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    61f7:	48 63 4b 04          	movslq 0x4(%rbx),%rcx
    61fb:	48 8b 43 18          	mov    0x18(%rbx),%rax
          data->tasks[t].available = 0;
    61ff:	c7 82 44 01 00 00 00 00 00 00 	movl   $0x0,0x144(%rdx)
          data->tasks[t].run(&data->threads[data->thread_index]->tasks[t]);
    6209:	48 8b 04 c8          	mov    (%rax,%rcx,8),%rax
    620d:	48 8b 78 38          	mov    0x38(%rax),%rdi
    6211:	4c 01 ef             	add    %r13,%rdi
    6214:	ff 92 18 01 00 00    	call   *0x118(%rdx)
          data->tasks[t].arrived++;
    621a:	48 8b 43 38          	mov    0x38(%rbx),%rax
    621e:	4c 01 e8             	add    %r13,%rax
    6221:	83 80 80 00 00 00 01 	addl   $0x1,0x80(%rax)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6228:	8b 43 40             	mov    0x40(%rbx),%eax
          data->iteration_count++;
    622b:	48 83 43 78 01       	addq   $0x1,0x78(%rbx)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    6230:	83 e8 01             	sub    $0x1,%eax
    6233:	44 39 e0             	cmp    %r12d,%eax
    6236:	0f 84 a4 00 00 00    	je     62e0 <barriered_thread+0x220>
          asm volatile ("sfence" ::: "memory");
    623c:	0f ae f8             	sfence
          if (waiting == 0) {
    623f:	85 ed                	test   %ebp,%ebp
    6241:	0f 84 d1 00 00 00    	je     6318 <barriered_thread+0x258>
        int arrived = 0; 
    6247:	bd 01 00 00 00       	mov    $0x1,%ebp
    624c:	e9 c7 fe ff ff       	jmp    6118 <barriered_thread+0x58>
  while (data->running == 1) {
    6251:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    6255:	0f 85 f7 00 00 00    	jne    6352 <barriered_thread+0x292>
    625b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
      data->cycles++;
    6260:	48 83 83 a8 00 00 00 01 	addq   $0x1,0xa8(%rbx)
    for (; t < data->task_count; t++) {
    6268:	85 c0                	test   %eax,%eax
    626a:	7e e5                	jle    6251 <barriered_thread+0x191>
    626c:	45 31 e4             	xor    %r12d,%r12d
    626f:	e9 7d fe ff ff       	jmp    60f1 <barriered_thread+0x31>
    6274:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6278:	83 fd 01             	cmp    $0x1,%ebp
    627b:	74 1b                	je     6298 <barriered_thread+0x1d8>
        int arrived = 0; 
    627d:	31 ed                	xor    %ebp,%ebp
    627f:	e9 3d ff ff ff       	jmp    61c1 <barriered_thread+0x101>
    6284:	0f 1f 40 00          	nopl   0x0(%rax)
          if (waiting == 1) {
    6288:	83 fd 01             	cmp    $0x1,%ebp
    628b:	0f 85 43 ff ff ff    	jne    61d4 <barriered_thread+0x114>
        int arrived = 0; 
    6291:	45 31 f6             	xor    %r14d,%r14d
    6294:	0f 1f 40 00          	nopl   0x0(%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    6298:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    629f:	bf 04 00 00 00       	mov    $0x4,%edi
        int arrived = 0; 
    62a4:	31 ed                	xor    %ebp,%ebp
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_end);
    62a6:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    62aa:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    62b1:	48 8d 74 d0 10       	lea    0x10(%rax,%rdx,8),%rsi
    62b6:	e8 b5 c0 ff ff       	call   2370 <clock_gettime@plt>
            data->task_timestamp_count = (data->task_timestamp_count + 1) % data->task_timestamp_limit;
    62bb:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
    62c2:	48 83 c0 01          	add    $0x1,%rax
    62c6:	48 99                	cqto
    62c8:	48 f7 bb a0 00 00 00 	idivq  0xa0(%rbx)
    62cf:	48 89 93 98 00 00 00 	mov    %rdx,0x98(%rbx)
            waiting = 0; 
    62d6:	e9 e6 fe ff ff       	jmp    61c1 <barriered_thread+0x101>
    62db:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
          if (t == data->task_count - 1 && data->timestamp_count < data->timestamp_limit) {
    62e0:	48 8b b3 80 00 00 00 	mov    0x80(%rbx),%rsi
    62e7:	48 3b b3 88 00 00 00 	cmp    0x88(%rbx),%rsi
    62ee:	0f 8d 48 ff ff ff    	jge    623c <barriered_thread+0x17c>
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->end[data->timestamp_count]);
    62f4:	48 c1 e6 04          	shl    $0x4,%rsi
    62f8:	bf 04 00 00 00       	mov    $0x4,%edi
    62fd:	48 03 73 70          	add    0x70(%rbx),%rsi
    6301:	e8 6a c0 ff ff       	call   2370 <clock_gettime@plt>
            data->timestamp_count = data->timestamp_count + 1;
    6306:	48 83 83 80 00 00 00 01 	addq   $0x1,0x80(%rbx)
    630e:	e9 29 ff ff ff       	jmp    623c <barriered_thread+0x17c>
    6313:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
            data->task_snapshot[data->task_timestamp_count].task = t;
    6318:	48 8b 83 98 00 00 00 	mov    0x98(%rbx),%rax
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    631f:	bf 04 00 00 00       	mov    $0x4,%edi
            data->task_snapshot[data->task_timestamp_count].task = t;
    6324:	48 8d 14 80          	lea    (%rax,%rax,4),%rdx
    6328:	48 8b 83 90 00 00 00 	mov    0x90(%rbx),%rax
    632f:	48 8d 34 d0          	lea    (%rax,%rdx,8),%rsi
    6333:	44 89 66 20          	mov    %r12d,0x20(%rsi)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->task_snapshot[data->task_timestamp_count].task_start);
    6337:	e8 34 c0 ff ff       	call   2370 <clock_gettime@plt>
            waiting = 1;
    633c:	e9 06 ff ff ff       	jmp    6247 <barriered_thread+0x187>
    6341:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  while (data->running == 1) {
    6348:	83 7b 44 01          	cmpl   $0x1,0x44(%rbx)
    634c:	0f 84 96 fd ff ff    	je     60e8 <barriered_thread+0x28>
}
    6352:	5b                   	pop    %rbx
    6353:	31 c0                	xor    %eax,%eax
    6355:	5d                   	pop    %rbp
    6356:	41 5c                	pop    %r12
    6358:	41 5d                	pop    %r13
    635a:	41 5e                	pop    %r14
    635c:	c3                   	ret
    635d:	0f 1f 00             	nopl   (%rax)
            clock_gettime(CLOCK_MONOTONIC_RAW, &data->start[data->timestamp_count]);
    6360:	48 c1 e6 04          	shl    $0x4,%rsi
    6364:	bf 04 00 00 00       	mov    $0x4,%edi
    6369:	48 03 73 68          	add    0x68(%rbx),%rsi
    636d:	e8 fe bf ff ff       	call   2370 <clock_gettime@plt>
          data->tasks[t].available = 0;
    6372:	48 8b 53 38          	mov    0x38(%rbx),%rdx
    6376:	4c 01 ea             	add    %r13,%rdx
    6379:	e9 79 fe ff ff       	jmp    61f7 <barriered_thread+0x137>
          barriered_work_ingest(&data->threads[data->thread_index]->tasks[t]);
    637e:	48 63 53 04          	movslq 0x4(%rbx),%rdx
    6382:	48 8b 43 18          	mov    0x18(%rbx),%rax
    6386:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    638a:	48 8b 78 38          	mov    0x38(%rax),%rdi
    638e:	4c 01 ef             	add    %r13,%rdi
    6391:	e8 1a fc ff ff       	call   5fb0 <barriered_work_ingest>
          break;
    6396:	e9 39 fd ff ff       	jmp    60d4 <barriered_thread+0x14>
    639b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

00000000000063a0 <receive>:
int receive(struct BarrierTask *data) {
    63a0:	f3 0f 1e fa          	endbr64
    63a4:	41 57                	push   %r15
    63a6:	41 56                	push   %r14
    63a8:	41 55                	push   %r13
    63aa:	41 54                	push   %r12
    63ac:	55                   	push   %rbp
    63ad:	53                   	push   %rbx
    63ae:	48 83 ec 08          	sub    $0x8,%rsp
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    63b2:	44 8b b7 40 01 00 00 	mov    0x140(%rdi),%r14d
    63b9:	45 85 f6             	test   %r14d,%r14d
    63bc:	0f 8e 37 01 00 00    	jle    64f9 <receive+0x159>
    if (n == data->thread->real_thread_index) { continue; }
    63c2:	4c 8b bf 28 01 00 00 	mov    0x128(%rdi),%r15
    63c9:	48 89 f9             	mov    %rdi,%rcx
    63cc:	45 31 e4             	xor    %r12d,%r12d
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    63cf:	31 db                	xor    %ebx,%ebx
    if (n == data->thread->real_thread_index) { continue; }
    63d1:	49 63 6f 08          	movslq 0x8(%r15),%rbp
    63d5:	49 89 ed             	mov    %rbp,%r13
    63d8:	0f 1f 84 00 00 00 00 00 	nopl   0x0(%rax,%rax,1)
    63e0:	41 39 dd             	cmp    %ebx,%r13d
    63e3:	0f 84 00 01 00 00    	je     64e9 <receive+0x149>
    struct Data *me = data->mailboxes[n].lower;
    63e9:	48 8b 81 70 01 00 00 	mov    0x170(%rcx),%rax
    63f0:	4a 8b 34 20          	mov    (%rax,%r12,1),%rsi
    if (me->available_reading == 1) {
    63f4:	8b 86 00 02 00 00    	mov    0x200(%rsi),%eax
    63fa:	83 f8 01             	cmp    $0x1,%eax
    63fd:	74 11                	je     6410 <receive+0x70>
    else if (me->kind == MAILBOX_FOREIGN && me->available_reading == 0) {
    63ff:	83 be 18 03 00 00 02 	cmpl   $0x2,0x318(%rsi)
    6406:	75 08                	jne    6410 <receive+0x70>
    6408:	85 c0                	test   %eax,%eax
    640a:	0f 84 d9 00 00 00    	je     64e9 <receive+0x149>
    for (int x = 0 ; x < me->messages_count ; x++) {
    6410:	48 8b be 80 00 00 00 	mov    0x80(%rsi),%rdi
    6417:	48 85 ff             	test   %rdi,%rdi
    641a:	0f 8e a0 00 00 00    	jle    64c0 <receive+0x120>
      data->sends++;
    6420:	48 8b 91 78 01 00 00 	mov    0x178(%rcx),%rdx
    6427:	4c 8b 06             	mov    (%rsi),%r8
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    642a:	4c 63 59 04          	movslq 0x4(%rcx),%r11
    642e:	49 89 d1             	mov    %rdx,%r9
    6431:	48 8d 42 01          	lea    0x1(%rdx),%rax
    6435:	49 f7 d9             	neg    %r9
    6438:	48 01 c7             	add    %rax,%rdi
    643b:	4f 8d 14 c8          	lea    (%r8,%r9,8),%r10
      data->n++;
    643f:	4c 8b 89 08 01 00 00 	mov    0x108(%rcx),%r9
      me->received++;
    6446:	4c 8b 86 10 03 00 00 	mov    0x310(%rsi),%r8
      data->n++;
    644d:	49 29 d1             	sub    %rdx,%r9
      me->received++;
    6450:	49 29 d0             	sub    %rdx,%r8
    6453:	eb 0c                	jmp    6461 <receive+0xc1>
    6455:	0f 1f 00             	nopl   (%rax)
    for (int x = 0 ; x < me->messages_count ; x++) {
    6458:	48 83 c0 01          	add    $0x1,%rax
    645c:	48 39 c7             	cmp    %rax,%rdi
    645f:	74 5f                	je     64c0 <receive+0x120>
      data->n++;
    6461:	49 8d 14 01          	lea    (%r9,%rax,1),%rdx
      data->sends++;
    6465:	48 89 81 78 01 00 00 	mov    %rax,0x178(%rcx)
      data->n++;
    646c:	48 89 91 08 01 00 00 	mov    %rdx,0x108(%rcx)
      me->received++;
    6473:	49 8d 14 00          	lea    (%r8,%rax,1),%rdx
    6477:	48 89 96 10 03 00 00 	mov    %rdx,0x310(%rsi)
      if (me->messages[x]->group == data->group) {
    647e:	49 8b 54 c2 f8       	mov    -0x8(%r10,%rax,8),%rdx
      if (me->messages[x]->task_index == data->task_index && me->messages[x]->thread_index == data->thread->real_thread_index) {
    6483:	4c 39 5a 10          	cmp    %r11,0x10(%rdx)
    6487:	75 cf                	jne    6458 <receive+0xb8>
    6489:	48 39 6a 08          	cmp    %rbp,0x8(%rdx)
    648d:	75 c9                	jne    6458 <receive+0xb8>
        printf("Received message from self %b %b\n", me->messages[x]->task_index == data->task_index, me->messages[x]->thread_index == data->thread->thread_index);
    648f:	49 63 47 04          	movslq 0x4(%r15),%rax
    6493:	31 c9                	xor    %ecx,%ecx
  return __printf_chk (__USE_FORTIFY_LEVEL - 1, __fmt, __va_arg_pack ());
    6495:	bf 01 00 00 00       	mov    $0x1,%edi
    649a:	ba 01 00 00 00       	mov    $0x1,%edx
    649f:	48 8d 35 62 21 00 00 	lea    0x2162(%rip),%rsi        # 8608 <_IO_stdin_used+0x608>
    64a6:	48 39 e8             	cmp    %rbp,%rax
    64a9:	0f 94 c1             	sete   %cl
    64ac:	31 c0                	xor    %eax,%eax
    64ae:	e8 2d c0 ff ff       	call   24e0 <__printf_chk@plt>
        exit(1);
    64b3:	bf 01 00 00 00       	mov    $0x1,%edi
    64b8:	e8 83 c0 ff ff       	call   2540 <exit@plt>
    64bd:	0f 1f 00             	nopl   (%rax)
    me->messages_count = 0;
    64c0:	48 c7 86 80 00 00 00 00 00 00 00 	movq   $0x0,0x80(%rsi)
      me->available_reading = 0;
    64cb:	c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi)
      me->finished_reading = 1;
    64d5:	c7 86 00 03 00 00 01 00 00 00 	movl   $0x1,0x300(%rsi)
      me->available_sending = 1;
    64df:	c7 86 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%rsi)
  for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    64e9:	83 c3 01             	add    $0x1,%ebx
    64ec:	49 83 c4 38          	add    $0x38,%r12
    64f0:	44 39 f3             	cmp    %r14d,%ebx
    64f3:	0f 85 e7 fe ff ff    	jne    63e0 <receive+0x40>
  asm volatile ("sfence" ::: "memory");
    64f9:	0f ae f8             	sfence
}
    64fc:	48 83 c4 08          	add    $0x8,%rsp
    6500:	31 c0                	xor    %eax,%eax
    6502:	5b                   	pop    %rbx
    6503:	5d                   	pop    %rbp
    6504:	41 5c                	pop    %r12
    6506:	41 5d                	pop    %r13
    6508:	41 5e                	pop    %r14
    650a:	41 5f                	pop    %r15
    650c:	c3                   	ret
    650d:	0f 1f 00             	nopl   (%rax)

0000000000006510 <sendm>:
int sendm(struct BarrierTask *data) {
    6510:	f3 0f 1e fa          	endbr64
    6514:	41 57                	push   %r15
    6516:	41 56                	push   %r14
    6518:	41 55                	push   %r13
    651a:	41 54                	push   %r12
    651c:	55                   	push   %rbp
    651d:	53                   	push   %rbx
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    651e:	44 8b a7 40 01 00 00 	mov    0x140(%rdi),%r12d
    6525:	45 85 e4             	test   %r12d,%r12d
    6528:	0f 8e ae 00 00 00    	jle    65dc <sendm+0xcc>
        if (n == data->thread->real_thread_index) { continue; }
    652e:	48 8b 87 28 01 00 00 	mov    0x128(%rdi),%rax
    6535:	48 89 fe             	mov    %rdi,%rsi
    6538:	31 d2                	xor    %edx,%edx
    653a:	44 8b 68 08          	mov    0x8(%rax),%r13d
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    653e:	31 c0                	xor    %eax,%eax
    6540:	eb 38                	jmp    657a <sendm+0x6a>
    6542:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)
          data->mailboxes[n].higher = them;
    6548:	4c 89 47 08          	mov    %r8,0x8(%rdi)
          them = data->mailboxes[n].pending;
    654c:	4c 89 c1             	mov    %r8,%rcx
          data->mailboxes[n].pending = NULL;
    654f:	48 c7 47 10 00 00 00 00 	movq   $0x0,0x10(%rdi)
        if (them->messages_count > 0) {
    6557:	49 8b b8 80 00 00 00 	mov    0x80(%r8),%rdi
          them->available_sending = 1;
    655e:	41 c7 80 00 01 00 00 01 00 00 00 	movl   $0x1,0x100(%r8)
        if (them->messages_count > 0) {
    6569:	48 85 ff             	test   %rdi,%rdi
    656c:	7e 4f                	jle    65bd <sendm+0xad>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    656e:	83 c0 01             	add    $0x1,%eax
    6571:	48 83 c2 38          	add    $0x38,%rdx
    6575:	44 39 e0             	cmp    %r12d,%eax
    6578:	74 62                	je     65dc <sendm+0xcc>
        if (n == data->thread->real_thread_index) { continue; }
    657a:	41 39 c5             	cmp    %eax,%r13d
    657d:	74 ef                	je     656e <sendm+0x5e>
        struct Data *them = data->mailboxes[n].higher;
    657f:	48 8b be 70 01 00 00 	mov    0x170(%rsi),%rdi
    6586:	48 01 d7             	add    %rdx,%rdi
        if (data->mailboxes[n].pending != NULL) {
    6589:	4c 8b 47 10          	mov    0x10(%rdi),%r8
        struct Data *them = data->mailboxes[n].higher;
    658d:	48 8b 4f 08          	mov    0x8(%rdi),%rcx
        if (data->mailboxes[n].pending != NULL) {
    6591:	4d 85 c0             	test   %r8,%r8
    6594:	75 b2                	jne    6548 <sendm+0x38>
        if (them->messages_count > 0) {
    6596:	48 8b b9 80 00 00 00 	mov    0x80(%rcx),%rdi
    659d:	48 85 ff             	test   %rdi,%rdi
    65a0:	7f cc                	jg     656e <sendm+0x5e>
        if (them->available_sending == 1) {
    65a2:	44 8b 81 00 01 00 00 	mov    0x100(%rcx),%r8d
    65a9:	41 83 f8 01          	cmp    $0x1,%r8d
    65ad:	74 0e                	je     65bd <sendm+0xad>
        else if (them->kind == MAILBOX_FOREIGN && them->available_sending == 0) {
    65af:	83 b9 18 03 00 00 02 	cmpl   $0x2,0x318(%rcx)
    65b6:	75 05                	jne    65bd <sendm+0xad>
    65b8:	45 85 c0             	test   %r8d,%r8d
    65bb:	74 b1                	je     656e <sendm+0x5e>
        if (data->sending == 1) {
    65bd:	83 be 80 01 00 00 01 	cmpl   $0x1,0x180(%rsi)
    65c4:	74 2a                	je     65f0 <sendm+0xe0>
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    65c6:	83 c0 01             	add    $0x1,%eax
    65c9:	48 83 c2 38          	add    $0x38,%rdx
          them->available_receiving = 1;
    65cd:	c7 81 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rcx)
      for (int n = 0 ; n < data->mailbox_thread_count; n++) {
    65d7:	44 39 e0             	cmp    %r12d,%eax
    65da:	75 9e                	jne    657a <sendm+0x6a>
      asm volatile ("sfence" ::: "memory");
    65dc:	0f ae f8             	sfence
}
    65df:	31 c0                	xor    %eax,%eax
    65e1:	5b                   	pop    %rbx
    65e2:	5d                   	pop    %rbp
    65e3:	41 5c                	pop    %r12
    65e5:	41 5d                	pop    %r13
    65e7:	41 5e                	pop    %r14
    65e9:	41 5f                	pop    %r15
    65eb:	c3                   	ret
    65ec:	0f 1f 40 00          	nopl   0x0(%rax)
          for (; them->messages_count < min;) {
    65f0:	48 63 99 88 00 00 00 	movslq 0x88(%rcx),%rbx
    65f7:	48 39 df             	cmp    %rbx,%rdi
    65fa:	0f 8d b2 00 00 00    	jge    66b2 <sendm+0x1a2>
    6600:	49 89 db             	mov    %rbx,%r11
    6603:	4c 8b be 08 01 00 00 	mov    0x108(%rsi),%r15
    660a:	4c 8b b1 08 03 00 00 	mov    0x308(%rcx),%r14
    6611:	49 29 fb             	sub    %rdi,%r11
            them->messages[them->messages_count++] = data->message; 
    6614:	4c 8b 11             	mov    (%rcx),%r10
    6617:	4d 8d 43 ff          	lea    -0x1(%r11),%r8
    661b:	4c 89 7c 24 e8       	mov    %r15,-0x18(%rsp)
    6620:	4c 89 74 24 f0       	mov    %r14,-0x10(%rsp)
    6625:	49 83 f8 02          	cmp    $0x2,%r8
    6629:	0f 86 11 01 00 00    	jbe    6740 <sendm+0x230>
    662f:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    6637:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    663f:	4f 8d 34 0a          	lea    (%r10,%r9,1),%r14
    6643:	4c 8d be 88 01 00 00 	lea    0x188(%rsi),%r15
    664a:	4b 8d 2c 02          	lea    (%r10,%r8,1),%rbp
    664e:	4d 39 f7             	cmp    %r14,%r15
    6651:	73 75                	jae    66c8 <sendm+0x1b8>
    6653:	4c 8d b6 90 01 00 00 	lea    0x190(%rsi),%r14
    665a:	4c 39 f5             	cmp    %r14,%rbp
    665d:	73 69                	jae    66c8 <sendm+0x1b8>
    665f:	4d 01 d0             	add    %r10,%r8
    6662:	4b 8d 3c 0a          	lea    (%r10,%r9,1),%rdi
    6666:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6670:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
          for (; them->messages_count < min;) {
    6677:	49 83 c0 08          	add    $0x8,%r8
            them->messages[them->messages_count++] = data->message; 
    667b:	4d 89 48 f8          	mov    %r9,-0x8(%r8)
          for (; them->messages_count < min;) {
    667f:	4c 39 c7             	cmp    %r8,%rdi
    6682:	75 ec                	jne    6670 <sendm+0x160>
    6684:	0f 1f 40 00          	nopl   0x0(%rax)
    6688:	48 8b 7c 24 e8       	mov    -0x18(%rsp),%rdi
    668d:	4c 01 df             	add    %r11,%rdi
    6690:	48 89 be 08 01 00 00 	mov    %rdi,0x108(%rsi)
    6697:	48 8b 7c 24 f0       	mov    -0x10(%rsp),%rdi
    669c:	48 89 99 80 00 00 00 	mov    %rbx,0x80(%rcx)
    66a3:	4c 01 df             	add    %r11,%rdi
    66a6:	48 89 b9 08 03 00 00 	mov    %rdi,0x308(%rcx)
    66ad:	4d 89 4c da f8       	mov    %r9,-0x8(%r10,%rbx,8)
          them->available_sending = 0;
    66b2:	c7 81 00 01 00 00 00 00 00 00 	movl   $0x0,0x100(%rcx)
    66bc:	e9 05 ff ff ff       	jmp    65c6 <sendm+0xb6>
    66c1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    66c8:	4d 89 de             	mov    %r11,%r14
    66cb:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
    66d2:	49 89 e8             	mov    %rbp,%r8
    66d5:	49 d1 ee             	shr    %r14
    66d8:	49 c1 e6 04          	shl    $0x4,%r14
    66dc:	66 49 0f 6e c1       	movq   %r9,%xmm0
    66e1:	4e 8d 7c 35 00       	lea    0x0(%rbp,%r14,1),%r15
    66e6:	41 83 e6 10          	and    $0x10,%r14d
    66ea:	66 0f 6c c0          	punpcklqdq %xmm0,%xmm0
    66ee:	74 10                	je     6700 <sendm+0x1f0>
            them->messages[them->messages_count++] = data->message; 
    66f0:	49 83 c0 10          	add    $0x10,%r8
    66f4:	0f 11 45 00          	movups %xmm0,0x0(%rbp)
          for (; them->messages_count < min;) {
    66f8:	4d 39 f8             	cmp    %r15,%r8
    66fb:	74 15                	je     6712 <sendm+0x202>
    66fd:	0f 1f 00             	nopl   (%rax)
            them->messages[them->messages_count++] = data->message; 
    6700:	41 0f 11 00          	movups %xmm0,(%r8)
    6704:	49 83 c0 20          	add    $0x20,%r8
    6708:	41 0f 11 40 f0       	movups %xmm0,-0x10(%r8)
          for (; them->messages_count < min;) {
    670d:	4d 39 f8             	cmp    %r15,%r8
    6710:	75 ee                	jne    6700 <sendm+0x1f0>
    6712:	4d 89 d8             	mov    %r11,%r8
    6715:	49 83 e0 fe          	and    $0xfffffffffffffffe,%r8
    6719:	4c 01 c7             	add    %r8,%rdi
    671c:	41 f6 c3 01          	test   $0x1,%r11b
    6720:	0f 84 62 ff ff ff    	je     6688 <sendm+0x178>
            them->messages[them->messages_count++] = data->message; 
    6726:	4c 8b 8e 88 01 00 00 	mov    0x188(%rsi),%r9
    672d:	4d 89 0c fa          	mov    %r9,(%r10,%rdi,8)
          for (; them->messages_count < min;) {
    6731:	e9 52 ff ff ff       	jmp    6688 <sendm+0x178>
    6736:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6740:	4c 8d 04 fd 00 00 00 00 	lea    0x0(,%rdi,8),%r8
    6748:	4c 8d 0c dd 00 00 00 00 	lea    0x0(,%rbx,8),%r9
    6750:	e9 0a ff ff ff       	jmp    665f <sendm+0x14f>
    6755:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)

0000000000006760 <barriered_work>:
int barriered_work(struct BarrierTask *data) {
    6760:	f3 0f 1e fa          	endbr64
    6764:	41 57                	push   %r15
    6766:	41 56                	push   %r14
    6768:	41 55                	push   %r13
    676a:	41 54                	push   %r12
    676c:	55                   	push   %rbp
    676d:	53                   	push   %rbx
      receive(data);
    676e:	48 89 fb             	mov    %rdi,%rbx
int barriered_work(struct BarrierTask *data) {
    6771:	48 83 ec 38          	sub    $0x38,%rsp
        int t = data->task_index;
    6775:	48 63 6f 04          	movslq 0x4(%rdi),%rbp
int barriered_work(struct BarrierTask *data) {
    6779:	48 89 3c 24          	mov    %rdi,(%rsp)
  if (data->thread_index == data->task_index) {
    677d:	39 af 30 01 00 00    	cmp    %ebp,0x130(%rdi)
    6783:	74 53                	je     67d8 <barriered_work+0x78>
    receive(data);
    6785:	e8 16 fc ff ff       	call   63a0 <receive>
    while (data->scheduled == 1) {
    678a:	83 bb 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbx)
    6791:	75 21                	jne    67b4 <barriered_work+0x54>
    6793:	48 8b 04 24          	mov    (%rsp),%rax
    6797:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
      data->n++;
    67a0:	48 83 80 08 01 00 00 01 	addq   $0x1,0x108(%rax)
      asm volatile ("sfence" ::: "memory");
    67a8:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    67ab:	83 b8 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rax)
    67b2:	74 ec                	je     67a0 <barriered_work+0x40>
    sendm(data);
    67b4:	48 8b 3c 24          	mov    (%rsp),%rdi
    67b8:	e8 53 fd ff ff       	call   6510 <sendm>
  asm volatile ("sfence" ::: "memory");
    67bd:	0f ae f8             	sfence
}
    67c0:	48 83 c4 38          	add    $0x38,%rsp
    67c4:	31 c0                	xor    %eax,%eax
    67c6:	5b                   	pop    %rbx
    67c7:	5d                   	pop    %rbp
    67c8:	41 5c                	pop    %r12
    67ca:	41 5d                	pop    %r13
    67cc:	41 5e                	pop    %r14
    67ce:	41 5f                	pop    %r15
    67d0:	c3                   	ret
    67d1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
      receive(data);
    67d8:	e8 c3 fb ff ff       	call   63a0 <receive>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    67dd:	44 8b 93 40 01 00 00 	mov    0x140(%rbx),%r10d
    67e4:	45 85 d2             	test   %r10d,%r10d
    67e7:	0f 8e 40 05 00 00    	jle    6d2d <barriered_work+0x5cd>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    67ed:	48 63 c5             	movslq %ebp,%rax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    67f0:	31 f6                	xor    %esi,%esi
    67f2:	48 8b bb 28 01 00 00 	mov    0x128(%rbx),%rdi
    67f9:	89 6c 24 2c          	mov    %ebp,0x2c(%rsp)
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    67fd:	48 c1 e0 09          	shl    $0x9,%rax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6801:	48 89 f3             	mov    %rsi,%rbx
    6804:	45 31 ed             	xor    %r13d,%r13d
    6807:	48 89 c6             	mov    %rax,%rsi
    680a:	eb 18                	jmp    6824 <barriered_work+0xc4>
    680c:	0f 1f 40 00          	nopl   0x0(%rax)
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6810:	48 83 c3 01          	add    $0x1,%rbx
    6814:	49 81 c5 d0 00 00 00 	add    $0xd0,%r13
    681b:	41 39 da             	cmp    %ebx,%r10d
    681e:	0f 8e 64 02 00 00    	jle    6a88 <barriered_work+0x328>
              int b = data->thread->real_thread_index;
    6824:	48 63 57 08          	movslq 0x8(%rdi),%rdx
              if (y == b) { continue; }
    6828:	89 d9                	mov    %ebx,%ecx
    682a:	39 da                	cmp    %ebx,%edx
    682c:	74 e2                	je     6810 <barriered_work+0xb0>
                  if (b == data->thread->real_thread_index && data->thread->all_threads[b].tasks[t].mailboxes[y].kind == MAILBOX_FOREIGN) {
    682e:	4c 63 e2             	movslq %edx,%r12
    6831:	4c 8b 47 20          	mov    0x20(%rdi),%r8
    6835:	4b 8d 04 64          	lea    (%r12,%r12,2),%rax
    6839:	4d 8d 34 84          	lea    (%r12,%rax,4),%r14
    683d:	48 8d 04 dd 00 00 00 00 	lea    0x0(,%rbx,8),%rax
    6845:	49 c1 e6 04          	shl    $0x4,%r14
    6849:	48 29 d8             	sub    %rbx,%rax
    684c:	4f 8b 44 30 38       	mov    0x38(%r8,%r14,1),%r8
    6851:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
    6859:	4d 8b 84 30 70 01 00 00 	mov    0x170(%r8,%rsi,1),%r8
    6861:	41 83 7c c0 30 02    	cmpl   $0x2,0x30(%r8,%rax,8)
    6867:	75 a7                	jne    6810 <barriered_work+0xb0>
  if (a < b) { return a; }
    6869:	39 da                	cmp    %ebx,%edx
    686b:	0f 8c 87 04 00 00    	jl     6cf8 <barriered_work+0x598>
  if (b < a) { return b; }
    6871:	48 63 c3             	movslq %ebx,%rax
    6874:	4d 89 e7             	mov    %r12,%r15
    6877:	48 0f 4e c2          	cmovle %rdx,%rax
                    pthread_mutex_lock(&data->thread->swapmutex[min]);   
    687b:	48 8d 04 80          	lea    (%rax,%rax,4),%rax
    687f:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    6884:	48 c1 e0 03          	shl    $0x3,%rax
    6888:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    688d:	48 03 87 c8 00 00 00 	add    0xc8(%rdi),%rax
    6894:	48 89 c7             	mov    %rax,%rdi
    6897:	e8 24 bd ff ff       	call   25c0 <pthread_mutex_lock@plt>
                    pthread_mutex_lock(&data->thread->swapmutex[max]);   
    689c:	4b 8d 04 bf          	lea    (%r15,%r15,4),%rax
    68a0:	4c 8b 3c 24          	mov    (%rsp),%r15
    68a4:	48 8d 3c c5 00 00 00 00 	lea    0x0(,%rax,8),%rdi
    68ac:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    68b3:	48 89 7c 24 10       	mov    %rdi,0x10(%rsp)
    68b8:	48 03 b8 c8 00 00 00 	add    0xc8(%rax),%rdi
    68bf:	e8 fc bc ff ff       	call   25c0 <pthread_mutex_lock@plt>
                    for (int nn = 0; nn < data->thread_count; nn++) {
    68c4:	4c 89 f8             	mov    %r15,%rax
    68c7:	45 8b bf 34 01 00 00 	mov    0x134(%r15),%r15d
    68ce:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    68d3:	45 85 ff             	test   %r15d,%r15d
    68d6:	0f 8e 2a 04 00 00    	jle    6d06 <barriered_work+0x5a6>
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    68dc:	4c 8b 90 28 01 00 00 	mov    0x128(%rax),%r10
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    68e3:	4e 8d 04 e5 00 00 00 00 	lea    0x0(,%r12,8),%r8
                    for (int nn = 0; nn < data->thread_count; nn++) {
    68eb:	4c 89 64 24 18       	mov    %r12,0x18(%rsp)
    68f0:	31 c9                	xor    %ecx,%ecx
    68f2:	48 89 74 24 20       	mov    %rsi,0x20(%rsp)
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    68f7:	4d 29 e0             	sub    %r12,%r8
    68fa:	bf 70 01 00 00       	mov    $0x170,%edi
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    68ff:	49 8b 42 20          	mov    0x20(%r10),%rax
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6903:	49 c1 e0 03          	shl    $0x3,%r8
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6907:	4e 8b 5c 30 38       	mov    0x38(%rax,%r14,1),%r11
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    690c:	4e 8b 4c 28 38       	mov    0x38(%rax,%r13,1),%r9
    6911:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
                      int next_task = abs((nn + 1) % data->thread_count);
    6918:	83 c1 01             	add    $0x1,%ecx
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    691b:	49 8b 34 3b          	mov    (%r11,%rdi,1),%rsi
                      int next_task = abs((nn + 1) % data->thread_count);
    691f:	89 c8                	mov    %ecx,%eax
    6921:	99                   	cltd
                      struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6922:	48 01 ee             	add    %rbp,%rsi
                      int next_task = abs((nn + 1) % data->thread_count);
    6925:	41 f7 ff             	idiv   %r15d
    return mailbox->lower;
    6928:	4c 8b 26             	mov    (%rsi),%r12
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    692b:	48 63 d2             	movslq %edx,%rdx
    692e:	48 c1 e2 09          	shl    $0x9,%rdx
    6932:	49 8b 84 11 70 01 00 00 	mov    0x170(%r9,%rdx,1),%rax
    mailbox->lower = data;
    693a:	48 8b 56 08          	mov    0x8(%rsi),%rdx
                      struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    693e:	4c 01 c0             	add    %r8,%rax
    return mailbox->higher;
    6941:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    6945:	48 89 10             	mov    %rdx,(%rax)
    return mailbox->lower;
    6948:	66 0f 6f c8          	movdqa %xmm0,%xmm1
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    694c:	0f 12 d0             	movhlps %xmm0,%xmm2
    return mailbox->lower;
    694f:	66 0f c6 c8 01       	shufpd $0x1,%xmm0,%xmm1
    mailbox->lower = data;
    6954:	0f 11 0e             	movups %xmm1,(%rsi)
    mailbox->higher = data;
    6957:	4c 89 60 08          	mov    %r12,0x8(%rax)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    695b:	49 8b 14 39          	mov    (%r9,%rdi,1),%rdx
                    for (int nn = 0; nn < data->thread_count; nn++) {
    695f:	48 81 c7 00 02 00 00 	add    $0x200,%rdi
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6966:	48 8b 76 08          	mov    0x8(%rsi),%rsi
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    696a:	48 8b 00             	mov    (%rax),%rax
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    696d:	4a 8b 54 02 08       	mov    0x8(%rdx,%r8,1),%rdx
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_reading = 0;
    6972:	c7 86 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rsi)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_reading = 0;
    697c:	c7 82 00 02 00 00 00 00 00 00 	movl   $0x0,0x200(%rdx)
                           ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].higher)->available_receiving = 1;
    6986:	c7 86 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rsi)
                           ((struct Data*) data->thread->all_threads[t2].tasks[l3].mailboxes[t4].higher)->available_receiving = 1;
    6990:	c7 82 80 01 00 00 01 00 00 00 	movl   $0x1,0x180(%rdx)
                          ((struct Data*) data->thread->all_threads[l2].tasks[l3].mailboxes[l4].lower)->available_reading = 1;
    699a:	66 48 0f 7e d2       	movq   %xmm2,%rdx
    699f:	c7 82 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rdx)
                          ((struct Data*) data->thread->all_threads[t2].tasks[t3].mailboxes[t4].lower)->available_reading = 1;
    69a9:	c7 80 00 02 00 00 01 00 00 00 	movl   $0x1,0x200(%rax)
                    for (int nn = 0; nn < data->thread_count; nn++) {
    69b3:	44 39 f9             	cmp    %r15d,%ecx
    69b6:	0f 85 5c ff ff ff    	jne    6918 <barriered_work+0x1b8>
    69bc:	4c 8b 64 24 18       	mov    0x18(%rsp),%r12
    69c1:	48 8b 74 24 20       	mov    0x20(%rsp),%rsi
                    pthread_mutex_unlock(&data->thread->swapmutex[min]);
    69c6:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    69cb:	49 03 ba c8 00 00 00 	add    0xc8(%r10),%rdi
    69d2:	48 89 74 24 18       	mov    %rsi,0x18(%rsp)
    69d7:	e8 b4 ba ff ff       	call   2490 <pthread_mutex_unlock@plt>
                    pthread_mutex_unlock(&data->thread->swapmutex[max]);
    69dc:	4c 8b 3c 24          	mov    (%rsp),%r15
    69e0:	48 8b 7c 24 10       	mov    0x10(%rsp),%rdi
    69e5:	49 8b 87 28 01 00 00 	mov    0x128(%r15),%rax
    69ec:	48 03 b8 c8 00 00 00 	add    0xc8(%rax),%rdi
    69f3:	e8 98 ba ff ff       	call   2490 <pthread_mutex_unlock@plt>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    69f8:	49 63 87 34 01 00 00 	movslq 0x134(%r15),%rax
    69ff:	48 8b 74 24 18       	mov    0x18(%rsp),%rsi
    6a04:	85 c0                	test   %eax,%eax
    6a06:	0f 8e 0a 03 00 00    	jle    6d16 <barriered_work+0x5b6>
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6a0c:	48 8b 3c 24          	mov    (%rsp),%rdi
    6a10:	4e 8d 1c e5 00 00 00 00 	lea    0x0(,%r12,8),%r11
    6a18:	48 c1 e0 09          	shl    $0x9,%rax
    6a1c:	4d 29 e3             	sub    %r12,%r11
    6a1f:	4c 8d 80 70 01 00 00 	lea    0x170(%rax),%r8
    6a26:	b8 70 01 00 00       	mov    $0x170,%eax
    6a2b:	48 8b bf 28 01 00 00 	mov    0x128(%rdi),%rdi
    6a32:	49 c1 e3 03          	shl    $0x3,%r11
    6a36:	48 8b 57 20          	mov    0x20(%rdi),%rdx
    6a3a:	4e 8b 54 32 38       	mov    0x38(%rdx,%r14,1),%r10
    6a3f:	4e 8b 4c 2a 38       	mov    0x38(%rdx,%r13,1),%r9
    6a44:	0f 1f 40 00          	nopl   0x0(%rax)
    6a48:	49 8b 14 01          	mov    (%r9,%rax,1),%rdx
    6a4c:	49 8b 0c 02          	mov    (%r10,%rax,1),%rcx
    6a50:	4a 8b 14 1a          	mov    (%rdx,%r11,1),%rdx
    6a54:	48 39 14 29          	cmp    %rdx,(%rcx,%rbp,1)
    6a58:	0f 84 df 02 00 00    	je     6d3d <barriered_work+0x5dd>
                      for (int nn = 0; nn < data->thread_count; nn++) {
    6a5e:	48 05 00 02 00 00    	add    $0x200,%rax
    6a64:	49 39 c0             	cmp    %rax,%r8
    6a67:	75 df                	jne    6a48 <barriered_work+0x2e8>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6a69:	48 8b 04 24          	mov    (%rsp),%rax
    6a6d:	48 83 c3 01          	add    $0x1,%rbx
    6a71:	49 81 c5 d0 00 00 00 	add    $0xd0,%r13
    6a78:	44 8b 90 40 01 00 00 	mov    0x140(%rax),%r10d
    6a7f:	41 39 da             	cmp    %ebx,%r10d
    6a82:	0f 8f 9c fd ff ff    	jg     6824 <barriered_work+0xc4>
    6a88:	48 63 6c 24 2c       	movslq 0x2c(%rsp),%rbp
          int k = data->group;
    6a8d:	48 8b 04 24          	mov    (%rsp),%rax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6a91:	48 63 97 c4 00 00 00 	movslq 0xc4(%rdi),%rdx
          int k = data->group;
    6a98:	8b 80 94 01 00 00    	mov    0x194(%rax),%eax
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6a9e:	85 d2                	test   %edx,%edx
    6aa0:	0f 8e 41 01 00 00    	jle    6be7 <barriered_work+0x487>
            int y = (k * data->thread->threads_per_group) + d;
    6aa6:	0f af c2             	imul   %edx,%eax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6aa9:	48 c1 e5 09          	shl    $0x9,%rbp
              int next_task = abs((t + 1) % (data->thread_count));
    6aad:	48 8b 1c 24          	mov    (%rsp),%rbx
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6ab1:	49 89 ed             	mov    %rbp,%r13
    6ab4:	4c 89 6c 24 10       	mov    %r13,0x10(%rsp)
              int next_task = abs((t + 1) % (data->thread_count));
    6ab9:	44 8b 8b 34 01 00 00 	mov    0x134(%rbx),%r9d
    6ac0:	48 98                	cltq
    6ac2:	48 8d 0c 40          	lea    (%rax,%rax,2),%rcx
    6ac6:	48 8d 0c 88          	lea    (%rax,%rcx,4),%rcx
    6aca:	48 c1 e1 04          	shl    $0x4,%rcx
    6ace:	48 03 4f 20          	add    0x20(%rdi),%rcx
    6ad2:	49 89 ce             	mov    %rcx,%r14
    6ad5:	48 8d 0c c5 00 00 00 00 	lea    0x0(,%rax,8),%rcx
    6add:	48 29 c1             	sub    %rax,%rcx
    6ae0:	48 01 d0             	add    %rdx,%rax
              int kind = data->thread->all_threads[y].tasks[t].mailboxes[b].kind; 
    6ae3:	4d 89 f2             	mov    %r14,%r10
    6ae6:	4d 89 f7             	mov    %r14,%r15
    6ae9:	48 8d 2c c5 00 00 00 00 	lea    0x0(,%rax,8),%rbp
    6af1:	4c 8d 04 cd 00 00 00 00 	lea    0x0(,%rcx,8),%r8
    6af9:	48 29 c5             	sub    %rax,%rbp
    6afc:	4d 89 c3             	mov    %r8,%r11
    6aff:	4c 89 c3             	mov    %r8,%rbx
    6b02:	48 c1 e5 03          	shl    $0x3,%rbp
    6b06:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)
    6b10:	4d 8b 62 38          	mov    0x38(%r10),%r12
    6b14:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6b19:	48 89 de             	mov    %rbx,%rsi
    6b1c:	4c 89 ff             	mov    %r15,%rdi
    6b1f:	4d 89 d0             	mov    %r10,%r8
    6b22:	4d 8b b4 04 70 01 00 00 	mov    0x170(%r12,%rax,1),%r14
    6b2a:	eb 18                	jmp    6b44 <barriered_work+0x3e4>
    6b2c:	0f 1f 40 00          	nopl   0x0(%rax)
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6b30:	48 83 c6 38          	add    $0x38,%rsi
    6b34:	48 81 c7 d0 00 00 00 	add    $0xd0,%rdi
    6b3b:	48 39 ee             	cmp    %rbp,%rsi
    6b3e:	0f 84 8c 00 00 00    	je     6bd0 <barriered_work+0x470>
              if (kind == MAILBOX_FRIEND) {
    6b44:	41 83 7c 36 30 01    	cmpl   $0x1,0x30(%r14,%rsi,1)
    6b4a:	75 e4                	jne    6b30 <barriered_work+0x3d0>
                  int other = data->thread->all_threads[b].tasks[t].mailboxes[y].other;
    6b4c:	4c 8b 57 38          	mov    0x38(%rdi),%r10
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6b50:	45 85 c9             	test   %r9d,%r9d
    6b53:	7e db                	jle    6b30 <barriered_work+0x3d0>
    6b55:	4c 89 74 24 08       	mov    %r14,0x8(%rsp)
    6b5a:	49 81 c2 70 01 00 00 	add    $0x170,%r10
    6b61:	31 c9                	xor    %ecx,%ecx
    6b63:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
                    int next_task = abs((nn + 1) % (data->thread_count));
    6b68:	83 c1 01             	add    $0x1,%ecx
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6b6b:	4d 8b 2a             	mov    (%r10),%r13
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6b6e:	49 81 c2 00 02 00 00 	add    $0x200,%r10
                    int next_task = abs((nn + 1) % (data->thread_count));
    6b75:	89 c8                	mov    %ecx,%eax
    6b77:	99                   	cltd
                    struct Data* source = mailboxkind(&data->thread->all_threads[l2].tasks[l3].mailboxes[l4], HIGHER);
    6b78:	4d 01 dd             	add    %r11,%r13
                    int next_task = abs((nn + 1) % (data->thread_count));
    6b7b:	41 f7 f9             	idiv   %r9d
    return mailbox->lower;
    6b7e:	4d 8b 75 00          	mov    0x0(%r13),%r14
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6b82:	48 63 d2             	movslq %edx,%rdx
    6b85:	48 c1 e2 09          	shl    $0x9,%rdx
    6b89:	49 8b 84 14 70 01 00 00 	mov    0x170(%r12,%rdx,1),%rax
    mailbox->lower = data;
    6b91:	49 8b 55 08          	mov    0x8(%r13),%rdx
                    struct Data *dest = mailboxkind(&data->thread->all_threads[t2].tasks[t3].mailboxes[t4], LOWER);
    6b95:	48 01 f0             	add    %rsi,%rax
    return mailbox->higher;
    6b98:	f3 0f 6f 00          	movdqu (%rax),%xmm0
    mailbox->lower = data;
    6b9c:	48 89 10             	mov    %rdx,(%rax)
    return mailbox->lower;
    6b9f:	66 0f c6 c0 01       	shufpd $0x1,%xmm0,%xmm0
    mailbox->lower = data;
    6ba4:	41 0f 11 45 00       	movups %xmm0,0x0(%r13)
    mailbox->higher = data;
    6ba9:	4c 89 70 08          	mov    %r14,0x8(%rax)
                   for (int nn = 0 ; nn < data->thread_count; nn++) {
    6bad:	41 39 c9             	cmp    %ecx,%r9d
    6bb0:	75 b6                	jne    6b68 <barriered_work+0x408>
            for (int m = 0 ; m < data->thread->threads_per_group ; m++) {
    6bb2:	48 83 c6 38          	add    $0x38,%rsi
    6bb6:	4c 8b 74 24 08       	mov    0x8(%rsp),%r14
    6bbb:	48 81 c7 d0 00 00 00 	add    $0xd0,%rdi
    6bc2:	48 39 ee             	cmp    %rbp,%rsi
    6bc5:	0f 85 79 ff ff ff    	jne    6b44 <barriered_work+0x3e4>
    6bcb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6bd0:	4d 89 c2             	mov    %r8,%r10
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6bd3:	49 83 c3 38          	add    $0x38,%r11
    6bd7:	49 81 c2 d0 00 00 00 	add    $0xd0,%r10
    6bde:	49 39 eb             	cmp    %rbp,%r11
    6be1:	0f 85 29 ff ff ff    	jne    6b10 <barriered_work+0x3b0>
      receive(data);
    6be7:	48 8b 1c 24          	mov    (%rsp),%rbx
    6beb:	48 89 df             	mov    %rbx,%rdi
    6bee:	e8 ad f7 ff ff       	call   63a0 <receive>
      asm volatile ("sfence" ::: "memory");
    6bf3:	0f ae f8             	sfence
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].start);
    6bf6:	48 89 d8             	mov    %rbx,%rax
    6bf9:	48 8b 9b 60 01 00 00 	mov    0x160(%rbx),%rbx
    6c00:	31 ff                	xor    %edi,%edi
    6c02:	48 89 de             	mov    %rbx,%rsi
    6c05:	48 89 5c 24 08       	mov    %rbx,0x8(%rsp)
    6c0a:	48 89 c3             	mov    %rax,%rbx
    6c0d:	48 c1 e6 05          	shl    $0x5,%rsi
    6c11:	48 03 b0 50 01 00 00 	add    0x150(%rax),%rsi
    6c18:	e8 53 b7 ff ff       	call   2370 <clock_gettime@plt>
    int modcount = ++data->thread->protected_state->modcount;
    6c1d:	48 8b 83 28 01 00 00 	mov    0x128(%rbx),%rax
    6c24:	48 89 df             	mov    %rbx,%rdi
    6c27:	48 8b 2c 24          	mov    (%rsp),%rbp
    6c2b:	48 8b 50 48          	mov    0x48(%rax),%rdx
    6c2f:	8b 5a 10             	mov    0x10(%rdx),%ebx
    6c32:	83 c3 01             	add    $0x1,%ebx
    while (data->scheduled == 1) {
    6c35:	83 bf 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rdi)
    int modcount = ++data->thread->protected_state->modcount;
    6c3c:	89 5a 10             	mov    %ebx,0x10(%rdx)
    while (data->scheduled == 1) {
    6c3f:	74 0e                	je     6c4f <barriered_work+0x4ef>
    6c41:	eb 61                	jmp    6ca4 <barriered_work+0x544>
    6c43:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    if (modcount != data->thread->protected_state->modcount) {
    6c48:	48 8b 85 28 01 00 00 	mov    0x128(%rbp),%rax
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6c4f:	48 63 95 30 01 00 00 	movslq 0x130(%rbp),%rdx
    6c56:	48 8b 40 18          	mov    0x18(%rax),%rax
    6c5a:	48 63 7d 04          	movslq 0x4(%rbp),%rdi
      data->n++;
    6c5e:	48 83 85 08 01 00 00 01 	addq   $0x1,0x108(%rbp)
      data->protected(&data->thread->threads[data->thread_index]->tasks[data->task_index]);
    6c66:	48 8b 04 d0          	mov    (%rax,%rdx,8),%rax
    6c6a:	48 c1 e7 09          	shl    $0x9,%rdi
    6c6e:	48 03 78 38          	add    0x38(%rax),%rdi
    6c72:	ff 95 20 01 00 00    	call   *0x120(%rbp)
      asm volatile ("sfence" ::: "memory");
    6c78:	0f ae f8             	sfence
    while (data->scheduled == 1) {
    6c7b:	83 bd 4c 01 00 00 01 	cmpl   $0x1,0x14c(%rbp)
    6c82:	74 c4                	je     6c48 <barriered_work+0x4e8>
    if (modcount != data->thread->protected_state->modcount) {
    6c84:	48 8b 04 24          	mov    (%rsp),%rax
    6c88:	48 8b 80 28 01 00 00 	mov    0x128(%rax),%rax
    6c8f:	48 8b 40 48          	mov    0x48(%rax),%rax
    6c93:	3b 58 10             	cmp    0x10(%rax),%ebx
    6c96:	74 0c                	je     6ca4 <barriered_work+0x544>
    6c98:	48 8d 3d a7 15 00 00 	lea    0x15a7(%rip),%rdi        # 8246 <_IO_stdin_used+0x246>
    6c9f:	e8 ac b6 ff ff       	call   2350 <puts@plt>
    clock_gettime(CLOCK_REALTIME, &data->snapshots[data->current_snapshot].end);
    6ca4:	48 8b 1c 24          	mov    (%rsp),%rbx
    6ca8:	31 ff                	xor    %edi,%edi
    6caa:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    6cb1:	48 89 c6             	mov    %rax,%rsi
    6cb4:	48 89 04 24          	mov    %rax,(%rsp)
    6cb8:	48 c1 e6 05          	shl    $0x5,%rsi
    6cbc:	48 03 b3 50 01 00 00 	add    0x150(%rbx),%rsi
    6cc3:	48 83 c6 10          	add    $0x10,%rsi
    6cc7:	e8 a4 b6 ff ff       	call   2370 <clock_gettime@plt>
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6ccc:	48 8b 83 60 01 00 00 	mov    0x160(%rbx),%rax
    sendm(data);
    6cd3:	48 89 df             	mov    %rbx,%rdi
    data->current_snapshot = ((data->current_snapshot + 1) % data->snapshot_count);
    6cd6:	48 89 04 24          	mov    %rax,(%rsp)
    6cda:	48 83 c0 01          	add    $0x1,%rax
    6cde:	48 99                	cqto
    6ce0:	48 f7 bb 58 01 00 00 	idivq  0x158(%rbx)
    6ce7:	48 89 93 60 01 00 00 	mov    %rdx,0x160(%rbx)
    sendm(data);
    6cee:	e8 1d f8 ff ff       	call   6510 <sendm>
    6cf3:	e9 c5 fa ff ff       	jmp    67bd <barriered_work+0x5d>
  if (b > a) { return b; }
    6cf8:	0f 4d ca             	cmovge %edx,%ecx
    6cfb:	4c 89 e0             	mov    %r12,%rax
                    pthread_mutex_lock(&data->thread->swapmutex[max]);   
    6cfe:	4c 63 f9             	movslq %ecx,%r15
    6d01:	e9 75 fb ff ff       	jmp    687b <barriered_work+0x11b>
                    pthread_mutex_unlock(&data->thread->swapmutex[min]);
    6d06:	48 8b 04 24          	mov    (%rsp),%rax
    6d0a:	4c 8b 90 28 01 00 00 	mov    0x128(%rax),%r10
    6d11:	e9 b0 fc ff ff       	jmp    69c6 <barriered_work+0x266>
        for (int y = 0; y < data->mailbox_thread_count ; y++) {
    6d16:	48 8b 04 24          	mov    (%rsp),%rax
    6d1a:	44 8b 90 40 01 00 00 	mov    0x140(%rax),%r10d
                        if (data->thread->all_threads[b].tasks[nn].mailboxes[y].lower == data->thread->all_threads[y].tasks[nn].mailboxes[b].lower) {
    6d21:	48 8b b8 28 01 00 00 	mov    0x128(%rax),%rdi
    6d28:	e9 e3 fa ff ff       	jmp    6810 <barriered_work+0xb0>
          for (int d = 0 ; d < data->thread->threads_per_group ; d++) {
    6d2d:	48 8b 04 24          	mov    (%rsp),%rax
    6d31:	48 8b b8 28 01 00 00 	mov    0x128(%rax),%rdi
    6d38:	e9 50 fd ff ff       	jmp    6a8d <barriered_work+0x32d>
    6d3d:	bf 01 00 00 00       	mov    $0x1,%edi
    6d42:	48 8d 35 e2 14 00 00 	lea    0x14e2(%rip),%rsi        # 822b <_IO_stdin_used+0x22b>
    6d49:	31 c0                	xor    %eax,%eax
    6d4b:	e8 90 b7 ff ff       	call   24e0 <__printf_chk@plt>
                          exit(1);
    6d50:	bf 01 00 00 00       	mov    $0x1,%edi
    6d55:	e8 e6 b7 ff ff       	call   2540 <exit@plt>
    6d5a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000006d60 <barriered_work_ingest_andwork>:
int barriered_work_ingest_andwork(struct BarrierTask *data) {
    6d60:	f3 0f 1e fa          	endbr64
    6d64:	53                   	push   %rbx
    6d65:	48 89 fb             	mov    %rdi,%rbx
  barriered_work_ingest(data);
    6d68:	e8 43 f2 ff ff       	call   5fb0 <barriered_work_ingest>
  barriered_work(data);
    6d6d:	48 89 df             	mov    %rbx,%rdi
}
    6d70:	5b                   	pop    %rbx
  barriered_work(data);
    6d71:	e9 ea f9 ff ff       	jmp    6760 <barriered_work>
    6d76:	66 2e 0f 1f 84 00 00 00 00 00 	cs nopw 0x0(%rax,%rax,1)

0000000000006d80 <mailboxkind>:
struct Data * mailboxkind(struct Mailbox * mailbox, int kind) {
    6d80:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6d84:	85 f6                	test   %esi,%esi
    6d86:	74 10                	je     6d98 <mailboxkind+0x18>
  return NULL;
    6d88:	31 c0                	xor    %eax,%eax
  else if (kind == 1) {
    6d8a:	83 fe 01             	cmp    $0x1,%esi
    6d8d:	74 01                	je     6d90 <mailboxkind+0x10>
}
    6d8f:	c3                   	ret
    return mailbox->higher;
    6d90:	48 8b 47 08          	mov    0x8(%rdi),%rax
}
    6d94:	c3                   	ret
    6d95:	0f 1f 00             	nopl   (%rax)
    return mailbox->lower;
    6d98:	48 8b 07             	mov    (%rdi),%rax
    6d9b:	c3                   	ret
    6d9c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000006da0 <setmailboxkind>:
int setmailboxkind(struct Mailbox * mailbox, struct Data* data, int kind) {
    6da0:	f3 0f 1e fa          	endbr64
  if (kind == 0) {
    6da4:	85 d2                	test   %edx,%edx
    6da6:	75 08                	jne    6db0 <setmailboxkind+0x10>
    mailbox->lower = data;
    6da8:	48 89 37             	mov    %rsi,(%rdi)
}
    6dab:	31 c0                	xor    %eax,%eax
    6dad:	c3                   	ret
    6dae:	66 90                	xchg   %ax,%ax
  if (kind == 1) {
    6db0:	83 fa 01             	cmp    $0x1,%edx
    6db3:	74 13                	je     6dc8 <setmailboxkind+0x28>
  if (kind == 2) {
    6db5:	83 fa 02             	cmp    $0x2,%edx
    6db8:	75 f1                	jne    6dab <setmailboxkind+0xb>
    mailbox->pending = data;
    6dba:	48 89 77 10          	mov    %rsi,0x10(%rdi)
}
    6dbe:	31 c0                	xor    %eax,%eax
    6dc0:	c3                   	ret
    6dc1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    mailbox->higher = data;
    6dc8:	48 89 77 08          	mov    %rsi,0x8(%rdi)
}
    6dcc:	31 c0                	xor    %eax,%eax
    6dce:	c3                   	ret
    6dcf:	90                   	nop

0000000000006dd0 <barriered_nulltask>:
int barriered_nulltask(struct BarrierTask *data) {
    6dd0:	f3 0f 1e fa          	endbr64
}
    6dd4:	31 c0                	xor    %eax,%eax
    6dd6:	c3                   	ret
    6dd7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006de0 <barriered_steal>:
int barriered_steal(struct BarrierTask *data) {
    6de0:	f3 0f 1e fa          	endbr64
    6de4:	31 c0                	xor    %eax,%eax
    6de6:	c3                   	ret
    6de7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)

0000000000006df0 <after>:
int after(struct timespec left, struct timespec right) {
    6df0:	f3 0f 1e fa          	endbr64
  return left.tv_sec > right.tv_sec &&
    6df4:	31 c0                	xor    %eax,%eax
    6df6:	48 39 d7             	cmp    %rdx,%rdi
    6df9:	7e 08                	jle    6e03 <after+0x13>
    6dfb:	31 c0                	xor    %eax,%eax
    6dfd:	48 39 ce             	cmp    %rcx,%rsi
    6e00:	0f 9f c0             	setg   %al
}
    6e03:	c3                   	ret
    6e04:	66 66 2e 0f 1f 84 00 00 00 00 00 	data16 cs nopw 0x0(%rax,%rax,1)
    6e0f:	90                   	nop

0000000000006e10 <within>:
int within(struct timespec a, struct timespec b, struct timespec c, struct timespec d) {
    6e10:	f3 0f 1e fa          	endbr64
    6e14:	4c 8b 5c 24 08       	mov    0x8(%rsp),%r11
    6e19:	4c 8b 54 24 10       	mov    0x10(%rsp),%r10
  return 0;
    6e1e:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6e20:	48 39 d7             	cmp    %rdx,%rdi
    6e23:	7f 18                	jg     6e3d <within+0x2d>
    6e25:	4d 39 d8             	cmp    %r11,%r8
    6e28:	0f 9e c2             	setle  %dl
    6e2b:	48 39 ce             	cmp    %rcx,%rsi
    6e2e:	0f 9e c0             	setle  %al
    6e31:	21 c2                	and    %eax,%edx
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6e33:	31 c0                	xor    %eax,%eax
    6e35:	4d 39 d1             	cmp    %r10,%r9
    6e38:	0f 9e c0             	setle  %al
    6e3b:	21 d0                	and    %edx,%eax
}
    6e3d:	c3                   	ret
    6e3e:	66 90                	xchg   %ax,%ax

0000000000006e40 <overlap>:
int overlap(struct Snapshot left, struct Snapshot right) {
    6e40:	f3 0f 1e fa          	endbr64
    6e44:	48 8b 7c 24 08       	mov    0x8(%rsp),%rdi
    6e49:	48 8b 74 24 28       	mov    0x28(%rsp),%rsi
    6e4e:	4c 8b 4c 24 18       	mov    0x18(%rsp),%r9
    6e53:	4c 8b 54 24 20       	mov    0x20(%rsp),%r10
    6e58:	4c 8b 44 24 38       	mov    0x38(%rsp),%r8
    6e5d:	4c 8b 5c 24 40       	mov    0x40(%rsp),%r11
  if (after(left.start, right.start) && after(right.end, left.end)) {
    6e62:	48 8b 4c 24 10       	mov    0x10(%rsp),%rcx
    6e67:	48 8b 54 24 30       	mov    0x30(%rsp),%rdx
  return left.tv_sec > right.tv_sec &&
    6e6c:	48 39 fe             	cmp    %rdi,%rsi
    6e6f:	7d 2f                	jge    6ea0 <overlap+0x60>
    6e71:	48 39 ca             	cmp    %rcx,%rdx
    6e74:	7d 62                	jge    6ed8 <overlap+0x98>
    6e76:	4d 39 da             	cmp    %r11,%r10
    6e79:	7d 0e                	jge    6e89 <overlap+0x49>
    return 1;
    6e7b:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6e80:	4d 39 c1             	cmp    %r8,%r9
    6e83:	0f 8c 7f 00 00 00    	jl     6f08 <overlap+0xc8>
  return 0;
    6e89:	31 c0                	xor    %eax,%eax
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6e8b:	4d 39 c1             	cmp    %r8,%r9
    6e8e:	7f 4c                	jg     6edc <overlap+0x9c>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6e90:	31 c0                	xor    %eax,%eax
    6e92:	4d 39 da             	cmp    %r11,%r10
    6e95:	0f 9e c0             	setle  %al
    6e98:	c3                   	ret
    6e99:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    6ea0:	7e 4e                	jle    6ef0 <overlap+0xb0>
    6ea2:	48 39 ca             	cmp    %rcx,%rdx
    6ea5:	7f 39                	jg     6ee0 <overlap+0xa0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6ea7:	75 31                	jne    6eda <overlap+0x9a>
    6ea9:	4d 39 c1             	cmp    %r8,%r9
    6eac:	7c 2c                	jl     6eda <overlap+0x9a>
    return 1;
    6eae:	b8 01 00 00 00       	mov    $0x1,%eax
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    6eb3:	4d 39 da             	cmp    %r11,%r10
    6eb6:	7d 24                	jge    6edc <overlap+0x9c>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6eb8:	48 39 ca             	cmp    %rcx,%rdx
    6ebb:	0f 94 c2             	sete   %dl
    6ebe:	48 39 fe             	cmp    %rdi,%rsi
    6ec1:	0f 94 c0             	sete   %al
    6ec4:	21 c2                	and    %eax,%edx
    6ec6:	31 c0                	xor    %eax,%eax
    6ec8:	4d 39 c1             	cmp    %r8,%r9
    6ecb:	0f 94 c0             	sete   %al
    6ece:	21 d0                	and    %edx,%eax
    6ed0:	c3                   	ret
    6ed1:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6ed8:	74 af                	je     6e89 <overlap+0x49>
  return 0;
    6eda:	31 c0                	xor    %eax,%eax
}
    6edc:	c3                   	ret
    6edd:	0f 1f 00             	nopl   (%rax)
  return left.tv_sec > right.tv_sec &&
    6ee0:	4d 39 da             	cmp    %r11,%r10
    6ee3:	7e c4                	jle    6ea9 <overlap+0x69>
    return 1;
    6ee5:	b8 01 00 00 00       	mov    $0x1,%eax
  return left.tv_sec > right.tv_sec &&
    6eea:	4d 39 c1             	cmp    %r8,%r9
    6eed:	7e ba                	jle    6ea9 <overlap+0x69>
    6eef:	c3                   	ret
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    6ef0:	48 39 ca             	cmp    %rcx,%rdx
    6ef3:	7c 94                	jl     6e89 <overlap+0x49>
    6ef5:	4d 39 c1             	cmp    %r8,%r9
    6ef8:	7d b4                	jge    6eae <overlap+0x6e>
    6efa:	48 39 ca             	cmp    %rcx,%rdx
    6efd:	74 91                	je     6e90 <overlap+0x50>
    6eff:	eb d9                	jmp    6eda <overlap+0x9a>
    6f01:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)
    6f08:	c3                   	ret
    6f09:	0f 1f 80 00 00 00 00 	nopl   0x0(%rax)

0000000000006f10 <verify>:
int verify(struct KernelThread *thread_data, int thread_count) {
    6f10:	f3 0f 1e fa          	endbr64
  for (int x = 0 ; x < thread_count; x++) {
    6f14:	85 f6                	test   %esi,%esi
    6f16:	0f 8e 44 03 00 00    	jle    7260 <verify+0x350>
int verify(struct KernelThread *thread_data, int thread_count) {
    6f1c:	41 57                	push   %r15
    6f1e:	41 89 f7             	mov    %esi,%r15d
    6f21:	41 56                	push   %r14
  for (int x = 0 ; x < thread_count; x++) {
    6f23:	45 31 f6             	xor    %r14d,%r14d
int verify(struct KernelThread *thread_data, int thread_count) {
    6f26:	41 55                	push   %r13
    6f28:	41 54                	push   %r12
    6f2a:	55                   	push   %rbp
    6f2b:	53                   	push   %rbx
    6f2c:	48 8d 5f 38          	lea    0x38(%rdi),%rbx
    6f30:	48 83 ec 58          	sub    $0x58,%rsp
  for (int x = 0 ; x < thread_count; x++) {
    6f34:	48 89 5c 24 18       	mov    %rbx,0x18(%rsp)
    for (int z = 0 ; z < thread_count; z++) {
    6f39:	48 89 5c 24 10       	mov    %rbx,0x10(%rsp)
    6f3e:	45 31 e4             	xor    %r12d,%r12d
      if (z != x)  {
    6f41:	45 39 e6             	cmp    %r12d,%r14d
    6f44:	0f 84 4e 02 00 00    	je     7198 <verify+0x288>
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    6f4a:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6f4f:	8b 50 08             	mov    0x8(%rax),%edx
    6f52:	85 d2                	test   %edx,%edx
    6f54:	0f 8e 3e 02 00 00    	jle    7198 <verify+0x288>
    6f5a:	48 89 5c 24 30       	mov    %rbx,0x30(%rsp)
    6f5f:	31 c9                	xor    %ecx,%ecx
    6f61:	44 89 64 24 3c       	mov    %r12d,0x3c(%rsp)
    6f66:	31 c0                	xor    %eax,%eax
    6f68:	44 89 f2             	mov    %r14d,%edx
    6f6b:	bf 01 00 00 00       	mov    $0x1,%edi
    6f70:	48 89 4c 24 08       	mov    %rcx,0x8(%rsp)
    6f75:	48 8d 35 da 12 00 00 	lea    0x12da(%rip),%rsi        # 8256 <_IO_stdin_used+0x256>
    6f7c:	e8 5f b5 ff ff       	call   24e0 <__printf_chk@plt>
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    6f81:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    6f86:	48 8b 4c 24 08       	mov    0x8(%rsp),%rcx
    6f8b:	8b 40 08             	mov    0x8(%rax),%eax
    6f8e:	85 c0                	test   %eax,%eax
    6f90:	0f 8e e6 01 00 00    	jle    717c <verify+0x26c>
    6f96:	48 89 c8             	mov    %rcx,%rax
            printf("%ld %ld\n", thread_data[z].tasks[k].current_snapshot, thread_data[x].tasks[y].current_snapshot);
    6f99:	48 89 4c 24 40       	mov    %rcx,0x40(%rsp)
    6f9e:	31 db                	xor    %ebx,%ebx
    6fa0:	48 c1 e0 09          	shl    $0x9,%rax
    6fa4:	44 89 74 24 48       	mov    %r14d,0x48(%rsp)
    6fa9:	48 89 44 24 08       	mov    %rax,0x8(%rsp)
    6fae:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    6fb3:	44 89 7c 24 4c       	mov    %r15d,0x4c(%rsp)
    6fb8:	4c 8b 20             	mov    (%rax),%r12
    6fbb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    6fc0:	48 8b 6c 24 10       	mov    0x10(%rsp),%rbp
    6fc5:	4c 8b 7c 24 08       	mov    0x8(%rsp),%r15
    6fca:	49 89 de             	mov    %rbx,%r14
    6fcd:	48 8d 35 97 12 00 00 	lea    0x1297(%rip),%rsi        # 826b <_IO_stdin_used+0x26b>
    6fd4:	49 c1 e6 09          	shl    $0x9,%r14
    6fd8:	bf 01 00 00 00       	mov    $0x1,%edi
    6fdd:	48 8b 45 00          	mov    0x0(%rbp),%rax
    6fe1:	4b 8b 8c 3c 60 01 00 00 	mov    0x160(%r12,%r15,1),%rcx
    6fe9:	4c 89 74 24 20       	mov    %r14,0x20(%rsp)
    6fee:	4a 8b 94 30 60 01 00 00 	mov    0x160(%rax,%r14,1),%rdx
    6ff6:	31 c0                	xor    %eax,%eax
    6ff8:	e8 e3 b4 ff ff       	call   24e0 <__printf_chk@plt>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    6ffd:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7002:	4c 8b 20             	mov    (%rax),%r12
    7005:	4b 83 bc 3c 60 01 00 00 00 	cmpq   $0x0,0x160(%r12,%r15,1)
    700e:	0f 8e 47 01 00 00    	jle    715b <verify+0x24b>
    7014:	4c 03 75 00          	add    0x0(%rbp),%r14
    7018:	48 89 5c 24 28       	mov    %rbx,0x28(%rsp)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    701d:	ba 01 00 00 00       	mov    $0x1,%edx
    7022:	4d 89 f5             	mov    %r14,%r13
    7025:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    702c:	4d 85 f6             	test   %r14,%r14
    702f:	0f 8e 21 01 00 00    	jle    7156 <verify+0x246>
    7035:	0f 1f 00             	nopl   (%rax)
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    7038:	48 89 d5             	mov    %rdx,%rbp
    703b:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7040:	31 db                	xor    %ebx,%ebx
    7042:	4d 89 f2             	mov    %r14,%r10
    7045:	48 c1 e5 05          	shl    $0x5,%rbp
    7049:	48 83 ed 20          	sub    $0x20,%rbp
    704d:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
    7051:	49 89 ee             	mov    %rbp,%r14
    7054:	48 89 dd             	mov    %rbx,%rbp
    7057:	48 89 d3             	mov    %rdx,%rbx
    705a:	eb 31                	jmp    708d <verify+0x17d>
    705c:	0f 1f 40 00          	nopl   0x0(%rax)
  return left.tv_sec > right.tv_sec &&
    7060:	4c 39 c2             	cmp    %r8,%rdx
    7063:	0f 8d 57 01 00 00    	jge    71c0 <verify+0x2b0>
    7069:	4c 39 df             	cmp    %r11,%rdi
    706c:	7e 05                	jle    7073 <verify+0x163>
    706e:	49 39 c1             	cmp    %rax,%r9
    7071:	7c 75                	jl     70e8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    7073:	4c 39 df             	cmp    %r11,%rdi
    7076:	0f 8d ab 01 00 00    	jge    7227 <verify+0x317>
    707c:	0f 1f 40 00          	nopl   0x0(%rax)
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7080:	48 83 c5 01          	add    $0x1,%rbp
    7084:	49 39 ea             	cmp    %rbp,%r10
    7087:	0f 8e a9 00 00 00    	jle    7136 <verify+0x226>
                if (overlap(thread_data[x].tasks[y].snapshots[n], thread_data[z].tasks[k].snapshots[m]) == 1) {
    708d:	49 8b 97 50 01 00 00 	mov    0x150(%r15),%rdx
    7094:	48 89 e8             	mov    %rbp,%rax
    7097:	48 c1 e0 05          	shl    $0x5,%rax
    709b:	49 03 85 50 01 00 00 	add    0x150(%r13),%rax
    70a2:	4c 01 f2             	add    %r14,%rdx
    70a5:	48 8b 08             	mov    (%rax),%rcx
    70a8:	48 8b 78 10          	mov    0x10(%rax),%rdi
    70ac:	48 8b 32             	mov    (%rdx),%rsi
    70af:	4c 8b 42 08          	mov    0x8(%rdx),%r8
    70b3:	4c 8b 5a 10          	mov    0x10(%rdx),%r11
    70b7:	4c 8b 4a 18          	mov    0x18(%rdx),%r9
    70bb:	48 8b 50 08          	mov    0x8(%rax),%rdx
    70bf:	48 8b 40 18          	mov    0x18(%rax),%rax
  return left.tv_sec > right.tv_sec &&
    70c3:	48 39 f1             	cmp    %rsi,%rcx
    70c6:	7c 98                	jl     7060 <verify+0x150>
    70c8:	0f 8e 42 01 00 00    	jle    7210 <verify+0x300>
    70ce:	4c 39 c2             	cmp    %r8,%rdx
    70d1:	0f 8f f9 00 00 00    	jg     71d0 <verify+0x2c0>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    70d7:	75 a7                	jne    7080 <verify+0x170>
    70d9:	4c 39 df             	cmp    %r11,%rdi
    70dc:	7f a2                	jg     7080 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    70de:	49 39 c1             	cmp    %rax,%r9
    70e1:	7c 9d                	jl     7080 <verify+0x170>
    70e3:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
    70e8:	49 89 c1             	mov    %rax,%r9
    70eb:	48 89 f9             	mov    %rdi,%rcx
    70ee:	48 89 f2             	mov    %rsi,%rdx
    70f1:	bf 01 00 00 00       	mov    $0x1,%edi
    70f6:	48 8d 35 33 15 00 00 	lea    0x1533(%rip),%rsi        # 8630 <_IO_stdin_used+0x630>
    70fd:	31 c0                	xor    %eax,%eax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    70ff:	48 83 c5 01          	add    $0x1,%rbp
    7103:	e8 d8 b3 ff ff       	call   24e0 <__printf_chk@plt>
    7108:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    710d:	4c 8b 6c 24 20       	mov    0x20(%rsp),%r13
    7112:	4c 03 28             	add    (%rax),%r13
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7115:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    711a:	4d 8b 95 60 01 00 00 	mov    0x160(%r13),%r10
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7121:	4c 8b 20             	mov    (%rax),%r12
    7124:	48 8b 44 24 08       	mov    0x8(%rsp),%rax
    7129:	4d 8d 3c 04          	lea    (%r12,%rax,1),%r15
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    712d:	49 39 ea             	cmp    %rbp,%r10
    7130:	0f 8f 57 ff ff ff    	jg     708d <verify+0x17d>
            for (int n = 0 ; n < thread_data[x].tasks[y].current_snapshot ; n++) {
    7136:	48 89 da             	mov    %rbx,%rdx
    7139:	49 3b 9f 60 01 00 00 	cmp    0x160(%r15),%rbx
    7140:	7d 14                	jge    7156 <verify+0x246>
              for (int m = 0 ; m < thread_data[z].tasks[k].current_snapshot ; m++) {
    7142:	4d 8b b5 60 01 00 00 	mov    0x160(%r13),%r14
    7149:	48 83 c2 01          	add    $0x1,%rdx
    714d:	4d 85 f6             	test   %r14,%r14
    7150:	0f 8f e2 fe ff ff    	jg     7038 <verify+0x128>
    7156:	48 8b 5c 24 28       	mov    0x28(%rsp),%rbx
          for (int k = 0 ; k < thread_data[z].task_count; k++) {
    715b:	48 8b 44 24 10       	mov    0x10(%rsp),%rax
    7160:	48 83 c3 01          	add    $0x1,%rbx
    7164:	39 58 08             	cmp    %ebx,0x8(%rax)
    7167:	0f 8f 53 fe ff ff    	jg     6fc0 <verify+0xb0>
    716d:	48 8b 4c 24 40       	mov    0x40(%rsp),%rcx
    7172:	44 8b 74 24 48       	mov    0x48(%rsp),%r14d
    7177:	44 8b 7c 24 4c       	mov    0x4c(%rsp),%r15d
        for (int y = 0 ; y < thread_data[x].task_count ; y++) {
    717c:	48 8b 44 24 18       	mov    0x18(%rsp),%rax
    7181:	48 83 c1 01          	add    $0x1,%rcx
    7185:	39 48 08             	cmp    %ecx,0x8(%rax)
    7188:	0f 8f d8 fd ff ff    	jg     6f66 <verify+0x56>
    718e:	48 8b 5c 24 30       	mov    0x30(%rsp),%rbx
    7193:	44 8b 64 24 3c       	mov    0x3c(%rsp),%r12d
    for (int z = 0 ; z < thread_count; z++) {
    7198:	48 81 44 24 10 d0 00 00 00 	addq   $0xd0,0x10(%rsp)
    71a1:	41 8d 44 24 01       	lea    0x1(%r12),%eax
    71a6:	41 39 c7             	cmp    %eax,%r15d
    71a9:	0f 84 86 00 00 00    	je     7235 <verify+0x325>
    71af:	41 89 c4             	mov    %eax,%r12d
    71b2:	e9 8a fd ff ff       	jmp    6f41 <verify+0x31>
    71b7:	66 0f 1f 84 00 00 00 00 00 	nopw   0x0(%rax,%rax,1)
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71c0:	0f 85 ba fe ff ff    	jne    7080 <verify+0x170>
    71c6:	e9 a8 fe ff ff       	jmp    7073 <verify+0x163>
    71cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  return left.tv_sec > right.tv_sec &&
    71d0:	49 39 c1             	cmp    %rax,%r9
    71d3:	7e 09                	jle    71de <verify+0x2ce>
    71d5:	4c 39 df             	cmp    %r11,%rdi
    71d8:	0f 8c 0a ff ff ff    	jl     70e8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71de:	4c 39 df             	cmp    %r11,%rdi
    71e1:	0f 8f 99 fe ff ff    	jg     7080 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    71e7:	49 39 c1             	cmp    %rax,%r9
    71ea:	0f 8d f8 fe ff ff    	jge    70e8 <verify+0x1d8>
  if (a.tv_sec <= b.tv_sec && a.tv_nsec <= b.tv_nsec &&
    71f0:	48 39 f1             	cmp    %rsi,%rcx
    71f3:	0f 85 87 fe ff ff    	jne    7080 <verify+0x170>
    71f9:	4c 39 c2             	cmp    %r8,%rdx
    71fc:	0f 85 7e fe ff ff    	jne    7080 <verify+0x170>
    7202:	4c 39 df             	cmp    %r11,%rdi
    7205:	0f 84 dd fe ff ff    	je     70e8 <verify+0x1d8>
    720b:	e9 70 fe ff ff       	jmp    7080 <verify+0x170>
    7210:	4c 39 c2             	cmp    %r8,%rdx
    7213:	0f 8c 5a fe ff ff    	jl     7073 <verify+0x163>
    7219:	4c 39 df             	cmp    %r11,%rdi
    721c:	7e c9                	jle    71e7 <verify+0x2d7>
    721e:	4c 39 c2             	cmp    %r8,%rdx
    7221:	0f 85 59 fe ff ff    	jne    7080 <verify+0x170>
   c.tv_sec <= d.tv_sec && c.tv_nsec <= d.tv_nsec && d.tv_sec >= c.tv_sec && d.tv_nsec >= c.tv_nsec) {
    7227:	49 39 c1             	cmp    %rax,%r9
    722a:	0f 8f 50 fe ff ff    	jg     7080 <verify+0x170>
    7230:	e9 b3 fe ff ff       	jmp    70e8 <verify+0x1d8>
  for (int x = 0 ; x < thread_count; x++) {
    7235:	48 81 44 24 18 d0 00 00 00 	addq   $0xd0,0x18(%rsp)
    723e:	41 8d 46 01          	lea    0x1(%r14),%eax
    7242:	45 39 e6             	cmp    %r12d,%r14d
    7245:	74 08                	je     724f <verify+0x33f>
    7247:	41 89 c6             	mov    %eax,%r14d
    724a:	e9 ea fc ff ff       	jmp    6f39 <verify+0x29>
}
    724f:	48 83 c4 58          	add    $0x58,%rsp
    7253:	31 c0                	xor    %eax,%eax
    7255:	5b                   	pop    %rbx
    7256:	5d                   	pop    %rbp
    7257:	41 5c                	pop    %r12
    7259:	41 5d                	pop    %r13
    725b:	41 5e                	pop    %r14
    725d:	41 5f                	pop    %r15
    725f:	c3                   	ret
    7260:	31 c0                	xor    %eax,%eax
    7262:	c3                   	ret

Disassembly of section .fini:

0000000000007264 <_fini>:
    7264:	f3 0f 1e fa          	endbr64
    7268:	48 83 ec 08          	sub    $0x8,%rsp
    726c:	48 83 c4 08          	add    $0x8,%rsp
    7270:	c3                   	ret
